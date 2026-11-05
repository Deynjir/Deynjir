import os
import re
import json
import csv
import hmac
from zoneinfo import ZoneInfo
import difflib
import unicodedata
from fastapi import FastAPI, Request
from supabase import create_client, Client
import requests
from dotenv import load_dotenv
from datetime import datetime, timedelta, timezone
import pandas as pd
from io import BytesIO, StringIO
from xml.sax.saxutils import escape

from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.lib import colors

load_dotenv()

APP_NAME = "Deynjir"

EAT = ZoneInfo("Africa/Mogadishu")

def now_eat():
    return datetime.now(EAT)

def today_eat():
    return now_eat().date()

# Setup the core application framework
app = FastAPI()

# Remembers the most recent customer statement so the user can request its PDF
# by sending "PDF" as a follow-up WhatsApp message. Cleared on server restart.
LAST_HISTORY_REQUESTS = {}

# Temporary manual reminder workflow. Sessions expire after 15 minutes and are
# cleared before sending so a repeated "HAA DIR" cannot resend the same batch.
REMINDER_SESSIONS = {}
REMINDER_SESSION_TTL = timedelta(minutes=15)
# Admin-assisted imports are staged for preview and explicit confirmation.
IMPORT_SESSIONS = {}
IMPORT_SESSION_TTL = timedelta(minutes=30)
DEFAULT_COUNTRY_CODE = re.sub(r"\D", "", os.getenv("DEFAULT_COUNTRY_CODE", ""))


def normalize_reminder_phone(raw_phone):
    """Return a Green-API-ready international number, or None if ambiguous."""
    if not raw_phone:
        return None
    raw = str(raw_phone).strip()
    digits = re.sub(r"\D", "", raw)
    if raw.startswith("00") and digits.startswith("00"):
        digits = digits[2:]
    elif raw.startswith("+"):
        pass
    elif digits.startswith("0") and DEFAULT_COUNTRY_CODE:
        digits = DEFAULT_COUNTRY_CODE + digits.lstrip("0")
    elif len(digits) < 10 and DEFAULT_COUNTRY_CODE:
        digits = DEFAULT_COUNTRY_CODE + digits
    # Without a configured default country code, short/local numbers are
    # excluded rather than risking sending a reminder to the wrong person.
    if not (10 <= len(digits) <= 15):
        return None
    return digits


def is_reminder_start_command(text):
    return bool(re.fullmatch(
        r"\s*(?:xusuusin|xusuusi|xasuusin|remind|remind customers|payment reminders)\s*[.!]?\s*",
        str(text or ""),
        flags=re.IGNORECASE,
    ))


def is_reminder_cancel_command(text):
    return bool(re.fullmatch(
        r"\s*(?:jooji|jooji xusuusinta|cancel|stop)\s*[.!]?\s*",
        str(text or ""),
        flags=re.IGNORECASE,
    ))


def is_reminder_confirm_command(text):
    return bool(re.fullmatch(
        r"\s*(?:haa dir|haa|dir|send|confirm|yes|confirm send)\s*[.!]?\s*",
        str(text or ""),
        flags=re.IGNORECASE,
    ))


def parse_reminder_selection(text, count):
    """Parse e.g. '1,3,5' and reject zero, out-of-range, or malformed input."""
    raw = str(text or "").strip()
    if not raw or not re.fullmatch(r"\d+(?:\s*[,; ]\s*\d+)*", raw):
        return None
    try:
        numbers = [int(part) for part in re.split(r"[,;\s]+", raw) if part]
    except ValueError:
        return None
    if not numbers or any(number < 1 or number > count for number in numbers):
        return None
    return list(dict.fromkeys(numbers))


def format_reminder_list(customers, missing_phone_count=0):
    lines = [
        "📣 *XUSUUSINTA DEYNTA*",
        "Dooro lambarrada macaamiisha aad rabto in la xusuusiyo.",
        "",
    ]
    for index, debtor in enumerate(customers, start=1):
        lines.append(
            f"{index}. {debtor.get('name') or 'Magac la’aan'} — "
            f"${float(debtor.get('amount') or 0):.2f}"
        )
    lines.extend([
        "",
        "✍️ Tusaale: *1,3,5*",
        "⏹️ Jooji: *JOOJI*",
    ])
    if missing_phone_count:
        lines.extend([
            "",
            f"ℹ️ {missing_phone_count} Lanbarkan ma saxna ama laguma isticmaalo WhatsApp.",
        ])
    return "\n".join(lines)
def build_debt_reminder(debtor, shopkeeper_name, shopkeeper_phone):
    name = str(debtor.get("name") or "Macmiil").strip()
    balance = float(debtor.get("amount") or 0)

    shopkeeper_name = str(shopkeeper_name or "").strip()
    shopkeeper_phone = str(shopkeeper_phone or "").strip()

    sender = (
        f"{shopkeeper_name} (+{shopkeeper_phone})"
        if shopkeeper_name
        else f"+{shopkeeper_phone}"
    )

    return (
    f"Asc {name},\n\n"

    f"Waxaan si xushmad leh kuu xusuusinayaa in aad soo bixiso "
    f"lacagtii daynta ahayd oo dhan: *${balance:.2f}*.\n\n"

    f"Fariintan waxaa kuu soo diray *{sender}*.\n\n"

    f"Fadlan sida ugu dhakhsaha badan u bixi lacagta.  Mahadsanid."
)


# Securely load credentials from Render's Environment panel variables
supabase: Client = create_client(os.getenv("SUPABASE_URL"), os.getenv("SUPABASE_KEY"))
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "").strip()
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-3.5-flash-lite").strip()

INSTANCE_ID = os.getenv("GREEN_API_INSTANCE_ID", "710722758620")
GREEN_API_TOKEN = os.getenv("GREEN_API_TOKEN", "")
GREEN_API_BASE = os.getenv("GREEN_API_BASE", "https://7107.api.greenapi.com")

SYSTEM_PROMPT = """You are {APP_NAME}, a Somali debt management assistant for small businesses. 
Extract transaction intent from chaotic, unstructured Somali text into raw JSON. 
Do not include any conversational filler, markdown syntax, or backticks.

Extract ALL debt entries from the message.
For each entry, extract: customer_name, amount, promised_date (YYYY-MM-DD), phone_number

ALWAYS return a JSON array, even for single entries.

Response format (JSON array):
[
  {"action": "ADD" or "PAY" or "LIST" or "SEARCH" or "EDIT" or "DELETE" or "HISTORY" or "REPORT" or "EXPORT", "customer_name": "string or null", "amount": number or null, "days_until_due": number or null, "customer_phone": "string or null", "promised_date": "YYYY-MM-DD or null", "filter_date": "YYYY-MM-DD or null", "filter_type": "today" or "tomorrow" or "date" or "week" or "month" or null, "new_amount": number or null, "new_date": "YYYY-MM-DD or null", "new_phone": "string or null", "payment_type": "FULL" or "PARTIAL" or "UNKNOWN" or null}
]

Examples - ADD:
'Cali 20$ oo bari ah' -> Use today's date + 1 day for promised_date
'Cali $34 oct 8, Axmed $50 oct 9' -> [{"action": "ADD", "customer_name": "Cali", "amount": 34, "days_until_due": 1, "customer_phone": null, "promised_date": "YYYY-MM-DD", "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}, {"action": "ADD", "customer_name": "Axmed", "amount": 50, "days_until_due": 2, "customer_phone": null, "promised_date": "YYYY-MM-DD", "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]

Examples - PAY:
'Cali wuu bixiyay' -> [{"action": "PAY", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null, "payment_type": "FULL"}]
'Gaawe wuxuu bixiyay $5' -> [{"action": "PAY", "customer_name": "Gaawe", "amount": 5, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null, "payment_type": "PARTIAL"}]
'Cali wuu bixiyay, Axmed wuu bixiyay' -> [{"action": "PAY", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}, {"action": "PAY", "customer_name": "Axmed", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]
'Cali wuxuu bixiyay $10, Axmed wuxuu bixiyay $20' -> [{"action": "PAY", "customer_name": "Cali", "amount": 10, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}, {"action": "PAY", "customer_name": "Axmed", "amount": 20, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]

Examples - LIST:
'Liiska deynta' -> [{"action": "LIST", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]
'Balamaha maanta' -> Use today's date for filter_date
'Balamaha berri' -> Use today's date + 1 day for filter_date
'Balamaha Oct 15' -> [{"action": "LIST", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": "2026-10-15", "filter_type": "date", "new_amount": null, "new_date": null, "new_phone": null}]

Examples - SEARCH:
'Cali' (when Cali exists in debts) -> [{"action": "SEARCH", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]
'Show Cali debt' -> [{"action": "SEARCH", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]

Examples - EDIT:
'edit Cali $50' -> [{"action": "EDIT", "customer_name": "Cali", "amount": 50, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": 50, "new_date": null, "new_phone": null}]
'edit Cali oct 20' -> [{"action": "EDIT", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": "2026-10-20", "filter_date": null, "filter_type": null, "new_amount": null, "new_date": "2026-10-20", "new_phone": null}]
'edit Cali $50 oct 20' -> [{"action": "EDIT", "customer_name": "Cali", "amount": 50, "days_until_due": null, "customer_phone": null, "promised_date": "2026-10-20", "filter_date": null, "filter_type": null, "new_amount": 50, "new_date": "2026-10-20", "new_phone": null}]

Examples - DELETE:
'delete Cali' -> [{"action": "DELETE", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]
'remove Cali' -> [{"action": "DELETE", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]

Examples - HISTORY:
'Cali history' -> [{"action": "HISTORY", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]
'Cali taariikh' -> [{"action": "HISTORY", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]
'payment history Cali' or 'statement Cali' or 'Cali xisaab' -> HISTORY for Cali

Examples - REPORT:
'Bishan report' -> [{"action": "REPORT", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": "month", "new_amount": null, "new_date": null, "new_phone": null}]
'Todobaadkan report' -> [{"action": "REPORT", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": "week", "new_amount": null, "new_date": null, "new_phone": null}]
'Weekly report' -> [{"action": "REPORT", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": "week", "new_amount": null, "new_date": null, "new_phone": null}]
'Monthly report' -> [{"action": "REPORT", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": "month", "new_amount": null, "new_date": null, "new_phone": null}]

Examples - EXPORT:
'Export' -> [{"action": "EXPORT", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]
'Download debts' -> [{"action": "EXPORT", "customer_name": null, "amount": null, "days_until_due": null, "customer_phone": null, "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": null}]

Examples - PHONE:
'Cali 615123456' -> [{"action": "ADD", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": "615123456", "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": "615123456"}]
'Save Cali phone 615123456' -> [{"action": "ADD", "customer_name": "Cali", "amount": null, "days_until_due": null, "customer_phone": "615123456", "promised_date": null, "filter_date": null, "filter_type": null, "new_amount": null, "new_date": null, "new_phone": "615123456"}]

Somali casual-language rules (understand spelling mistakes and informal phrasing):
- "Yuusuf $30 amaah ah ayuu qaatay" -> ADD, customer_name="Yuusuf", amount=30.
- "Jaamac 60 ayuu iga qaatay" -> ADD, customer_name="Jaamac", amount=60.
- "Axmed $10 deyn ah" -> ADD, customer_name="Axmed", amount=10.
- "Cali ka jar $10" -> PAY, customer_name="Cali", amount=10, payment_type="PARTIAL".
- "Cali waan ka helay $10" -> PAY, customer_name="Cali", amount=10, payment_type="PARTIAL".
- "Cali wuxuu bixiyay $10" -> PAY, customer_name="Cali", amount=10, payment_type="PARTIAL".
- "Cali wuu bixiyay" or "Cali deyntii oo dhan wuu bixiyay" -> PAY, customer_name="Cali", amount=null, payment_type="FULL".
- "Cali waan ka helay" without an amount -> PAY, customer_name="Cali", amount=null, payment_type="UNKNOWN". Do not assume full payment; ask how much was received.
- "Cali deyntiisa ka dhig $50" -> EDIT, customer_name="Cali", new_amount=50.
- "Cali balantiisa ka dhig 2026-10-20" -> EDIT, customer_name="Cali", new_date="2026-10-20".
- "Cali deynta $50 ka dhig, balantana 2026-10-20" -> EDIT with new_amount=50 and new_date="2026-10-20".

TRANSACTION DIRECTION SAFETY:
- "Cali $50" or "Axmed 30" has no direction. Extract the name and amount as a provisional ADD entry; the application will ask the user to choose ADD or PAY before saving anything.
- "Cali $50 ayuu iga qaatay" is ADD.
- "Cali $50 ayuu bixiyay" and "Cali wuxuu iga soo celiyay $50" are PAY.
- For multiple name+amount entries without direction, extract every entry; the application asks one clarification and applies the answer to all entries.

PAYMENT SAFETY:
- Return the field payment_type for every entry: "FULL", "PARTIAL", "UNKNOWN", or null.
- Use FULL only when the message clearly means the entire debt was paid.
- If a payment amount is stated, use PARTIAL; the code will cap it at the outstanding balance.
- If the message suggests money was received but gives no amount and does not clearly say the entire debt was paid, use UNKNOWN.
- Do not confuse taking/borrowing money (ADD) with paying money back (PAY).
- For EDIT, use new_amount and new_date. For ADD/PAY, use amount.
- If intent is unclear, choose SEARCH only when the user is asking about a debt; otherwise ask for clarification rather than changing data.

CUSTOMER NAME EXTRACTION RULES:
- Extract the complete customer name, including first and second names, whenever provided.
- For HISTORY, PAY, EDIT, and DELETE, remove only command/action words; do not drop other words that may be part of the name.
- Example: "Bagadh mamulka history" -> action="HISTORY", customer_name="Bagadh mamulka".
- Example: "Delete Dhakalaf" -> action="DELETE", customer_name="Dhakalaf".
- Example: "Bagadh mamulka wuxuu bixiyay $90" -> action="PAY", customer_name="Bagadh mamulka", amount=90.
- Never return only the last word of a multi-word customer name when the full name appears in the message.

Also support English:
'Add debt' = ADD action
'List debts' = LIST action
'Pay' = PAY action
'Search' = SEARCH action
'Edit' = EDIT action
'Delete' = DELETE action
'History' = HISTORY action
'Report' = REPORT action
'Export' = EXPORT action
""".replace("{APP_NAME}", APP_NAME)

def send_whatsapp(to_phone: str, message: str):
    clean_phone = str(to_phone).lstrip("+").split("@")[0].strip()
    if not GREEN_API_TOKEN:
        print("❌ GREEN_API_TOKEN is not configured in environment variables")
        return False
    url = f"{GREEN_API_BASE}/waInstance{INSTANCE_ID}/sendMessage/{GREEN_API_TOKEN}"
    chat_id = f"{clean_phone}@c.us"
    payload = {"chatId": chat_id, "message": message}
    print(f"🔍 send_whatsapp called:")
    print(f"   to_phone: {to_phone}")
    print(f"   clean_phone: {clean_phone}")
    print(f"   chat_id: {chat_id}")
    try:
        res = requests.post(url, json=payload, timeout=10)
        print(f"📡 Green-API Status: {res.status_code} - Response: {res.text}")
        if not res.ok:
            return False
        try:
            body = res.json()
            return bool(body.get("idMessage")) or body.get("status") == "success"
        except Exception:
            return res.ok
    except Exception as e:
        print(f"❌ Error sending WhatsApp: {e}")
        return False

def send_whatsapp_file(to_phone: str, filename: str, content: bytes, mime_type: str, caption: str = ""):
    """Send a generated file through Green-API's sendFileByUpload endpoint."""
    clean_phone = str(to_phone).lstrip("+").split("@")[0].strip()
    if not GREEN_API_TOKEN:
        print("❌ GREEN_API_TOKEN is not configured; cannot send file")
        return False
    url = f"{GREEN_API_BASE}/waInstance{INSTANCE_ID}/sendFileByUpload/{GREEN_API_TOKEN}"
    try:
        response = requests.post(
            url,
            data={"chatId": f"{clean_phone}@c.us", "caption": caption, "fileName": filename},
            files={"file": (filename, content, mime_type)},
            timeout=45,
        )
        print(f"📎 Green-API file upload: {response.status_code} - {response.text[:500]}")
        response.raise_for_status()
        return True
    except Exception as exc:
        print(f"❌ Could not send WhatsApp file {filename}: {type(exc).__name__}: {exc}")
        return False

def build_statement_pdf(customer_name, debts, payments_by_debt, total_paid, total_balance, business_name=None):
    """Create a clean, compact one-page customer statement PDF in memory."""
    from reportlab.lib.styles import ParagraphStyle
    from reportlab.lib.enums import TA_LEFT, TA_RIGHT, TA_CENTER
    from reportlab.platypus import KeepInFrame

    buffer = BytesIO()
    doc = SimpleDocTemplate(
        buffer, pagesize=A4,
        rightMargin=38, leftMargin=38, topMargin=34, bottomMargin=34
    )
    styles = getSampleStyleSheet()
    ink = colors.HexColor("#172B3A")
    muted = colors.HexColor("#64748B")
    green = colors.HexColor("#167A55")
    pale = colors.HexColor("#F1F6F3")
    line = colors.HexColor("#DCE5E0")

    normal = ParagraphStyle(
        "StatementNormal", parent=styles["Normal"],
        fontName="Helvetica", fontSize=8.5, leading=11, textColor=ink
    )
    small = ParagraphStyle(
        "StatementSmall", parent=normal, fontSize=7.5,
        leading=9, textColor=muted
    )
    section = ParagraphStyle(
        "StatementSection", parent=normal, fontName="Helvetica-Bold",
        fontSize=9, leading=11, spaceBefore=3, spaceAfter=4
    )
    customer_style = ParagraphStyle(
        "StatementCustomer", parent=styles["Heading1"],
        fontName="Helvetica-Bold", fontSize=17, leading=20,
        textColor=ink, spaceAfter=2
    )
    balance_style = ParagraphStyle(
        "StatementBalance", parent=styles["Heading1"],
        fontName="Helvetica-Bold", fontSize=25, leading=28,
        textColor=green, alignment=TA_RIGHT
    )
    right_small = ParagraphStyle(
        "StatementRightSmall", parent=small, alignment=TA_RIGHT
    )
    center_small = ParagraphStyle(
        "StatementCenterSmall", parent=small, alignment=TA_CENTER
    )

    safe_name = escape(str(customer_name or "Customer"))
    safe_business_name = escape(str(business_name or "DEYNJIR"))
    statement_date = today_eat().strftime("%d %b %Y")

    original_total = 0.0
    calculated_paid = 0.0
    clean_balance = 0.0
    payment_items = []

    for index, debt in enumerate(debts, 1):
        balance = max(float(debt.get("amount") or 0), 0.0)
        original = debt.get("original_amount")
        debt_payments = payments_by_debt.get(str(debt.get("id")), [])
        paid_for_debt = sum(float(p.get("amount") or 0) for p in debt_payments)

        # Prefer the stored original amount. If it is absent, reconstruct it
        # from the current balance plus the payment ledger for this debt.
        if original is None:
            original = balance + paid_for_debt
        original = max(float(original or 0), balance)

        original_total += original
        calculated_paid += paid_for_debt
        clean_balance += balance

        for payment in debt_payments:
            payment_items.append((
                str(payment.get("paid_at") or "")[:10] or "Date unavailable",
                float(payment.get("amount") or 0),
                index
            ))

    # Use the supplied totals from the statement calculation; the original
    # debt figure is based on original_amount (or balance + ledger fallback).
    paid_total = float(total_paid or calculated_paid)
    balance_total = float(total_balance or 0)

    story = []
    header = Table(
        [[Paragraph(f"<b>{safe_business_name}</b>", ParagraphStyle(
            "Brand", parent=normal, fontName="Helvetica-Bold",
            fontSize=16, leading=19, textColor=green
        )),
          Paragraph("CUSTOMER STATEMENT<br/><font size='7' color='#64748B'>Generated " +
                    escape(statement_date) + "</font>", right_small)]],
        colWidths=[doc.width * 0.48, doc.width * 0.52]
    )
    header.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("LINEBELOW", (0, 0), (-1, -1), 1, green),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 9),
        ("LEFTPADDING", (0, 0), (-1, -1), 0),
        ("RIGHTPADDING", (0, 0), (-1, -1), 0),
    ]))
    story.extend([header, Spacer(1, 14)])

    customer_row = Table(
        [[Paragraph("CUSTOMER", small), Paragraph("OUTSTANDING BALANCE", right_small)],
         [Paragraph(safe_name, customer_style),
          Paragraph(f"${balance_total:,.2f}", balance_style)]],
        colWidths=[doc.width * 0.55, doc.width * 0.45]
    )
    customer_row.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, -1), pale),
        ("BOX", (0, 0), (-1, -1), 0.6, line),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("LEFTPADDING", (0, 0), (-1, -1), 11),
        ("RIGHTPADDING", (0, 0), (-1, -1), 11),
        ("TOPPADDING", (0, 0), (-1, -1), 8),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 8),
    ]))
    story.extend([customer_row, Spacer(1, 12)])

    summary = Table(
        [[Paragraph("ORIGINAL DEBT", small),
          Paragraph("TOTAL PAID", small),
          Paragraph("REMAINING", small)],
         [Paragraph(f"${original_total:,.2f}", section),
          Paragraph(f"${paid_total:,.2f}", section),
          Paragraph(f"${balance_total:,.2f}", section)]],
        colWidths=[doc.width / 3] * 3
    )
    summary.setStyle(TableStyle([
        ("LINEBELOW", (0, 0), (-1, 0), 0.5, line),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("LEFTPADDING", (0, 0), (-1, -1), 7),
        ("RIGHTPADDING", (0, 0), (-1, -1), 7),
        ("TOPPADDING", (0, 0), (-1, -1), 5),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
    ]))
    story.extend([summary, Spacer(1, 12), Paragraph("PAYMENT HISTORY", section)])

    payment_items.sort(key=lambda item: item[0], reverse=True)
    payment_rows = [[
        Paragraph("<b>Date</b>", normal),
        Paragraph("<b>Amount paid</b>", right_small),
        Paragraph("<b>Debt</b>", right_small)
    ]]
    for paid_date, amount, debt_number in payment_items[:8]:
        payment_rows.append([
            Paragraph(escape(paid_date), normal),
            Paragraph(f"${amount:,.2f}", right_small),
            Paragraph(f"#{debt_number}", right_small)
        ])

    if not payment_items:
        payment_rows.append([
            Paragraph("No payments recorded", small),
            Paragraph("$0.00", right_small),
            Paragraph("—", right_small)
        ])

    history = Table(
        payment_rows,
        colWidths=[doc.width * 0.48, doc.width * 0.32, doc.width * 0.20],
        repeatRows=1
    )
    history.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), pale),
        ("LINEBELOW", (0, 0), (-1, 0), 0.6, line),
        ("LINEBELOW", (0, 1), (-1, -1), 0.35, line),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("LEFTPADDING", (0, 0), (-1, -1), 7),
        ("RIGHTPADDING", (0, 0), (-1, -1), 7),
        ("TOPPADDING", (0, 0), (-1, -1), 5),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
    ]))
    story.append(history)

    if len(payment_items) > 8:
        story.append(Paragraph(
            f"Showing the latest 8 of {len(payment_items)} recorded payments.",
            small
        ))

    story.extend([
        Spacer(1, 14),
        Paragraph(
            "Waad ila soo xidhiidhi kartaa hadii aad qabto wax su'aal ah.",
            center_small
        ),
        Spacer(1, 4),
        Paragraph("DEYNJIR  •  Clear and reliable debt records", center_small)
    ])

    # Keep the complete statement to one A4 page, shrinking slightly only if
    # the customer has many payment rows or a long name.
    fitted = KeepInFrame(doc.width, doc.height, story, mode="shrink")
    doc.build([fitted])
    return buffer.getvalue()

OWNER_PHONE = os.getenv("OWNER_PHONE", "").lstrip("+").strip()
# Required for /cron/* endpoints: set a long random CRON_SECRET and send it as
# the x-cron-secret header (or Authorization: Bearer <secret>).

@app.get("/")
def home():
    return {"status": f"{APP_NAME} Bot Engine is running live.", "app": APP_NAME}
def normalize_customer_name(value):
    """Normalize names for case/punctuation/spacing-insensitive comparison."""
    value = unicodedata.normalize("NFKD", str(value or "").casefold())
    value = "".join(ch for ch in value if not unicodedata.combining(ch))
    value = re.sub(r"[^\w\s]", " ", value)
    return " ".join(value.split())


def message_has_explicit_amount_for_name(message_text, customer_name):
    """Return whether the user's own message states an amount for this name.

    This guards against the AI copying a stored balance into an ADD result when
    the user actually sent only a due-date update. Currency-marked values are
    strongest evidence; plain numbers are accepted after date expressions are
    removed (e.g. 'Jaamac 60 ayuu iga qaatay').
    """
    requested = normalize_customer_name(customer_name)
    if not requested:
        return False

    raw = str(message_text or "")
    segments = [part.strip() for part in re.split(r"[\n;,|]+", raw) if part.strip()]
    if not segments:
        segments = [raw]

    month_pattern = (
        r"jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|"
        r"jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|oct(?:ober)?|"
        r"nov(?:ember)?|dec(?:ember)?|january|february|march|april|june|july|"
        r"august|september|october|november|december"
    )
    for segment in segments:
        normalized_segment = normalize_customer_name(segment)
        if requested not in normalized_segment:
            # AI may shorten a stored full name; require at least one meaningful
            # name token to be present in the source segment before trusting it.
            requested_tokens = requested.split()
            if not any(len(token) >= 3 and token in normalized_segment.split() for token in requested_tokens):
                continue

        # Remove dates before looking for unmarked numbers, so "Name Oct 10"
        # doesn't accidentally look like a $10 debt.
        cleaned = re.sub(r"\b\d{4}-\d{1,2}-\d{1,2}\b", " ", segment, flags=re.I)
        cleaned = re.sub(r"\b\d{1,2}[/-]\d{1,2}(?:[/-]\d{2,4})?\b", " ", cleaned)
        cleaned = re.sub(rf"\b(?:{month_pattern})\s+\d{{1,2}}(?:st|nd|rd|th)?\b", " DATE ", cleaned, flags=re.I)
        cleaned = re.sub(rf"\b\d{{1,2}}(?:st|nd|rd|th)?\s+(?:{month_pattern})\b", " DATE ", cleaned, flags=re.I)

        # Explicit currency formats are unambiguous.
        if re.search(r"(?:\$\s*\d+(?:[.,]\d+)?|\d+(?:[.,]\d+)?\s*\$|\b(?:usd|dollars?|dollar)\b)", cleaned, flags=re.I):
            return True

        # Common Somali/English transaction wording is also amount evidence.
        if re.search(r"\b(?:iga\s+qaatay|qaatey|amaah|deyn|deyn\s+ah|wuxuu\s+iga\s+qaatay|added|add)\b", cleaned, flags=re.I) and re.search(r"\d+(?:[.,]\d+)?", cleaned):
            return True

        # Bare numbers are allowed as amounts only when not part of a date.
        if re.search(r"\d+(?:[.,]\d+)?", cleaned) and not re.search(r"\b(?:today|tomorrow|berri|maanta|oct|nov|dec|jan|feb|mar|apr|may|jun|jul|aug|sep)\b", cleaned, flags=re.I):
            return True

    return False


def classify_transaction_direction(message_text):
    """Return ADD/PAY only when the user's wording clearly states direction."""
    text = normalize_customer_name(str(message_text or ""))
    add_patterns = [
        r"\b(?:deyn cusub|dayn cusub|new debt|add debt|added debt)\b",
        r"\b(?:iga qaatay|wuu qaatay|ayaa qaatay|ayuu qaatay|qaatey|amaah)\b",
        r"\b(?:took|borrowed)\b",
    ]
    pay_patterns = [
        r"\b(?:bixiyay|bixiyey|bixisay|bixiyeen|soo celiyay|soo celiyey|celiyay|celiyey)\b",
        r"\b(?:waan ka helay|waxaan ka helay|lacag ayuu soo celiyay)\b",
        r"\b(?:paid|payment received|paid back|repaid|returned the money)\b",
    ]
    has_add = any(re.search(pattern, text, flags=re.I) for pattern in add_patterns)
    has_pay = any(re.search(pattern, text, flags=re.I) for pattern in pay_patterns)
    if has_add and not has_pay:
        return "ADD"
    if has_pay and not has_add:
        return "PAY"
    return None


def parse_transaction_clarification(message_text):
    """Recognize numbered or written replies to the pending transaction question."""
    text = normalize_customer_name(str(message_text or ""))

    # Numbered WhatsApp choices: 1 = new debt, 2 = payment, 3 = cancel.
    if re.fullmatch(r"1", text):
        return "ADD"
    if re.fullmatch(r"2", text):
        return "PAY"
    if re.fullmatch(r"3", text):
        return "CANCEL"

    if re.fullmatch(r"(?:deyn cusub|dayn cusub|deyn cusub oo baxday|lacag baxday|add|new debt|deyn baa baxday)", text, re.I):
        return "ADD"
    if re.fullmatch(r"(?:deyn soo xarootay|lacag soo xarootay|lacag baa soo gashay|lacag la helay|pay|payment|money received|received payment)", text, re.I):
        return "PAY"
    if re.fullmatch(r"(?:jooji|cancel|baaji)", text, re.I):
        return "CANCEL"
    return None


def local_fallback_parse(message_text):
    """Conservatively parse common commands when Gemini is unavailable.

    This intentionally supports clear, single-customer commands only. It returns
    None rather than guessing for multi-customer, ambiguous, or unsupported text.
    """
    raw = " ".join(str(message_text or "").strip().split())
    if not raw:
        return None
    low = raw.casefold()

    base = {
        "customer_name": None, "amount": None, "days_until_due": None,
        "customer_phone": None, "promised_date": None, "filter_date": None,
        "filter_type": None, "new_amount": None, "new_date": None,
        "new_phone": None, "payment_type": None,
    }

    # Clear commands that do not require natural-language interpretation.
    if re.fullmatch(r"(?:liiska(?:\s+deynta)?|deyn(?:aha)?\s+liiskooda|list(?:\s+debts?)?)", low):
        return [{**base, "action": "LIST"}]
    if re.fullmatch(r"(?:export|download\s+debts?|soo\s+dejiso)", low):
        return [{**base, "action": "EXPORT"}]
    if re.fullmatch(r"(?:report|warbixin|bishan\s+report|monthly\s+report|weekly\s+report|todobaadkan\s+report)", low):
        period = "week" if ("week" in low or "todobaad" in low) else ("month" if ("month" in low or "bishan" in low) else None)
        return [{**base, "action": "REPORT", "filter_type": period}]

    # Preserve bare name+amount entries for the explicit clarification flow.
    # This is intentionally NOT an ADD decision: the webhook asks whether the
    # money was a new debt or a received payment before writing any transaction.
    if classify_transaction_direction(raw) is None and not re.search(
        r"\b(?:edit|kadhig|ka\s+dhig|delete|remove|search|find|history|taariikh|report|export)\b",
        low,
    ):
        segments = [part.strip() for part in re.split(r"[,;\n]+", raw) if part.strip()]
        ambiguous_entries = []
        for segment in segments:
            match = re.search(r"(?:\$\s*(\d+(?:[.,]\d{1,2})?)|(\d+(?:[.,]\d{1,2})?)\s*\$|(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)(?![\w/.-]))", segment)
            if not match:
                ambiguous_entries = []
                break
            amount_text = next((value for value in match.groups() if value is not None), None)
            name_text = (segment[:match.start()] + " " + segment[match.end():]).strip(" -:,$")
            name_text = re.sub(r"\b(?:usd|dollars?|dollar)\b", " ", name_text, flags=re.I)
            name_text = " ".join(name_text.split()).strip()
            if not name_text:
                ambiguous_entries = []
                break
            ambiguous_entries.append({**base, "action": "ADD", "customer_name": name_text,
                                      "amount": float(amount_text.replace(",", "."))})
        if ambiguous_entries:
            return ambiguous_entries

    # Identify a single amount. Currency-marked amounts are safe; plain numbers
    # are accepted only when transaction wording makes their meaning explicit.
    amount_matches = list(re.finditer(r"\$\s*(\d+(?:[.,]\d{1,2})?)|(?<!\w)(\d+(?:[.,]\d{1,2})?)\s*\$", raw))
    currency_marked = bool(amount_matches)
    if not amount_matches:
        if re.search(r"\b(?:iga\s+qaatay|wuxuu\s+iga\s+qaatay|qaatey|amaah|deyn\s+ah|added|add)\b", low):
            amount_matches = list(re.finditer(r"(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)(?![\w/.-])", raw))
        elif re.search(r"\b(?:bixiyay|bixisay|paid|payment)\b", low):
            amount_matches = list(re.finditer(r"(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)(?![\w/.-])", raw))
    # Do not guess if there are multiple amounts in a message.
    if len(amount_matches) > 1:
        return None

    is_replace = bool(re.search(r"\b(?:edit|kadhig|ka\s+dhig|ka\s+dhigo)\b", low))
    is_delete = bool(re.match(r"^(?:delete|remove|tirtir)\b", low))
    is_search = bool(re.match(r"^(?:search|find|lookup|look\s+up|raadi|raadso|show|check|hubi)\b", low))
    is_history = bool(re.search(r"\b(?:history|taariikh|statement|xisaab(?:ta)?)\b",
        low
    ))
    is_payment = bool(re.search(r"\b(?:bixiyay|bixiyey|bixisay|bixiyeen|wuu\s+bixiyay|wuxuu\s+bixiyay|soo\s+celiyay|soo\s+celiyey|celiyay|celiyey|waan\s+ka\s+helay|waxaan\s+ka\s+helay|paid|payment|repaid|paid\s+back)\b", low))

    if not amount_matches and not any((is_delete, is_search, is_history, is_payment)):
        # A bare name can be searched safely only if the caller verifies it exists.
        return None

    amount = None
    if amount_matches:
        m = amount_matches[0]
        amount_text = next((g for g in m.groups() if g is not None), None)
        if amount_text is None:
            return None
        try:
            amount = float(amount_text.replace(",", "."))
        except ValueError:
            return None
        if amount < 0:
            return None

    # Remove amount tokens, action words and common transaction filler to recover
    # the customer's name without allowing the parser to invent one.
    name_text = raw
    for m in reversed(amount_matches):
        name_text = name_text[:m.start()] + " " + name_text[m.end():]

    name_text = re.sub(r"\b(?:\$|usd|dollars?|ayuu|ayuu\s+iga\s+qaatay)\b", " ", name_text, flags=re.I)

    name_text = re.sub(r"^(?:edit|add|deyn|delete|remove|tirtir|search|find|lookup|look\s+up|raadi|raadso|show|check|hubi)\b\s*[:,-]?\s*", "", name_text, flags=re.I)

    name_text = re.sub(r"\b(?:deyntiisa|deynta|deynteeda|balance|amount)\s+(?:ka\s+dhig|kadhig|ka\s+dhigo)\b", " ", name_text, flags=re.I)

    name_text = re.sub(r"\b(?:ka\s+dhig|kadhig|ka\s+dhigo|wuu|wuxuu|ayuu|soo\s+celiyay|soo\s+celiyey|celiyay|celiyey|waan\s+ka\s+helay|waxaan\s+ka\s+helay|bixiyay|bixiyey|bixisay|bixiyeen|paid|payment|repaid|iga\s+soo|iga\s+qaatay|wuxuu\s+iga\s+qaatay|qaatey|amaah|deyn\s+ah|deyntii|deynta|oo\s+dhan|added|add)\b", " ", name_text, flags=re.I)

    name_text = re.sub(
        r"\b(?:history|taariikh|statement|xisaab(?:ta)?)\b",
        " ",
        name_text,
        flags=re.I
    )
    name_text = re.sub(r"\b(?:debt|debts|show|search|find|lookup|look\s+up|check|raadi|raadso|hubi)\b", " ", name_text, flags=re.I)
    name_text = re.sub(r"[^\w\s'/-]", " ", name_text, flags=re.UNICODE)
    name = " ".join(name_text.split()).strip(" -_/,")
    if not name:
        return None

    if is_delete:
        return [{**base, "action": "DELETE", "customer_name": name}]
    if is_search:
        return [{**base, "action": "SEARCH", "customer_name": name}]
    if is_history:
        return [{**base, "action": "HISTORY", "customer_name": name}]
    if is_payment:
        return [{**base, "action": "PAY", "customer_name": name, "amount": amount,
                 "payment_type": "PARTIAL" if amount is not None else "FULL"}]
    if amount is not None and is_replace:
        return [{**base, "action": "EDIT", "customer_name": name,
                 "amount": amount, "new_amount": amount}]
    if amount is not None and (currency_marked or re.search(r"\b(?:iga\s+qaatay|wuxuu\s+iga\s+qaatay|qaatey|amaah|deyn\s+ah|added|add)\b", low)):
        return [{**base, "action": "ADD", "customer_name": name, "amount": amount}]
    return None


def is_fuzzy_debt_list_command(message_text):
    """Recognize clear debt-list commands with small typing mistakes.

    Deliberately limited to read-only LIST commands. It never guesses
    EDIT, DELETE, ADD, or PAY commands.
    """
    raw = str(message_text or "").casefold().strip()
    raw = unicodedata.normalize("NFKD", raw)
    raw = "".join(ch for ch in raw if not unicodedata.combining(ch))
    raw = re.sub(r"[^\\w\\s]", " ", raw)
    words = raw.split()

    known_commands = [
        ["liiska", "deynta"],
        ["liiska", "daynta"],
        ["liiska", "deynta", "iyo", "balamaha"],
        ["liiska", "daynta", "iyo", "balamaha"],
    ]

    for target in known_commands:
        if len(words) != len(target):
            continue
        scores = [
            difflib.SequenceMatcher(None, typed, expected).ratio()
            for typed, expected in zip(words, target)
        ]
        if min(scores, default=0) >= 0.68 and sum(scores) / len(scores) >= 0.72:
            return True
    return False


def _edit_distance(left, right):
    """Levenshtein distance, used to tolerate small typing/spelling mistakes."""
    previous = list(range(len(right) + 1))
    for i, left_char in enumerate(left, 1):
        current = [i]
        for j, right_char in enumerate(right, 1):
            current.append(min(
                current[j - 1] + 1,
                previous[j] + 1,
                previous[j - 1] + (left_char != right_char),
            ))
        previous = current
    return previous[-1]


def _token_match_score(left, right):
    if left == right:
        return 1.0
    distance = _edit_distance(left, right)
    longest = max(len(left), len(right))
    # Permit 1 typo for short names and up to 2 for longer names.
    max_errors = 1 if longest <= 4 else 2
    if distance > max_errors:
        return 0.0
    # Once within the allowed edit-distance window, keep the score high enough
    # that a legitimate one-character typo (e.g. Ali/Aly) is not rejected.
    return 0.80 + 0.20 * (1.0 - distance / max(1, longest))


def _name_similarity(requested, stored):
    """Score full names while allowing small spelling errors in each name part."""
    requested_norm = normalize_customer_name(requested)
    stored_norm = normalize_customer_name(stored)
    if not requested_norm or not stored_norm:
        return 0.0
    if requested_norm == stored_norm:
        return 1.0

    requested_parts = requested_norm.split()
    stored_parts = stored_norm.split()

    # Match every supplied name part against a distinct stored name part.
    # This prevents a shared first name alone from overriding a matching surname.
    available = list(stored_parts)
    part_scores = []
    for part in requested_parts:
        if not available:
            return 0.0
        best = max(range(len(available)), key=lambda i: _token_match_score(part, available[i]))
        score = _token_match_score(part, available[best])
        if score == 0.0:
            return 0.0
        part_scores.append(score)
        available.pop(best)

    # If the user provided only one part of a multi-part name, allow it as a
    # lookup, but the caller will be shown alternatives when names are ambiguous.
    token_score = sum(part_scores) / len(part_scores)
    if len(requested_parts) == 1 and len(stored_parts) > 1:
        return min(token_score, 0.88)

    # A typo of one or two characters is accepted, but full-name alignment matters.
    return 0.65 * token_score + 0.35 * difflib.SequenceMatcher(None, requested_norm, stored_norm).ratio()


def resolve_name_from_original_message(business_user_id, message_text, ai_name):
    """Recover a complete stored debtor name when the original message contains it.

    This corrects cases where the AI extracts only the first name from a full
    name such as 'Edit Hinda bire oct 10'. It only resolves names that actually
    appear as a complete phrase in the original message, and prefers the
    longest phrase to avoid matching a shorter name inside a longer one.
    """
    if not ai_name or not message_text:
        return None

    normalized_message = f" {normalize_customer_name(message_text)} "
    ai_norm = normalize_customer_name(ai_name)
    if not ai_norm:
        return None

    result = (
        supabase.table("customers")
        .select("name")
        .eq("business_user_id", business_user_id)
        .execute()
    )
    stored_names = {}
    for row in (result.data or []):
        display = str(row.get("name") or "").strip()
        normalized = normalize_customer_name(display)
        if normalized:
            stored_names.setdefault(normalized, display)

    # First accept an exact full-name phrase. If the customer typed a small
    # spelling variation (e.g. MAT AAN vs MATAN), compare same-length word
    # windows from the original message against stored names.
    message_parts = normalize_customer_name(message_text).split()
    requested_parts = normalize_customer_name(ai_name).split()
    candidates = []

    for normalized, display in stored_names.items():
        stored_parts = normalized.split()
        if not stored_parts:
            continue
        if f" {normalized} " in normalized_message:
            score = 1.0
        else:
            # Compare contiguous phrase windows of the same word count. This
            # avoids treating a shared token like CALI as a full-name match.
            windows = [
                " ".join(message_parts[i:i + len(stored_parts)])
                for i in range(max(0, len(message_parts) - len(stored_parts) + 1))
            ]
            score = max((_name_similarity(window, normalized) for window in windows), default=0.0)

        has_related_token = any(
            _token_match_score(req, stored) >= 0.78
            for req in requested_parts
            for stored in stored_parts
        )
        if score >= 0.78 and has_related_token:
            candidates.append((score, len(stored_parts), len(normalized), display, normalized))

    if not candidates:
        return None

    candidates.sort(key=lambda c: (c[0], c[1], c[2]), reverse=True)
    best_score = candidates[0][0]
    # Only auto-resolve when one stored name clearly wins. If two names are
    # similarly close, leave the AI's name unchanged so normal disambiguation runs.
    best = [c for c in candidates if best_score - c[0] <= 0.04]
    unique_names = {c[3] for c in best}
    if len(unique_names) == 1:
        resolved = next(iter(unique_names))
        print(f"🔎 Recovered full debtor name from original message: {ai_name!r} -> {resolved!r} (score={best_score:.3f})")
        return resolved
    return None


def find_debtor_matches(business_user_id, name):
    """Find exact names first, then aligned partial names, then safe fuzzy matches.

    A fuzzy match is not silently selected when another distinct customer name is
    nearly as likely; in that case all candidates are returned for clarification.
    """
    requested = normalize_customer_name(name)
    if not requested:
        return []

    result = (
        supabase.table("customers")
        .select("*")
        .eq("business_user_id", business_user_id)
        .order("name")
        .execute()
    )
    rows = result.data or []
    if not rows:
        return []

    # Keep each distinct spelling/name together so repeated debts for the same
    # customer do not count as different people during name disambiguation.
    names = {}
    for row in rows:
        display_name = str(row.get("name") or "").strip()
        names.setdefault(normalize_customer_name(display_name), {"display": display_name, "rows": []})["rows"].append(row)

    # Exact normalized full-name match has priority.
    if requested in names:
        return names[requested]["rows"]

    requested_parts = requested.split()

    # Prefer exact stored name tokens before fuzzy matching.
    exact_token_matches = []
    for normalized, item in names.items():
        stored_parts = normalized.split()
        if all(part in stored_parts for part in requested_parts):
            exact_token_matches.append((len(stored_parts), normalized, item))
    if exact_token_matches:
        shortest_length = min(item[0] for item in exact_token_matches)
        preferred = [item for item in exact_token_matches if item[0] == shortest_length]
        return [row for _, _, item in preferred for row in item["rows"]]

    # Next try word-boundary partial names.
    partial = [
        item for normalized, item in names.items()
        if f" {requested} " in f" {normalized} " or f" {normalized} " in f" {requested} "
    ]
    if partial:
        return [row for item in partial for row in item["rows"]]

    # Only then consider typo-tolerant fuzzy matches.
    scored = []
    for normalized, item in names.items():
        score = _name_similarity(requested, normalized)
        if score >= 0.78:
            scored.append((score, normalized, item))

    if not scored:
        return []

    scored.sort(key=lambda x: x[0], reverse=True)
    best_score = scored[0][0]
    # If another distinct name is almost as close, ask the user to identify the
    # right full name rather than risking a payment, edit, or deletion on the wrong person.
    close = [entry for entry in scored if best_score - entry[0] <= 0.08]
    if len(close) > 1:
        return [row for _, _, item in close for row in item["rows"]]
    return scored[0][2]["rows"]


def ask_for_full_name(sender_phone, matches, action):
    message = "⚠️ Waxaan helay macaamiil isku magac ah:\n\n"

    for number, debtor in enumerate(matches, start=1):
        due_date = debtor.get("promised_date") or "lama gelin"
        message += (
            f"{number}. {debtor['name']} — "
            f"${debtor['amount']} — Ballan: {due_date}\n"
        )

    if action == "PAY":
        example = f"{matches[0]['name']} wuu bixiyay"
    elif action == "DELETE":
        example = f"delete {matches[0]['name']}"
    elif action == "HISTORY":
        example = f"{matches[0]['name']} history"
    elif action == "SEARCH":
        example = f"Show {matches[0]['name']} debt"
    else:
        example = f"edit {matches[0]['name']} $50"

    message += (
        "\n✍️ Fadlan mar kale qor magaca oo buuxa si aan qofka saxda ah u doorto.\n"
        f"Tusaale: {example}"
    )

    send_whatsapp(sender_phone, message)
  
def send_due_list_followup(phone):
    send_whatsapp(
        phone,
        "Si aad u aragto dhammaan deymaha, soo qor:\n"
        "*Liiska daynta*\n"
        "Ama si aad u aragto deymaha iyo taariikhaha ballanta, soo qor:\n"
        "*Liiska daynta iyo balamaha*"
    )
def _import_parse_date(value):
    if value is None or str(value).strip().lower() in ("", "nan", "nat", "none", "null"):
        return today_eat().isoformat()
    if hasattr(value, "strftime"):
        return value.strftime("%Y-%m-%d")
    raw = str(value).strip()
    for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%m/%d/%Y"):
        try:
            return datetime.strptime(raw, fmt).date().isoformat()
        except ValueError:
            continue
    raise ValueError(f"Taariikh aan la fahmi karin: {raw}")


def _validate_import_entries(entries):
    if not isinstance(entries, list) or not entries:
        raise ValueError("Wax macaamiil ah lagama helin.")
    clean = []
    for i, entry in enumerate(entries, start=1):
        if not isinstance(entry, dict):
            raise ValueError(f"Saf {i} ma saxna.")
        name = str(entry.get("name") or entry.get("customer_name") or "").strip()
        if not name or name.lower() in ("nan", "none"):
            raise ValueError(f"Saf {i}: magaca macmiilka ma cadda.")
        try:
            amount = float(entry.get("amount"))
        except (TypeError, ValueError):
            raise ValueError(f"Saf {i} ({name}): lacagtu ma cadda.")
        if amount <= 0:
            raise ValueError(f"Saf {i} ({name}): lacagtu waa inay ka weyn tahay eber.")
        phone = entry.get("phone_number") or entry.get("customer_phone")
        if str(phone or "").strip().lower() in ("nan", "none", "null"):
            phone = None
        phone = re.sub(r"[^0-9+]", "", str(phone)) if phone else None
        clean.append({
            "name": name,
            "amount": round(amount, 2),
            "promised_date": _import_parse_date(entry.get("promised_date") or entry.get("due_date") or entry.get("due")),
            "phone_number": phone or None,
        })
    return clean


def _extract_import_text(raw_text, import_mode="debt"):
    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY lama dejin.")
    if import_mode == "payment":
        task = (
            "Extract every customer PAYMENT received from the following text. Return ONLY a JSON array. "
            "Each item must have name and amount (number). Do not guess unclear names or amounts; "
            "use null for unclear values. Do not interpret these rows as new debts."
        )
    else:
        task = (
            "Extract every customer NEW DEBT from the following text. Return ONLY a JSON array. "
            "Each item must have name, amount (number), promised_date (YYYY-MM-DD or null), "
            "phone_number (string or null). Do not guess unclear names or amounts; use null "
            "for unclear values. Today's date is " + today_eat().isoformat() + "."
        )
    prompt = task + "\n\nTEXT:\n" + raw_text
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"
    response = requests.post(url, headers={"x-goog-api-key": GEMINI_API_KEY, "Content-Type": "application/json"},
        json={"contents":[{"role":"user","parts":[{"text":prompt}]}],
              "generationConfig":{"temperature":0,"responseMimeType":"application/json"}}, timeout=45)
    response.raise_for_status()
    data = response.json()
    text = "".join(x.get("text", "") for x in data.get("candidates", [{}])[0].get("content", {}).get("parts", []))
    parsed = json.loads(text)
    return _validate_import_entries(parsed)


def _extract_import_image(image_bytes, mime_type, import_mode="debt"):
    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY lama dejin.")
    import base64
    if import_mode == "payment":
        prompt = (
            "Read this handwritten or printed list of customer PAYMENTS RECEIVED. Extract ALL rows. "
            "Return ONLY a JSON array with name and amount (number). Do not guess unclear names "
            "or amounts; use null for unclear values. These are payments against existing debts, "
            "not new debts."
        )
    else:
        prompt = (
            "Read this handwritten or printed debt list. Extract ALL rows. Return ONLY a JSON array "
            "with name, amount (number), promised_date (YYYY-MM-DD or null), phone_number (string or null). "
            "Do not guess unclear names or amounts; use null for unclear values. Today's date is " + today_eat().isoformat()
        )
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"
    payload = {"contents":[{"role":"user","parts":[{"text":prompt},
        {"inline_data":{"mime_type":mime_type,"data":base64.b64encode(image_bytes).decode("ascii")}}]}],
        "generationConfig":{"temperature":0,"responseMimeType":"application/json"}}
    response = requests.post(url, headers={"x-goog-api-key":GEMINI_API_KEY,"Content-Type":"application/json"}, json=payload, timeout=60)
    response.raise_for_status()
    data=response.json()
    text="".join(x.get("text","") for x in data.get("candidates",[{}])[0].get("content",{}).get("parts",[]))
    return _validate_import_entries(json.loads(text))


def _stage_import(admin_phone, entries, import_mode="debt"):
    total = sum(item["amount"] for item in entries)
    if import_mode == "payment":
        lines = ["📋 *HORDHACA LACAG-BIXINTA*", f"Tirada lacag-bixinnada: {len(entries)}", ""]
        for i, item in enumerate(entries, 1):
            lines.append(f"{i}. {item['name']} — ${item['amount']:.2f}")
        lines += ["", f"*Wadarta lacagta: ${total:.2f}*", "", "Hubi magacyada iyo lacagaha.",
                  "Haddii ay sax yihiin, soo qor *OK* si lacag-bixinnada loo diiwaangeliyo.",
                  "Haddii kale, soo qor *CANCEL* si loo joojiyo.",
                  "", "Lacagaha waxaa laga jarayaa deymaha hadda jira."]
    else:
        lines = ["📋 *HORDHACA DEYNTA LA DIIWAANGELINAYO*", f"Tirada macaamiisha: {len(entries)}", ""]
        for i, item in enumerate(entries, 1):
            lines.append(f"{i}. {item['name']} — ${item['amount']:.2f} — {item['promised_date']}")
        lines += ["", f"*Wadarta guud: ${total:.2f}*", "", "Hubi magacyada iyo lacagaha.",
                  "Haddii ay sax yihiin, soo qor *OK* si loo kaydiyo.",
                  "Haddii kale, soo qor *CANCEL* si loo joojiyo."]
    send_whatsapp(admin_phone, "\n".join(lines))


def _commit_import(admin_phone, session):
    entries = session["entries"]
    business_user_id = session["business_user_id"]
    import_mode = session.get("mode", "debt")

    if import_mode == "payment":
        # Validate every row before making any changes. A name must resolve to
        # exactly one unpaid debt, and cumulative imported payments cannot exceed it.
        prepared = []
        cumulative = {}
        debt_cache = {}
        for item in entries:
            matches = find_debtor_matches(business_user_id, item["name"])
            unpaid = [m for m in matches if not m.get("is_paid") and _safe_money(m.get("amount")) > 0]
            if len(unpaid) != 1:
                reason = "lama helin deyn aan la bixin" if not unpaid else "waxaa jira deymo badan oo magacaas leh"
                raise ValueError(f"{item['name']}: {reason}. Hubi magaca ama kala saar deymaha.")
            debtor = unpaid[0]
            debt_id = str(debtor["id"])
            debt_cache[debt_id] = debtor
            cumulative[debt_id] = cumulative.get(debt_id, 0.0) + float(item["amount"])
            if cumulative[debt_id] - _safe_money(debtor.get("amount")) > 0.009:
                raise ValueError(
                    f"{item['name']}: lacagta la soo gelinayo (${cumulative[debt_id]:.2f}) "
                    f"waxay ka badan tahay haraaga (${_safe_money(debtor.get('amount')):.2f})."
                )
            prepared.append((item, debtor))

        saved = 0
        try:
            for item, debtor in prepared:
                rpc_result = supabase.rpc("record_debt_payment", {
                    "p_customer_id": str(debtor["id"]),
                    "p_business_user_id": str(business_user_id),
                    "p_amount": round(float(item["amount"]), 2),
                }).execute()
                rpc_data = rpc_result.data
                if isinstance(rpc_data, list):
                    rpc_data = rpc_data[0] if rpc_data else None
                if not isinstance(rpc_data, dict) or not rpc_data.get("id"):
                    raise RuntimeError("record_debt_payment ma xaqiijin lacag-bixinta. Hubi Supabase.")
                saved += 1
        except Exception as exc:
            if saved:
                send_whatsapp(
                    admin_phone,
                    f"⚠️ Import-ku qayb ayuu u dhacay: {saved} lacag-bixin waa la kaydiyey, "
                    "inta kale way fashilantay. Ha ku celin isla liiska; marka hore hubi xisaabta."
                )
                exc.partial_import = True
            raise

        send_whatsapp(
            admin_phone,
            f"✅ Import-ka lacag-bixinta waa dhammaaday.\n"
            f"Lacag-bixin la diiwaangeliyay: {saved}\n"
            f"Wadarta lacagta: ${sum(float(x['amount']) for x in entries):.2f}\n"
            "Lacagaha waxaa laga jaray deymaha dukaanka la doortay."
        )
        return

    added = 0
    skipped = 0
    for item in entries:
        # Conservative duplicate guard: don't re-add an identical unpaid debt for the same shop.
        existing = (supabase.table("customers").select("id")
            .eq("business_user_id", business_user_id)
            .eq("name", item["name"]).eq("amount", item["amount"])
            .eq("is_paid", False).limit(1).execute())
        if existing.data:
            skipped += 1
            continue
        row = {"business_user_id": business_user_id, "name": item["name"],
               "amount": item["amount"], "original_amount": item["amount"],
               "promised_date": item["promised_date"], "phone_number": item["phone_number"],
               "is_paid": False}
        supabase.table("customers").insert(row).execute()
        added += 1
    send_whatsapp(admin_phone, f"✅ Diiwaangelinta liiska deynta waa dhammaatay.\nMacaamiil cusub oo la daray: {added}\nDeyn hore u jirtay oo laga booday: {skipped}\nDeymaha waxaa lagu kaydiyey ganacsiga aad dooratay.")


@app.post("/webhook")
async def whatsapp_webhook(request: Request):
    data = await request.json()
    print(f"📥 Green-API webhook received: type={data.get('typeWebhook')}")

    type_webhook = data.get("typeWebhook")

    # Green-API reports messages typed/sent from the WhatsApp phone
    # as outgoingMessageReceived.
    #
    # Messages sent by our bot through the API are
    # outgoingAPIMessageReceived, so ignore those to prevent
    # the bot from processing its own replies.
    allowed_types = {
        "incomingMessageReceived",
        "outgoingMessageReceived",
    }

    if type_webhook not in allowed_types:
        return {"status": "ignored"}

    sender_data = data.get("senderData", {})
    sender_chat_id = sender_data.get("chatId")

    if not sender_chat_id:
        return {"status": "no_chat_id"}

    sender_phone = sender_chat_id.split("@")[0]
    print(f"🔍 SENDER PHONE: {sender_phone}")

    message_data = data.get("messageData", {})
    type_message = message_data.get("typeMessage")

    message_text = ""
        
    sender_data = data.get("senderData", {})
    sender_chat_id = sender_data.get("chatId")
    if not sender_chat_id:
        return {"status": "no_chat_id"}
        
    sender_phone = sender_chat_id.split("@")[0]
    print(f"🔍 SENDER PHONE: {sender_phone}")
    
    message_data = data.get("messageData", {})
    type_message = message_data.get("typeMessage")
    
    message_text = ""
    
    # Import files are accepted only during an authenticated approved-user
    # import session. Nothing is saved before the sender confirms with OK.
    if type_message == "documentMessage":
        if sender_phone not in IMPORT_SESSIONS:
            send_whatsapp(sender_phone, "Marka hore dir *IMPORT* si aad u bilowdo soo gelinta liiska.")
            return {"status": "import_session_required"}
        if IMPORT_SESSIONS[sender_phone].get("mode") not in {"debt", "payment"}:
            send_whatsapp(sender_phone, "Marka hore dooro nooca import-ka: qor *DEYN* ama *LACAG BIXIN*.")
            return {"status": "import_mode_required"}
        try:
            doc = message_data.get("fileMessageData", {})
            filename = str(doc.get("fileName") or "")
            url = doc.get("downloadUrl")
            if not filename.lower().endswith((".xlsx", ".xls", ".csv")) or not url:
                send_whatsapp(sender_phone, "Fadlan dir Excel (.xlsx), CSV ama XLS fayl leh.")
                return {"status": "unsupported_or_missing_file"}
            response = requests.get(url, timeout=30)
            response.raise_for_status()
            if filename.lower().endswith(".csv"):
                frame = pd.read_csv(BytesIO(response.content))
            else:
                frame = pd.read_excel(BytesIO(response.content))
            columns = {str(c).strip().lower(): c for c in frame.columns}
            name_col = columns.get("name") or columns.get("customer") or columns.get("customer name")
            amount_col = (
                columns.get("amount") or columns.get("debt")
                or columns.get("payment") or columns.get("paid amount")
                or columns.get("paid_amount")
            )
            if not name_col or not amount_col:
                raise ValueError("Faylku waa inuu leeyahay Name iyo Amount columns.")
            due_col = next((columns[k] for k in ("due", "due date", "due_date", "promised_date") if k in columns), None)
            phone_col = next((columns[k] for k in ("phone", "phone number", "phone_number") if k in columns), None)
            raw=[]
            for _, row in frame.iterrows():
                raw.append({"name": row[name_col], "amount": row[amount_col],
                    "promised_date": row[due_col] if due_col else None,
                    "phone_number": row[phone_col] if phone_col else None})
            entries = _validate_import_entries(raw)
            IMPORT_SESSIONS[sender_phone]["entries"] = entries
            IMPORT_SESSIONS[sender_phone]["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
            _stage_import(sender_phone, entries, IMPORT_SESSIONS[sender_phone].get("mode", "debt"))
            return {"status": "import_preview_ready", "count": len(entries)}
        except Exception as exc:
            print(f"❌ Import document error: {type(exc).__name__}: {exc}")
            send_whatsapp(sender_phone, f"❌ Faylka lama akhrin karin: {str(exc)[:250]}")
            return {"status": "import_document_error"}

    if type_message == "imageMessage":
        if sender_phone not in IMPORT_SESSIONS:
            send_whatsapp(sender_phone, "Marka hore dir *IMPORT* si aad u bilowdo soo gelinta sawirka.")
            return {"status": "import_session_required"}
        if IMPORT_SESSIONS[sender_phone].get("mode") not in {"debt", "payment"}:
            send_whatsapp(sender_phone, "Marka hore dooro nooca import-ka: qor *DEYN* ama *LACAG BIXIN*.")
            return {"status": "import_mode_required"}
        try:
            image_data = message_data.get("imageMessageData") or message_data.get("fileMessageData", {})
            download_url = image_data.get("downloadUrl")
            if not download_url:
                raise ValueError("Sawirka lama soo dejisan karin.")
            image_response = requests.get(download_url, timeout=30)
            image_response.raise_for_status()
            mime = image_data.get("mimeType") or "image/jpeg"
            import_mode = IMPORT_SESSIONS[sender_phone].get("mode", "debt")
            entries = _extract_import_image(image_response.content, mime, import_mode)
            IMPORT_SESSIONS[sender_phone]["entries"] = entries
            IMPORT_SESSIONS[sender_phone]["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
            _stage_import(sender_phone, entries, import_mode)
            return {"status": "import_image_preview_ready", "count": len(entries)}
        except Exception as exc:
            print(f"❌ Import image error: {type(exc).__name__}: {exc}")
            send_whatsapp(sender_phone, f"❌ Sawirka si sax ah looma akhrin karin: {str(exc)[:250]}")
            return {"status": "import_image_error"}

    # ✅ HANDLE TEXT MESSAGES
    try:
        if type_message == "textMessage":
            message_text = message_data["textMessageData"]["textMessage"]
        elif type_message == "extendedTextMessage":
            message_text = message_data["extendedTextMessageData"]["text"]
        else:
            return {"status": "unsupported_message_type"}
    except KeyError:
        return {"status": "no_text_payload"}
        
    if not message_text:
        return {"status": "empty_text"}
    
    # Normalize sender; GREEN-API chat IDs may include "@c.us".
    sender_phone = str(sender_phone).replace("+", "").split("@")[0].strip()
    owner_phone = str(OWNER_PHONE).replace("+", "").split("@")[0].strip()

    # Approved users import into their own shop with IMPORT. The owner may
    # additionally select another approved shop using IMPORT +252... .
    import_text = str(message_text or "").strip()
    is_import_command = bool(re.fullmatch(r"\s*IMPORT(?:\s+\+?\d{8,15})?\s*", import_text, re.I))
    if sender_phone == owner_phone or sender_phone in IMPORT_SESSIONS or is_import_command:
        if re.fullmatch(r"\s*CANCEL\s*", import_text, re.I) and sender_phone in IMPORT_SESSIONS:
            IMPORT_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "✅ Import waa la joojiyey. Waxba lama kaydin.")
            return {"status": "import_cancelled"}
        if re.fullmatch(r"\s*OK\s*", import_text, re.I):
            session = IMPORT_SESSIONS.get(sender_phone)
            if not session or not session.get("entries"):
                send_whatsapp(sender_phone, "Ma jiro liis sugaya xaqiijin. Marka hore dir liiska.")
                return {"status": "no_import_to_confirm"}
            if datetime.now(timezone.utc) > session.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
                IMPORT_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Waqtigii import-ka wuu dhammaaday. Bilow mar kale: IMPORT 252...")
                return {"status": "import_expired"}
            try:
                _commit_import(sender_phone, session)
                IMPORT_SESSIONS.pop(sender_phone, None)
                return {"status": "import_confirmed"}
            except Exception as exc:
                print(f"❌ Import commit error: {type(exc).__name__}: {exc}")
                if getattr(exc, "partial_import", False):
                    IMPORT_SESSIONS.pop(sender_phone, None)
                    send_whatsapp(sender_phone, "❌ Qayb ka mid ah import-ka waa la kaydiyey. Fadlan hubi liiska deymaha iyo lacag-bixinnada ka hor intaadan mar kale soo gelin.")
                else:
                    send_whatsapp(sender_phone, f"❌ Import lama dhammeystirin: {str(exc)[:250]}\nWaxba lama beddelin haddii khaladku dhacay intaan kaydintu bilaaban. Sax liiska ama qor *CANCEL*.")
                return {"status": "import_commit_error"}
        # IMPORT without a phone number starts an import for the sender's own
        # approved shop. Unknown or unapproved numbers are never auto-registered.
        if re.fullmatch(r"\s*IMPORT\s*", import_text, re.I):
            try:
                own_shop_result = (supabase.table("business_users")
                    .select("id, phone_number, name, approval_status")
                    .eq("phone_number", sender_phone).limit(1).execute())
                if not own_shop_result.data:
                    send_whatsapp(sender_phone, "❌ Lambarkan dukaan kuma jiro Deynjir.")
                    return {"status": "import_shop_not_found"}
                own_shop = own_shop_result.data[0]
                if own_shop.get("approval_status") != "approved":
                    send_whatsapp(sender_phone, "❌ Dukaanka lama ansixin. Import lama bilaabi karo.")
                    return {"status": "import_shop_not_approved"}
                IMPORT_SESSIONS[sender_phone] = {
                    "business_user_id": own_shop["id"], "shop_phone": sender_phone,
                    "shop_name": own_shop.get("name") or sender_phone,
                    "entries": None, "mode": None,
                    "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL,
                }
                send_whatsapp(sender_phone,
                    f"✅ Dukaanka waa la doortay: {own_shop.get('name') or sender_phone}.\n\n"
                    "Maxaad rabtaa inaad soo geliso?\n"
                    "*DEYN* — deymo cusub.\n"
                    "*LACAG BIXIN* — lacagaha laga bixiyay deymaha jira.\n\n"
                    "Kadib ii soo dir qoraal, Excel/CSV ama sawir.\n"
                    "Hubi hordhaca, kadib qor *OK* si loo kaydiyo ama *CANCEL* si loo joojiyo.")
                return {"status": "import_own_shop_selected"}
            except Exception as exc:
                print(f"❌ Own-shop import lookup error: {exc}")
                send_whatsapp(sender_phone, "❌ Dukaanka lama hubin karin. Mar kale isku day.")
                return {"status": "import_own_shop_lookup_error"}

        match = re.fullmatch(r"\s*IMPORT\s+(\+?\d{8,15})\s*", import_text, re.I)
        if match and sender_phone != owner_phone:
            send_whatsapp(sender_phone, "❌ Waxaad soo gelin kartaa oo keliya liiska dukaankaaga. Dir *IMPORT* adigoon number raacin.")
            return {"status": "cross_shop_import_not_allowed"}
        if match:
            target_phone = match.group(1).replace("+", "")
            try:
                target = (supabase.table("business_users")
                    .select("id, phone_number, name, approval_status")
                    .eq("phone_number", target_phone).limit(1).execute())
                if not target.data:
                    send_whatsapp(sender_phone, "❌ Lambarkan dukaan kuma jiro Deynjir. Hubi numberka.")
                    return {"status": "import_shop_not_found"}
                shop = target.data[0]
                if shop.get("approval_status") != "approved":
                    send_whatsapp(sender_phone, "❌ Dukaankan lama ansixin. Import lama bilaabi karo.")
                    return {"status": "import_shop_not_approved"}
                IMPORT_SESSIONS[sender_phone] = {"business_user_id": shop["id"], "shop_phone": target_phone,
                    "shop_name": shop.get("name") or target_phone, "entries": None, "mode": None,
                    "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL}
                send_whatsapp(sender_phone, f"✅ Dukaanka waa la doortay: {shop.get('name') or target_phone}.\n\nMaxaad rabtaa inaad soo geliso?\n*DEYN* — deymo cusub.\n*LACAG BIXIN* — lacagaha laga bixiyay deymaha jira.\n\nKadib ii soo dir qoraal, Excel/CSV ama sawir.\nHubi hordhaca, kadib qor *OK* si loo kaydiyo ama *CANCEL* si loo joojiyo.")
                return {"status": "import_shop_selected"}
            except Exception as exc:
                print(f"❌ Import shop lookup error: {exc}")
                send_whatsapp(sender_phone, "❌ Dukaanka lama hubin karin. Mar kale isku day.")
                return {"status": "import_shop_lookup_error"}
        active_import = IMPORT_SESSIONS.get(sender_phone)
        if active_import and not re.fullmatch(r"\s*(?:APPROVE|REJECT)\b.*", import_text, re.I):
            if datetime.now(timezone.utc) > active_import.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
                IMPORT_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Waqtigii import-ka wuu dhammaaday. Bilow mar kale: IMPORT 252...")
                return {"status": "import_expired"}
            mode_choice = normalize_customer_name(import_text)
            if mode_choice in {"deyn", "dayn", "deyn cusub", "dayn cusub"}:
                active_import["mode"] = "debt"
                active_import["entries"] = None
                active_import["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
                send_whatsapp(sender_phone, "✅ Waxaad dooratay *DEYN*. Hadda soo dir liiska deynta qoraal ahaan, Excel/CSV ama sawir ahaan.")
                return {"status": "import_mode_debt_selected"}
            if mode_choice in {"lacag bixin", "lacag bixinta", "payment", "payments", "bixin"}:
                active_import["mode"] = "payment"
                active_import["entries"] = None
                active_import["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
                send_whatsapp(sender_phone, "✅ Waxaad dooratay *LACAG BIXIN*. Soo dir magacyada macaamiisha iyo lacagta ay bixiyeen, qoraal ahaan, Excel/CSV ama sawir ahaan. Lacagtu waxay ka go'aysaa deynta hadda u furan.")
                return {"status": "import_mode_payment_selected"}
            if active_import.get("mode") not in {"debt", "payment"}:
                send_whatsapp(sender_phone, "Marka hore dooro nooca import-ka: qor *DEYN* ama *LACAG BIXIN*.")
                return {"status": "import_mode_required"}
            if re.fullmatch(r"\s*OK\s*", import_text, re.I):
                pass
            else:
                try:
                    entries = _extract_import_text(import_text, active_import.get("mode", "debt"))
                    active_import["entries"] = entries
                    active_import["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
                    _stage_import(sender_phone, entries, active_import.get("mode", "debt"))
                    return {"status": "import_text_preview_ready", "count": len(entries), "mode": active_import.get("mode", "debt")}
                except Exception as exc:
                    print(f"❌ Import text parse error: {type(exc).__name__}: {exc}")
                    send_whatsapp(sender_phone, "❌ Liiska si sax ah looma akhrin karin. Fadlan caddee magacyada iyo lacagaha, dabadeed mar kale soo dir.")
                    return {"status": "import_text_parse_error"}

    # Owner approves/rejects with: APPROVE 252... or REJECT 252...
    parts = message_text.strip().split(maxsplit=1)
    command = parts[0].upper() if parts else ""

    if sender_phone == owner_phone and command in {"APPROVE", "REJECT"}:
        if len(parts) != 2:
            send_whatsapp(sender_phone, "Isticmaal mid ka mid ah amarradan:\n*APPROVE 252...* — oggolow codsiga.\n*REJECT 252...* — diid codsiga.")
            return {"status": "invalid_approval_command"}

        applicant_phone = parts[1].replace("+", "").split("@")[0].strip()
        new_status = "approved" if command == "APPROVE" else "rejected"

        try:
            applicant = (
                supabase.table("business_users")
                .select("id, phone_number")
                .eq("phone_number", applicant_phone)
                .execute()
            )

            if not applicant.data:
                send_whatsapp(sender_phone, f"❌ Codsi sugaya lama helin lambarkan: {applicant_phone}.")
                return {"status": "applicant_not_found"}

            (
                supabase.table("business_users")
                .update({"approval_status": new_status})
                .eq("phone_number", applicant_phone)
                .execute()
            )

            decision_so = "waa la oggolaaday" if new_status == "approved" else "waa la diiday"
            send_whatsapp(sender_phone, f"✅ Codsiga lambarka {applicant_phone} {decision_so}.")
            send_whatsapp(
                applicant_phone,
                "✅ Codsigaaga waa la oggolaaday. Hadda waad isticmaali kartaa Deynjir."
                if new_status == "approved"
                else "❌ Waan ka xunnahay, codsigaaga isticmaalka Deynjir waa la diiday."
            )
            return {"status": new_status}

        except Exception as approval_err:
            print(f"❌ APPROVAL UPDATE ERROR: {approval_err}")
            send_whatsapp(sender_phone, "❌ Codsiga lama cusboonaysiin. Fadlan mar kale isku day ama la xiriir maamulka.")
            return {"status": "approval_update_error"}

    # Find this sender's business user; do NOT auto-create unknown senders here.
    try:
        business_user_query = (
            supabase.table("business_users")
            .select("id, phone_number, name, approval_status")
            .eq("phone_number", sender_phone)
            .execute()
        )

        if not business_user_query.data:
            send_whatsapp(
                sender_phone,
                f"⏳ Ku soo dhawoow {APP_NAME}.\n\n"
                "Lambarkan wuxuu u adeegaa ganacsiyada.\n"
                "Haddii aad rabto inaad isticmaasho, fadlan la xiriir: +252633732215."
            )
            return {"status": "not_registered"}

        business_user = business_user_query.data[0]

        if business_user.get("approval_status") != "approved":
            send_whatsapp(
                sender_phone,
                "⏳ Codsigaaga weli waa la sugayaa. Fadlan sug inta maamulka ka oggolaanayo."
            )
            return {"status": "not_approved"}

        business_user_id = business_user["id"]

    except Exception as db_err:
        print(f"❌ DATABASE ERROR (Business User Lookup): {db_err}")
        return {"status": "business_user_db_error"}

    # A pending transaction clarification is persisted in Supabase so it survives
    # Render restarts. The original message is replayed only after a clear answer.
    pending_clarification = None
    forced_transaction_action = None
    try:
        pending_result = (
            supabase.table("pending_transaction_clarifications")
            .select("sender_phone, original_message, parsed_entries, created_at")
            .eq("sender_phone", sender_phone)
            .eq("business_user_id", business_user_id)
            .limit(1)
            .execute()
        )
        if pending_result.data:
            candidate = pending_result.data[0]
            created_raw = candidate.get("created_at")
            created_at = datetime.fromisoformat(str(created_raw).replace("Z", "+00:00")) if created_raw else None
            if created_at and created_at.tzinfo is None:
                created_at = created_at.replace(tzinfo=timezone.utc)
            if not created_at or datetime.now(timezone.utc) - created_at > timedelta(minutes=30):
                supabase.table("pending_transaction_clarifications").delete().eq("sender_phone", sender_phone).execute()
            else:
                pending_clarification = candidate
    except Exception as pending_err:
        print(f"⚠️ Pending clarification lookup failed: {pending_err}")
        send_whatsapp(sender_phone, "❌ Ma hubin karo fariintii sugaysay. Fadlan mar kale isku day.")
        return {"status": "pending_clarification_lookup_error"}

    if pending_clarification:
        clarification_action = parse_transaction_clarification(message_text)
        if clarification_action == "CANCEL":
            try:
                (
                    supabase.table("pending_transaction_clarifications")
                    .delete()
                    .eq("sender_phone", sender_phone)
                    .eq("business_user_id", business_user_id)
                    .execute()
                )
            except Exception as pending_err:
                print(f"❌ Pending clarification cancellation failed: {pending_err}")
                send_whatsapp(sender_phone, "❌ Joojinta way fashilantay. Fadlan mar kale isku day.")
                return {"status": "pending_clarification_cancel_error"}
            send_whatsapp(sender_phone, "Waa la joojiyay. Wax deyn ah lama diiwaangelin.")
            return {"status": "pending_clarification_cancelled"}
        elif clarification_action in {"ADD", "PAY"}:
            try:
                entries = pending_clarification.get("parsed_entries") or []
                if isinstance(entries, str):
                    entries = json.loads(entries)
                if not isinstance(entries, list) or not entries:
                    raise ValueError("Saved pending entries are empty or invalid")
                forced_transaction_action = clarification_action
                message_text = pending_clarification.get("original_message") or message_text
                supabase.table("pending_transaction_clarifications").delete().eq("sender_phone", sender_phone).execute()
                print(f"✅ Clarification received; replaying saved message as {forced_transaction_action}")
            except Exception as pending_err:
                print(f"❌ Pending clarification restore failed: {pending_err}")
                send_whatsapp(sender_phone, "❌ Fariintii hore dib looma soo celin karin. Fadlan mar kale dir.")
                return {"status": "pending_clarification_restore_error"}
        else:
            send_whatsapp(sender_phone, "Fadlan marka hore ka jawaab fariintii sugaysay: *DEYN CUSUB* ama *DEYN SOO XAROOTAY*. Qor *JOOJI* si aad u baajiso.")
            return {"status": "awaiting_transaction_clarification"}

    # Manual debt-reminder workflow: fully rule-based, no Gemini request.
    # Start: XUSUUSIN -> numbered unpaid-customer list -> "1,3" -> confirmation.
    reminder_text = str(message_text or "").strip()
    reminder_state = REMINDER_SESSIONS.get(sender_phone)

    if reminder_state:
        expires_at = reminder_state.get("expires_at")
        if not expires_at or datetime.now(timezone.utc) > expires_at:
            REMINDER_SESSIONS.pop(sender_phone, None)
            reminder_state = None
            if is_reminder_confirm_command(reminder_text) or re.fullmatch(
                r"\s*\d+(?:\s*[,; ]\s*\d+)*\s*", reminder_text
            ):
                send_whatsapp(sender_phone, "⌛ codsigii xusuusintu wuu dhacay. Soo qor *XUSUUSIN* si aad mar kale u bilowdo.")
                return {"status": "reminder_session_expired"}

    if is_reminder_start_command(reminder_text):
        try:
            debtor_result = (
                supabase.table("customers")
                .select("id, name, amount, phone_number, is_paid")
                .eq("business_user_id", business_user_id)
                .eq("is_paid", False)
                .order("name")
                .execute()
            )
            all_unpaid = [
                row for row in (debtor_result.data or [])
                if float(row.get("amount") or 0) > 0
            ]
            eligible = []
            missing_phone_count = 0
            for row in all_unpaid:
                normalized_phone = normalize_reminder_phone(row.get("phone_number"))
                if not normalized_phone:
                    missing_phone_count += 1
                    continue
                prepared = dict(row)
                prepared["_reminder_phone"] = normalized_phone
                eligible.append(prepared)

            if not eligible:
                send_whatsapp(
                    sender_phone,
                    "ℹ️ Macaamiisha deynta kugu leh midkoodna ma laha lambar WhatsApp oo sax ah. Fadlan hubi lambarada telefoonka."
                )
                return {"status": "no_reminder_eligible_customers"}

            REMINDER_SESSIONS[sender_phone] = {
                "business_user_id": business_user_id,
                "stage": "selecting",
                "customers": eligible,
                "selected": [],
                "expires_at": datetime.now(timezone.utc) + REMINDER_SESSION_TTL,
            }
            send_whatsapp(sender_phone, format_reminder_list(eligible, missing_phone_count))
            print(f"📣 Reminder selection started: shopkeeper={business_user_id}, eligible={len(eligible)}, missing_phone={missing_phone_count}")
            return {"status": "reminder_selection_started", "eligible": len(eligible)}
        except Exception as reminder_err:
            print(f"❌ REMINDER LIST ERROR: {reminder_err}")
            send_whatsapp(sender_phone, "❌ Liiska xusuusinta lama soo saari karin. Fadlan mar kale isku day.")
            return {"status": "reminder_list_error"}

    if reminder_state and is_reminder_cancel_command(reminder_text):
        REMINDER_SESSIONS.pop(sender_phone, None)
        send_whatsapp(sender_phone, "✅ Xusuusintii waa la joojiyey. Wax fariin ah looma dirin macaamiisha.")
        return {"status": "reminder_cancelled"}

    if reminder_state and reminder_state.get("stage") == "selecting":
        selected_numbers = parse_reminder_selection(
            reminder_text, len(reminder_state.get("customers", []))
        )
        if selected_numbers:
            selected_customers = [
                reminder_state["customers"][number - 1]
                for number in selected_numbers
            ]
            reminder_state["selected"] = selected_numbers
            reminder_state["stage"] = "confirming"
            reminder_state["expires_at"] = datetime.now(timezone.utc) + REMINDER_SESSION_TTL
            preview_lines = ["🔎 *XUSUUSINTA LA DOORTAY*", ""]
            for debtor in selected_customers:
                preview_lines.append(
                    f"• {debtor.get('name')} — ${float(debtor.get('amount') or 0):.2f}"
                )
            total = sum(float(row.get("amount") or 0) for row in selected_customers)
            preview_lines.extend([
                "",
                f"👥 Tirada: {len(selected_customers)} macmiil",
                f"💰 Wadarta deynta: ${total:.2f}",
                "",
                "Haddii aad hubisay, soo qor *HAA DIR* si fariimaha loo diro.",
                "Haddii kale soo qor *JOOJI*."
            ])
            send_whatsapp(sender_phone, "\n".join(preview_lines))
            return {"status": "reminder_selection_confirm_required", "selected": len(selected_customers)}
        if re.fullmatch(r"\s*\d+(?:\s*[,; ]\s*\d+)*\s*", reminder_text):
            send_whatsapp(
                sender_phone,
                f"❌ Xulasho khaldan. Geli lambarro u dhexeeya 1 iyo {len(reminder_state.get('customers', []))}, tusaale *1,3*; ama soo qor *JOOJI*."
            )
            return {"status": "invalid_reminder_selection"}
        # A non-selection message exits this temporary flow and is handled
        # normally by Daynjir, so ordinary debt operations still work.
        REMINDER_SESSIONS.pop(sender_phone, None)
        reminder_state = None

    if reminder_state and reminder_state.get("stage") == "confirming":
        if is_reminder_confirm_command(reminder_text):
            # Pop before network calls so a repeated confirmation cannot resend.
            state = REMINDER_SESSIONS.pop(sender_phone, None)
            if not state or state.get("business_user_id") != business_user_id:
                send_whatsapp(sender_phone, "⌛ Xulashadu ma jirto ama way dhacday. Soo qor *XUSUUSIN* mar kale.")
                return {"status": "reminder_state_missing"}

            
            sent_count = 0
            skipped_count = 0
            failed_count = 0

            for number in state.get("selected") or []:
                original = state["customers"][number - 1]
                customer_name = original.get("name") or "Macmiil"

                try:
                    fresh_result = (
                        supabase.table("customers")
                        .select("id, name, amount, phone_number, is_paid")
                        .eq("id", original["id"])
                        .eq("business_user_id", business_user_id)
                        .execute()
                    )

                    if not fresh_result.data:
                        skipped_count += 1
                        status_message = (
                            "Xusuusinta waa laga booday "
                            "(deyn la bixiyay/lambar maqan)."
                        )
                    else:
                        fresh = fresh_result.data[0]
                        customer_name = fresh.get("name") or customer_name

                        if fresh.get("is_paid") is True or float(fresh.get("amount") or 0) <= 0:
                            skipped_count += 1
                            status_message = (
                                "Xusuusinta waa laga booday "
                                "(deyn la bixiyay/lambar maqan)."
                            )

                        else:
                            target_phone = normalize_reminder_phone(
                                fresh.get("phone_number")
                            )

                            if not target_phone:
                                skipped_count += 1
                                status_message = (
                                    "Xusuusinta waa laga booday "
                                    "(deyn la bixiyay/lambar maqan)."
                                )
                            else:
                                send_ok = send_whatsapp(
                                    target_phone,
                                    build_debt_reminder(
                                        fresh,
                                        business_user.get("name"),
                                        business_user.get("phone_number") or sender_phone,
                                    ),
                                )

                                if send_ok is False:
                                    failed_count += 1
                                    status_message = "Xusuusintan lama dirin."
                                else:
                                    sent_count += 1
                                    status_message = "Fariinta xusuusinta waa la diray."

                except Exception as send_err:
                    failed_count += 1
                    status_message = "Xusuusintan lama dirin."
                    print(
                        f"❌ REMINDER SEND ERROR for debtor "
                        f"id={original.get('id')}: {send_err}"
                    )

                # Send one result to the shopkeeper for this customer.
                send_whatsapp(
                    sender_phone,
                    f"*{customer_name}*\n{status_message}"
                )

            print(
                f"📣 Reminder batch complete: sent={sent_count}, "
                f"skipped={skipped_count}, failed={failed_count}"
            )

            return {
                "status": "reminder_batch_complete",
                "accepted": sent_count,
                "skipped": skipped_count,
                "failed": failed_count,
            }

        send_whatsapp(
            sender_phone,
            "⚠️ Xusuusintu weli ma dirmin. Soo qor *HAA DIR* si aad u xaqiijiso, ama *JOOJI* si aad u baajiso."
        )
        return {"status": "reminder_waiting_for_confirmation"}

    # A standalone PDF command exports the most recently requested statement.
    pdf_only_requested = bool(re.fullmatch(
        r"\s*(?:pdf|soo\s+dir\s+pdf|pdf\s+soo\s+dir|pdf\s+xisaabta|xisaabta\s+pdf)\s*[.!]?\s*",
        message_text,
        flags=re.IGNORECASE,
    ))
    pdf_customer_name = None
    if pdf_only_requested:
        previous_statement = LAST_HISTORY_REQUESTS.get(sender_phone)
        if not previous_statement or previous_statement.get("business_user_id") != business_user_id:
            send_whatsapp(
                sender_phone,
                "ℹ️ Marka hore codso xisaabta macmiilka, tusaale: *Cali taariikh*. "
                "Kadib soo qor *PDF* si aan PDF ugu diro."
            )
            return {"status": "no_recent_statement_for_pdf"}
        pdf_customer_name = previous_statement.get("customer_name")
        if not pdf_customer_name:
            send_whatsapp(sender_phone, "❌ Magaca macmiilka lama helin. Fadlan mar kale codso xisaabtiisa.")
            return {"status": "missing_pdf_customer_name"}
        print(f"📄 PDF-only request detected for {pdf_customer_name!r}")

    # Fast read-only command matching: avoid a Gemini request for debt lists.
    fuzzy_list_requested = is_fuzzy_debt_list_command(message_text)

    today_str = today_eat().isoformat()
    dynamic_system_prompt = f"{SYSTEM_PROMPT}\nToday's date is strictly: {today_str}. Use this to calculate calendar targets or relative days offsets like 'berri'."
    
    if pdf_only_requested:
        entries = [{"action": "HISTORY", "customer_name": pdf_customer_name}]
        print(f"📄 Skipping Gemini for PDF follow-up; using saved customer {pdf_customer_name!r}")
    elif forced_transaction_action:
        print(f"🔁 Using saved entries with confirmed action {forced_transaction_action}")
    elif fuzzy_list_requested:
        entries = [{
            "action": "LIST",
            "customer_name": None,
            "amount": None,
            "filter_date": None,
            "filter_type": None,
        }]
        print(f"⚡ Fuzzy debt-list command recognized locally: {message_text!r}; skipping Gemini")
    else:
        try:
            if not GEMINI_API_KEY:
                raise RuntimeError("GEMINI_API_KEY is not configured in environment variables")

            gemini_url = (
                "https://generativelanguage.googleapis.com/v1beta/"
                f"models/{GEMINI_MODEL}:generateContent"
            )
            gemini_payload = {
                "systemInstruction": {
                    "parts": [{"text": dynamic_system_prompt}]
                },
                "contents": [{
                    "role": "user",
                    "parts": [{"text": message_text}]
                }],
                "generationConfig": {
                    "temperature": 0.0,
                    "responseMimeType": "application/json"
                }
            }
            gemini_response = requests.post(
                gemini_url,
                headers={
                    "x-goog-api-key": GEMINI_API_KEY,
                    "Content-Type": "application/json"
                },
                json=gemini_payload,
                timeout=45
            )
            if not gemini_response.ok:
                # Include the provider's error message, but never log the API key.
                raise RuntimeError(
                    f"Gemini API HTTP {gemini_response.status_code}: "
                    f"{gemini_response.text[:1000]}"
                )
            gemini_data = gemini_response.json()
            candidate_parts = (
                gemini_data.get("candidates", [{}])[0]
                .get("content", {}).get("parts", [])
            )
            ai_response = "".join(
                part.get("text", "") for part in candidate_parts
                if isinstance(part, dict)
            ).strip()
            if not ai_response:
                block_reason = (
                    gemini_data.get("promptFeedback", {}).get("blockReason")
                    or gemini_data.get("candidates", [{}])[0].get("finishReason")
                    or "No text returned"
                )
                raise ValueError(f"Gemini returned no usable text: {block_reason}")
            print(f"🤖 Gemini AI Processed Output: {ai_response}")
            json_match = re.search(r'[\[{].*[\]}]', ai_response, re.DOTALL)
            if not json_match:
                raise ValueError("No JSON found in Gemini output")
            parsed = json.loads(json_match.group())
            entries = [parsed] if isinstance(parsed, dict) else parsed
            if not entries:
                raise ValueError("Empty Gemini entries")
        except Exception as ai_err:
            # Gemini is optional: when rate-limited or unavailable, use conservative
            # local rules and continue through the SAME Supabase transaction logic.
            error_text = str(ai_err)
            is_rate_limited = (
                "429" in error_text or "rate_limit" in error_text.lower()
                or "RateLimitError" in type(ai_err).__name__
            )
            print(f"❌ Gemini request/parse failed: {error_text}")
            entries = local_fallback_parse(message_text)
            if entries:
                print(f"🛟 Local fallback parsed command: {entries}")
                print("🛟 Continuing through shared Supabase transaction logic; Gemini will be tried again on the next message.")
            else:
                # A plain customer name is a safe SEARCH only if it matches this
                # shopkeeper's own records; unsupported text must never create debt.
                raw_query = str(message_text or "").strip()
                has_date_words = bool(re.search(
                    r"\b(?:today|tomorrow|maanta|berri|jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)\b|\b\d{4}-\d{1,2}-\d{1,2}\b|\b\d{1,2}[/-]\d{1,2}(?:[/-]\d{2,4})?\b",
                    raw_query, flags=re.I
                ))
                if raw_query and not has_date_words and not re.search(r"[,$]\s*\d|\d\s*\$", raw_query):
                    try:
                        fallback_matches = find_debtor_matches(business_user_id, raw_query)
                    except Exception as fallback_err:
                        print(f"⚠️ Local customer-search fallback failed: {fallback_err}")
                        fallback_matches = []
                    if fallback_matches:
                        entries = [{"action": "SEARCH", "customer_name": raw_query}]
                        print(f"🛟 Local fallback routing known customer name to SEARCH: {raw_query!r}")
            if not entries:
                if is_rate_limited:
                    reply = (
                        "⏳ AI-gu wuxuu gaaray xadka isticmaalka.\n\n"
                        "Fadlan isticmaal qaab kale sida: Deyn cusub: MAGACA $lacagta, waxka bedelka: edit MAGACA $lacagta, "
                        "delete MAGACA, ama search MAGACA."
                    )
                    send_whatsapp(sender_phone, reply)
                    return {"status": "gemini_rate_limited_unparsed"}
                send_whatsapp(
                    sender_phone,
                    "⚠️ AI-gu hadda ma shaqaynayo. "
                    "Fadlan isticmaal tusaalayaashan MAGACA $ lacagta ama search MAGACA."
                )
                return {"status": "gemini_error_unparsed"}

    # If the user answered the pending question, apply that answer to every
    # entry extracted from the saved original message. Otherwise require an
    # explicit direction before any ADD/PAY financial operation.
    if forced_transaction_action:
        for parsed_entry in entries:
            if parsed_entry.get("action") in {"ADD", "PAY"}:
                parsed_entry["action"] = forced_transaction_action
    elif not pdf_only_requested:
        explicit_direction = classify_transaction_direction(message_text)
        has_financial_entries = any(
            isinstance(item, dict)
            and item.get("action") in {"ADD", "PAY"}
            and item.get("customer_name")
            and item.get("amount") is not None
            for item in entries
        )
        # Only intercept likely debt/payment entries. Non-financial commands
        # (LIST, SEARCH, HISTORY, EDIT, etc.) continue through normal handling.
        if has_financial_entries and explicit_direction is None:
            try:
                supabase.table("pending_transaction_clarifications").upsert({
                    "sender_phone": sender_phone,
                    "business_user_id": business_user_id,
                    "original_message": str(message_text),
                    "parsed_entries": entries,
                    "created_at": datetime.now(timezone.utc).isoformat(),
                }, on_conflict="sender_phone").execute()
            except Exception as pending_err:
                print(f"❌ Could not save pending transaction clarification: {pending_err}")
                send_whatsapp(sender_phone, "❌ Ma kaydin karo fariinta sugaysa. Waxba lama diiwaangelin; fadlan mar kale isku day.")
                return {"status": "pending_clarification_save_error"}
            send_whatsapp(
                sender_phone,
                "Waxaad soo qortay magac iyo lacag keliya.\n\n"
                "*Maxaad ula jeeddaa?*\n\n"
                "1️⃣ Dayn cusub – Taabo 1\n\n"
                "2️⃣ Dayn bixin – Taabo 2\n\n"
                "3️⃣ JOOJI – Taabo 3\n\n"
                "Waxba lama diiwaangelinayo ilaa aad doorato."
            )
            return {"status": "awaiting_transaction_clarification"}
        elif has_financial_entries and explicit_direction:
            for parsed_entry in entries:
                if parsed_entry.get("action") in {"ADD", "PAY"}:
                    parsed_entry["action"] = explicit_direction

    # Both Gemini and local fallback use the same downstream business rules.
    # In particular, ordinary amounts add; explicit edit/ka dhig replaces.
    
    # Make explicit customer-search commands deterministic, like HISTORY:
    # don't depend on Gemini choosing the correct action or extracting the full name.
    # HISTORY/statement wording takes priority and is never converted to SEARCH.
    original_text = str(message_text or "").strip()
    lower_text = original_text.casefold()
    is_history_request = any(word in lower_text for word in (
        "history", "taariikh", "statement", "xisaab"
    ))
    search_prefix = re.match(
        r"^\s*(?:search|find|lookup|look up|raadi|raadso)\b\s*[:,-]?\s*(.+?)\s*$",
        original_text,
        flags=re.IGNORECASE,
    )
    if search_prefix and not is_history_request:
        explicit_search_name = search_prefix.group(1).strip()
        if explicit_search_name:
            print(f"🔎 Explicit search command detected; routing directly to SEARCH: {explicit_search_name!r}")
            entries = [{"action": "SEARCH", "customer_name": explicit_search_name}]

    # Deterministic amount semantics: ordinary "Name $10" means ADD $10 to
    # the existing active debt if one exists; explicit EDIT / "ka dhig" means
    # replace the balance instead. Do not leave this decision to the AI model.
    explicit_replace_amount = bool(re.search(
        r"(?:^\s*(?:edit|kadhig|ka\s+dhig|ka\s+dhigo)\b|\bka\s+dhig(?:\s|$)|\bkadhig(?:\s|$))",
        original_text,
        flags=re.IGNORECASE,
    ))
    if explicit_replace_amount and not is_history_request and not search_prefix:
        for parsed_entry in entries:
            if parsed_entry.get("action") in {"ADD", "EDIT"}:
                source_has_amount_for_entry = message_has_explicit_amount_for_name(
                    original_text, parsed_entry.get("customer_name")
                )
                if (
                    parsed_entry.get("new_amount") is None
                    and parsed_entry.get("amount") is not None
                    and source_has_amount_for_entry
                ):
                    parsed_entry["new_amount"] = parsed_entry.get("amount")
                elif not source_has_amount_for_entry:
                    # Do not let a guessed/copied amount overwrite a balance
                    # when the user's explicit edit only names a date or person.
                    parsed_entry["amount"] = None
                    parsed_entry["new_amount"] = None
                if parsed_entry.get("new_date") is None and parsed_entry.get("promised_date") is not None:
                    parsed_entry["new_date"] = parsed_entry.get("promised_date")
                parsed_entry["action"] = "EDIT"
                print(f"✏️ Explicit edit/ka dhig wording detected; replacing fields for {parsed_entry.get('customer_name')!r}")

    successful_inserts = []
    failed_inserts = []
    
    for entry in entries:
        action = entry.get("action", "ADD")
        name = entry.get("customer_name")
        amount = entry.get("amount")
        promised_date = entry.get("promised_date")
        days_until_due = entry.get("days_until_due")
        customer_phone = entry.get("customer_phone")
        new_amount = entry.get("new_amount")
        new_date = entry.get("new_date")
        new_phone = entry.get("new_phone")
        payment_type = str(entry.get("payment_type") or "UNKNOWN").upper()
        filter_date = entry.get("filter_date")
        filter_type = entry.get("filter_type")

        date_only_update = False
        # If a message has a customer name + due date but NO amount, treat it as
        # a request to update that customer's existing debt date, not create a
        # second debt with amount 0. Example: existing debt is $4 with no due
        # date; "C/SAMAD SANDHEERE oct 10" should update its date to Oct 10.
        source_has_amount = message_has_explicit_amount_for_name(message_text, name) if name else False
        if action == "ADD" and amount is not None and not source_has_amount and not new_phone:
            # The model may hallucinate/copy a balance not present in the user's
            # message. Never apply that amount as a financial transaction.
            print(f"⚠️ Ignoring AI amount not present in source message for {name!r}: {amount!r}")
            amount = None
            entry["amount"] = None
        # If the user gave a due date but no amount in their own message, treat
        # this as a date-only edit even if the AI hallucinated/copied an amount.
        date_intent_without_amount = (
            (promised_date is not None or days_until_due is not None)
            and not source_has_amount
        )
        if action == "ADD" and not new_phone and (amount is None or date_intent_without_amount):
            date_only = promised_date
            if not date_only and days_until_due is not None:
                try:
                    date_only = (today_eat() + timedelta(days=int(days_until_due))).isoformat()
                except (TypeError, ValueError):
                    date_only = None
            if date_only:
                action = "EDIT"
                date_only_update = True
                new_date = date_only
                # Ignore any amount the AI may have copied/inferred; the source
                # message did not state one, so this operation must change only
                # the due date and must preserve the existing balance.
                amount = None
                new_amount = None
                entry["amount"] = None
                entry["new_amount"] = None
                entry["action"] = "EDIT"
                entry["new_date"] = date_only
                print(f"🗓️ Date-only ADD converted to EDIT for {name!r}: {date_only} (amount preserved)")
            else:
                send_whatsapp(
                    sender_phone,
                    "⚠️ Lacagta deynta lama sheegin.\n\n"
                    "Haddii aad rabto inaad beddesho taariikhda ballanta deyn hore, qor magaca macmiilka iyo taariikhda cusub.\n"
                    "Tusaale: Faarax oct 10\n"
                    "Deyn cusubna sidan u qor: Axmed $5 oct 11"
                )
                failed_inserts.append({"name": name or "Unknown", "reason": "Amount missing for new debt"})
                continue

        # Recover the full stored name from the original WhatsApp message if AI shortened it.
        if name and action in {"PAY", "EDIT", "DELETE", "HISTORY", "SEARCH"}:
            try:
                recovered_name = resolve_name_from_original_message(
                    business_user_id, message_text, name
                )
                if recovered_name:
                    name = recovered_name
                    entry["customer_name"] = recovered_name
            except Exception as name_err:
                print(f"⚠️ Original-message name resolution failed: {name_err}")
        
        if not name and action not in ["LIST", "REPORT", "EXPORT"]:
            failed_inserts.append({"name": "Unknown", "reason": "No name"})
            continue
        
        if action == "ADD":
            try:
                if amount is None and not new_phone:
                    send_whatsapp(sender_phone, "⚠️ Lacagta deynta lama sheegin. Tusaale: C/SAMAD SANDHEERE $4 oct 10")
                    failed_inserts.append({"name": name, "reason": "Amount missing for new debt"})
                    continue
                if not promised_date and days_until_due is not None:
                    promised_date = (today_eat() + timedelta(days=int(days_until_due))).isoformat()
                # Keep promised_date as None when the user did not specify a due date.
                
                if new_phone and not amount:
                    phone_matches = find_debtor_matches(business_user_id, name)
                    distinct_phone_names = {normalize_customer_name(d.get("name")) for d in phone_matches}
                    if len(distinct_phone_names) > 1:
                        ask_for_full_name(sender_phone, phone_matches, "EDIT")
                        continue
                    if phone_matches:
                        matched_name = phone_matches[0]["name"]
                        updated = (supabase.table("customers").update({"phone_number": new_phone})
                                   .eq("business_user_id", business_user_id).eq("name", matched_name).execute())
                        if updated.data:
                            send_whatsapp(sender_phone, f"✅ {matched_name} phone number saved: {new_phone}")
                            successful_inserts.append(entry)
                        else:
                            send_whatsapp(sender_phone, f"❌ Lambarka {matched_name} lama cusboonaysiin.")
                            failed_inserts.append({"name": name, "reason": "Phone update returned no rows"})
                        continue
                    else:
                        send_whatsapp(sender_phone, f"❌ Lama helin qofka {name} si lambarkiisa loo kaydiyo.")
                        failed_inserts.append({"name": name, "reason": "Debtor not found for phone update"})
                        continue
                
                # Amounts without an explicit EDIT / "ka dhig" are additive.
                # If this customer already has exactly one active debt, update
                # that row instead of creating a duplicate debtor/debt record.
                # If the name is ambiguous or multiple active rows exist, ask
                # the user rather than changing the wrong balance.
                if amount is not None and not new_phone:
                    matches = find_debtor_matches(business_user_id, name)
                    distinct_names = {normalize_customer_name(row.get("name")) for row in matches}
                    if len(distinct_names) > 1:
                        ask_for_full_name(sender_phone, matches, "EDIT")
                        continue

                    active_matches = [
                        row for row in matches
                        if row.get("is_paid") is not True and float(row.get("amount") or 0) > 0
                    ]
                    if len(active_matches) > 1:
                        ask_for_full_name(sender_phone, active_matches, "EDIT")
                        continue

                    if len(active_matches) == 1:
                        existing = active_matches[0]
                        try:
                            add_amount = float(amount)
                        except (TypeError, ValueError):
                            send_whatsapp(sender_phone, "❌ Lacagta lagu darayo ma saxna.")
                            failed_inserts.append({"name": name, "reason": "Invalid additive amount"})
                            continue
                        if add_amount <= 0:
                            send_whatsapp(sender_phone, "❌ Lacagta lagu darayo waa inay ka badan tahay $0.")
                            failed_inserts.append({"name": name, "reason": "Additive amount must be positive"})
                            continue

                        old_amount = float(existing.get("amount") or 0)
                        update_data = {"amount": round(old_amount + add_amount, 2), "is_paid": False}
                        if promised_date:
                            try:
                                update_data["promised_date"] = datetime.strptime(str(promised_date), "%Y-%m-%d").date().isoformat()
                            except (TypeError, ValueError):
                                send_whatsapp(sender_phone, "❌ Taariikh khaldan. Isticmaal YYYY-MM-DD.")
                                continue
                        if new_phone:
                            update_data["phone_number"] = new_phone

                        updated_result = (
                            supabase.table("customers")
                            .update(update_data)
                            .eq("id", existing["id"])
                            .eq("business_user_id", business_user_id)
                            .select("id, name, amount, promised_date, is_paid")
                            .execute()
                        )
                        if not updated_result.data:
                            send_whatsapp(sender_phone, "❌ Lacagta laguma darin. Database-ku wax jawaab ah ma soo celin.")
                            failed_inserts.append({"name": name, "reason": "Add-to-existing update returned no rows"})
                            continue

                        updated = updated_result.data[0]
                        send_whatsapp(
                            sender_phone,
                            f"✅ Lacag ayaa lagu daray deyntii hore!\n\n"
                            f"👤 Macmiilka: {updated['name']}\n"
                            f"➕ Lacag lagu daray: ${add_amount:.2f}\n"
                            f"💵 Deynta cusub: ${float(updated.get('amount') or 0):.2f}\n"
                            f"📅 Ballanta: {updated.get('promised_date') or 'lama gelin'}"
                        )
                        entry["action"] = "ADJUST"
                        successful_inserts.append(entry)
                        continue

                    # If matching records exist but all are paid, start a new
                    # debt row using the canonical stored spelling.
                    if matches:
                        name = matches[0].get("name") or name
                        entry["customer_name"] = name

                debtor_data = {
                    'business_user_id': business_user_id,
                    'name': name,
                    'amount': float(amount) if amount is not None else 0,
                    'promised_date': promised_date,
                    'phone_number': new_phone if new_phone else None,
                    'is_paid': False
                }

                result = supabase.table("customers").insert(debtor_data).execute()
                if not result.data:
                    send_whatsapp(sender_phone, f"❌ Deynta {name} lama diiwaangelin. Database-ku wax jawaab ah ma soo celin.")
                    failed_inserts.append({"name": name, "reason": "Insert returned no rows"})
                    continue
                successful_inserts.append(entry)
                
            except Exception as e:
                failed_inserts.append({"name": name, "reason": str(e)})
        
        elif action == "PAY":
            try:
                payment_amount = entry.get("amount")
                payment_type = str(entry.get("payment_type") or "UNKNOWN").upper()
                matches = find_debtor_matches(business_user_id, name)

                if len(matches) == 0:
                    send_whatsapp(sender_phone, f"❌ Lama helin deynta aan weli la bixin ee {name}.")
                    failed_inserts.append({"name": name, "reason": "Unpaid debtor not found"})
                    continue

                if len(matches) > 1:
                    ask_for_full_name(sender_phone, matches, "PAY")
                    continue

                debtor = matches[0]
                current_balance = float(debtor.get("amount") or 0)

                if current_balance <= 0 or debtor.get("is_paid") is True:
                    send_whatsapp(sender_phone, f"✅ {debtor['name']} hore ayuu u bixiyay deyntiisa.")
                    continue

                # A missing amount is a full payment ONLY when the AI explicitly says FULL.
                if payment_amount is None and payment_type != "FULL":
                    send_whatsapp(
                        sender_phone,
                        f"💵 {debtor['name']} lacag intee le'eg ayaad ka heshay?\n"
                        f"Tusaale: {debtor['name']} ka jar $10.\n"
                        "Haddii uu deynta oo dhan bixiyay, qor: "
                        f"{debtor['name']} wuu bixiyay deyntii oo dhan."
                    )
                    continue

                if payment_amount is None:
                    payment_amount = current_balance
                else:
                    try:
                        payment_amount = float(payment_amount)
                    except (TypeError, ValueError):
                        send_whatsapp(sender_phone, "❌ Lacagta ma fahmin. Tusaale: Cali ka jar $10.")
                        continue

                if payment_amount <= 0:
                    send_whatsapp(sender_phone, "❌ Lacagta la bixiyay waa inay ka badan tahay $0.")
                    continue

                if payment_amount - current_balance > 0.009:
                    send_whatsapp(
                        sender_phone,
                        f"⚠️ {debtor['name']} haraaga deyntiisu waa ${current_balance:.2f}, "
                        f"laakiin waxaad sheegtay ${payment_amount:.2f}. Lacag-bixinta lama diiwaangelin "
                        "si aan haraaga uga dhigin tiro taban. Hubi lacagta oo mar kale dir."
                    )
                    continue
                actual_payment = round(payment_amount, 2)
                new_balance = round(max(0.0, current_balance - actual_payment), 2)
                is_now_paid = new_balance <= 0

                # Atomically insert the payment and update the balance inside PostgreSQL.
                # Apply the companion SQL migration file before deploying this version.
                rpc_result = supabase.rpc("record_debt_payment", {
                    "p_customer_id": str(debtor["id"]),
                    "p_business_user_id": str(business_user_id),
                    "p_amount": actual_payment,
                }).execute()
                rpc_data = rpc_result.data
                if isinstance(rpc_data, list):
                    rpc_data = rpc_data[0] if rpc_data else None
                if not isinstance(rpc_data, dict) or not rpc_data.get("id"):
                    raise RuntimeError("record_debt_payment returned no debt row; apply supabase_record_debt_payment.sql and check RLS")
                updated_debtor = rpc_data
                new_balance = float(updated_debtor.get("amount") or 0)
                is_now_paid = bool(updated_debtor.get("is_paid")) or new_balance <= 0
                if is_now_paid:
                    send_whatsapp(
                        sender_phone,
                        f"✅ {updated_debtor['name']} deyntii oo dhan waa la bixiyay. "
                        f"Lacagta la diiwaangeliyay: ${actual_payment:.2f}."
                    )
                else:
                    send_whatsapp(
                        sender_phone,
                        f"✅ {updated_debtor['name']} wuxuu bixiyay ${actual_payment:.2f}. "
                        f"Haray: ${float(updated_debtor['amount']):.2f}."
                    )

            except Exception as e:
                print(f"❌ Payment error: {type(e).__name__}: {e}")
                send_whatsapp(
                    sender_phone,
                    f"❌ Lacag-bixintu way fashilantay ({type(e).__name__}). Hubi server logs-ka."
                )
                failed_inserts.append({"name": name, "reason": f"Payment error: {type(e).__name__}: {e}"})
        
        elif action == "LIST":
            try:
                # Detect whether the user asked for due dates
                text_lower = message_text.lower()

                wants_due_dates = any(keyword in text_lower for keyword in [
                    "balanta",
                    "balamaha",
                    "ballanta",
                    "ballamaha",
                    "balan",
                    "due",
                    "date"
                ])

                # Start with unpaid debts only
                query = (
                    supabase.table("customers")
                    .select("*")
                    .eq("business_user_id", business_user_id)
                    .eq("is_paid", False)
                )

                # If a specific date was requested, filter by that date
                if filter_date:
                    query = query.eq("promised_date", filter_date)

                    if filter_type == "today":
                        message_title = "📋 *Balamaha Maanta*"
                    elif filter_type == "tomorrow":
                        message_title = "📋 *Balamaha Berri*"
                    else:
                        message_title = f"📋 *Balamaha {filter_date}*"

                    wants_due_dates = True
                else:
                    query = query.order("promised_date", desc=False)

                    if wants_due_dates:
                        message_title = "📋 *Liiska Deynta iyo Balamaha*"
                    else:
                        message_title = "📋 *Liiska Deynta*"

                debts_query = query.execute()

                if not debts_query.data:
                    if filter_date:
                        send_whatsapp(
                            sender_phone,
                            f"✅ Ma jiraan deymo balantoodu tahay {filter_date}."
                        )
                        send_due_list_followup(sender_phone)
                    else:
                        send_whatsapp(
                            sender_phone,
                            "✅ Ma jiraan deyn aan la bixin."
                        )
                    continue

                debt_list = []
                total = 0
                overdue_count = 0
                today = today_eat()

                for index, debt in enumerate(debts_query.data, start=1):
                    debtor_name = debt["name"]
                    debtor_amount = float(debt["amount"])
                    due_date = debt.get("promised_date")

                    total += debtor_amount

                    if wants_due_dates:
                        status = ""

                        if due_date:
                            try:
                                due = datetime.strptime(
                                    due_date,
                                    "%Y-%m-%d"
                                ).date()

                                days_left = (due - today).days

                                if days_left < 0:
                                    status = (
                                        f" ⚠️ Balan dhaaf "
                                        f"({abs(days_left)} maalin)"
                                    )
                                    overdue_count += 1
                                elif days_left == 0:
                                    status = " 🔴 Balanta maanta"
                                else:
                                    status = f" 📅 {due_date}"

                            except (TypeError, ValueError):
                                status = f" 📅 {due_date}"

                        debt_list.append(
                            f"{index}. {debtor_name}: "
                            f"${debtor_amount:.2f}{status} "
                            f" {due_date or 'lama gelin'}"
                        )
                    else:
                        debt_list.append(
                            f"{index}. {debtor_name}: "
                            f"${debtor_amount:.2f}"
                        )

                message = (
                    f"{message_title} "
                    f"({len(debts_query.data)} macmiil):\n\n"
                    + "\n".join(debt_list)
                )

                if wants_due_dates and overdue_count > 0:
                    message = (
                        f"⚠️ {overdue_count} deyn balan dhaaftay:\n\n"
                        + message
                    )

                message += (
                    f"\n\n💰 Lacagta guud: "
                    f"${total:.2f}"
                )

                send_whatsapp(sender_phone, message)

                if filter_date:
                    send_due_list_followup(sender_phone)

            except Exception as e:
                print(f"❌ List error: {e}")
                send_whatsapp(
                    sender_phone,
                    "❌ Khalad ayaa dhacay marka liiska la soo saarayay."
                )
                failed_inserts.append({
                    "name": "LIST",
                    "reason": f"List error: {str(e)}"
                })

        elif action == "EDIT":
            try:
                matches = find_debtor_matches(business_user_id, name)

                if len(matches) == 0:
                    send_whatsapp(sender_phone, f"❌ Lama helin deynta aan weli la bixin ee {name}.")
                    failed_inserts.append({"name": name, "reason": "Debtor not found"})
                    continue

                if date_only_update:
                    # Do not select by due date if fuzzy matching returned different people.
                    distinct_names = {normalize_customer_name(row.get("name")) for row in matches}
                    if len(distinct_names) > 1:
                        ask_for_full_name(sender_phone, matches, "EDIT")
                        continue
                    # Prefer the unique unpaid debt without a due date. Never create
                    # a new debt for a date-only message or guess between records.
                    undated_matches = [
                        row for row in matches
                        if not row.get("promised_date")
                        and float(row.get("amount") or 0) > 0
                        and row.get("is_paid") is not True
                    ]
                    if not undated_matches:
                        # Older code assigned today's date automatically when
                        # none was provided. Support that legacy case only when
                        # exactly one positive, unpaid row is due today.
                        today_str = today_eat().isoformat()
                        legacy_today_matches = [
                            row for row in matches
                            if row.get("promised_date") == today_str
                            and float(row.get("amount") or 0) > 0
                            and row.get("is_paid") is not True
                        ]
                        if len(legacy_today_matches) == 1:
                            undated_matches = legacy_today_matches
                    if len(undated_matches) == 1:
                        matches = undated_matches
                    elif len(undated_matches) == 0 and len(matches) == 1 and matches[0].get("is_paid") is not True and float(matches[0].get("amount") or 0) > 0:
                        # A single existing unpaid debt is an unambiguous target even if it already has a date.
                        pass
                    else:
                        ask_for_full_name(sender_phone, matches, "EDIT")
                        continue
                elif len(matches) > 1:
                    ask_for_full_name(sender_phone, matches, "EDIT")
                    continue

                debtor = matches[0]
                update_data = {}

                # Fallbacks support inconsistent model output, e.g. amount instead of new_amount.
                amount_to_set = new_amount if new_amount is not None else amount
                date_to_set = new_date if new_date is not None else promised_date

                if amount_to_set is not None:
                    try:
                        amount_to_set = float(amount_to_set)
                    except (TypeError, ValueError):
                        send_whatsapp(sender_phone, "❌ Lacagta cusub ma saxna.")
                        continue
                    if amount_to_set < 0:
                        send_whatsapp(sender_phone, "❌ Lacagtu ma noqon karto tiro taban.")
                        continue
                    update_data["amount"] = amount_to_set
                    update_data["is_paid"] = amount_to_set <= 0

                if date_to_set is not None:
                    try:
                        parsed_date = datetime.strptime(str(date_to_set), "%Y-%m-%d").date()
                        update_data["promised_date"] = parsed_date.isoformat()
                    except (TypeError, ValueError):
                        send_whatsapp(sender_phone, "❌ Taariikh khaldan. Isticmaal YYYY-MM-DD, tusaale 2026-10-20.")
                        continue

                if not update_data:
                    send_whatsapp(
                        sender_phone,
                        "❌ Ma helin lacag ama taariikh cusub.\n"
                        "Tusaale: Cali deyntiisa ka dhig $50\n"
                        "Ama: Cali balantiisa ka dhig 2026-10-20"
                    )
                    failed_inserts.append({"name": name, "reason": "No changes supplied"})
                    continue

                result = (
                    supabase.table("customers")
                    .update(update_data)
                    .eq("id", debtor["id"])
                    .eq("business_user_id", business_user_id)
                    .select("id, name, amount, promised_date, is_paid")
                    .execute()
                )
                if not result.data:
                    send_whatsapp(sender_phone, "❌ Waxba lama beddelin. Hubi rukhsadaha database-ka (RLS).")
                    failed_inserts.append({"name": name, "reason": "Update returned no rows"})
                    continue

                updated = result.data[0]
                changes = []
                if "amount" in update_data:
                    changes.append(f"💵 Lacag: ${float(debtor['amount']):.2f} → ${float(updated['amount']):.2f}")
                if "promised_date" in update_data:
                    changes.append(f"📅 Ballan: {debtor.get('promised_date') or 'lama gelin'} → {updated['promised_date']}")

                send_whatsapp(sender_phone, f"✅ {updated['name']} waa la cusboonaysiiyay:\n" + "\n".join(changes))
                successful_inserts.append(entry)

            except Exception as e:
                print(f"❌ Edit error: {type(e).__name__}: {e}")
                send_whatsapp(sender_phone, f"❌ Wax ka beddelku wuu fashilmay ({type(e).__name__}). Hubi server logs-ka.")
                failed_inserts.append({"name": name, "reason": f"Edit error: {type(e).__name__}: {e}"})
        
        elif action == "DELETE":
            try:
                matches = find_debtor_matches(business_user_id, name)

                if len(matches) == 0:
                    send_whatsapp(sender_phone, f"❌ Lama helin {name}.")
                    failed_inserts.append({
                        "name": name,
                        "reason": "Debtor not found"
                    })
                    continue

                if len(matches) > 1:
                    ask_for_full_name(sender_phone, matches, "DELETE")
                    continue

                debtor = matches[0]

                (
                    supabase.table("customers")
                    .delete()
                    .eq("id", debtor["id"])
                    .eq("business_user_id", business_user_id)
                    .execute()
                )

                send_whatsapp(
                    sender_phone,
                    f"✅ Deynta {debtor['name']} (${debtor['amount']}) waa la tirtiray."
                )
                successful_inserts.append(entry)

            except Exception as e:
                print(f"❌ Delete error: {e}")
                send_whatsapp(
                    sender_phone,
                    "❌ Khalad ayaa dhacay marka deynta la tirtirayay."
                )
                failed_inserts.append({
                    "name": name,
                    "reason": f"Delete error: {str(e)}"
                })
        
        elif action == "SEARCH":
            try:
                search_matches = find_debtor_matches(business_user_id, name)
                if not search_matches:
                    send_whatsapp(sender_phone, f"❌ Lama helin qofka {name}. Hubi higgaadda magaca ama isku day magaciisa oo buuxa.")
                    continue

                distinct_search_names = {
                    normalize_customer_name(d.get("name"))
                    for d in search_matches
                }

                if len(distinct_search_names) > 1:
                    ask_for_full_name(sender_phone, search_matches, "SEARCH")
                    continue

                matched_name = search_matches[0].get("name", name)

                total_debt = sum(
                    float(d.get("amount") or 0)
                    for d in search_matches
                    if not d.get("is_paid")
                )

                paid_count = sum(
                    1 for d in search_matches
                    if d.get("is_paid")
                )

                message = (
                    f"🔎 *Natiijada raadinta: {matched_name}*\n"
                    
                    f"💰 Wadarta deynta hadhsan: *${total_debt:.2f}*\n"
                    
                    f"Deyn bixin hore: {paid_count}"
                )

                
                send_whatsapp(sender_phone, message)
                
            except Exception as e:
                print(f"❌ Search error: {type(e).__name__}: {e}")
                send_whatsapp(sender_phone, "❌ Khalad ayaa dhacay. Fadlan isku day inaad saxdo magaca.")
                failed_inserts.append({"name": name, "reason": f"Search error: {type(e).__name__}: {e}"})

       
        elif action == "HISTORY":
            try:
                # Full customer statement: debt records, payment events, and current outstanding balance.
                history_matches = find_debtor_matches(business_user_id, name)

                if not history_matches:
                    send_whatsapp(
                        sender_phone,
                        f"❌ Taariikh looma helin macmiilka {name}."
                    )

                elif len({normalize_customer_name(d.get("name")) for d in history_matches}) > 1:
                    ask_for_full_name(
                        sender_phone,
                        history_matches,
                        "HISTORY"
                    )

                else:
                    history_matches.sort(
                        key=lambda d: str(d.get("created_at") or "")
                    )

                    customer_ids = [
                        d.get("id")
                        for d in history_matches
                        if d.get("id") is not None
                    ]

                    payment_rows = []

                    if customer_ids:
                        payment_result = (
                            supabase.table("payments")
                            .select("amount, paid_at, customer_id")
                            .eq("business_user_id", business_user_id)
                            .in_("customer_id", customer_ids)
                            .order("paid_at")
                            .execute()
                        )
                        payment_rows = payment_result.data or []

                    payments_by_debt = {}

                    for payment in payment_rows:
                        payments_by_debt.setdefault(
                            str(payment.get("customer_id")),
                            []
                        ).append(payment)

                    lines = [
                        f"📒 *STATEMENT / XISAABTA MACMIILKA: {history_matches[0].get('name', name)}*",
                        ""
                    ]

                    total_balance = 0.0
                    total_paid = 0.0

                    for index, debt in enumerate(history_matches, 1):
                        balance = float(debt.get("amount") or 0)
                        debt_paid = (
                            bool(debt.get("is_paid"))
                            or balance <= 0
                        )

                        total_balance += max(balance, 0.0)

                        lines.append(
                            f"*Deyn #{index}* — "
                            f"{str(debt.get('created_at') or '')[:10] or 'Taariikh lama hayo'}"
                        )

                        lines.append(
                            f"  • Haraaga hadda: ${max(balance, 0.0):.2f}"
                        )

                        due_date = debt.get("promised_date")

                        lines.append(
                            f"  • Ballan: {due_date if due_date else 'Lama cayimin'}"
                        )

                        lines.append(
                            f"  • Xaalad: "
                            f"{'✅ LA BIXIYAY' if debt_paid else '⏳ WELI LAMA BIXIN'}"
                        )

                        debt_payments = payments_by_debt.get(
                            str(debt.get("id")),
                            []
                        )

                        if debt_payments:
                            lines.append("  • Lacag-bixinnada:")

                            for payment in debt_payments:
                                paid_amount = float(
                                    payment.get("amount") or 0
                                )

                                total_paid += paid_amount

                                paid_date = (
                                    str(payment.get("paid_at") or "")[:10]
                                    or "Taariikh lama hayo"
                                )

                                lines.append(
                                    f"    - {paid_date}: ${paid_amount:.2f}"
                                )

                        else:
                            lines.append(
                                "  • Lacag-bixin hore: Ma jirto"
                            )

                        lines.append("")

                    if not payment_rows:
                        total_paid = 0.0

                    lines.extend([
                        "━━━━━━━━━━━━━━",
                        f"💵 *Wadarta lacagta la bixiyay ee diiwaangashan:* ${total_paid:.2f}",
                        f"📌 *Wadarta hadhaaga deynta:* ${total_balance:.2f}",
                    ])

                    message = "\n".join(lines)

                    if len(message) > 6000:
                        message = (
                            message[:5850]
                            + "\n\n… Liiska waa la soo gaabiyay; "
                            "macmiilku wuxuu leeyahay diiwaanno badan."
                        )

                    matched_customer_name = history_matches[0].get(
                        "name",
                        name
                    )

                    LAST_HISTORY_REQUESTS[sender_phone] = {
                        "business_user_id": business_user_id,
                        "customer_name": matched_customer_name,
                    }

                    if not pdf_only_requested:
                        send_whatsapp(
                            sender_phone,
                            message
                            + "\n\n📎 Haddii aad PDF ku rabto "
                              "xisaabta macmiilkan, soo qor *PDF*."
                        )

                    else:
                        try:
                            pdf_bytes = build_statement_pdf(
                                matched_customer_name,
                                history_matches,
                                payments_by_debt,
                                total_paid,
                                total_balance,
                                business_user.get("name")
                            )

                            send_whatsapp_file(
                                sender_phone,
                                (
                                    "daynjir_statement_"
                                    f"{re.sub(r'[^A-Za-z0-9_-]+', '_', str(matched_customer_name))}"
                                    ".pdf"
                                ),
                                pdf_bytes,
                                "application/pdf",
                                f"📄 PDF — Xisaabta {matched_customer_name}"
                            )

                        except Exception as pdf_error:
                            print(
                                "⚠️ PDF statement generation failed: "
                                f"{type(pdf_error).__name__}: {pdf_error}"
                            )

                            send_whatsapp(
                                sender_phone,
                                "❌ PDF lama samayn karo hadda. "
                                "Fadlan mar kale isku day."
                            )

            except Exception as e:
                print(
                    f"❌ History error: {type(e).__name__}: {e}"
                )

                send_whatsapp(
                    sender_phone,
                    "❌ Khalad ayaa dhacay markii "
                    "statement-ka la diyaarinayay."
                )

                failed_inserts.append({
                    "name": name,
                    "reason": f"History error: {type(e).__name__}: {e}"
                })


        elif action == "REPORT":
            try:
                all_debts_result = (
                    supabase.table("customers")
                    .select("*")
                    .eq("business_user_id", business_user_id)
                    .execute()
                )

                all_debts = all_debts_result.data or []

                if not all_debts:
                    send_whatsapp(
                        sender_phone,
                        "✅ Ma jiraan deymo ku jira nidaamka."
                    )
                    continue

                today = today_eat()

                if filter_type == "week":
                    period_start = (
                        today - timedelta(days=today.weekday())
                    )
                    title = "📊 Warbixinta toddobaadka"

                elif filter_type == "month":
                    period_start = today.replace(day=1)
                    title = "📊 Warbixinta bisha"

                else:
                    period_start = today
                    title = "📊 Warbixinta maanta"

                start_utc = (
                    datetime.combine(
                        period_start,
                        datetime.min.time(),
                        tzinfo=EAT
                    ).astimezone(timezone.utc)
                )

                end_utc = (
                    datetime.combine(
                        today + timedelta(days=1),
                        datetime.min.time(),
                        tzinfo=EAT
                    ).astimezone(timezone.utc)
                )

                start_iso = start_utc.isoformat()
                end_iso = end_utc.isoformat()

                payments_result = (
                    supabase.table("payments")
                    .select("amount, paid_at, customer_id")
                    .eq("business_user_id", business_user_id)
                    .gte("paid_at", start_iso)
                    .lt("paid_at", end_iso)
                    .execute()
                )

                period_payments = payments_result.data or []

                new_debts = [
                    d
                    for d in all_debts
                    if d.get("created_at")
                    and start_iso <= str(d.get("created_at")) < end_iso
                ]

                new_debt_amount = sum(
                    float(d.get("amount") or 0)
                    for d in new_debts
                )

                total_outstanding = sum(
                    max(float(d.get("amount") or 0), 0.0)
                    for d in all_debts
                    if d.get("is_paid") is not True
                )

                period_collected = sum(
                    float(p.get("amount") or 0)
                    for p in period_payments
                )

                overdue = [
                    d
                    for d in all_debts
                    if d.get("is_paid") is not True
                    and d.get("promised_date")
                    and str(d.get("promised_date"))
                    < today.isoformat()
                ]

                overdue_amount = sum(
                    float(d.get("amount") or 0)
                    for d in overdue
                )

                due_today = [
                    d
                    for d in all_debts
                    if d.get("is_paid") is not True
                    and d.get("promised_date") == today.isoformat()
                ]

                message = (
                    f"{title}\n\n"
                    f"🆕 Tirada Deymaha cusub ee la diwaangeliyay: "
                    f"{len(new_debts)}\n"
                    f"💵 Lacagta soo xarootay: "
                    f"${period_collected:.2f}\n"
                    f"📌 Hadhaaga guud ee deynta hadda: "
                    f"${total_outstanding:.2f}\n"
                    f"⚠️ Deymaha ballan dhaafka ah: "
                    f"{len(overdue)}\n"
                    f"📅 Ballamaha maanta: "
                    f"{len(due_today)}\n"
                )

                send_whatsapp(
                    sender_phone,
                    message
                )

            except Exception as e:
                print(
                    f"❌ Report error: {type(e).__name__}: {e}"
                )

                send_whatsapp(
                    sender_phone,
                    "❌ Warbixinta lama diyaarin."
                )

                failed_inserts.append({
                    "name": "REPORT",
                    "reason": str(e)
                })


        elif action == "EXPORT":
            try:
                all_debts_result = (
                    supabase.table("customers")
                    .select("*")
                    .eq("business_user_id", business_user_id)
                    .order("promised_date", desc=False)
                    .execute()
                )

                debts_to_export = all_debts_result.data or []

                if not debts_to_export:
                    send_whatsapp(
                        sender_phone,
                        "✅ Ma jiraan deymo la soo saari karo."
                    )
                    continue

                csv_buffer = StringIO()

                writer = csv.writer(csv_buffer)

                writer.writerow([
                    "Name",
                    "Current Balance",
                    "Due Date",
                    "Phone",
                    "Status",
                    "Created At"
                ])

                for debt in debts_to_export:
                    balance = max(
                        float(debt.get("amount") or 0),
                        0.0
                    )

                    status = (
                        "PAID"
                        if debt.get("is_paid") is True
                        or balance <= 0
                        else "UNPAID"
                    )

                    writer.writerow([
                        debt.get("name", ""),
                        f"{balance:.2f}",
                        debt.get("promised_date") or "",
                        debt.get("phone_number") or "",
                        status,
                        debt.get("created_at") or ""
                    ])

                csv_content = (
                    csv_buffer
                    .getvalue()
                    .encode("utf-8-sig")
                )

                sent = send_whatsapp_file(
                    sender_phone,
                    f"daynjir_debts_{today_eat().isoformat()}.csv",
                    csv_content,
                    "text/csv",
                    f"📥 Deymaha la dhoofiyay: "
                    f"{len(debts_to_export)} diiwaan"
                )

                if not sent:
                    send_whatsapp(
                        sender_phone,
                        "❌ Faylka CSV lama dirin."
                    )

            except Exception as e:
                print(
                    f"❌ Export error: {type(e).__name__}: {e}"
                )

                send_whatsapp(
                    sender_phone,
                    "❌ Dhoofinta CSV way fashilantay. "
                    "Hubi server logs-ka."
                )

                failed_inserts.append({
                    "name": "EXPORT",
                    "reason": str(e)
                })

    # Send confirmation for ADD actions
    if successful_inserts:
        add_entries = [e for e in successful_inserts if e.get('action') == 'ADD']
        if add_entries:
            if len(add_entries) == 1:
                entry = add_entries[0]
                if entry.get('customer_phone'):
                    success_message = f"✅ Phone saved for {entry['customer_name']}: {entry['customer_phone']}"
                else:
                    success_message = f"""✅ Deyntan waa la keydiyay!

👤 Macmiilka: {entry['customer_name']}
💵 Lacagta: ${entry['amount']}
📅 Ballanta: {entry['promised_date']}"""
            else:
                success_message = f"""✅ Deymahan waa la keydiyay!

"""
                for entry in add_entries:
                    success_message += f"""👤 {entry['customer_name']}: ${entry['amount']} - {entry['promised_date']}
"""
            
            send_whatsapp(sender_phone, success_message)

    if failed_inserts:
        error_message = f"❌ {len(failed_inserts)} deyntii ma keydsamin:\n"
        for fail in failed_inserts:
            error_message += f"- {fail['name']}: {fail['reason']}\n"
        send_whatsapp(sender_phone, error_message)
    
    return {"status": "success"}


def cron_authorized(request: Request):
    """Authorize Render cron requests with CRON_SECRET.

    Render cron jobs should send either x-cron-secret or Authorization: Bearer <secret>.
    """
    secret = os.getenv("CRON_SECRET", "").strip()
    if not secret:
        return False

    supplied = request.headers.get("x-cron-secret", "").strip()
    auth = request.headers.get("authorization", "").strip()
    if auth.lower().startswith("bearer "):
        supplied = auth[7:].strip()

    return bool(supplied) and hmac.compare_digest(supplied, secret)


def _cron_date_boundaries():
    """Return today's East Africa date and UTC database boundaries."""
    today = today_eat()
    start_utc = datetime.combine(
        today,
        datetime.min.time(),
        tzinfo=EAT,
    ).astimezone(timezone.utc)
    end_utc = start_utc + timedelta(days=1)
    return today, start_utc.isoformat(), end_utc.isoformat()


def _safe_money(value):
    try:
        return float(value or 0)
    except (TypeError, ValueError):
        return 0.0


@app.get("/cron/daily-digest")
async def daily_digest(request: Request):
    """Send daily due/overdue reminders to every registered business user.

    This endpoint is intentionally lightweight:
    - only required database columns are selected
    - one business user's failure does not stop the others
    - WhatsApp calls already have a 10-second timeout in send_whatsapp()
    - logs contain counts rather than every database row
    """
    if not cron_authorized(request):
        from fastapi import HTTPException
        raise HTTPException(status_code=401, detail="Unauthorized cron request")

    print("🔔 DAILY DIGEST STARTED")
    today = today_eat().isoformat()

    sent_count = 0
    skipped_count = 0
    error_count = 0

    try:
        users_result = (
            supabase.table("business_users")
            .select("id, phone_number, name")
            .execute()
        )
        users = users_result.data or []
        print(f"👥 Business users found: {len(users)}")
    except Exception as e:
        print(f"❌ DAILY DIGEST database error loading business users: {type(e).__name__}: {e}")
        return {"status": "database_error"}

    for user in users:
        business_user_id = user.get("id")
        phone = str(user.get("phone_number") or "").strip()
        name = str(user.get("name") or "").strip()

        if not business_user_id or not phone:
            skipped_count += 1
            continue

        try:
            debts_result = (
                supabase.table("customers")
                .select("name, amount, promised_date")
                .eq("business_user_id", business_user_id)
                .eq("is_paid", False)
                .order("promised_date", desc=False)
                .execute()
            )
            debts = debts_result.data or []

            due_today = []
            for debt in debts:
                due_date = debt.get("promised_date")
                if not due_date:
                    continue
                if str(due_date) <= today:
                    due_today.append(
                        f"• {debt.get('name') or 'Macmiil'}: "
                        f"${_safe_money(debt.get('amount')):.2f} "
                        f"(due_date)"
                    )

            if not due_today:
                skipped_count += 1
                continue

            # Keep scheduled messages reasonably sized. The complete customer
            # list remains available through LIST/HISTORY in WhatsApp.
            max_items = 40
            shown = due_today[:max_items]
            omitted = len(due_today) - len(shown)

            message_lines = [
                "☀️ *Xasuusin* ☀️",
                "",
                "*Balamaha maanta & kuwa Balan dhaafka ah:*",
                *shown,
            ]
            if omitted > 0:
                message_lines.extend([
                    "",
                    f"➕ {omitted} kale ayaa jira. Qor *Liiska daynta* si aad u aragto dhammaan.",
                ])

            if name:
                message_lines.insert(1, f"👤 *{name}*")

            ok = send_whatsapp(phone, "\n".join(message_lines))
            if ok:
                sent_count += 1
                print(f"✅ Daily digest sent: user={business_user_id}, items={len(due_today)}")
            else:
                error_count += 1
                print(f"❌ Daily digest WhatsApp failed: user={business_user_id}")

        except Exception as e:
            error_count += 1
            print(
                f"❌ Daily digest user failed: user={business_user_id}, "
                f"{type(e).__name__}: {e}"
            )
            continue

    print(
        f"🏁 DAILY DIGEST FINISHED: sent={sent_count}, "
        f"skipped={skipped_count}, errors={error_count}"
    )
    return {
        "status": "done",
        "sent": sent_count,
        "skipped": skipped_count,
        "errors": error_count,
    }


@app.get("/cron/evening-checkin")
async def evening_checkin(request: Request):
    """Send a compact end-of-day activity summary to each business user."""
    if not cron_authorized(request):
        from fastapi import HTTPException
        raise HTTPException(status_code=401, detail="Unauthorized cron request")

    print("🌙 EVENING CHECK-IN STARTED")
    today, start_iso, end_iso = _cron_date_boundaries()

    sent_count = 0
    skipped_count = 0
    error_count = 0

    try:
        users_result = (
            supabase.table("business_users")
            .select("id, phone_number, name")
            .execute()
        )
        users = users_result.data or []
        print(f"👥 Business users found: {len(users)}")
    except Exception as e:
        print(f"❌ EVENING CHECK-IN database error loading business users: {type(e).__name__}: {e}")
        return {"status": "database_error"}

    for user in users:
        business_user_id = user.get("id")
        phone = str(user.get("phone_number") or "").strip()
        name = str(user.get("name") or "").strip()

        if not business_user_id or not phone:
            skipped_count += 1
            continue

        try:
            # Load today's customers once. This avoids one Supabase request per payment.
            customers_result = (
                supabase.table("customers")
                .select("id, name, amount, created_at")
                .eq("business_user_id", business_user_id)
                .execute()
            )
            customers = customers_result.data or []
            customer_by_id = {str(row.get("id")): row for row in customers}

            new_debts = []
            for customer in customers:
                created_at = customer.get("created_at")
                if created_at and start_iso <= str(created_at) < end_iso:
                    new_debts.append(customer)

            payments_result = (
                supabase.table("payments")
                .select("amount, paid_at, customer_id")
                .eq("business_user_id", business_user_id)
                .gte("paid_at", start_iso)
                .lt("paid_at", end_iso)
                .execute()
            )
            payments = payments_result.data or []

            # Inactivity has its own separate reminder. Do not send an empty
            # evening report as well, otherwise the user receives two messages.
            if not new_debts and not payments:
                skipped_count += 1
                print(f"⏭️ Evening report skipped: no activity for user={business_user_id}")
                continue

            lines = ["🌙 *Natiijada maanta*"]
            if name:
                lines.append(f"👤 *{name}*")
            lines.append("")

            if new_debts or payments:
                if new_debts:
                    lines.append("🆕 *Deymaha cusub maanta:*")
                    for debt in new_debts[:40]:
                        lines.append(
                            f"• {debt.get('name') or 'Macmiil'}: "
                            f"${_safe_money(debt.get('amount')):.2f}"
                        )
                    if len(new_debts) > 40:
                        lines.append(f"• ➕ {len(new_debts) - 40} kale")

                if payments:
                    lines.append("")
                    lines.append("💵 *Lacagihii maanta la helay:*")
                    total_paid = 0.0
                    for payment in payments[:40]:
                        amount = _safe_money(payment.get("amount"))
                        total_paid += amount
                        customer = customer_by_id.get(str(payment.get("customer_id")), {})
                        customer_name = customer.get("name") or "Macmiil"
                        lines.append(f"• {customer_name}: ${amount:.2f}")
                    if len(payments) > 40:
                        lines.append(f"• ➕ {len(payments) - 40} kale")
                    lines.append(f"*Wadarta lacagta la helay: ${sum(_safe_money(p.get('amount')) for p in payments):.2f}*")

                if new_debts:
                    total_new = sum(_safe_money(d.get("amount")) for d in new_debts)
                    lines.append(f"\n*Wadarta deynta cusub: ${total_new:.2f}*")

            lines.extend([
                "",
                "Si aad u diiwaangeliso deyn cusub ama lacag-bixin, ii soo dir magaca macmiilka iyo lacagta."
            ])

            ok = send_whatsapp(phone, "\n".join(lines))
            if ok:
                sent_count += 1
                print(
                    f"✅ Evening check-in sent: user={business_user_id}, "
                    f"new_debts={len(new_debts)}, payments={len(payments)}"
                )
            else:
                error_count += 1
                print(f"❌ Evening check-in WhatsApp failed: user={business_user_id}")

        except Exception as e:
            error_count += 1
            print(
                f"❌ Evening check-in user failed: user={business_user_id}, "
                f"{type(e).__name__}: {e}"
            )
            continue

    print(
        f"🏁 EVENING CHECK-IN FINISHED: sent={sent_count}, "
        f"skipped={skipped_count}, errors={error_count}"
    )
    return {
        "status": "done",
        "sent": sent_count,
        "skipped": skipped_count,
        "errors": error_count,
        "date": today.isoformat(),
    }


@app.get("/cron/inactivity-checkin")
async def inactivity_checkin(request: Request):
    """Send a 6 PM reminder only to approved users with no debt activity today."""
    if not cron_authorized(request):
        from fastapi import HTTPException
        raise HTTPException(status_code=401, detail="Unauthorized cron request")

    print("🌙 INACTIVITY CHECK-IN STARTED")
    today, start_iso, end_iso = _cron_date_boundaries()

    sent_count = 0
    skipped_count = 0
    error_count = 0

    try:
        users_result = (
            supabase.table("business_users")
            .select("id, phone_number, name")
            .eq("approval_status", "approved")
            .execute()
        )
        users = users_result.data or []
    except Exception as e:
        print(f"❌ Error loading business users: {type(e).__name__}: {e}")
        return {"status": "database_error"}

    message = (
        "🌙 *Xusuusin*\n\n"
        "Maanta wax dhaqdhaqaaq deyn ah lama diiwaangelin.\n\n"
        "Ma jiraan deymo cusub ama lacag-bixinno maanta dhacay?\n\n"
        "Haddii ay jiraan, ii soo dir si aan diiwaankaaga u cusboonaysiiyo.\n\n"
        "Mahadsanid! 🤝"
    )

    for user in users:
        business_user_id = user.get("id")
        phone = str(user.get("phone_number") or "").strip()

        if not business_user_id or not phone:
            skipped_count += 1
            continue

        try:
            # Check whether any new debt was recorded today.
            debts_result = (
                supabase.table("customers")
                .select("id")
                .eq("business_user_id", business_user_id)
                .gte("created_at", start_iso)
                .lt("created_at", end_iso)
                .limit(1)
                .execute()
            )

            # Check whether any payment was recorded today.
            payments_result = (
                supabase.table("payments")
                .select("id")
                .eq("business_user_id", business_user_id)
                .gte("paid_at", start_iso)
                .lt("paid_at", end_iso)
                .limit(1)
                .execute()
            )

            has_new_debt = bool(debts_result.data)
            has_payment = bool(payments_result.data)

            # Do not send the inactivity reminder if there was activity.
            if has_new_debt or has_payment:
                skipped_count += 1
                print(
                    f"⏭️ Reminder skipped: user={business_user_id}, "
                    f"new_debt={has_new_debt}, payment={has_payment}"
                )
                continue

            ok = send_whatsapp(phone, message)

            if ok:
                sent_count += 1
                print(f"✅ Inactivity reminder sent: user={business_user_id}")
            else:
                error_count += 1
                print(f"❌ Inactivity reminder failed: user={business_user_id}")

        except Exception as e:
            error_count += 1
            print(
                f"❌ Inactivity reminder error: user={business_user_id}, "
                f"{type(e).__name__}: {e}"
            )

    print(
        f"🏁 INACTIVITY CHECK-IN FINISHED: "
        f"sent={sent_count}, skipped={skipped_count}, errors={error_count}"
    )

    return {
        "status": "done",
        "sent": sent_count,
        "skipped": skipped_count,
        "errors": error_count,
        "date": today.isoformat(),
    }

if __name__ == "__main__":
    import uvicorn
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
