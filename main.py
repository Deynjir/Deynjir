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

    f"Fadlan sida ugu dhakhsaha badan u bixi lacagta. 
    Mahadsanid."
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

def build_statement_pdf(customer_name, debts, payments_by_debt, total_paid, total_balance):
    """Build a compact PDF statement in memory; never writes customer data to disk."""
    buffer = BytesIO()
    doc = SimpleDocTemplate(buffer, pagesize=A4, rightMargin=36, leftMargin=36, topMargin=36, bottomMargin=36)
    styles = getSampleStyleSheet()
    story = [Paragraph(f"{APP_NAME} - Customer Debt Statement", styles["Title"]),
             Paragraph(f"Customer: {escape(str(customer_name))}", styles["Heading2"]),
             Spacer(1, 10)]
    rows = [["Debt #", "Created", "Due date", "Current balance", "Status"]]
    for idx, debt in enumerate(debts, 1):
        balance = max(float(debt.get("amount") or 0), 0.0)
        status = "Paid" if debt.get("is_paid") is True or balance <= 0 else "Unpaid"
        rows.append([str(idx), str(debt.get("created_at") or "")[:10] or "Unknown",
                     str(debt.get("promised_date") or "Not set"), f"${balance:.2f}", status])
    table = Table(rows, repeatRows=1, colWidths=[42, 85, 85, 100, 70])
    table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#E8EEF5")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.black),
        ("GRID", (0, 0), (-1, -1), 0.4, colors.grey),
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("PADDING", (0, 0), (-1, -1), 6),
    ]))
    story.extend([table, Spacer(1, 14),
                  Paragraph(f"Recorded payments: ${total_paid:.2f}", styles["Normal"]),
                  Paragraph(f"Current outstanding balance: ${total_balance:.2f}", styles["Heading2"]),
                  Spacer(1, 10), Paragraph("Payment ledger", styles["Heading2"])])
    payment_rows = [["Debt #", "Payment date", "Amount"]]
    for idx, debt in enumerate(debts, 1):
        for payment in payments_by_debt.get(str(debt.get("id")), []):
            payment_rows.append([str(idx), str(payment.get("paid_at") or "")[:10] or "Unknown",
                                 f"${float(payment.get('amount') or 0):.2f}"])
    if len(payment_rows) == 1:
        payment_rows.append(["-", "No payments recorded", "$0.00"])
    pay_table = Table(payment_rows, repeatRows=1, colWidths=[70, 150, 100])
    pay_table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#E8EEF5")),
        ("GRID", (0, 0), (-1, -1), 0.4, colors.grey),
        ("PADDING", (0, 0), (-1, -1), 6),
    ]))
    story.append(pay_table)
    doc.build(story)
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
    """Recognize a short reply to the pending ADD-vs-PAY question."""
    text = normalize_customer_name(str(message_text or ""))
    if re.fullmatch(r"(?:deyn cusub|dayn cusub|deyn cusub oo baxday|lacag baxday|add|new debt|deyn baa baxday)", text, re.I):
        return "ADD"
    if re.fullmatch(r"(?:deyn soo xarootay|lacag soo xarootay|lacag baa soo gashay|lacag la helay|pay|payment|money received|received payment)", text, re.I):
        return "PAY"
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
    is_history = bool(re.search(r"\b(?:history|taariikh|statement|xisaab)\b", low))
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
    name_text = re.sub(r"\b(?:history|taariikh|statement|xisaab)\b", " ", name_text, flags=re.I)
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
    message = "⚠️ Dad isku magac ah ayaan helay:\n\n"

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
        "\n✍️ Fadlan mar kale qor magaca oo buuxa.\n"
        f"Tusaale: {example}"
    )

    send_whatsapp(sender_phone, message)
  
def send_due_list_followup(phone):
    send_whatsapp(
        phone,
        "Si aad u eegto liiska deynta oo dhan soo qor:\n"
        "Liiska daynta\n"
        "ama\n"
        "Liiska daynta iyo balamaha"
    )
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
    
    # ✅ HANDLE EXCEL/CSV FILES
    if type_message == "documentMessage":
        print("📄 Excel/CSV file detected!")
        try:
            doc_data = message_data["fileMessageData"]
            file_name = doc_data.get("fileName", "")
            
            if not str(file_name).lower().endswith((".xlsx", ".xls", ".csv")):
                send_whatsapp(sender_phone, "❌ Please send Excel (.xlsx, .xls) or CSV file only.")
                return {"status": "unsupported_file_type"}
            
            download_url = doc_data.get("downloadUrl")
            if not download_url:
                send_whatsapp(sender_phone, "❌ Could not download file.")
                return {"status": "no_download_url"}
            
            print(f"📥 Downloading file: {file_name}")
            
            file_response = requests.get(download_url, timeout=30)
            if file_response.status_code != 200:
                send_whatsapp(sender_phone, "❌ Failed to download file.")
                return {"status": "download_failed"}
            
            try:
                print("🔍 Parsing file...")
                if str(file_name).lower().endswith('.csv'):
                    df = pd.read_csv(BytesIO(file_response.content))
                else:
                    df = pd.read_excel(BytesIO(file_response.content), engine='openpyxl')
                
                print(f"📊 Found {len(df)} rows in file")
                print(f"📋 Columns: {list(df.columns)}")
                if 'Due' in df.columns:
                    print(f"🔍 Due values: {df['Due'].tolist()}")
                elif 'Due Date' in df.columns:
                    print(f"🔍 Due Date values: {df['Due Date'].tolist()}")
                elif 'due_date' in df.columns:
                    print(f"🔍 due_date values: {df['due_date'].tolist()}")
                else:
                    print("🔍 No Due column found!")
                
                required_cols = ['Name', 'Amount']
                if not all(col in df.columns for col in required_cols):
                    send_whatsapp(sender_phone, "❌ File must have 'Name' and 'Amount' columns.")
                    return {"status": "missing_columns"}
                
                try:
                    sk_query = supabase.table("business_users").select("*").eq("phone_number", sender_phone).execute()
                    if not sk_query.data:
                        sk_insert = supabase.table("business_users").insert({"phone_number": sender_phone}).execute()
                        business_user_id = sk_insert.data[0]["id"]
                    else:
                        business_user_id = sk_query.data[0]["id"]
                except Exception as db_err:
                    print(f"❌ DATABASE ERROR: {db_err}")
                    send_whatsapp(sender_phone, "❌ Database error.")
                    return {"status": "shopkeeper_db_error"}
                
                added_count = 0
                failed_count = 0
                
                for index, row in df.iterrows():
                    try:
                        name = str(row['Name']).strip()
                        amount = float(row['Amount'])
                        
                        # FIX: Handle Excel date properly - check all column variations
                        due_date = None
                        due_val = None
                        
                        # Try all possible column names
                        for col_name in ['Due', 'Due Date', 'due_date', 'due']:
                            if col_name in df.columns:
                                due_val = row[col_name]
                                break
                        
                        if due_val is not None and str(due_val).strip().lower() not in ("nan", ""):
                            if hasattr(due_val, "strftime"):
                                due_date = due_val.strftime("%Y-%m-%d")
                            else:
                                due_str = str(due_val).strip()
                                due_date = None

                                for fmt in (
                                    "%Y-%m-%d",
                                    "%d/%m/%Y",
                                    "%d-%m-%Y",
                                    "%m/%d/%Y",
                                ):
                                    try:
                                        parsed_date = datetime.strptime(due_str, fmt)
                                        due_date = parsed_date.strftime("%Y-%m-%d")
                                        break
                                    except ValueError:
                                        pass

                                if due_date is None:
                                    due_date = (
                                        now_eat()
                                    ).date().isoformat()
                        else:
                            due_date = (
                                now_eat()
                            ).date().isoformat()

                        starting_amount = float(amount)

                        debtor_data = {
                            "business_user_id": business_user_id,
                            "name": name,
                            "amount": starting_amount,
                            "original_amount": starting_amount,
                            "promised_date": due_date,
                            "is_paid": False
                        }

                        supabase.table("customers").insert(debtor_data).execute()
                        added_count += 1
                        print(f"  ✅ Added: {name} - ${amount}")
                        
                    except Exception as row_err:
                        print(f"  ❌ Row {index} failed: {row_err}")
                        failed_count += 1
                
                if added_count > 0:
                    send_whatsapp(sender_phone, f"✅ Imported {added_count} debts from Excel!\n\n📊 **Summary**:\n✅ Added: {added_count}")
                else:
                    send_whatsapp(sender_phone, "❌ No valid debts found in file.")
                
                return {"status": "success"}
                
            except Exception as parse_err:
                print(f"❌ Parse error: {parse_err}")
                send_whatsapp(sender_phone, f"❌ File error: {parse_err}")
                return {"status": "parse_error"}
                
        except Exception as file_err:
            print(f"❌ File error: {str(file_err)}")
            send_whatsapp(sender_phone, f"❌ File error: {str(file_err)}")
            return {"status": "file_error"}
    
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

    # Owner approves/rejects with: APPROVE 252... or REJECT 252...
    parts = message_text.strip().split(maxsplit=1)
    command = parts[0].upper() if parts else ""

    if sender_phone == owner_phone and command in {"APPROVE", "REJECT"}:
        if len(parts) != 2:
            send_whatsapp(sender_phone, "Use: APPROVE 252... or REJECT 252...")
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
                send_whatsapp(sender_phone, f"❌ No request found for {applicant_phone}.")
                return {"status": "applicant_not_found"}

            (
                supabase.table("business_users")
                .update({"approval_status": new_status})
                .eq("phone_number", applicant_phone)
                .execute()
            )

            send_whatsapp(sender_phone, f"✅ {applicant_phone} is {new_status}.")
            send_whatsapp(
                applicant_phone,
                "✅ Your access is approved."
                if new_status == "approved"
                else "❌ Your access request was rejected."
            )
            return {"status": new_status}

        except Exception as approval_err:
            print(f"❌ APPROVAL UPDATE ERROR: {approval_err}")
            send_whatsapp(sender_phone, "❌ Could not update the request. Check server logs.")
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
                "⏳ Your request is pending approval. Please wait for the owner."
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
        if clarification_action:
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
        elif re.fullmatch(r"\s*(?:jooji|cancel|baaji)\s*", str(message_text), re.I):
            supabase.table("pending_transaction_clarifications").delete().eq("sender_phone", sender_phone).execute()
            send_whatsapp(sender_phone, "Waa la joojiyay. Wax deyn ah lama diiwaangelin.")
            return {"status": "pending_clarification_cancelled"}
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
                    "ℹ️ Macmiilkan ma isticmaalo WhatsApp hubi in numberku saxan yahay."
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

    today_str = today_eat().isoformat()
    dynamic_system_prompt = f"{SYSTEM_PROMPT}\nToday's date is strictly: {today_str}. Use this to calculate calendar targets or relative days offsets like 'berri'."
    
    if pdf_only_requested:
        entries = [{"action": "HISTORY", "customer_name": pdf_customer_name}]
        print(f"📄 Skipping Gemini for PDF follow-up; using saved customer {pdf_customer_name!r}")
    elif forced_transaction_action:
        print(f"🔁 Using saved entries with confirmed action {forced_transaction_action}")
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
                "Waxaad soo qortay magac iyo tiro keliya.\n\n"
                "Ma *Deyn cusub oo baxday* baa mise *Deyn soo xarootay*?\n"
                "Ku jawaab: *DEYN CUSUB* ama *DEYN SOO XAROOTAY*.\n"
                "Waxba lama diiwaangelinayo ilaa aad caddeyso."
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
                    "Haddii aad rabto inaad beddesho ballanta deyn hore, qor magaca iyo taariikhda.\n"
                    "Tusaale: Faarax oct 10\n"
                    "Deyn cusubna ku qor: Axmed $5 oct 11"
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
                            f"— Ballan: {due_date or 'lama gelin'}"
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
                        f"⚠️ {overdue_count} deyn balan dhaafay:\n\n"
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
                                total_balance
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
                        f"(ballan: {due_date})"
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
                "*Balamaha maanta & kuwa dhaafay:*",
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

            lines = ["🌙 *Natiijada maanta*"]
            if name:
                lines.append(f"👤 *{name}*")
            lines.append("")

            if not new_debts and not payments:
                lines.append("Maanta wax deyn cusub ama lacag-bixin ah lama diiwaangelin.")
            else:
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
                "Fadlan ii soo dir magaca iyo lacagta haddii aad rabto inaad diiwaangeliso deyn cusub ama lacag-bixin."
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


if __name__ == "__main__":
    import uvicorn
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
