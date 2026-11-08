import os
import re
import json
import csv
import hmac
import time
import secrets
import math
from zoneinfo import ZoneInfo
import difflib
import unicodedata
from fastapi import FastAPI, Request, HTTPException
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
# Remembers the last customer added, searched, or opened for this sender.
# Used for short-lived, same-shop follow-ups that clearly refer to that customer.
LAST_SELECTED_CUSTOMERS = {}
# First-contact onboarding choices are temporary per-sender conversations.
ONBOARDING_SESSIONS = {}

# Temporary manual reminder workflow. Sessions expire after 15 minutes and are
# cleared before sending so a repeated "HAA DIR" cannot resend the same batch.
REMINDER_SESSIONS = {}
# Two-step customer-name correction sessions (sender -> shop/name/stage).
RENAME_SESSIONS = {}
# Amount edits are staged and require explicit confirmation before changing a balance.
AMOUNT_EDIT_SESSIONS = {}
REMINDER_SESSION_TTL = timedelta(minutes=15)
# Admin-assisted imports are staged for preview and explicit confirmation.
IMPORT_SESSIONS = {}
PAYMENT_EXPORT_SESSIONS = {}
IMPORT_SESSION_TTL = timedelta(minutes=30)
# Short, guided WhatsApp conversations for users who do not remember commands.
GUIDED_SESSIONS = {}
GUIDED_SESSION_TTL = timedelta(minutes=15)
# Pending ADD/PAY customer identity confirmations. No transaction is saved until resolved.
CUSTOMER_MATCH_SESSIONS = {}
# Explicit, confirmed DELETE workflow; sender/shop scoped and temporary.
DELETE_SESSIONS = {}
DELETE_SESSION_TTL = timedelta(minutes=15)


def deynjir_main_menu():
    """Return the welcome menu with real WhatsApp line breaks."""
    return (
        "👋 *Soo Dhawoow!*\n\n"
        "Nidaamkan waxaad kula soconaysaa daymaha, lacag-bixinta iyo ballamaha ganacsigaaga.\n\n"
        "*Raac Tilmaamahan Hoose:*\n\n"
        "Deyn cusub – Taabo 1️⃣\n"
        "Lacag bixin – Taabo 2️⃣\n"
        "liiska daynta – Taabo 3️⃣\n"
        "Raadi macmiil – Taabo 4️⃣\n"
        "Ballamaha maanta – Taabo 5️⃣\n"
        "Caawimaad – Taabo 6️⃣\n\n"
        "Amarro kale: *DHIGAAL Cali $100* ama *UNDO Cali*.\n"
        "Soo qor lambar 1 ilaa 6."
    )

def deynjir_unrecognized_message():
    """One short fallback; the active guided menu accepts the numeric choices."""
    return (
        "Qoraalkaaga ma fahmin. Fadlan dooro: "
        "1️⃣ Deyn cusub, 2️⃣ Lacag-bixin, 3️⃣ Liiska daynta, "
        "4️⃣ Raadi macmiil, 5️⃣ Ballamaha, 6️⃣ Caawimaad."
    )


def activate_guided_menu(sender_phone):
    """Make the next numeric reply a valid choice after showing the action menu."""
    GUIDED_SESSIONS[sender_phone] = {
        "stage": "menu",
        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
    }


def deynjir_help_message():
    return (
        "ℹ️ *Raac Tilmaamahan*\n\n"
        "• Deyn cusub: qor *ADD Cali $50*\n"
        "• Lacag bixin: qor *Lacag bixin Cali $20*\n"
        "• Liiska daynta: qor *LIISKA DAYNTA*\n"
        "• Raadi qof: qor *Raadi Cali*\n"
        "• Faahfaahin: qor *FAAHFAAHIN Cali*\n"
        "• Ballamaha: qor *Balamaha Maanta* ama *Balamaha Berri*\n"
        "• Soo geli sawir/Excel: qor *IMPORT*\n"
        "• Dhigaal macmiil: qor *DHIGAAL Cali $100*\n"
        "• Hubi dhigaalka: qor *DHIGAAL Cali*\n"
        "• Ka noqo macaamilkii ugu dambeeyay: qor *UNDO Cali*\n\n"
        "Soo Qor *MENU* marka aad u baahato hagid."
    )


def deynjir_confusion_help_message():
    return (
        "😊 Dhib ma leh, waan ku caawinayaa.\n\n"
        "Nidaamkan wuxuu kaa caawinayaa inaad\n"
        "diiwaangeliso daymaha, lacag-bixinta iyo balamaha Ganacsigaaga.\n\n"
        "Tusaale:\n"
        "Waxaad Dayn $10 ku leedahay Qof lagu magacaabo Cali.\n"
        "si aad Nidaamka ugu darto soo Qor:\n"
        "*ADD Cali $10*\n\n"
        "Haddii Cali bixiyay $5, soo qor:\n\n"
        "*Lacag bixin Cali $5*"
    )


def is_somali_confusion_request(message_text):
    """Recognize common Somali requests for help understanding how to use Deynjir."""
    text = normalize_customer_name(str(message_text or ""))
    patterns = (
        r"\bbarnaamijka\s+(?:waxba\s+)?ma\s+fahmin\b",
        r"\bbarnaamijka\s+waxba\s+kama\s+fahmin\b",
        r"\b(?:waxba\s+kama\s+fahmin|ma\s+fahmin)\b",
        r"\bsidee\s+(?:loo\s+)?isticmaalaa\b",
        r"\bsidee\s+loo\s+isticmaali\s+karaa\b",
        r"\bmaxaan\s+sameeyaa\b",
        r"\bii\s+sharax\b",
        r"\bma\s+garanayo\s+sida\s+loo\s+isticmaalo\b",
        r"\bsidee\s+dayn\s+loo\s+geliyaa\b",
        r"\bsidee\s+nidaamkan\s+u\s+shaqeeyaa\b",
    )
    return any(re.search(pattern, text, flags=re.I) for pattern in patterns)


def normalize_easy_command(value):
    """Normalize a small, explicit set of common Somali typing mistakes."""
    raw = " ".join(str(value or "").strip().split())
    folded = raw.casefold().strip(" .!؟?")
    aliases = {
        "inbort": "IMPORT", "inport": "IMPORT", "importi": "IMPORT",
        "menu": "MENU", "manu": "MENU", "menyu": "MENU", "menue": "MENU",
        "caawi": "HELP", "caawimaad": "HELP",
        "help me": "HELP", "salaan": "MENU", "asc": "MENU",
        "assalamu alaikum": "MENU", "asalaamu calaykum": "MENU",
        "lacag bixn": "GUIDED_PAYMENT",
        "lacag bixinta": "LIISKA LACAG BIXINTA",
        "ku dar deyn": "GUIDED_DEBT", "ku dar dayn": "GUIDED_DEBT",
        "balanta beri": "BALAMAHA BERRI", "ballanta beri": "BALAMAHA BERRI",
        "balamaha beri": "BALAMAHA BERRI", "ballamaha beri": "BALAMAHA BERRI",

        # Common Somali merchant spelling and phrasing variants.
        "lacgta": "LACAGTA", "lacg": "LACAG",
        "dayn": "DEYN", "daynta": "DEYNTA", "dayntii": "DEYNTII",
        "wakhtiga balanta": "BALLANTA", "waqtiga balanta": "BALLANTA",
        "wakhtiga balanta waa": "BALLAN", "waqtiga balanta waa": "BALLAN",
        "ballan": "BALLAN", "lacg bixin": "LACAG BIXIN",
        "lacg bixn": "LACAG BIXIN",
    }
    return aliases.get(folded, raw)


def _guided_amount(text):
    raw = str(text or "").strip().replace(",", ".")
    match = re.fullmatch(r"(?:\$\s*)?(\d+(?:\.\d{1,2})?)(?:\s*(?:usd|dollar|dollars))?", raw, re.I)
    if not match:
        return None
    try:
        amount = float(match.group(1))
        return amount if amount > 0 else None
    except (TypeError, ValueError):
        return None

# Payment-report commands are handled locally; they must never enter import,
# Gemini, or the generic debt fallback parser.
PAYMENT_REPORT_MONTH_PATTERN = (
    r"jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|"
    r"jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|"
    r"oct(?:ober)?|nov(?:ember)?|dec(?:ember)?"
)
PAYMENT_REPORT_DATE_PATTERN = (
    r"\d{1,2}[/-]\d{1,2}[/-]\d{4}|\d{4}-\d{2}-\d{2}|"
    r"\d{1,2}\s+[A-Za-z]+(?:\s+\d{4})?|"
    r"[A-Za-z]+\s+\d{1,2}(?:,?\s+\d{4})?"
)

def is_payment_report_command(value):
    """Recognize shop-wide payment reports before any import/AI parser runs."""
    text = " ".join(str(value or "").strip().split())
    return bool(re.fullmatch(
        rf"(?:liiska\s+)?lacag\s*bixinta(?:\s+(?:{PAYMENT_REPORT_MONTH_PATTERN}|"
        rf"(?:{PAYMENT_REPORT_DATE_PATTERN})(?:\s*(?:-|ilaa|to)\s*(?:{PAYMENT_REPORT_DATE_PATTERN}))?))?",
        text, re.I
    ))
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
def build_debt_reminder(debtor, shopkeeper_name, shopkeeper_phone, is_repeat=False):
    name = str(debtor.get("name") or "Macmiil").strip()
    balance = float(debtor.get("amount") or 0)

    # First reminder keeps the original wording. Second and later reminders
    # use the shorter message and the current outstanding balance.
    if is_repeat:
        return (
            f"Asc {name},\n\n"
            f"Waxaa weli lagugu leeyahay *${balance:.2f}*.\n\n"
            "Fadlan soo bixi lacagta. Mahadsanid."
        )

    shopkeeper_name = str(shopkeeper_name or "").strip()
    shopkeeper_phone = str(shopkeeper_phone or "").strip()
    sender = (
        f"{shopkeeper_name} (+{shopkeeper_phone})"
        if shopkeeper_name else f"+{shopkeeper_phone}"
    )
    return (
        f"Asc {name},\n\n"
        f"Waxaan si xushmad leh kuu xusuusinayaa in aad soo bixiso "
        f"lacagtii daynta ahayd oo dhan: *${balance:.2f}*.\n\n"
        f"Fariintan waxaa kuu soo diray *{sender}*.\n\n"
        "Fadlan sida ugu dhakhsaha badan u bixi lacagta.  Mahadsanid."
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

Extract ALL debt entries from the message. Understand informal, messy, phonetic, regional, and misspelled Somali; interpret intent from the whole sentence rather than requiring exact command words. Do not guess financial intent when unclear.

SOMALI UNDERSTANDING (IMPORTANT): Understand the whole sentence, not only exact command phrases. Accept natural Somali word order, dialects, gender/number verb forms, omitted pronouns, and common spelling variations. Examples:
- "Muna 100 ayay qaadatay", "Muna waxay iga qaadatay 100", "Muna 100 bay qaadatay" -> ADD 100 (new debt).
- "Yuusuf 50 ayuu qaatay", "Yuusuf 50 buu amaahday", "50 ayaan Yuusuf ka siiyay" -> ADD 50 when the context says the customer received/borrowed credit.
- "Axmed 20 ayaan ka qabtay", "Axmed 20 ayuu ii keenay", "Axmed lacag buu ii keenay", "Axmed 20 ayuu soo celiyay" -> PAY 20 (money received).
- "Muna 20 ayay iga soo celisay", "Muna 20 ayay bixisay", "Muna 20 ayay soo shubtay" -> PAY 20.
- Understand forms such as qaatay, qaadatay, qaateen, qaadanayo; bixiyay, bixisay, bixiyeen; keenay, keentay; qabtay, qabatay; celiyay, celisay; shubay, shubtay.
- "ka siiyay" can mean the shop gave the customer credit; classify as ADD only when the sentence clearly describes money given to that customer as a debt. Do not confuse it with money the customer paid back.
- Remove grammatical filler (wuu, wuxuu, ayay, waxay, ayaan, baan, buu, bay) from the customer name, but preserve every actual name part.
- If a sentence says only that a customer has not paid, do not create a transaction. If the direction or amount is unclear, ask a short clarification. Never invent an amount or mark a partial payment as full.
- Also understand common informal variants and typos: "wuu qaatay", "wuu qaaty", "qaatey", "qaadatay", "qaateen", "wuu soo celiyey", "soo celisay", "lacagtii wuu keenay", "lacag buu soo shubay", "lacagta waan ka qabtay", "wuu iga soo celiyey", and missing/extra spaces. Normalize spelling for intent, but preserve the customer's actual name as written.
- Debt examples: "Cali maanta 50 buu qaatay", "Cali 50 ayuu iga qaaty", "Cali raashin ayuu ku qaatay 50", "Cali 50 ku dar xisaabtii hore". The last example is an addition to the existing customer's account, not a replacement of the balance.
- Payment examples: "Cali 20 buu ii keenay", "Cali 20 ayuu soo celiyey", "Cali lacagtii qayb ayuu bixiyey", "Cali 15 ayaan ka qabtay". These are PAY only when the sentence clearly says money was received from the customer.
- Do not classify "Cali lacag ma keenin", "Cali wali ma bixin", or "Cali ima soo celin" as a payment. A negative statement is not a transaction.
- PHONE NUMBERS: A phone number is not a money amount. When the user says "Lambarka Cali waa +252...", "Cali numberkiisa +252...", "save Cali phone +252...", or sends "Cali +252...", extract the full customer name and phone number, with amount=null. Never add a debt from a phone-only message.
- DUE DATES: Understand maanta, caawa, berri/bari, saaka, isniinta, talaadada, arbacada, khamiista, jimcaha, sabtida, axadda, toddobaadka dambe, usbuuca dambe, bisha dambe, and explicit DD/MM/YYYY dates. Resolve weekdays to the next upcoming occurrence after today's date; if the user says "isniinta soo socota", choose the next Monday, not a past date. If uncertain, ask instead of guessing.
- DESCRIPTIONS: Keep item/reason words such as raashin, bariis, sonkor, shidaal, alaab, adeeg, iyo lacag hormaris as the transaction description; do not absorb them into the customer's name. Description is per transaction.

For each entry, extract: customer_name, amount, promised_date (YYYY-MM-DD), transaction_date (YYYY-MM-DD), phone_number, description. transaction_date is the date the ADD or PAY actually happened when the user explicitly provides it (including labelled notes such as "Taariikhda 06/11/2026"); interpret Somali numeric dates as DD/MM/YYYY. Do not substitute today's date when an explicit transaction date is present. Description is the item/reason text belonging to that specific debt or payment; use null when none is stated.
IMPORTANT DATE-ONLY EDIT RULE: If a message names an existing customer and gives a new due/promised date but no amount, return action EDIT, set new_date and promised_date to that date, and keep amount and new_amount null. Apply this independently to EVERY customer in a comma-separated or multi-line message. A date's day number is never an amount. Never turn "Xasan 8 Nov" into an $8 transaction.

ALWAYS return a JSON array, even for single entries.

Response format (JSON array):
[
  {"action": "ADD" or "PAY" or "LIST" or "SEARCH" or "EDIT" or "DELETE" or "HISTORY" or "REPORT" or "EXPORT", "customer_name": "string or null", "amount": number or null, "days_until_due": number or null, "customer_phone": "string or null", "promised_date": "YYYY-MM-DD or null", "transaction_date": "YYYY-MM-DD or null", "filter_date": "YYYY-MM-DD or null", "filter_type": "today" or "tomorrow" or "date" or "week" or "month" or null, "new_amount": number or null, "new_date": "YYYY-MM-DD or null", "new_name": "string or null", "new_phone": "string or null", "payment_type": "FULL" or "PARTIAL" or "UNKNOWN" or null, "description": "short transaction detail or null"}
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
'edit Cali name to Cali Maxamed' -> EDIT, customer_name="Cali", new_name="Cali Maxamed".
'SAX Cali -> Cali Maxamed' -> EDIT, customer_name="Cali", new_name="Cali Maxamed".
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
- Treat these as PAY when the context says money was received: "bixiyay", "bixiyey", "bixisay", "bixiyeen", "bixin", "lacag bixin", "lacag qabasho", "lacag soo xarootay", "wuu bixiyay", "wuxuu bixiyay", "waan ka helay", "ka jar", "ka reeb", "soo celiyay", "soo celiyey", "celiyay", "celiyey", "lacagtii wuu keenay", "lacagtii waa la helay".
- Also understand common Somali spelling mistakes, shortened forms, repeated letters, and informal word order. Do not classify as PAY if the message clearly says the customer took/borrowed new money.
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

TRANSACTION DESCRIPTIONS:
- Extract a short description for each individual ADD or PAY transaction when the user's message includes one (e.g. "Cali $10 raashin ayuu qaatay" -> description="raashin").
- Do not copy a previous description or infer one. If no detail is stated, return description=null; the application stores and displays it as "-".
- Description belongs to this one transaction only, never to the customer's combined balance.

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

CONTEXT-AWARE FOLLOW-UPS:
- If the previous bot message asked "Deyn cusub baa mise lacag-bixin?", then:
  "1" = ADD
  "2" = PAY
  "3" = CANCEL
  "HAA" = ADD
  "MAYA" = PAY

MULTI-LINE MESSAGES:
"Mahad cabdi
Lacgta oo ah 10
1"
-> ADD, customer_name="Mahad Cabdi", amount=10

"Menu
1 mxmed cabdi 20
Wakhtiga balanta waa 8/11/2026"
-> ADD, customer_name="Mxmed Cabdi", amount=20, promised_date="2026-11-08"

SPELLING AND PHRASING:
- "Lacgta" means "Lacagta"
- "Dayn" means "Deyn"
- "Wakhtiga balanta waa" means due date
- "Ballan" means due date

MISSING INFORMATION:
- "Cali ka jar" -> PAY, customer_name="Cali", amount=null, payment_type="UNKNOWN"
- "Ka jar" -> PAY, customer_name=null, amount=null, payment_type="UNKNOWN"
- "Ma jirtoh" -> Do not return SEARCH; return no usable financial action.

DELETE CONFIRMATION:
- If the previous bot message asked to confirm deletion, then:
  "Haa tirtir" = CONFIRM_DELETE, not a customer-name search.

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

def _process_pending_payment_confirmation(pending_id, actor_phone, admin=False):
    """Claim, validate, and atomically record one staged payment exactly once."""
    lookup = (
        supabase.table("pending_payment_confirmations")
        .select("*")
        .eq("id", str(pending_id))
        .limit(1)
        .execute()
    )
    if not lookup.data:
        return False, "Lacag-bixinta sugaysa lama helin."
    pending = lookup.data[0]
    if not admin and str(pending.get("sender_phone")) != str(actor_phone):
        return False, "Lacag-bixintan adiga kuma xirna."
    current_status = str(pending.get("status") or "")
    if current_status != "pending" and not (admin and current_status == "rejected"):
        return False, f"Xaaladda lacag-bixintan waa {current_status}; mar kale lama diiwaangelin karo."
    if admin and current_status == "rejected":
        newer_active = (
            supabase.table("pending_payment_confirmations")
            .select("id")
            .eq("sender_phone", str(pending.get("sender_phone")))
            .eq("business_user_id", str(pending.get("business_user_id")))
            .in_("status", ["pending", "processing"])
            .limit(1)
            .execute()
        )
        if newer_active.data:
            return False, "Waxaa jira saxitaan cusub oo sugaya xaqiijin. Fadlan dib u eeg ID-ga saxitaanka cusub."
    expires_raw = pending.get("expires_at")
    expires = datetime.fromisoformat(str(expires_raw).replace("Z", "+00:00")) if expires_raw else None
    if expires and expires.tzinfo is None:
        expires = expires.replace(tzinfo=timezone.utc)
    if current_status == "pending" and (not expires or datetime.now(timezone.utc) > expires):
        supabase.table("pending_payment_confirmations").update({"status": "expired"}).eq("id", str(pending_id)).eq("status", "pending").execute()
        return False, "Waqtigii xaqiijinta wuu dhammaaday. Lacag lama kaydin. Fadlan macaamilka mar kale dir."

    # Conditional update is the one-time claim. A second HAA cannot claim it.
    try:
        claimed = (
            supabase.table("pending_payment_confirmations")
            .update({"status": "processing", "actor_phone": str(actor_phone)})
            .eq("id", str(pending_id))
            .eq("status", current_status)
            .select("id")
            .execute()
        )
    except Exception as claim_error:
        print(f"⚠️ Could not claim pending payment {pending_id}: {claim_error}")
        return False, "Lacag-bixinta lama qaban karin si ammaan ah. Waxba lama diiwaangelin; maamulka ha hubiyo."
    if not claimed.data:
        return False, "Lacag-bixintan hore ayaa loo xaqiijiyey ama waa la farsamaynayaa."

    payment_rpc_succeeded = False
    try:
        customer_result = (
            supabase.table("customers")
            .select("id, name, amount, is_paid")
            .eq("id", str(pending.get("customer_id")))
            .eq("business_user_id", str(pending.get("business_user_id")))
            .eq("is_archived", False)
            .limit(1)
            .execute()
        )
        if not customer_result.data:
            raise ValueError("Macmiilka lama helin dukaanka saxda ah.")
        debtor = customer_result.data[0]
        balance = float(debtor.get("amount") or 0)
        amount = float(pending.get("amount") or 0)
        if not math.isfinite(balance) or not math.isfinite(amount) or amount <= 0:
            raise ValueError("Lacagta ama haraaga ma saxna.")
        if debtor.get("is_paid") is True or balance <= 0:
            raise ValueError("Deyntan hore ayaa loo bixiyey.")
        if amount - balance > 0.009:
            raise ValueError(f"Lacagta ${amount:.2f} waxay ka badan tahay haraaga ${balance:.2f}.")

        rpc_result = supabase.rpc("record_debt_payment_with_history", {
            "p_customer_id": str(debtor["id"]),
            "p_business_user_id": str(pending.get("business_user_id")),
            "p_amount": round(amount, 2),
            "p_description": str(pending.get("description") or "-").strip() or "-",
        }).execute()
        rpc_data = rpc_result.data
        if isinstance(rpc_data, list):
            rpc_data = rpc_data[0] if rpc_data else None
        if not isinstance(rpc_data, dict) or not rpc_data.get("id"):
            raise RuntimeError("Payment RPC did not return the updated customer")
        payment_rpc_succeeded = True
        supabase.table("pending_payment_confirmations").update({
            "status": "confirmed",
            "processed_at": datetime.now(timezone.utc).isoformat(),
        }).eq("id", str(pending_id)).eq("status", "processing").execute()
        return True, (
            f"✅ Lacag-bixinta waa la diiwaangeliyey.\n"
            f"{rpc_data.get('name') or pending.get('customer_name')}: ${amount:.2f}\n"
            f"Baaqiga: ${float(rpc_data.get('amount') or 0):.2f}"
        )
    except Exception as exc:
        print(f"❌ Pending payment confirmation failed: {type(exc).__name__}: {exc}")
        if payment_rpc_succeeded:
            # The ledger RPC committed. Never make this proposal confirmable again,
            # even if updating its status failed; that could duplicate the payment.
            return False, (
                "⚠️ Lacag-bixinta database-ka waa la qoray, balse xaaladda xaqiijinta "
                "lama cusboonaysiin. Ha ku celin HAA. Maamulka ha hubiyo Supabase."
            )
        supabase.table("pending_payment_confirmations").update({"status": "pending", "actor_phone": None}).eq("id", str(pending_id)).eq("status", "processing").execute()
        return False, f"❌ Lacag-bixinta lama diiwaangelin: {str(exc)[:220]}"


def _reject_pending_payment_confirmation(pending_id, actor_phone, admin=False):
    query = supabase.table("pending_payment_confirmations").select("*").eq("id", str(pending_id)).limit(1).execute()
    if not query.data:
        return False, "Lacag-bixinta sugaysa lama helin."
    pending = query.data[0]
    if not admin and str(pending.get("sender_phone")) != str(actor_phone):
        return False, "Lacag-bixintan adiga kuma xirna."
    updated = (
        supabase.table("pending_payment_confirmations")
        .update({"status": "rejected", "actor_phone": str(actor_phone), "processed_at": datetime.now(timezone.utc).isoformat()})
        .eq("id", str(pending_id)).eq("status", "pending").select("id").execute()
    )
    if not updated.data:
        return False, "Lacag-bixintan hore ayaa looga jawaabay ama waa la farsamaynayaa."
    return True, pending


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
    statement_date = today_eat().strftime("%Y-%m-%d")

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


def send_customer_statement_pdf(sender_phone, business_user_id, customer_name, business_name=None):
    """Generate and send the customer's detailed statement PDF; never changes data."""
    history_matches = find_debtor_matches(
        business_user_id, customer_name, include_archived=True
    )
    if not history_matches:
        return False

    distinct_names = {
        normalize_customer_name(row.get("name"))
        for row in history_matches
    }
    if len(distinct_names) != 1:
        print(
            "⚠️ Statement PDF not sent because customer name is ambiguous: "
            f"{customer_name!r}"
        )
        return False

    customer_ids = [
        row.get("id") for row in history_matches if row.get("id") is not None
    ]
    payment_rows = []
    if customer_ids:
        result = (
            supabase.table("payments")
            .select("amount, paid_at, customer_id")
            .eq("business_user_id", str(business_user_id))
            .in_("customer_id", customer_ids)
            .order("paid_at")
            .execute()
        )
        payment_rows = result.data or []

    payments_by_debt = {}
    for payment in payment_rows:
        payments_by_debt.setdefault(str(payment.get("customer_id")), []).append(payment)

    total_paid = sum(float(row.get("amount") or 0) for row in payment_rows)
    total_balance = sum(
        max(float(row.get("amount") or 0), 0.0)
        for row in history_matches
    )
    canonical_name = history_matches[0].get("name") or customer_name
    pdf_bytes = build_statement_pdf(
        canonical_name,
        history_matches,
        payments_by_debt,
        total_paid,
        total_balance,
        business_name,
    )
    safe_filename = re.sub(r"[^A-Za-z0-9_-]+", "_", str(canonical_name))
    return send_whatsapp_file(
        sender_phone,
        f"daynjir_statement_{safe_filename}.pdf",
        pdf_bytes,
        "application/pdf",
        f"📄 PDF — Xisaabta {canonical_name}",
    )


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


def parse_customer_phone_update(message_text):
    """Parse a clear customer + phone-only message before Gemini.

    Only accepts a 9-15 digit phone token, rejects currency/date/transaction
    wording, and returns the existing ADD phone-update shape (amount=None).
    The ADD handler already updates phone_number without creating a debt.
    """
    raw = " ".join(str(message_text or "").strip().split())
    if not raw:
        return None
    low = raw.casefold()
    if re.search(r"[$]|\b(?:usd|dollars?|dollar)\b", low):
        return None
    if classify_transaction_direction(raw) in {"ADD", "PAY"}:
        return None
    if re.search(r"\b(?:today|tomorrow|maanta|berri|bari|jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)\b|\b\d{1,2}[/-]\d{1,2}(?:[/-]\d{2,4})?\b", low, re.I):
        return None

    phone_match = re.search(r"(?<!\w)(\+?\d[\d\s().-]{5,}\d)(?!\w)", raw)
    if not phone_match:
        return None
    phone_raw = phone_match.group(1).strip()
    digits = re.sub(r"\D", "", phone_raw)
    if not 9 <= len(digits) <= 15:
        return None
    has_phone_context = bool(re.search(
        r"\b(?:phone|phone\s+number|number|numberka|numberkiisa|numberkeeda|"
        r"lambarka|lambarkiisa|lambarkeeda|telefoonka|save|update|ku\s+kaydi)\b",
        low, re.I
    ))
    if not phone_raw.startswith("+") and len(digits) < 10 and not has_phone_context:
        return None

    before = raw[:phone_match.start()].strip(" ,:;-.")
    after = raw[phone_match.end():].strip(" ,:;-.")
    # Support both "Cali +252..." and "+252... waa Cali".
    if before:
        name_text = before
    elif after:
        name_text = after
    else:
        return None

    name_text = re.sub(
        r"^(?:(?:save|set|update|add|ku\s+kaydi|ii\s+keydi|ii\s+geli|lambarka|lambarka\s+macmiilka|numberka|number|phone(?:\s+number)?|telefoonka)\s+)+",
        "", name_text, flags=re.I
    )
    name_text = re.sub(
        r"\s+(?:waa|weeye|numberkiisa|numberkeeda|lambarkiisa|lambarkeeda|phone|number)$",
        "", name_text, flags=re.I
    ).strip(" ,:;-.")
    name_text = re.sub(r"^(?:waa|weeye)\s+", "", name_text, flags=re.I).strip()
    name_text = re.sub(r"['’]s$", "", name_text, flags=re.I).strip()
    if len(name_text) < 2 or len(name_text) > 100 or not re.search(r"[A-Za-z\u0080-\uffff]", name_text):
        return None
    # Avoid treating generic phone labels as a customer's name.
    if normalize_customer_name(name_text) in {"phone", "number", "lambarka", "numberka", "telefoonka"}:
        return None

    return [{
        "action": "ADD",
        "customer_name": name_text,
        "amount": None,
        "customer_phone": digits,
        "new_phone": digits,
        "promised_date": None,
        "days_until_due": None,
        "new_amount": None,
        "new_date": None,
        "payment_type": None,
        "description": None,
        "_phone_update_only": True,
    }]


def remember_selected_customer(sender_phone, business_user_id, customer_name):
    """Remember a customer briefly for clear, context-dependent follow-up messages."""
    clean_name = str(customer_name or "").strip()
    if not clean_name:
        return
    LAST_SELECTED_CUSTOMERS[str(sender_phone)] = {
        "business_user_id": str(business_user_id),
        "customer_name": clean_name,
        "selected_at": datetime.now(timezone.utc).isoformat(),
    }


def get_recent_selected_customer(sender_phone, business_user_id, max_age_minutes=2):
    """Return the recently selected customer only for the same shop and short time window."""
    saved = LAST_SELECTED_CUSTOMERS.get(str(sender_phone)) or {}
    if str(saved.get("business_user_id") or "") != str(business_user_id):
        return None
    selected_at = saved.get("selected_at")
    if not selected_at:
        # Old in-memory entries without a timestamp are not safe to reuse.
        return None
    try:
        timestamp = datetime.fromisoformat(str(selected_at).replace("Z", "+00:00"))
        if timestamp.tzinfo is None:
            timestamp = timestamp.replace(tzinfo=timezone.utc)
    except (TypeError, ValueError):
        return None
    age = datetime.now(timezone.utc) - timestamp
    if age < timedelta(0) or age > timedelta(minutes=max_age_minutes):
        return None
    name = str(saved.get("customer_name") or "").strip()
    return name or None


def parse_contextual_somali_payment(message_text, recent_customer_name):
    """Resolve a name-omitting Somali payment follow-up against a recent customer.

    This parser is intentionally narrow: it only handles clear PAY wording where
    the remaining words contain no customer name. The normal payment validation
    and confirmation workflow still runs after this extraction.
    """
    raw = " ".join(str(message_text or "").strip().split())
    if not raw or not recent_customer_name:
        return None
    if classify_transaction_direction(raw) != "PAY":
        return None

    folded = normalize_customer_name(raw)
    removable = {
        "waxay", "wuxuu", "wuu", "way", "ayaa", "ayuu", "bay", "baa",
        "bixisay", "bixiyay", "bixiyey", "bixiyeen", "bixi", "bixiso",
        "celisay", "celiyay", "celiyey", "celiyeen", "soo", "celi",
        "soo celisay", "soo celiyay", "soo celiyey", "ka", "jar", "jartay",
        "reebtay", "reebay", "helay", "heshay", "waan", "waxaan", "ka helay",
        "lacag", "lacagta", "lacagtii", "deynta", "daynta", "deyntii",
        "oo", "dhan", "wada", "dhamaan", "dhammaan", "inta", "qayb",
        "qaybta", "bixinta", "la", "waa", "ah", "uu", "iyadoo", "isagoo",
        "isaga", "iyada", "iyadu", "isagu", "waxa", "uu", "ayaa",
    }
    # Remove numbers/currency and common Somali pronouns/payment words. If any
    # meaningful name-like words remain, let the normal named-customer parser run.
    without_amount = re.sub(r"(?<![\w/.-])\$?\s*\d+(?:[.,]\d{1,2})?\s*\$?(?![\w/.-])", " ", folded)
    remaining = [word for word in without_amount.split() if word not in removable]
    if remaining:
        return None

    numbers = re.findall(r"(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)(?![\w/.-])", raw)
    if len(numbers) > 1:
        return None
    amount = None
    if numbers:
        try:
            amount = float(numbers[0].replace(",", "."))
        except ValueError:
            return None
        if not math.isfinite(amount) or amount <= 0:
            return None

    clearly_full = bool(re.search(
        r"\b(?:deynta|daynta|deyntii|dayntii|lacagta|lacagtii)\s+(?:oo\s+)?(?:dhan|wada)\b|\b(?:dhamaan|dhammaan)\s+(?:deynta|daynta|lacagta)\b",
        folded,
        flags=re.I,
    ))
    payment_type = "PARTIAL" if amount is not None else ("FULL" if clearly_full else "UNKNOWN")
    return {
        "action": "PAY",
        "customer_name": str(recent_customer_name).strip(),
        "amount": amount,
        "payment_type": payment_type,
        "description": None,
        "_contextual_customer_used": True,
    }


def is_emoji_only_message(value):
    """True when text contains only emoji/symbols, whitespace, or punctuation."""
    text = str(value or "").strip()
    if not text:
        return False
    allowed_format = {"\u200d", "\ufe0e", "\ufe0f", "\u20e3"}
    saw_emoji = False
    for char in text:
        if char.isspace() or unicodedata.category(char).startswith("P"):
            continue
        if char in allowed_format:
            continue
        category = unicodedata.category(char)
        code = ord(char)
        if category.startswith("S") or 0x1F1E6 <= code <= 0x1F1FF:
            saw_emoji = True
            continue
        # Keycap emoji contain a digit followed by VS16 + COMBINING ENCLOSING KEYCAP.
        if char.isdigit() and "\u20e3" in text:
            saw_emoji = True
            continue
        return False
    return saw_emoji


def is_missing_value(value):
    """Reject empty values and literal null-like strings returned by an AI parser."""
    if value is None:
        return True
    if not isinstance(value, str):
        return False
    return normalize_customer_name(value) in {
        "", "none", "null", "undefined", "unknown", "n a", "na"
    }


def is_explicit_list_request(message_text):
    """Recognize explicit debt-list and appointment-list commands."""
    raw = normalize_customer_name(message_text)
    return bool(re.fullmatch(
        r"(?:deyn|dayn|liis|liiska|liiska deynta|liiska daynta|"
        r"liiska daynta iyo balamaha|liiska deynta iyo balamaha|"
        r"deynaha liiskooda|list|list debts?|debt list|show debts?|"
        r"balamaha(?: maanta| beri)?|ballamaha(?: maanta| beri)?|"
        r"balanta(?: maanta| beri)?|ballanta(?: maanta| beri)?|"
        r"balan(?:ta)?(?: maanta| beri)?)",
        raw,
        flags=re.I,
    )) or is_fuzzy_debt_list_command(message_text)


def parse_customer_rename_command(message_text):
    """Parse an explicit customer rename without relying on AI interpretation.

    Supported examples:
      SAX Old customer name -> Correct customer name
      EDIT Old customer name TO Correct customer name
      SAX Old customer name ku beddel Correct customer name
    """
    raw = " ".join(str(message_text or "").strip().split())
    patterns = [
        r"^(?:sax|rename|rename\s+customer|edit\s+name|edit|change\s+name)\s+(.+?)\s*(?:->|=>|\bto\b)\s*(.+?)\s*[.!]?$",
        r"^(?:sax|edit)\s+(.+?)\s+\b(?:ku\s+bedel|u\s+bedel|magaca\s+cusub)\b\s+(.+?)\s*[.!]?$",
    ]
    for pattern in patterns:
        match = re.match(pattern, raw, flags=re.IGNORECASE)
        if match:
            old_name, new_name = (part.strip(" \t,;:-") for part in match.groups())
            if old_name and new_name and normalize_customer_name(old_name) != normalize_customer_name(new_name):
                return old_name, new_name
    return None


def parse_somali_amount_edit(message_text):
    """Parse explicit single-customer balance edits such as 'Muna ka dhig 25'.

    Currency symbols are optional because the verb phrase clearly expresses an
    edit. This parser never handles bare name+amount messages.
    """
    raw = " ".join(str(message_text or "").strip().split())
    patterns = [
        r"^(?:(?:deynta|daynta|deyn|dayn)\s+)?(?P<name>.+?)\s+(?:(?:deynta|daynta|deyn|dayn)\s+)?(?:ka\s+dhig|ka\s+dhigo|kadhig|kadhigo)\s+\$?\s*(?P<amount>\d+(?:[.,]\d{1,2})?)\s*[.!]?$",
        r"^(?:(?:deynta|daynta|deyn|dayn)\s+)(?P<name>.+?)\s+(?:u\s+dhig|uga\s+dhig)\s+\$?\s*(?P<amount>\d+(?:[.,]\d{1,2})?)\s*[.!]?$",
    ]
    for pattern in patterns:
        match = re.match(pattern, raw, flags=re.I)
        if not match:
            continue
        name = match.group("name").strip(" .,:;-")
        amount_text = match.group("amount").replace(",", ".")
        if not name or re.search(r"\d", name):
            return None
        try:
            amount = float(amount_text)
        except (TypeError, ValueError):
            return None
        if not math.isfinite(amount) or amount < 0:
            return None
        return {
            "action": "EDIT",
            "customer_name": name,
            "amount": amount,
            "new_amount": amount,
            "new_date": None,
            "promised_date": None,
            "_source_amount_verified": True,
            "_explicit_balance_edit": True,
        }
    return None


def parse_sax_name_only(message_text):
    """Return the old customer name for a two-step SAX command, if supplied."""
    raw = " ".join(str(message_text or "").strip().split())
    match = re.match(r"^(?:sax|edit\s+name)\s+(.+?)\s*[.!]?$", raw, re.IGNORECASE)
    if not match or re.search(r"(?:->|=>|\bto\b|\bku\s+bedel\b|\bu\s+bedel\b)", raw, re.I):
        return None
    old_name = match.group(1).strip(" \t,;:-")
    # A trailing number in SAX is an amount correction, not a customer name.
    if re.search(r"\d", old_name):
        return None
    return old_name or None


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
    # Negated statements describe an unpaid/undelivered state, not a payment.
    # Check these before broad verb stems such as "bixin" or "keenay".
    negative_transaction_patterns = (
        r"\b(?:wali\s+)?ma\s+(?:bixin|bixinin|bixinayo|bixinay|bixin|keenin|keenay|soo\s+celin|soo\s+celinayo|soo\s+celinay)\b",
        r"\b(?:ima|uma)\s+(?:bixin|keenin|soo\s+celin)\b",
        r"\b(?:bixin\s+maayo|bixin\s+mayso|keenin\s+maayo|soo\s+celin\s+maayo)\b",
        r"\b(?:ma\s+uusan|ma\s+aysan|ma\s+uu|ma\s+ay)\s+(?:bixin|keenin|soo\s+celin)\b",
        r"\b(?:not\s+paid|hasn.t\s+paid|didn.t\s+pay|unpaid|payment\s+not\s+received)\b",
    )
    if any(re.search(pattern, text, re.I) for pattern in negative_transaction_patterns):
        return None
    add_patterns = [
        r"\b(?:deyn cusub|dayn cusub|new debt|add debt|added debt)\b",
        r"\b(?:iga\s+qaatay|wuu\s+qaatay|wuxuu\s+qaatay|ayaa\s+qaatay|ayuu\s+qaatay|"
        r"way\s+qaadatay|waxay\s+qaadatay|ayay\s+qaadatay|ayaan\s+qaadatay|"
        r"qaatey|qaadatay|qaateen|qaaty|qaatay|qaadan(?:ayaa|ayo|ey| doonaan)?|qaato|"
        r"dayn\s+qaato|deyn\s+qaato|dayn\s+qaatay|deyn\s+qaatay|"
        r"dayn\s+qaadatay|deyn\s+qaadatay|dayn\s+qaatey|deyn\s+qaatey|"
        r"dayn\s+qaadasho|deyn\s+qaadasho|amaah|"
        r"ka\s+siiyay|ka\s+siiyey|u\s+siiyay|u\s+siiyey)\b",
        r"\b(?:ku\s+dar|kudar|ku\s+biir|ku\s+biiri|ku\s+darid|add\s+to\s+(?:the\s+)?existing)\b",
        r"\b(?:took|borrowed)\b",
    ]
    pay_patterns = [
        r"\b(?:ka\s+jar|ka\s+jarey|ka\s+reeb|ka\s+reebay|ka\s+reebtay|ka\s+reebeen|"
        r"ka\s+qabatay|ka\s+qabtay|ka\s+qabteen|ka\s+qabtay)\b",
        r"\b(?:bixiyay|bixiyey|bixisay|bixiyeen|bixiya|bixiyaa|bixiyo|bixin|bixinta|"
        r"bixiyayaa|bixisay|bixiye|bixiyeen|soo\s+celiyay|soo\s+celiyey|"
        r"soo\s+celisay|soo\s+celiyeen|soo\s+celiyey|celiyay|celiyey|celisay|celiyeen|"
        r"keenay|keentay|keeney|ii\s+keenay|ii\s+keentay|ii\s+keeneen|"
        r"soo\s+shubay|soo\s+shubtay|shubay|shubtay|xareeyay|xareysay)\b",
        r"\b(?:lacag\s*bixin(?:ta)?|lacag\s*qabasho|lacag\s+qabtay|"
        r"lacag\s+soo\s+xarootay|lacagtii\s+(?:waa\s+la\s+helay|wuu\s+keenay)|"
        r"lacag\s+(?:ayaa\s+la\s+helay|waa\s+la\s+helay)|"
        r"waan\s+ka\s+helay|waxaan\s+ka\s+helay|lacag\s+uu\s+bixiyay|"
        r"lacag\s+buu\s+ii\s+keenay|lacag\s+ayay\s+ii\s+keentay)\b",
        r"\b(?:wuu\s+bixiyay|wuxuu\s+bixiyay|ayaa\s+bixiyay|ayuu\s+bixiyay|"
        r"wuu\s+bixiyey|wuxuu\s+bixiyey|ayaa\s+bixiyey|ayuu\s+bixiyey|"
        r"lacag\s+ayuu\s+bixiyay|lacag\s+ayuu\s+bixiyey)\b",
        r"\b(?:paid|payment received|paid back|repaid|returned the money|received payment|collected payment)\b",
    ]
    has_add = any(re.search(pattern, text, flags=re.I) for pattern in add_patterns)
    has_pay = any(re.search(pattern, text, flags=re.I) for pattern in pay_patterns)
    if has_add and not has_pay:
        return "ADD"
    if has_pay and not has_add:
        return "PAY"
    return None


def _parse_somali_date(value):
    """Parse an explicit date; Somali day/month/year is interpreted as DD/MM/YYYY."""
    raw = str(value or "").strip()
    if not raw:
        return None
    for fmt in ("%d/%m/%Y", "%d-%m-%Y", "%Y-%m-%d", "%d/%m/%y", "%d-%m-%y"):
        try:
            return datetime.strptime(raw, fmt).date()
        except ValueError:
            pass
    return None


def parse_structured_somali_transaction(message_text):
    """Parse labelled multiline Somali debt/payment notes without depending on Gemini.

    Supports labelled notes and unlabelled multiline ADD notes with an explicit
    currency amount, a customer-name line, and optional standalone phone/item
    lines. It deliberately requires a name, amount, and identifiable direction.
    Payment notes continue through the existing payment parser and atomic RPC.
    """
    raw = str(message_text or "").replace("\r", "\n").strip()
    if not raw:
        return None

    lines = [" ".join(line.split()).strip() for line in raw.split("\n")]
    lines = [line for line in lines if line]
    if len(lines) < 3:
        return None

    folded = normalize_customer_name(raw)
    add_markers = (
        r"\b(?:dayn|deyn)\s+qaato\b",
        r"\b(?:dayn|deyn)\s+qaatay\b",
        r"\b(?:dayn|deyn)\s+qaadatay\b",
        r"\b(?:dayn|deyn)\s+qaatey\b",
        r"\b(?:deyn|dayn)\s+c cusub\b",
        r"\b(?:deyn|dayn)\s+cusub\b",
        r"\b(?:iga\s+qaatay|wuxuu\s+iga\s+qaatay|ayuu\s+qaatay|amaah)\b",
    )
    pay_markers = (
        r"\b(?:lacag\s*bixin|lacag\s+bixiyay|lacag\s+bixisay|lacag\s+soo\s+xarootay)\b",
        r"\b(?:wuu|wuxuu|ayaa)\s+bixiyay\b",
        r"\b(?:soo\s+celiyay|soo\s+celiyey|celiyay|celiyey)\b",
    )
    is_add = any(re.search(p, folded, re.I) for p in add_markers)
    is_pay = any(re.search(p, folded, re.I) for p in pay_markers)
    if is_add == is_pay:  # neither clear nor both directions
        return None
    action = "ADD" if is_add else "PAY"
    name = None
    phone = None
    amount = None
    description = None
    transaction_date = None

    for line_index, line in enumerate(lines):
        # Date label may share its line with the date or appear on the line above it.
        date_match = re.match(r"^(?:taariikh(?:da)?|tarikh(?:da)?)\s*[:：-]?\s*(.*?)\s*$", line, re.I)
        if date_match:
            date_text = date_match.group(1).strip()
            if not date_text and line_index + 1 < len(lines):
                date_text = lines[line_index + 1]
            candidate = re.search(r"\b(\d{1,2}[/-]\d{1,2}[/-]\d{2,4}|\d{4}-\d{1,2}-\d{1,2})\b", date_text)
            if candidate:
                transaction_date = _parse_somali_date(candidate.group(1))
            continue

        name_match = re.match(r"^(?:magaca(?:\s+macmiilka)?|customer\s+name)\s*[:：-]?\s*(.+?)\s*$", line, re.I)
        if name_match:
            name = name_match.group(1).strip(" .,:;-\t")
            continue

        phone_match = re.match(r"^(?:numberkisa|numberkeeda|lambarkiisa|lambarkeeda|telefoon(?:kiisa)?|phone(?:\s+number)?)\s*[:：-]?\s*(.+?)\s*$", line, re.I)
        if phone_match:
            digits = re.sub(r"\D", "", phone_match.group(1))
            if 7 <= len(digits) <= 15:
                phone = digits
            continue

        # A standalone 7-15 digit line is commonly the customer's phone number.
        if re.fullmatch(r"\s*\+?[\d\s().-]+\s*", line):
            digits = re.sub(r"\D", "", line)
            if 7 <= len(digits) <= 15:
                phone = digits
                continue

        amount_match = re.match(r"^(?:lacagta|lacag|amount)\s*[:：-]?\s*(.+?)\s*$", line, re.I)
        amount_text = amount_match.group(1).strip() if amount_match else line
        # Also accept a standalone amount line with an explicit currency marker,
        # e.g. "123 $" or "$123"; never mistake a long phone number for money.
        has_currency_marker = bool(re.search(r"[$]|\b(?:usd|dollars?|dollar)\b", amount_text, re.I))
        if amount_match or (action == "ADD" and has_currency_marker):
            number_match = re.search(r"(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)(?![\w/.-])", amount_text)
            if number_match:
                try:
                    parsed_amount = float(number_match.group(1).replace(",", "."))
                except ValueError:
                    return None
                if math.isfinite(parsed_amount) and parsed_amount > 0:
                    amount = parsed_amount
                    tail = (amount_text[:number_match.start()] + " " + amount_text[number_match.end():]).strip()
                    tail = re.sub(r"(?i)\b(?:usd|dollars?|dollar)\b|[$]", " ", tail)
                    tail = " ".join(tail.split()).strip(" .,:;-\t")
                    if tail:
                        description = tail
            continue

    # For unlabelled multiline ADD notes, identify the customer before a
    # description cue such as "oo ah", and collect the following item lines.
    if action == "ADD":
        description_cue_index = None
        for idx, source_line in enumerate(lines):
            if re.search(r"\b(?:oo\s+ah|shayga|alaabta|faahfaahin(?:ta)?)\b", source_line, re.I):
                description_cue_index = idx
                break

        if description is None and description_cue_index is not None:
            detail_lines = lines[description_cue_index + 1:]
            cleaned_details = []
            for detail_line in detail_lines:
                detail_line = re.sub(r"\s+ah$", "", detail_line, flags=re.I).strip(" .,:;-")
                if detail_line:
                    cleaned_details.append(detail_line)
            if cleaned_details:
                description = " ".join(cleaned_details)

        if not name:
            possible_names = []
            for idx, source_line in enumerate(lines):
                if description_cue_index is not None and idx >= description_cue_index:
                    break
                if re.match(r"^(?:taariikh|tarikh|magaca|customer\s+name|numberkisa|numberkeeda|lambarkiisa|lambarkeeda|telefoon|phone|lacagta|lacag|amount)\b", source_line, re.I):
                    continue
                if re.fullmatch(r"\s*\+?[\d\s().-]+\s*", source_line):
                    continue
                if re.search(r"[$]|\b(?:usd|dollars?|dollar)\b", source_line, re.I):
                    continue
                normalized_line = normalize_customer_name(source_line)
                if re.search(r"\b(?:amaah|deyn|dayn)\b", normalized_line, re.I):
                    continue
                if re.search(r"\b(?:bixinayso|bixinayo|bixin doonta|mar dhow)\b", normalized_line, re.I):
                    continue
                if re.search(r"[A-Za-z\u0080-\uffff]", source_line):
                    possible_names.append(source_line.strip(" .,:;-\t"))
            if possible_names:
                name = possible_names[-1]

    # Do not silently infer missing names or amounts from unrelated text.
    if not name or len(name) > 120 or amount is None:
        return None
    if not re.search(r"[A-Za-z\u0080-\uffff]", name):
        return None

    entry = {
        "action": action,
        "customer_name": name,
        "amount": amount,
        "customer_phone": phone,
        "new_phone": phone,
        "promised_date": None,
        "days_until_due": None,
        "payment_type": "PARTIAL" if action == "PAY" else None,
        "description": description,
        "transaction_date": transaction_date.isoformat() if transaction_date else None,
        "_source_amount_verified": True,
        "_structured_somali_transaction": True,
    }
    return [entry]


def parse_transaction_clarification(message_text):
    """Recognize natural Somali/English answers to a pending ADD-vs-PAY question.

    This parser is intentionally limited to the direction of the pending
    transaction. It never changes the saved customer name or amount.
    """
    text = normalize_customer_name(str(message_text or ""))
    text = re.sub(r"[.!؟?،,:;]+", " ", text)
    text = " ".join(text.split()).strip()

    # Numbered WhatsApp choices: 1 = new debt, 2 = payment, 3 = cancel.
    if text == "1":
        return "ADD"
    if text == "2":
        return "PAY"
    if text == "3":
        return "CANCEL"

    # Remove conversational wrappers without removing the transaction meaning.
    text = re.sub(
        r"^(?:waa|taasi waa|taas waa|waxaan ula jeedaa|waxaan ka wadaa|"
        r"waxay ahayd|waxay aheyd)\s+",
        "",
        text,
        flags=re.I,
    ).strip()

    # Somali answers often end with "weeye/waaye", "baa", or "bay ahayd".
    text = re.sub(r"\s+(?:weeye|waaye|weeyaan|baa|bay ahayd|bay aheyd|"
                  r"ayay ahayd|ayay aheyd|weeye.)$", "", text, flags=re.I).strip()

    # ADD: new debt / customer took or borrowed money.
    add_patterns = (
        r"^(?:deyn|dayn)\s*(?:cusub|baxday|cusub oo baxday)$",
        r"^(?:deyn|dayn)\s+(?:(?:ayuu|ayaa|wuu|wuxuu|way|waxay|ayay|ayaan)\s+)?"
        r"(?:qaatay|qaadatay|qaatey|qaateen)$",
        r"^(?:(?:wuu|wuxuu|ayuu|ayaa|way|waxay|ayay|ayaan)\s+)?(?:qaatay|qaadatay|qaatey|qaateen)$",
        r"^(?:iga qaatay|wuxuu iga qaatay|amaah|add|new debt)$",
    )
    if any(re.fullmatch(pattern, text, re.I) for pattern in add_patterns):
        return "ADD"

    # PAY: payment received / deduct from the customer's outstanding balance.
    pay_patterns = (
        r"^(?:lacag\s*bixin(?:ta)?|lacag soo xarootay|deyn soo xarootay)$",
        r"^(?:lacag baa soo gashay|lacag la helay|lacag ayaa la helay|"
        r"lacagtii waa la helay|lacag ayuu bixiyay|lacag ayu(u|y) bixiyay)$",
        r"^(?:ka jar|ka jarey|ka reeb|ka reebay|ka reebtay|ka qabtay|ka qabatay|"
        r"bixiyay|bixiyey|bixisay|bixiyeen|wuu bixiyay|wuxuu bixiyay|"
        r"ii keenay|ii keentay|keenay|keentay|soo shubay|soo shubtay|"
        r"soo celiyay|soo celiyey|lacag bixin weeye)$",
        r"^(?:pay|payment|money received|received payment|paid|paid back)$",
    )
    if any(re.fullmatch(pattern, text, re.I) for pattern in pay_patterns):
        return "PAY"

    if re.fullmatch(
        r"(?:jooji|cancel|baaji|stop|midna|midna maaha|midna ma ahan|"
        r"midna ma aha|midna ma ahan|midna midna|midna ma rabo)",
        text,
        re.I,
    ):
        return "CANCEL"

    # Do not treat a complete new transaction as an answer to the old
    # clarification. For example, while waiting for DEYN CUSUB/LACAG BIXIN,
    # "Ka jar Muna $10" is a NEW payment command, not confirmation of the
    # previous message. Only the exact short answers above (or the explicit
    # answer patterns) may replay a saved transaction.
    return None


def parse_multiline_menu_transaction(message_text):
    """Understand a menu choice, customer, amount, and optional due date
    sent together, for example:

    Menu
    1 Mxmed Cabdi 20
    Wakhtiga balanta waa 8/11/2026

    This is additive: it runs before Gemini and returns a standard ADD entry.
    """
    raw = " ".join(str(message_text or "").splitlines())
    raw = " ".join(raw.split())

    match = re.search(
        r"(?:^|\s)1\s+([A-Za-z\u0080-\uffff][A-Za-z\u0080-\uffff\s'-]{1,80}?)\s+"
        r"(?:\$)?(\d+(?:[.,]\d{1,2})?)(?:\s*\$)?"
        r"(?:.*?(?:ballan(?:ta)?|wakhtiga\s+balanta|waqtiga\s+balanta)\s*"
        r"(?:waa)?\s*[:\-]?\s*"
        r"(\d{1,2}[/-]\d{1,2}[/-]\d{2,4}|\d{4}-\d{1,2}-\d{1,2}))?",
        raw,
        flags=re.IGNORECASE,
    )

    if not match:
        return None

    name = match.group(1).strip()
    amount_text = match.group(2).replace(",", ".")
    due_text = match.group(3)

    try:
        amount = float(amount_text)
    except (TypeError, ValueError):
        return None

    if amount <= 0 or not name:
        return None

    due_date = None
    if due_text:
        for fmt in ("%d/%m/%Y", "%d-%m-%Y", "%Y-%m-%d"):
            try:
                due_date = datetime.strptime(due_text, fmt).date().isoformat()
                break
            except ValueError:
                continue

    return [{
        "action": "ADD",
        "customer_name": name.title(),
        "amount": amount,
        "promised_date": due_date,
        "days_until_due": None,
        "customer_phone": None,
        "transaction_date": None,
        "filter_date": None,
        "filter_type": None,
        "new_amount": None,
        "new_date": None,
        "new_name": None,
        "new_phone": None,
        "payment_type": None,
        "description": None,
    }]


def local_fallback_parse(message_text):
    """Conservatively parse common commands when Gemini is unavailable.

    This intentionally supports clear, single-customer commands only. It returns
    None rather than guessing for multi-customer, ambiguous, or unsupported text.
    """
    raw = " ".join(str(message_text or "").strip().split())
    if not raw:
        return None
    low = raw.casefold()

    if is_payment_report_command(raw):
        return None

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
            tail_description = segment[match.end():].strip(" .,:;-")
            tail_description = re.sub(
                r"\b(?:ayuu|wuxuu|wuu|ayaa|iga|qaatay|qaatey|qaato|bixiyay|bixiyey|bixisay|celiyay|celiyey|paid|repaid|amaah|deyn|dayn|cusub|usd|dollars?|dollar)\b",
                " ", tail_description, flags=re.I
            )
            tail_description = " ".join(tail_description.split()).strip(" .,:;-")
            if tail_description:
                name_text = re.sub(re.escape(tail_description), " ", name_text, count=1, flags=re.I)
                name_text = " ".join(name_text.split()).strip()
            ambiguous_entries.append({**base, "action": "ADD", "customer_name": name_text,
                                      "amount": float(amount_text.replace(",", ".")),
                                      "description": tail_description or None})
        if ambiguous_entries:
            return ambiguous_entries

    # Identify a single amount. Currency-marked amounts are safe; plain numbers
    # are accepted only when transaction wording makes their meaning explicit.
    amount_matches = list(re.finditer(r"\$\s*(\d+(?:[.,]\d{1,2})?)|(?<!\w)(\d+(?:[.,]\d{1,2})?)\s*\$", raw))
    currency_marked = bool(amount_matches)
    if not amount_matches:
        if classify_transaction_direction(raw) == "ADD":
            amount_matches = list(re.finditer(r"(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)(?![\w/.-])", raw))
        elif classify_transaction_direction(raw) == "PAY":
            amount_matches = list(re.finditer(r"(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)(?![\w/.-])", raw))
    # Do not guess if there are multiple amounts in a message.
    if len(amount_matches) > 1:
        return None

    is_replace = bool(re.search(r"\b(?:edit|kadhig|ka\s+dhig|ka\s+dhigo)\b", low))
    is_delete = bool(re.match(r"^(?:delete|remove|tirtir)\b", low))
    is_search = bool(re.match(r"^(?:search|find|lookup|look\s+up|raadi|raadso|show|check|hubi)\b", low))
    is_history = bool(re.search(r"\b(?:history|taariikh|statement|xisaab(?:ta)?|faahfaahin|faahfaahinta|description)\b",
        low
    ))
    is_payment = classify_transaction_direction(raw) == "PAY" or bool(re.search(
        r"\b(?:bixiyay|bixiyey|bixisay|bixiyeen|wuu\s+bixiyay|wuxuu\s+bixiyay|"
        r"soo\s+celiyay|soo\s+celiyey|celiyay|celiyey|waan\s+ka\s+helay|"
        r"waxaan\s+ka\s+helay|lacag\s*bixin(?:ta)?|paid|payment|repaid|paid\s+back)\b",
        low
    ))

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

    # Recover a description only from text after the stated amount. Never infer it
    # from stored customer data or from words that indicate transaction direction.
    transaction_description = None
    if amount_matches and (is_payment or classify_transaction_direction(raw) == "ADD"):
        # In amount-first Somali sentences ("50 ayaan Yuusuf ka siiyay"),
        # the words after the amount contain the customer's name, not a detail.
        amount_first = bool(re.match(r"^\s*(?:\$\s*)?\d", raw))
        tail = "" if amount_first else raw[amount_matches[0].end():].strip(" .,:;-")
        tail = re.sub(
            r"\b(?:ayuu|wuxuu|wuu|ayaa|ayay|ayaan|waxay|way|buu|bay|iga|"
            r"qaatay|qaadatay|qaateen|qaatey|qaaty|qaato|bixiyay|bixiyey|bixisay|bixiye|"
            r"celiyay|celiyey|celisay|celiyeen|soo|helay|keenay|keentay|qabatay|qabtay|"
            r"shubay|shubtay|xareeyay|xareysay|ii|ka|lacag|bixin|paid|repaid|amaah|deyn|dayn|cusub|usd|dollars?|dollar)\b",
            " ", tail, flags=re.I
        )
        tail = " ".join(tail.split()).strip(" .,:;-")
        transaction_description = tail or None

    # Remove amount tokens, action words and common transaction filler to recover
    # the customer's name without allowing the parser to invent one.
    name_text = raw
    for m in reversed(amount_matches):
        name_text = name_text[:m.start()] + " " + name_text[m.end():]
    if transaction_description:
        name_text = re.sub(re.escape(transaction_description), " ", name_text, count=1, flags=re.I)

    name_text = re.sub(r"\b(?:\$|usd|dollars?|ayuu|ayuu\s+iga\s+qaatay)\b", " ", name_text, flags=re.I)

    name_text = re.sub(r"^(?:edit|add|deyn|dayn|delete|remove|tirtir|search|find|lookup|look\s+up|raadi|raadso|show|check|hubi|ka\s+jar|ka\s+jarey|ka\s+reeb|ka\s+reebay)\b\s*[:,-]?\s*", "", name_text, flags=re.I)

    name_text = re.sub(r"\b(?:deyntiisa|deynta|deynteeda|balance|amount)\s+(?:ka\s+dhig|kadhig|ka\s+dhigo)\b", " ", name_text, flags=re.I)

    name_text = re.sub(
        r"\b(?:ka\s+dhig|kadhig|ka\s+dhigo|wuu|wuxuu|ayuu|ayaa|ayay|ayaan|"
        r"way|waxay|waan|waxaan|iga|buu|bay|soo\s+celiyay|soo\s+celiyey|celiyay|celiyey|"
        r"waan\s+ka\s+helay|waxaan\s+ka\s+helay|bixiyay|bixiyey|bixisay|bixiyeen|"
        r"qaadatay|qaateen|qaadanayaa|qaadaney|qaatey|qaaty|qaatay|qaato|"
        r"ka\s+qabatay|ka\s+qabtay|ka\s+qabteen|qabatay|qabtay|keenay|keentay|"
        r"ii\s+keenay|ii\s+keentay|soo\s+shubay|soo\s+shubtay|shubay|shubtay|"
        r"celisay|celiyeen|keeney|bixiye|soo|ii|lacag|xareeyay|xareysay|"
        r"ka\s+siiyay|ka\s+siiyey|u\s+siiyay|u\s+siiyey|"
        r"paid|payment|repaid|iga\s+soo|iga\s+qaatay|wuxuu\s+iga\s+qaatay|"
        r"amaah|deyn\s+ah|deyntii|deynta|oo\s+dhan|added|add)\b",
        " ", name_text, flags=re.I
    )
    name_text = re.sub(r"\b(?:lacag\s*bixin(?:ta)?|lacagta\s+soo\s+xarootay)\b", " ", name_text, flags=re.I)
    name_text = re.sub(r"^(?:waa|waxay ahayd|waxay aheyd)\s+", " ", name_text, flags=re.I)

    name_text = re.sub(
        r"\b(?:history|taariikh|statement|xisaab(?:ta)?|faahfaahin|faahfaahinta|description)\b",
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
        explicit_full_payment = bool(re.search(
            r"\b(?:deyntii\s+oo\s+dhan|dhammaan\s+deynta|deynta\s+oo\s+dhan|"
            r"paid\s+in\s+full|fully\s+paid|wuu\s+bixiyay|wuxuu\s+bixiyay)\b",
            low,
            flags=re.I,
        ))
        payment_type = (
            "PARTIAL" if amount is not None
            else "FULL" if explicit_full_payment
            else "UNKNOWN"
        )
        return [{**base, "action": "PAY", "customer_name": name, "amount": amount,
                 "payment_type": payment_type, "description": transaction_description}]
    if amount is not None and is_replace:
        return [{**base, "action": "EDIT", "customer_name": name,
                 "amount": amount, "new_amount": amount}]
    if amount is not None and (currency_marked or classify_transaction_direction(raw) == "ADD"):
        return [{**base, "action": "ADD", "customer_name": name, "amount": amount,
                 "description": transaction_description}]
    return None


def is_fuzzy_debt_list_command(message_text):
    """Recognize clear debt-list commands with small typing mistakes.

    Deliberately limited to read-only LIST commands. It never guesses
    EDIT, DELETE, ADD, or PAY commands.
    """
    raw = str(message_text or "").casefold().strip()
    raw = unicodedata.normalize("NFKD", raw)
    raw = "".join(ch for ch in raw if not unicodedata.combining(ch))
    raw = re.sub(r"[^\w\s]", " ", raw)
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
        .eq("is_archived", False)
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


def find_debtor_matches(business_user_id, name, include_archived=False):
    """Find exact names first, then aligned partial names, then safe fuzzy matches.

    A fuzzy match is not silently selected when another distinct customer name is
    nearly as likely; in that case all candidates are returned for clarification.
    """
    requested = normalize_customer_name(name)
    if not requested:
        return []

    query = (
        supabase.table("customers")
        .select("*")
        .eq("business_user_id", business_user_id)
    )
    # Ordinary debt operations see active customers only. HISTORY deliberately
    # includes archived rows so their statements remain retrievable.
    if not include_archived:
        query = query.eq("is_archived", False)
    result = query.order("name").execute()
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



def is_existing_account_add_request(message_text):
    """Detect wording that explicitly asks to extend an existing customer account."""
    text = normalize_customer_name(str(message_text or ""))
    patterns = (
        r"\b(?:kudar|ku\s+dar|ku\s+biir|ku\s+biiri|ku\s+biirid)\b",
        r"\b(?:xisaabtii|xisaabta)\s+(?:hore|jirta)\b",
        r"\b(?:deyntii|dayntii|deynta|daynta)\s+(?:hore|jirta)\b",
        r"\b(?:horey?\s+(?:ugu\s+)?dar|ku\s+dar\s+haraaga)\b",
        r"\badd\s+to\s+(?:the\s+)?existing\s+(?:account|balance)\b",
    )
    return any(re.search(pattern, text, re.I) for pattern in patterns)


def _unique_customer_names(matches):
    """Return one display name per distinct normalized customer name."""
    unique = {}
    for row in matches or []:
        display = str(row.get("name") or "").strip()
        normalized = normalize_customer_name(display)
        if normalized and normalized not in unique:
            unique[normalized] = display
    return list(unique.values())


def start_customer_match_session(sender_phone, business_user_id, entry,
                                 original_message, matches, stage,
                                 remaining_entries=None, allow_new=False):
    """Pause an ADD/PAY safely while the sender identifies the intended customer."""
    names = _unique_customer_names(matches)
    CUSTOMER_MATCH_SESSIONS[sender_phone] = {
        "business_user_id": str(business_user_id),
        "entry": dict(entry),
        "original_message": str(original_message or ""),
        "candidate_names": names,
        "stage": stage,
        "remaining_entries": [dict(item) for item in (remaining_entries or [])],
        "allow_new": bool(allow_new),
        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
    }

    if stage == "confirm_single":
        prompt = (
            f"Waxaan helay hal macmiil oo magacaagu u egyahay: *{names[0]}*.\n\n"
            "Ma isaga/iyada ayaad ula jeeddaa? Soo qor *HAA* ama *MAYA*."
        )
        if allow_new:
            prompt += "\nHaddii aad rabto macmiil cusub, qor *CUSUB*."
    elif stage == "enter_full_name":
        prompt = (
            f"Ma helin *{entry.get('customer_name')}* liiska macaamiisha.\n"
            "Fadlan qor magaca buuxa ee macmiilka jira. Waxba lama diiwaangelin."
        )
    else:
        prompt = "⚠️ *Waxaan helay macaamiil magacyadoodu isku dhow yihiin.*\n\n"
        for index, customer_name in enumerate(names[:10], start=1):
            prompt += f"{index}️⃣ {customer_name}\n"
        prompt += "\nDooro lambarka macmiilka saxda ah."
        if allow_new:
            prompt += "\nHaddii uusan ku jirin, qor *CUSUB*."
        else:
            prompt += "\nHaddii uusan ku jirin, qor magaca oo buuxa."

    prompt += "\n\nQor *JOOJI* si aad u baajiso."
    send_whatsapp(sender_phone, prompt)


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


def find_delete_customer_candidates(business_user_id, requested_name):
    """Find all plausible distinct customer names for DELETE; never pick one by shortest-name bias."""
    requested = normalize_customer_name(requested_name)
    if not requested:
        return []

    result = (
        supabase.table("customers")
        .select("id, name, amount, business_user_id")
        .eq("business_user_id", business_user_id)
        .eq("is_archived", False)
        .order("name")
        .execute()
    )
    rows = result.data or []
    grouped = {}
    for row in rows:
        display = str(row.get("name") or "").strip()
        normalized = normalize_customer_name(display)
        if not normalized:
            continue
        item = grouped.setdefault(normalized, {"name": display, "rows": [], "score": 0.0})
        item["rows"].append(row)

    if requested in grouped:
        return [grouped[requested]]

    request_tokens = requested.split()
    token_matches = []
    for normalized, item in grouped.items():
        stored_tokens = normalized.split()
        # Every typed token must correspond to a stored token. Partial spelling
        # is allowed, but all possible full-name matches are retained.
        token_scores = []
        for token in request_tokens:
            best = max(
                (difflib.SequenceMatcher(None, token, stored).ratio() for stored in stored_tokens),
                default=0.0,
            )
            token_scores.append(best)
        if token_scores and all(score >= 0.78 for score in token_scores):
            item["score"] = sum(token_scores) / len(token_scores)
            token_matches.append(item)
    if token_matches:
        token_matches.sort(key=lambda item: item["score"], reverse=True)
        return token_matches

    # Word-boundary partial match, preserving every distinct matching name.
    partial = [
        item for normalized, item in grouped.items()
        if f" {requested} " in f" {normalized} " or f" {normalized} " in f" {requested} "
    ]
    if partial:
        return partial

    # Last resort: full-name fuzzy candidates. A single clear candidate is
    # acceptable only because it will still require an explicit confirmation.
    scored = []
    for normalized, item in grouped.items():
        score = _name_similarity(requested, normalized)
        if score >= 0.78:
            item["score"] = score
            scored.append(item)
    if not scored:
        return []
    scored.sort(key=lambda item: item["score"], reverse=True)
    best_score = scored[0]["score"]
    return [item for item in scored if best_score - item["score"] <= 0.08]


def begin_delete_flow(sender_phone, business_user_id, requested_name):
    """Resolve a DELETE name and stage exact row IDs for a second-step confirmation."""
    requested_name = " ".join(str(requested_name or "").split()).strip(" .,:;")
    if not requested_name:
        DELETE_SESSIONS[sender_phone] = {
            "business_user_id": str(business_user_id),
            "stage": "name",
            "expires_at": datetime.now(timezone.utc) + DELETE_SESSION_TTL,
        }
        send_whatsapp(sender_phone, "Waa qofkee? Fadlan qor magaca macmiilka aad rabto inaad tirtirto.\nQor *JOOJI* si aad uga baxdo.")
        return {"status": "delete_name_requested"}

    candidates = find_delete_customer_candidates(business_user_id, requested_name)
    if not candidates:
        DELETE_SESSIONS.pop(sender_phone, None)
        send_whatsapp(sender_phone, f"❌ Ma hayo *{requested_name}*. Hubi magaca oo mar kale isku day.")
        return {"status": "delete_customer_not_found"}

    if len(candidates) > 1:
        DELETE_SESSIONS[sender_phone] = {
            "business_user_id": str(business_user_id),
            "stage": "choose",
            "candidates": candidates,
            "expires_at": datetime.now(timezone.utc) + DELETE_SESSION_TTL,
        }
        lines = ["⚠️ Magacaasi wuxuu la mid yahay macaamiil kala duwan. Dooro qofka saxda ah:"]
        for index, candidate in enumerate(candidates[:10], 1):
            balance = sum(float(row.get("amount") or 0) for row in candidate["rows"])
            lines.append(f"{index}. {candidate['name']} — ${balance:.2f}")
        lines.extend(["", "Soo qor lambarka saxda ah ama magaca buuxa.", "Qor *JOOJI* si aad u baajiso."])
        send_whatsapp(sender_phone, "\n".join(lines))
        return {"status": "delete_customer_choice_required", "candidate_count": len(candidates)}

    candidate = candidates[0]
    rows = candidate["rows"]
    balance = sum(float(row.get("amount") or 0) for row in rows)
    DELETE_SESSIONS[sender_phone] = {
        "business_user_id": str(business_user_id),
        "stage": "confirm",
        "customer_name": candidate["name"],
        "customer_ids": [str(row["id"]) for row in rows if row.get("id") is not None],
        "balance": balance,
        "expires_at": datetime.now(timezone.utc) + DELETE_SESSION_TTL,
    }
    send_whatsapp(
        sender_phone,
        f"⚠️ *Xaqiiji tirtiridda*\n\n"
        f"Macmiil: *{candidate['name']}*\n"
        f"Wadarta deynta: *${balance:.2f}*\n"
        f"Inta laga jarayo: *{len(rows)}*\n\n"
        "Haddii ay sax tahay, soo qor *HAA, TIRTIR*.\n"
        "Haddii macmiilku leeyahay lacag-bixin ama taariikh macaamil, waa la archive-gareynayaa; haddii kale waa la tirtirayaa.\n"
        "Qor *JOOJI* si aad uga baxdo."
    )
    return {"status": "delete_confirmation_required", "customer": candidate["name"], "rows": len(rows)}


def handle_delete_session(sender_phone, business_user_id, message_text):
    """Handle the name, disambiguation, confirmation, and cancellation steps."""
    state = DELETE_SESSIONS.get(sender_phone)
    if not state:
        return None
    if state.get("business_user_id") != str(business_user_id):
        DELETE_SESSIONS.pop(sender_phone, None)
        return None

    now = datetime.now(timezone.utc)
    expires_at = state.get("expires_at")
    if not expires_at or now > expires_at:
        DELETE_SESSIONS.pop(sender_phone, None)
        send_whatsapp(sender_phone, "⌛ Waqtigii tirtiriddu wuu dhammaaday. Waxba lama tirtirin. Mar kale qor *DELETE*.")
        return {"status": "delete_session_expired"}

    answer = " ".join(str(message_text or "").strip().split())
    folded = normalize_customer_name(answer)
    if re.fullmatch(r"(?:jooji|cancel|baaji|stop|maya)", folded, re.I):
        DELETE_SESSIONS.pop(sender_phone, None)
        send_whatsapp(sender_phone, "✅ Tirtiridda waa la joojiyey. Waxba lama tirtirin.")
        return {"status": "delete_cancelled"}

    stage = state.get("stage")
    if stage == "name":
        return begin_delete_flow(sender_phone, business_user_id, answer)

    if stage == "choose":
        candidates = state.get("candidates") or []
        chosen = None
        if re.fullmatch(r"\d+", answer):
            index = int(answer)
            if 1 <= index <= min(len(candidates), 10):
                chosen = candidates[index - 1]
        else:
            exact = [item for item in candidates if normalize_customer_name(item.get("name")) == folded]
            if len(exact) == 1:
                chosen = exact[0]
        if not chosen:
            send_whatsapp(sender_phone, "Doorashada lama fahmin. Soo qor lambarka liiska ama magaca buuxa ee saxda ah. *JOOJI* si aad u baajiso.")
            return {"status": "delete_choice_invalid"}
        candidate_rows = chosen["rows"]
        balance = sum(float(row.get("amount") or 0) for row in candidate_rows)
        state.update({
            "stage": "confirm",
            "customer_name": chosen["name"],
            "customer_ids": [str(row["id"]) for row in candidate_rows if row.get("id") is not None],
            "balance": balance,
            "expires_at": now + DELETE_SESSION_TTL,
        })
        send_whatsapp(
            sender_phone,
            f"⚠️ *Xaqiiji tirtiridda*\n\nMacmiil: *{chosen['name']}*\n"
            f"Wadarta deynta: *${balance:.2f}*\n"
            f"Diiwaannada macmiilka: *{len(candidate_rows)}*\n\n"
            "Haddii tani sax tahay, soo qor *HAA, TIRTIR*.\n"
            "Haddii uu leeyahay lacag-bixin ama taariikh macaamil, waa la archive-gareynayaa; haddii kale waa la tirtirayaa.\n"
            "Qor *JOOJI* si aad uga baxdo."
        )
        return {"status": "delete_confirmation_required", "customer": chosen["name"]}

    if stage == "confirm":
        if not re.fullmatch(r"(?:haa\s*,?\s*tirtir|tirtir|confirm\s+delete|yes\s+delete)", folded, re.I):
            send_whatsapp(sender_phone, "Fadlan xaqiiji adigoo qoraya *HAA, TIRTIR*, ama soo qor *JOOJI*. si aan loo tirtirin.")
            return {"status": "delete_waiting_confirmation"}

        customer_name = state.get("customer_name") or "macmiilka"
        customer_ids = state.get("customer_ids") or []
        if not customer_ids:
            DELETE_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "❌ Diiwaanka macmiilka lama xaqiijin karin. Waxba lama tirtirin.")
            return {"status": "delete_missing_ids"}

        try:
            # Financial history is authoritative: any payment OR transaction
            # means the customer row must be retained and archived.
            payment_history = (
                supabase.table("payments")
                .select("customer_id")
                .eq("business_user_id", business_user_id)
                .in_("customer_id", customer_ids)
                .limit(1)
                .execute()
            )
            transaction_history = (
                supabase.table("customer_transactions")
                .select("customer_id")
                .eq("business_user_id", business_user_id)
                .in_("customer_id", customer_ids)
                .limit(1)
                .execute()
            )
            has_history = bool(payment_history.data or transaction_history.data)

            if has_history:
                result = (
                    supabase.table("customers")
                    .update({"is_archived": True, "archived_at": datetime.now(timezone.utc).isoformat()})
                    .eq("business_user_id", business_user_id)
                    .in_("id", customer_ids)
                    .eq("is_archived", False)
                    .select("id")
                    .execute()
                )
                affected = len(result.data or [])
                DELETE_SESSIONS.pop(sender_phone, None)
                if affected != len(customer_ids):
                    send_whatsapp(sender_phone, f"⚠️ Macmiilka *{customer_name}* qayb ahaan ayaa loo archive-gareeyay ({affected}/{len(customer_ids)}). Fadlan hubi liiska.")
                    return {"status": "archive_partial", "archived": affected}
                send_whatsapp(sender_phone, f"✅ *{customer_name}* waa la archive-gareeyay. Deymihii iyo lacag-bixinnadii hore way kaydsan yihiin; magaca waxaad ka heli kartaa markaad codsato taariikhdiisa.")
                return {"status": "customer_archived", "archived": affected}

            deleted_count = 0
            for customer_id in customer_ids:
                result = (
                    supabase.table("customers")
                    .delete()
                    .eq("id", customer_id)
                    .eq("business_user_id", business_user_id)
                    .eq("is_archived", False)
                    .select("id")
                    .execute()
                )
                deleted_count += len(result.data or [])
            DELETE_SESSIONS.pop(sender_phone, None)
            if deleted_count != len(customer_ids):
                send_whatsapp(sender_phone, f"⚠️ {customer_name}: {deleted_count} ka mid ah {len(customer_ids)} diiwaan ayaa la tirtiray. Fadlan hubi liiska daynta.")
                return {"status": "delete_partial", "deleted": deleted_count}
            send_whatsapp(sender_phone, f"✅ *{customer_name}* waa la tirtiray. Ma lahayn lacag-bixin ama taariikh macaamil.")
            return {"status": "delete_confirmed", "deleted": deleted_count}
        except Exception as exc:
            print(f"❌ Confirmed delete/archive failed: {type(exc).__name__}: {exc}")
            DELETE_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "❌ Tirtiridda/archiving-ku way fashilantay. Waxba lama xaqiijin; fadlan hubi database-ka.")
            return {"status": "delete_error"}

    DELETE_SESSIONS.pop(sender_phone, None)
    return None


def parse_explicit_delete_command(message_text):
    """Return the customer name for a direct DELETE/REMOVE/TIRTIR command."""
    raw = " ".join(str(message_text or "").strip().split())
    match = re.match(r"^(?:delete|remove|tirtir)\b\s*[:,-]?\s*(.*?)\s*[.!]?$", raw, re.I)
    if not match:
        return None
    return match.group(1).strip(" .,:;") or ""


def send_due_list_followup(phone):
    send_whatsapp(
        phone,
        "Si aad u aragto dhammaan deymaha, soo qor:\n"
        "*Liiska daynta*\n"
        "Ama\n"
        "*Liiska daynta iyo balamaha*"
    )
def _import_parse_date(value):
    # Missing due dates stay empty; never invent a promise date of today.
    if value is None or str(value).strip().lower() in ("", "nan", "nat", "none", "null"):
        return None
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
        if not math.isfinite(amount) or amount <= 0:
            raise ValueError(f"Saf {i} ({name}): lacagtu waa inay noqotaa tiro sax ah oo ka weyn eber.")
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


def _gemini_generate_content(url, payload, timeout=60):
    """Retry temporary Gemini capacity/server failures before reporting failure."""
    retryable_statuses = {429, 500, 502, 503, 504}
    delays = (2, 5)
    for attempt in range(3):
        try:
            response = requests.post(
                url,
                headers={"x-goog-api-key": GEMINI_API_KEY,
                         "Content-Type": "application/json"},
                json=payload,
                timeout=timeout,
            )
        except requests.RequestException:
            if attempt < 2:
                time.sleep(delays[attempt])
                continue
            raise RuntimeError("GEMINI_TEMPORARILY_UNAVAILABLE: network error")
        if response.ok:
            return response
        if response.status_code in retryable_statuses:
            if attempt < 2:
                print(f"⚠️ Gemini temporary HTTP {response.status_code}; retry {attempt + 1}/2")
                time.sleep(delays[attempt])
                continue
            raise RuntimeError(
                f"GEMINI_TEMPORARILY_UNAVAILABLE: Gemini HTTP {response.status_code} after retries"
            )
        response.raise_for_status()
    raise RuntimeError("GEMINI_TEMPORARILY_UNAVAILABLE: Gemini unavailable")


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
    response = _gemini_generate_content(url, payload, timeout=60)
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
            lines.append(f"{i}. {item['name']} — ${item['amount']:.2f} — {item.get('promised_date') or 'Lama sheegin'}")
        lines += ["", f"*Wadarta guud: ${total:.2f}*", "", "Hubi magacyada iyo lacagaha.",
                  "Haddii ay sax yihiin, soo qor *OK* si loo kaydiyo.",
                  "Haddii kale, soo qor *CANCEL* si loo joojiyo."]
    send_whatsapp(admin_phone, "\n".join(lines))


def _import_duplicate_groups(business_user_id, entries):
    """Find possible repeated unpaid debts, ignoring due date by design.

    The user decides whether same-name/same-amount rows are one debt or
    separate debts. Existing unpaid rows are included in the same check.
    """
    groups = {}
    for index, item in enumerate(entries):
        key = (normalize_customer_name(item.get("name")), round(float(item.get("amount") or 0), 2))
        groups.setdefault(key, []).append(index)

    existing_result = (supabase.table("customers")
        .select("id, name, amount, promised_date")
        .eq("business_user_id", business_user_id)
        .eq("is_archived", False)
        .eq("is_paid", False).execute())
    existing_rows = existing_result.data or []
    duplicates = []
    for key, indexes in groups.items():
        existing_matches = [row for row in existing_rows
            if normalize_customer_name(row.get("name")) == key[0]
            and round(float(row.get("amount") or 0), 2) == key[1]]
        if len(indexes) > 1 or existing_matches:
            duplicates.append({
                "key": key,
                "indexes": indexes,
                "existing": existing_matches,
                "name": entries[indexes[0]]["name"],
                "amount": float(entries[indexes[0]]["amount"]),
            })
    return duplicates


def _apply_import_duplicate_choice(session, choice):
    """Apply 1=keep one / 2=save all possible duplicates."""
    entries = list(session.get("entries") or [])
    groups = session.get("duplicate_groups") or []
    if choice == "2":
        session["duplicate_choice"] = "2"
        return

    drop_indexes = set()
    for group in groups:
        indexes = group.get("indexes") or []
        # If an identical unpaid debt already exists, keep that existing row
        # and do not add another import row for this duplicate group.
        if group.get("existing"):
            drop_indexes.update(indexes)
        elif len(indexes) > 1:
            drop_indexes.update(indexes[1:])
    session["entries"] = [item for i, item in enumerate(entries) if i not in drop_indexes]
    session["pre_skipped"] = len(drop_indexes)
    session["duplicate_choice"] = "1"


def _commit_import(admin_phone, session):
    """Commit a reviewed import, reporting partial writes rather than hiding them."""
    entries = list(session.get("entries") or [])
    business_user_id = session["business_user_id"]
    import_mode = session.get("mode", "debt")

    if not entries:
        raise ValueError("Liiska import-ku waa madhan yahay.")

    if import_mode == "payment":
        # Validate every row before making changes. Each payment must resolve to
        # exactly one currently unpaid debt, and cumulative rows cannot exceed it.
        prepared = []
        cumulative = {}
        for item in entries:
            amount = float(item["amount"])
            if not math.isfinite(amount) or amount <= 0:
                raise ValueError(f"{item.get('name')}: lacagtu ma saxna.")
            matches = find_debtor_matches(business_user_id, item["name"])
            unpaid = [
                row for row in matches
                if row.get("is_paid") is not True and _safe_money(row.get("amount")) > 0
            ]
            if len(unpaid) != 1:
                reason = (
                    "lama helin deyn aan la bixin"
                    if not unpaid
                    else "waxaa jira deymo badan oo magacaas leh"
                )
                raise ValueError(f"{item['name']}: {reason}. Hubi magaca ama kala saar deymaha.")
            debtor = unpaid[0]
            debt_id = str(debtor["id"])
            cumulative[debt_id] = cumulative.get(debt_id, 0.0) + amount
            if cumulative[debt_id] - _safe_money(debtor.get("amount")) > 0.009:
                raise ValueError(
                    f"{item['name']}: lacagta la soo gelinayo (${cumulative[debt_id]:.2f}) "
                    f"waxay ka badan tahay haraaga (${_safe_money(debtor.get('amount')):.2f})."
                )
            prepared.append((item, debtor))

        saved = 0
        try:
            for item, debtor in prepared:
                rpc_result = supabase.rpc("record_debt_payment_with_history", {
                    "p_customer_id": str(debtor["id"]),
                    "p_business_user_id": str(business_user_id),
                    "p_amount": round(float(item["amount"]), 2),
                    "p_description": str(item.get("description") or "-").strip() or "-",
                }).execute()
                rpc_data = rpc_result.data
                if isinstance(rpc_data, list):
                    rpc_data = rpc_data[0] if rpc_data else None
                if not isinstance(rpc_data, dict) or not rpc_data.get("id"):
                    raise RuntimeError(
                        "record_debt_payment ma xaqiijin lacag-bixinta. Hubi Supabase."
                    )
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

        total_paid = sum(float(item["amount"]) for item in entries)
        send_whatsapp(
            admin_phone,
            "✅ Import-ka lacag-bixinta waa dhammaaday.\\n"
            f"Lacag-bixin la diiwaangeliyay: {saved}\\n"
            f"Wadarta lacagta: ${total_paid:.2f}\\n"
            "Lacagaha waxaa laga jaray deymaha dukaanka la doortay."
        )

        shop_phone = ""
        shop_name = str(session.get("shop_name") or "Dukaankaaga")
        try:
            shop_result = (
                supabase.table("business_users")
                .select("phone_number, name")
                .eq("id", business_user_id)
                .limit(1)
                .execute()
            )
            if shop_result.data:
                shop_phone = str(shop_result.data[0].get("phone_number") or "")
                shop_name = str(shop_result.data[0].get("name") or shop_name)
        except Exception as lookup_exc:
            print(
                "⚠️ Could not look up business user for payment-import notification: "
                f"{type(lookup_exc).__name__}: {lookup_exc}"
            )

        if not shop_phone:
            shop_phone = str(session.get("shop_phone") or "")
        shop_phone = shop_phone.replace("+", "").split("@")[0].strip()
        admin_clean = str(admin_phone or "").replace("+", "").split("@")[0].strip()

        if shop_phone and shop_phone != admin_clean:
            business_message = (
                "✅ *Lacag-bixinnada waa la diiwaangeliyey.*\\n\\n"
                f"Dukaan: *{shop_name}*\\n"
                f"Tirada lacag-bixinnada: *{saved}*\\n"
                f"Wadarta lacagta: *${total_paid:.2f}*\\n\\n"
                "Lacagahan waxaa laga jaray deymaha macaamiisha ee dukaankaaga.\\n"
                "Qor *LIISKA DAYNTA* si aad u aragto haraaga cusub."
            )
            notification_sent = send_whatsapp(shop_phone, business_message)
            print(
                "📨 Payment-import business confirmation: "
                f"shop_phone={shop_phone}, sent={notification_sent}"
            )
        return

    if import_mode != "debt":
        raise ValueError("Nooca import-ka lama aqoonsan.")

    added = 0
    skipped = int(session.get("pre_skipped", 0) or 0)
    allow_duplicates = session.get("duplicate_choice") == "2"

    try:
        for item in entries:
            amount = float(item["amount"])
            if not math.isfinite(amount) or amount <= 0:
                raise ValueError(f"{item.get('name')}: lacagtu ma saxna.")

            # Choice 2 explicitly allows same-name/same-amount rows as separate
            # debts. Otherwise, recheck before insert to avoid a duplicate race.
            if not allow_duplicates:
                existing = (
                    supabase.table("customers")
                    .select("id")
                    .eq("business_user_id", business_user_id)
                    .eq("is_archived", False)
                    .eq("name", item["name"])
                    .eq("amount", amount)
                    .eq("is_paid", False)
                    .limit(1)
                    .execute()
                )
                if existing.data:
                    skipped += 1
                    continue

            result = supabase.rpc("record_debt_addition", {
                "p_customer_id": None,
                "p_business_user_id": str(business_user_id),
                "p_name": str(item["name"]),
                "p_amount": round(amount, 2),
                "p_description": str(item.get("description") or "-").strip() or "-",
                "p_promised_date": item.get("promised_date"),
                "p_phone_number": item.get("phone_number"),
                "p_created_at": None,
            }).execute()
            if not result.data:
                raise RuntimeError(f"Deynta {item['name']} lama xaqiijin in la kaydiyey.")
            added += 1
    except Exception as exc:
        if added:
            send_whatsapp(
                admin_phone,
                f"⚠️ Import-ku qayb ayuu u dhacay: {added} deyn waa la kaydiyey. "
                "Ha ku celin isla liiska; marka hore hubi LIISKA DAYNTA."
            )
            exc.partial_import = True
        raise

    if skipped:
        admin_confirmation = (
            "⚠️ Liiska deynta qayb ahaan ayaa loo diiwaangeliyey.\\n\\n"
            f"✅ Deymo cusub oo lagu daray: {added}\\n"
            f"⏭️ Deymo hore oo laga booday: {skipped}\\n\\n"
            "Deymaha hore laguma darin mar labaad."
        )
    else:
        admin_confirmation = (
            "✅ Liiska deynta waa la diiwaangeliyey.\\n\\n"
            f"👥 Deymo cusub oo lagu daray: {added}"
        )
    send_whatsapp(admin_phone, admin_confirmation)

    shop_phone = ""
    shop_name = str(session.get("shop_name") or "Dukaankaaga")
    try:
        shop_result = (
            supabase.table("business_users")
            .select("phone_number, name")
            .eq("id", business_user_id)
            .limit(1)
            .execute()
        )
        if shop_result.data:
            shop_phone = str(shop_result.data[0].get("phone_number") or "")
            shop_name = str(shop_result.data[0].get("name") or shop_name)
    except Exception as lookup_exc:
        print(
            "⚠️ Could not look up business user for debt-import notification: "
            f"{type(lookup_exc).__name__}: {lookup_exc}"
        )

    if not shop_phone:
        shop_phone = str(session.get("shop_phone") or "")
    shop_phone = shop_phone.replace("+", "").split("@")[0].strip()
    admin_clean = str(admin_phone or "").replace("+", "").split("@")[0].strip()

    if shop_phone and shop_phone != admin_clean:
        business_message = (
        "✅ *Deymo cusub ayaa lagu daray liiskaaga.*\n\n"
        f"Dukaan: *{shop_name}*\n"
        f"Macaamiil/deymo cusub: *{added}*\n"
        "Qor *LIISKA DAYNTA* si aad u aragto deymaha cusub."
        )
        notification_sent = send_whatsapp(shop_phone, business_message)
        print(
            "📨 Debt-import business confirmation: "
            f"shop_phone={shop_phone}, sent={notification_sent}"
        )
    else:
        print(
            "⚠️ Debt-import business confirmation skipped: "
            f"shop_phone={shop_phone!r}, admin_phone={admin_clean!r}"
        )


def is_duplicate_webhook(event_id):
    """Record an event ID once; return True only for a confirmed duplicate.

    A unique constraint on processed_webhook_events.event_id is required.
    Database/network errors raise HTTP 503 so Green-API can retry instead of
    silently dropping a legitimate financial command.
    """
    if not event_id:
        # No stable event ID means this delivery cannot safely be deduplicated.
        return False

    try:
        (
            supabase.table("processed_webhook_events")
            .insert({"event_id": str(event_id)})
            .execute()
        )
        return False
    except Exception as dedup_error:
        # PostgREST/Supabase reports PostgreSQL unique violations as 23505.
        error_code = getattr(dedup_error, "code", None)
        if error_code == "23505" or "23505" in str(dedup_error):
            return True

        print(
            "⚠️ Webhook deduplication unavailable: "
            f"{type(dedup_error).__name__}: {dedup_error}"
        )
        raise HTTPException(
            status_code=503,
            detail="Webhook deduplication is temporarily unavailable; retry delivery.",
        ) from dedup_error


@app.post("/webhook")
async def whatsapp_webhook(request: Request):
    data = await request.json()
    print(f"📥 Green-API webhook received: type={data.get('typeWebhook')}")

    # Ignore a repeated Green-API webhook delivery before it can create a
    # duplicate action or duplicate WhatsApp reply.
    message_data_for_id = data.get("messageData") or {}
    webhook_event_id = (
        data.get("id")
        or data.get("eventId")
        or message_data_for_id.get("idMessage")
        or message_data_for_id.get("id")
    )
    if is_duplicate_webhook(webhook_event_id):
        return {"status": "duplicate_webhook_ignored"}

    type_webhook = data.get("typeWebhook")

    # Accept messages received from WhatsApp contacts AND messages manually
    # sent from the linked WhatsApp phone. Green-API uses
    # outgoingMessageReceived for phone-originated messages, while messages
    # sent by this bot through Green-API use outgoingAPIMessageReceived.
    # Ignore outgoingAPIMessageReceived to prevent the bot processing its
    # own replies as fresh commands.
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

    # Voice notes/audio are intentionally not transcribed or sent to Gemini.
    if type_message in {"audioMessage", "pttMessage", "voiceMessage", "voiceNoteMessage"}:
        send_whatsapp(sender_phone, "Fadlan Qoraal soo qor.")
        return {"status": "audio_not_supported"}

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
        import_state = IMPORT_SESSIONS.get(sender_phone)
        if import_state and datetime.now(timezone.utc) > import_state.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
            IMPORT_SESSIONS.pop(sender_phone, None)
            import_state = None
        if import_state is None:
            send_whatsapp(sender_phone, "Waan arkay faylkaaga. Si aan u akhriyo, marka hore qor *IMPORT*, kadib dooro *DEYN* ama *LACAG BIXIN*, markaa soo dir faylka. Hada Waxba lama kaydin.")
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
            IMPORT_SESSIONS[sender_phone].pop("duplicate_choice", None)
            IMPORT_SESSIONS[sender_phone].pop("duplicate_groups", None)
            IMPORT_SESSIONS[sender_phone]["stage"] = "ready"
            IMPORT_SESSIONS[sender_phone]["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
            _stage_import(sender_phone, entries, IMPORT_SESSIONS[sender_phone].get("mode", "debt"))
            return {"status": "import_preview_ready", "count": len(entries)}
        except Exception as exc:
            print(f"❌ Import document error: {type(exc).__name__}: {exc}")
            send_whatsapp(sender_phone, f"❌ Faylka lama akhrin karin: {str(exc)[:250]}")
            return {"status": "import_document_error"}

    if type_message == "imageMessage":
        import_state = IMPORT_SESSIONS.get(sender_phone)
        if import_state and datetime.now(timezone.utc) > import_state.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
            IMPORT_SESSIONS.pop(sender_phone, None)
            import_state = None
        if import_state is None:
            send_whatsapp(sender_phone, "Waan arkay sawirkaaga. Si aan u akhriyo, marka hore soo Qor *IMPORT*, kadib dooro *DEYN* ama *LACAG BIXIN*.")
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
            IMPORT_SESSIONS[sender_phone].pop("duplicate_choice", None)
            IMPORT_SESSIONS[sender_phone].pop("duplicate_groups", None)
            IMPORT_SESSIONS[sender_phone]["stage"] = "ready"
            IMPORT_SESSIONS[sender_phone]["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
            _stage_import(sender_phone, entries, import_mode)
            return {"status": "import_image_preview_ready", "count": len(entries)}
        except Exception as exc:
            error_text = str(exc)
            print(f"❌ Import image error: {type(exc).__name__}: {error_text}")
            if "GEMINI_TEMPORARILY_UNAVAILABLE" in error_text:
                send_whatsapp(
                    sender_phone,
                    "⏳ Adeegga akhrinta sawirradu hadda waa mashquul. "
                    "Tani macnaheedu ma aha in sawirku khaldan yahay. hada Waxba lama kaydin. "
                    "Fadlan sug dhowr daqiiqo kadibna isla sawirka mar kale soo dir."
                )
                return {"status": "import_image_ai_temporarily_unavailable"}
            send_whatsapp(
                sender_phone,
                "❌ Sawirka lama farsamayn karin. hada Waxba lama kaydin. "
                "Fadlan mar kale isku day ama sawirka si cad u soo dir."
            )
            return {"status": "import_image_error"}

    # ✅ HANDLE TEXT MESSAGES, INCLUDING WHATSAPP QUOTED REPLIES
    try:
        if type_message == "textMessage":
            message_text = message_data.get("textMessageData", {}).get("textMessage", "")
        elif type_message == "extendedTextMessage":
            message_text = message_data.get("extendedTextMessageData", {}).get("text", "")
        elif type_message == "quotedMessage":
            # Green-API sends a WhatsApp reply/quote as typeMessage="quotedMessage".
            # The user's actual reply text is in extendedTextMessageData.text;
            # quotedMessage contains the message being replied to, not the new text.
            message_text = message_data.get("extendedTextMessageData", {}).get("text", "")
        else:
            print(f"⚠️ Unsupported incoming message type: {type_message}")
            return {"status": "unsupported_message_type", "type_message": type_message}
    except (KeyError, TypeError) as exc:
        print(f"❌ Could not extract incoming text: {type_message} - {exc}")
        return {"status": "no_text_payload"}

    print(f"📩 INCOMING MESSAGE TYPE: {type_message}")
    print(f"💬 EXTRACTED MESSAGE TEXT: {message_text!r}")

    # Emoji-only messages (including checkmarks/reactions) are acknowledgements,
    # not requests. Ignore them silently: never send "Fadlan Qoraal soo qor."
    if is_emoji_only_message(message_text):
        print(f"ℹ️ Emoji-only acknowledgement ignored: {message_text!r}")
        return {"status": "emoji_only_ignored"}

    if not message_text:
        return {"status": "empty_text"}

    # Help users who misspell common commands without changing free-form messages.
    message_text = normalize_easy_command(message_text)

    # Normalize sender; GREEN-API chat IDs may include "@c.us".
    sender_phone = str(sender_phone).replace("+", "").split("@")[0].strip()
    owner_phone = str(OWNER_PHONE).replace("+", "").split("@")[0].strip()

    # Resolve UNDO only after the approved business account is known.
    undo_match = re.fullmatch(
        r"\s*(?:undo(?:\s+last)?|ka\s+noqo|ka\s+noqo\s+kii\s+ugu\s+dambeeyay|ka\s+noqo\s+tii\s+ugu\s+dambeeysay)(?:\s+(.+?))?\s*[.!]?\s*",
        str(message_text or ""), re.I
    )

    # DHIGAAL is handled after the approved business account is resolved,
    # where the customer can be matched safely before any money is recorded.
    if re.fullmatch(r"\s*dhigaal\s*[.!]?\s*", str(message_text or ""), re.I):
        send_whatsapp(
            sender_phone,
            "💰 *DHIGAAL*\n\n"
            "Lacag dhigasho: *DHIGAAL Magaca $100*\n"
            "Hubi haraaga dhigaalka: *DHIGAAL Magaca*\n"
            "Tusaale: *DHIGAAL Cali $100*"
        )
        return {"status": "deposit_usage_help"}

    # Owner-only intervention works even if the owner is not a normal shop user.
    admin_command = re.fullmatch(r"\s*(APPROVE|REJECT)\s+PAYMENT\s+([0-9a-fA-F-]{36})\s*", str(message_text or ""), re.I)
    if sender_phone == owner_phone and admin_command:
        admin_action, pending_id = admin_command.groups()
        if admin_action.upper() == "APPROVE":
            pending_owner = supabase.table("pending_payment_confirmations").select("sender_phone").eq("id", pending_id).limit(1).execute()
            ok, result_text = _process_pending_payment_confirmation(pending_id, sender_phone, admin=True)
            send_whatsapp(sender_phone, result_text)
            if ok and pending_owner.data:
                send_whatsapp(pending_owner.data[0]["sender_phone"], result_text)
            return {"status": "admin_payment_approved" if ok else "admin_payment_approval_failed"}
        ok, pending_or_text = _reject_pending_payment_confirmation(pending_id, sender_phone, admin=True)
        if ok:
            send_whatsapp(sender_phone, "Lacag-bixinta waa la diiday. Waxba lama kaydin.")
            send_whatsapp(pending_or_text.get("sender_phone"), "Maamulka ayaa diiday lacag-bixintan. Waxba lama kaydin. Fadlan sax faahfaahinta oo mar kale dir.")
            return {"status": "admin_payment_rejected"}
        send_whatsapp(sender_phone, pending_or_text)
        return {"status": "admin_payment_rejection_failed"}

    # Approved users import into their own shop with IMPORT. The owner may
    # additionally select another approved shop using IMPORT +252... .
    import_text = str(message_text or "").strip()
    is_import_command = bool(re.fullmatch(r"\s*IMPORT(?:\s+\+?\d{8,15})?\s*", import_text, re.I))
    if (sender_phone == owner_phone or sender_phone in IMPORT_SESSIONS or is_import_command) and not (
        is_payment_report_command(import_text) or sender_phone in PAYMENT_EXPORT_SESSIONS
    ):
        if re.fullmatch(r"\s*CANCEL\s*", import_text, re.I) and sender_phone in IMPORT_SESSIONS:
            IMPORT_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "✅ Import waa la joojiyey. Hada Waxba lama kaydin.")
            return {"status": "import_cancelled"}
        session_for_choice = IMPORT_SESSIONS.get(sender_phone)
        if session_for_choice and session_for_choice.get("stage") == "duplicate_choice":
            if re.fullmatch(r"\s*2\s*", import_text):
                _apply_import_duplicate_choice(session_for_choice, "2")
                session_for_choice["stage"] = "ready"
                send_whatsapp(sender_phone, "✅ Labada deymood waa la kala gelinayaa. soo qor *OK* si loo kaydiyo ama *CANCEL* si loo joojiyo.")
                return {"status": "import_duplicates_confirmed_separate"}
            if re.fullmatch(r"\s*1\s*", import_text):
                _apply_import_duplicate_choice(session_for_choice, "1")
                session_for_choice["stage"] = "ready"
                send_whatsapp(sender_phone, "✅ Hal deyn oo keliya ayaan kaydinayaa. soo qor *OK* si aan u kaydiyo ama *CANCEL* si loo joojiyo.")
                return {"status": "import_duplicates_confirmed_single"}
            send_whatsapp(sender_phone, "ku Jawaab *2* si labada deymoodba loo geliyo, ama *1* si hal mid keliya loo geliyo. ama *CANCEL* si loo joojiyo.")
            return {"status": "awaiting_import_duplicate_choice"}

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
                if session.get("mode", "debt") == "debt" and session.get("duplicate_choice") is None:
                    duplicate_groups = _import_duplicate_groups(session["business_user_id"], session["entries"])
                    if duplicate_groups:
                        session["duplicate_groups"] = duplicate_groups
                        session["stage"] = "duplicate_choice"
                        session["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
                        lines = ["⚠️ *Deyn isku mid ah ayaa la helay:*", ""]
                        for group in duplicate_groups[:8]:
                            lines.append(f"• {group['name']} — ${group['amount']:.2f}")
                            for idx in group["indexes"][:4]:
                                item = session["entries"][idx]
                                lines.append(f"  Taariikh: {item.get('promised_date') or 'Lama sheegin'}")
                            if group.get("existing"):
                                lines.append("  Deyn noocan ah hore ayay dukaanka ugu jirtaa.")
                        lines.extend(["", "*2* — Deymaha kala duwan labadaba geli.", "*1* — Hal deyn keliya hay.", "*CANCEL* — Jooji import-ka."])
                        send_whatsapp(sender_phone, "\n".join(lines))
                        return {"status": "import_duplicate_choice_required", "groups": len(duplicate_groups)}
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
                    send_whatsapp(sender_phone, "❌ Lambarkan dukaan kuma jiro systemka.")
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
                    f"✅ Magaca: {own_shop.get('name') or sender_phone}.\n\n"
                    "Maxaad rabtaa inaad soo xarayso?\n"
                    "*DEYN* — deymo cusub.\n"
                    "*LACAG BIXIN* — Deyn soo xarootay.\n\n"
                    "Kadib ii soo dir qoraal, Excel/CSV ama sawir.\n"
                    "Xaqiiji, kadib soo qor *OK* si loo kaydiyo ama *CANCEL* si loo joojiyo.")
                return {"status": "import_own_shop_selected"}
            except Exception as exc:
                print(f"❌ Own-shop import lookup error: {exc}")
                send_whatsapp(sender_phone, "❌ Dukaanka lama hubin karin. Mar kale isku day.")
                return {"status": "import_own_shop_lookup_error"}

        match = re.fullmatch(r"\s*IMPORT\s+(\+?\d{8,15})\s*", import_text, re.I)
        if match and sender_phone != owner_phone:
            send_whatsapp(sender_phone, "❌ Waxaad soo gelin kartaa oo keliya liiska Ganacsigaaga. Dir *IMPORT* adigoon number raacin.")
            return {"status": "cross_shop_import_not_allowed"}
        if match:
            target_phone = match.group(1).replace("+", "")
            try:
                target = (supabase.table("business_users")
                    .select("id, phone_number, name, approval_status")
                    .eq("phone_number", target_phone).limit(1).execute())
                if not target.data:
                    send_whatsapp(sender_phone, "❌ Lambarkan kuma jiro systemka. Hubi numberka.")
                    return {"status": "import_shop_not_found"}
                shop = target.data[0]
                if shop.get("approval_status") != "approved":
                    send_whatsapp(sender_phone, "❌ Ganacsigan lama ansixin. Import lama bilaabi karo.")
                    return {"status": "import_shop_not_approved"}
                IMPORT_SESSIONS[sender_phone] = {"business_user_id": shop["id"], "shop_phone": target_phone,
                    "shop_name": shop.get("name") or target_phone, "entries": None, "mode": None,
                    "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL}
                send_whatsapp(sender_phone, f"✅ Dukaanka waa la doortay: {shop.get('name') or target_phone}.\n\nMaxaad rabtaa inaad soo geliso?\n*DEYN* — deymo cusub.\n*LACAG BIXIN* — lacagaha laga bixiyay deymaha jira.\n\nKadib ii soo dir qoraal, Excel/CSV ama sawir.\nHubi hordhaca, kadib qor *OK* si loo kaydiyo ama *CANCEL* si loo joojiyo.")
                return {"status": "import_shop_selected"}
            except Exception as exc:
                print(f"❌ Import shop lookup error: {exc}")
                send_whatsapp(sender_phone, "❌ Ganacsigan lama xaqiijin karo. Mar kale isku day.")
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
                send_whatsapp(sender_phone, "✅ Waxaad dooratay *DEYN*. soo dir liiska deynta qoraal ahaan, Excel/CSV ama sawir ahaan.")
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
                    active_import.pop("duplicate_choice", None)
                    active_import.pop("duplicate_groups", None)
                    active_import["stage"] = "ready"
                    active_import["expires_at"] = datetime.now(timezone.utc) + IMPORT_SESSION_TTL
                    _stage_import(sender_phone, entries, active_import.get("mode", "debt"))
                    return {"status": "import_text_preview_ready", "count": len(entries), "mode": active_import.get("mode", "debt")}
                except Exception as exc:
                    print(f"❌ Import text parse error: {type(exc).__name__}: {exc}")
                    send_whatsapp(sender_phone, "❌ Liiska si sax ah looma akhrin karo. Fadlan caddee magacyada iyo lacagaha, dabadeed mar kale soo dir.")
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
                "🎉 *Codsigaaga waa la oggolaaday!*\n\n" + deynjir_main_menu()
                if new_status == "approved"
                else "❌ Waan ka xunnahay, codsigaaga waa la diiday."
            )
            return {"status": new_status}

        except Exception as approval_err:
            print(f"❌ APPROVAL UPDATE ERROR: {approval_err}")
            send_whatsapp(sender_phone, "❌ Codsiga lama cusboonaysiin. Fadlan mar kale isku day ama la xiriir maamulka.")
            return {"status": "approval_update_error"}

    # First-contact onboarding for unknown and not-yet-approved numbers.
    # Approved business users continue into the existing Deynjir workflow unchanged.
    try:
        business_user_query = (
            supabase.table("business_users")
            .select("id, phone_number, name, approval_status")
            .eq("phone_number", sender_phone)
            .limit(1)
            .execute()
        )
        business_user = business_user_query.data[0] if business_user_query.data else None
        approval_status = str((business_user or {}).get("approval_status") or "").casefold()
        onboarding_text = str(message_text or "").strip()
        onboarding_command = onboarding_text.casefold().strip(" .!؟?")

        # TEMPORARY SILENT MODE:
        # Unknown, pending, and rejected users receive no automated replies.
        # The owner can still approve/reject applicants using the admin commands
        # handled immediately above this lookup. No approval records are changed.
        if not business_user or approval_status != "approved":
            ONBOARDING_SESSIONS.pop(sender_phone, None)
            print(
                f"🔕 UNAPPROVED USER SILENCED: phone={sender_phone}, "
                f"status={approval_status or 'not_registered'}"
            )
            return {"status": "unapproved_user_silenced"}

        business_user_id = business_user["id"]

        if undo_match:
            undo_key = str(undo_match.group(1) or "").strip()
            if not undo_key:
                recent = get_recent_selected_customer(sender_phone, business_user_id)
                undo_key = str((recent or {}).get("customer_name") or "").strip()
            if not undo_key:
                send_whatsapp(
                    sender_phone,
                    "↩️ Si aad macaamil uga noqoto, qor *UNDO Magaca Macmiilka*.\n"
                    "Tusaale: *UNDO Cali*. Haddii magaca uu leeyahay diiwaanno badan, isticmaal ID-ga 5-ta xaraf ah."
                )
                return {"status": "undo_customer_required"}
            try:
                undo_customer = None
                if re.fullmatch(r"[A-Za-z0-9]{5}", undo_key):
                    undo_lookup = (
                        supabase.table("customers")
                        .select("id, name")
                        .eq("id", undo_key.upper())
                        .eq("business_user_id", str(business_user_id))
                        .eq("is_archived", False)
                        .limit(1).execute()
                    )
                    undo_customer = undo_lookup.data[0] if undo_lookup.data else None
                if undo_customer is None:
                    undo_matches = find_debtor_matches(business_user_id, undo_key)
                    if not undo_matches:
                        send_whatsapp(sender_phone, f"❌ Lama helin macmiilka *{undo_key}*. Waxba lama beddelin.")
                        return {"status": "undo_customer_not_found"}
                    if len(undo_matches) > 1:
                        options = "\n".join(
                            f"• {row.get('name')} — ID: `{row.get('id')}`"
                            for row in undo_matches[:8]
                        )
                        send_whatsapp(
                            sender_phone,
                            "⚠️ Macmiilkan wuxuu leeyahay diiwaanno badan. Dooro ID-ga saxda ah:\n\n"
                            f"{options}\n\nTusaale: *UNDO ABC12*"
                        )
                        return {"status": "undo_customer_ambiguous"}
                    undo_customer = undo_matches[0]

                undo_result = supabase.rpc("undo_last_customer_transaction", {
                    "p_customer_id": str(undo_customer["id"]),
                    "p_business_user_id": str(business_user_id),
                }).execute()
                undo_data = undo_result.data
                if isinstance(undo_data, list):
                    undo_data = undo_data[0] if undo_data else None
                if not isinstance(undo_data, dict) or not undo_data.get("success"):
                    raise RuntimeError("Database-ku ma xaqiijin ka-noqoshada.")
                undone_amount = float(undo_data.get("amount") or 0)
                undone_type = str(undo_data.get("transaction_type") or "").upper()
                customer_after = undo_data.get("customer") or {}
                type_so = {
                    "ADD": "deyn lagu daray",
                    "PAY": "lacag-bixin",
                    "DEPOSIT": "dhigaal",
                }.get(undone_type, "macaamil")
                credit_restored = undo_data.get("restored_credit_balance")
                credit_note = (
                    f"\nHaraaga dhigaalka kadib ka-noqoshada: ${float(credit_restored):.2f}"
                    if credit_restored is not None else ""
                )
                send_whatsapp(
                    sender_phone,
                    f"✅ Macaamilkii ugu dambeeyay waa laga noqday.\n\n"
                    f"Macmiil: *{customer_after.get('name') or undo_customer.get('name')}*\n"
                    f"Nooca: {type_so}\nLacagta: *${undone_amount:.2f}*\n"
                    f"Haraaga deynta hadda: *${float(customer_after.get('amount') or 0):.2f}*"
                    f"{credit_note}\n\nTaariikhda macaamilka waa la hayey si loo helo raad-raac."
                )
                return {"status": "undo_completed", "transaction_type": undone_type, "amount": undone_amount}
            except Exception as undo_error:
                print(f"❌ UNDO error: {type(undo_error).__name__}: {undo_error}")
                send_whatsapp(
                    sender_phone,
                    "⚠️ Macaamilka lama celin. Waxaa laga yaabaa inuu yahay macaamil hore oo aan lahayn xiriir payment ID, ama haraagu wuu isbeddelay. Waxba lama beddelin."
                )
                return {"status": "undo_failed"}

        # Customer deposits are stored separately from debt. Deposits can be
        # attached by an exact 5-character customer ID or by a unique customer name.
        dhigaal_text = str(message_text or "").strip()
        dhigaal_match = re.fullmatch(
            r"dhigaal\s+(.+?)(?:\s+\$?\s*(\d+(?:[.,]\d{1,2})?))?\s*[.!]?",
            dhigaal_text,
            re.I,
        )
        if dhigaal_match:
            customer_key = str(dhigaal_match.group(1) or "").strip()
            amount_text = dhigaal_match.group(2)
            try:
                customer_row = None
                # A short customer ID is the safest selector when a person has
                # multiple debt records with the same name.
                if re.fullmatch(r"[A-Za-z0-9]{5}", customer_key):
                    id_result = (
                        supabase.table("customers")
                        .select("id, name, amount, is_paid")
                        .eq("id", customer_key.upper())
                        .eq("business_user_id", str(business_user_id))
                        .eq("is_archived", False)
                        .limit(1)
                        .execute()
                    )
                    customer_row = id_result.data[0] if id_result.data else None

                if customer_row is None:
                    customer_matches = find_debtor_matches(business_user_id, customer_key)
                    if len(customer_matches) == 0:
                        send_whatsapp(
                            sender_phone,
                            f"❌ Lama helin macmiilka *{customer_key}*. Hubi magaca ama ID-ga macmiilka."
                        )
                        return {"status": "dhigaal_customer_not_found"}
                    if len(customer_matches) > 1:
                        options = "\n".join(
                            f"• *{row.get('name')}* — ID: `{row.get('id')}`"
                            for row in customer_matches[:8]
                        )
                        send_whatsapp(
                            sender_phone,
                            "⚠️ Macmiilkan wuxuu leeyahay diiwaanno deyn oo badan. "
                            "Si aan dhigaalka ugu xiro diiwaanka saxda ah, isticmaal ID-ga 5-ta xaraf ah:\n\n"
                            f"{options}\n\n"
                            "Tusaale: *DHIGAAL ABC12 $100*"
                        )
                        return {"status": "dhigaal_customer_ambiguous"}
                    customer_row = customer_matches[0]

                if not amount_text:
                    balance_result = supabase.rpc("get_customer_credit_balance", {
                        "p_customer_id": str(customer_row["id"]),
                        "p_business_user_id": str(business_user_id),
                    }).execute()
                    balance_data = balance_result.data
                    if isinstance(balance_data, list):
                        balance_data = balance_data[0] if balance_data else None
                    balance = float((balance_data or {}).get("credit_balance") or 0)
                    send_whatsapp(
                        sender_phone,
                        f"💰 *Dhigaalka {customer_row.get('name')}*\n\n"
                        f"Haraaga dhigaalka: *${balance:.2f}*"
                    )
                    return {"status": "dhigaal_balance_checked", "credit_balance": balance}

                deposit_amount = float(amount_text.replace(",", "."))
                if not math.isfinite(deposit_amount) or deposit_amount <= 0:
                    raise ValueError("Lacagtu waa inay ka weyn tahay eber.")
                deposit_result = supabase.rpc("record_customer_credit_deposit", {
                    "p_customer_id": str(customer_row["id"]),
                    "p_business_user_id": str(business_user_id),
                    "p_amount": round(deposit_amount, 2),
                    "p_description": "DHIGAAL",
                }).execute()
                deposit_data = deposit_result.data
                if isinstance(deposit_data, list):
                    deposit_data = deposit_data[0] if deposit_data else None
                if not isinstance(deposit_data, dict) or not deposit_data.get("success"):
                    raise RuntimeError("Database-ku ma xaqiijin dhigaalka.")
                send_whatsapp(
                    sender_phone,
                    f"✅ *Dhigaal waa la diiwaangeliyey.*\n\n"
                    f"Macmiil: *{customer_row.get('name')}*\n"
                    f"Lacagta la dhigay: *${deposit_amount:.2f}*\n"
                    f"Haraaga dhigaalka: *${float(deposit_data.get('credit_balance') or 0):.2f}*\n\n"
                    "Marka deyn cusub lagu daro diiwaankan, nidaamku si toos ah ayuu uga isticmaali doonaa dhigaalka."
                )
                return {"status": "dhigaal_deposited", "credit_balance": deposit_data.get("credit_balance")}
            except Exception as dhigaal_error:
                print(f"❌ DHIGAAL error: {type(dhigaal_error).__name__}: {dhigaal_error}")
                send_whatsapp(
                    sender_phone,
                    "❌ Dhigaalka lama diiwaangelin. Hubi magaca iyo lacagta, kadib mar kale isku day."
                )
                return {"status": "dhigaal_error"}

        # Resolve a staged balance edit before interpreting the reply as a new command.
        amount_edit_state = AMOUNT_EDIT_SESSIONS.get(sender_phone)
        if amount_edit_state and amount_edit_state.get("business_user_id") == str(business_user_id):
            if datetime.now(timezone.utc) > amount_edit_state.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
                AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Waqtigii xaqiijinta wax-ka-beddelka wuu dhammaaday. Waxba lama beddelin. Fadlan codsiga mar kale dir.")
                return {"status": "amount_edit_expired"}
            edit_answer = normalize_customer_name(str(message_text or ""))
            if edit_answer in {"haa", "h", "1", "yes", "y", "ok", "sax"}:
                try:
                    current_result = (supabase.table("customers")
                        .select("id, name, amount, is_paid, promised_date")
                        .eq("id", str(amount_edit_state["customer_id"]))
                        .eq("business_user_id", str(business_user_id))
                        .eq("is_archived", False).limit(1).execute())
                    if not current_result.data:
                        AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                        send_whatsapp(sender_phone, "❌ Macmiilka lama helin. Waxba lama beddelin.")
                        return {"status": "amount_edit_customer_missing"}
                    current_customer = current_result.data[0]
                    if abs(_safe_money(current_customer.get("amount")) - float(amount_edit_state["old_amount"])) > 0.009:
                        AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                        send_whatsapp(sender_phone, "⚠️ Haraaga macmiilka wuu isbeddelay intii xaqiijintu sugaysay. Waxba lama beddelin. Fadlan dib u eeg liiska deynta.")
                        return {"status": "amount_edit_stale_balance"}
                    payment_history = (supabase.table("payments").select("customer_id")
                        .eq("business_user_id", str(business_user_id))
                        .eq("customer_id", str(amount_edit_state["customer_id"]))
                        .limit(1).execute())
                    transaction_history = (supabase.table("customer_transactions").select("customer_id")
                        .eq("business_user_id", str(business_user_id))
                        .eq("customer_id", str(amount_edit_state["customer_id"]))
                        .limit(1).execute())
                    if payment_history.data or transaction_history.data:
                        AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                        send_whatsapp(sender_phone, "⚠️ Macmiilkani wuxuu leeyahay taariikh macaamil/lacag-bixin. Si aan taariikhda iyo haraaga isugu khaldin, si toos ah looma beddeli karo lacagta. Waxba lama beddelin.")
                        return {"status": "amount_edit_blocked_by_ledger"}
                    update_data = dict(amount_edit_state.get("update_data") or {})
                    updated_result = (supabase.table("customers").update(update_data)
                        .eq("id", str(amount_edit_state["customer_id"]))
                        .eq("business_user_id", str(business_user_id))
                        .eq("is_archived", False)
                        .eq("amount", float(amount_edit_state["old_amount"]))
                        .select("id, name, amount, promised_date, is_paid").execute())
                    AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                    if not updated_result.data:
                        send_whatsapp(sender_phone, "❌ Waxba lama beddelin. Hubi rukhsadaha database-ka (RLS).")
                        return {"status": "amount_edit_update_empty"}
                    updated_customer = updated_result.data[0]
                    lines = []
                    if "amount" in update_data:
                        lines.append(f"💵 Lacag: ${float(current_customer.get('amount') or 0):.2f} → ${float(updated_customer.get('amount') or 0):.2f}")
                    if "promised_date" in update_data:
                        lines.append(f"📅 Ballan: {current_customer.get('promised_date') or 'lama gelin'} → {updated_customer.get('promised_date')}")
                    send_whatsapp(sender_phone, f"✅ Wax-ka-beddelka waa la xaqiijiyey.\n{updated_customer.get('name')}:\n" + "\n".join(lines))
                    return {"status": "amount_edit_confirmed"}
                except Exception as edit_confirm_error:
                    AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                    print(f"❌ Amount edit confirmation failed: {type(edit_confirm_error).__name__}: {edit_confirm_error}")
                    send_whatsapp(sender_phone, "❌ Wax-ka-beddelka lama xaqiijin karin. Waxba lama beddelin; maamulka ha hubiyo.")
                    return {"status": "amount_edit_confirmation_error"}
            if edit_answer in {"maya", "2", "no", "n", "cancel", "jooji", "baaji"}:
                AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "✅ Wax-ka-beddelka waa la joojiyey. Waxba lama beddelin.")
                return {"status": "amount_edit_cancelled"}
            send_whatsapp(sender_phone, "Fadlan qor *HAA* si loo xaqiijiyo ama *MAYA* si loo joojiyo. Waxba lama beddelin weli.")
            return {"status": "amount_edit_confirmation_required"}

        # Resolve the sender's persisted payment confirmation before parsing new commands.
        # A corrected customer name may reveal that the original message was a new debt,
        # not a payment. In that case, reject the mistaken payment proposal and replay
        # the debt through the normal ADD handler without changing any balance here.
        pending_payment_replay_entry = None
        pending_payment_result = (
            supabase.table("pending_payment_confirmations")
            .select("id, customer_name, amount, status, expires_at, original_message")
            .eq("sender_phone", sender_phone)
            .eq("business_user_id", str(business_user_id))
            .in_("status", ["pending", "processing"])
            .order("created_at", desc=True)
            .limit(1)
            .execute()
        )
        if pending_payment_result.data:
            pending_payment = pending_payment_result.data[0]
            if pending_payment.get("status") == "processing":
                send_whatsapp(sender_phone, "Lacag-bixintan hadda waa la farsamaynayaa. Fadlan sug; ha ku celin xaqiijinta.")
                return {"status": "payment_confirmation_processing"}
            pending_expiry_raw = pending_payment.get("expires_at")
            pending_expiry = datetime.fromisoformat(str(pending_expiry_raw).replace("Z", "+00:00")) if pending_expiry_raw else None
            if pending_expiry and pending_expiry.tzinfo is None:
                pending_expiry = pending_expiry.replace(tzinfo=timezone.utc)
            if not pending_expiry or datetime.now(timezone.utc) > pending_expiry:
                supabase.table("pending_payment_confirmations").update({"status": "expired"}).eq("id", pending_payment["id"]).eq("status", "pending").execute()
                send_whatsapp(sender_phone, "Waqtigii xaqiijinta wuu dhammaaday. Waxba lama kaydin. Fadlan lacag-bixinta mar kale soo dir.")
                return {"status": "payment_confirmation_expired"}
            answer_raw = str(message_text or "").strip()
            answer = normalize_customer_name(answer_raw)
            if answer not in {"1", "haa", "h", "yes", "y", "ok", "sax", "2", "maya", "may", "no", "n", "cancel", "jooji"}:
                # Accept a natural-language customer correction instead of trapping
                # the user in the numeric confirmation prompt.
                corrected_name = re.sub(
                    r"^\s*(?:(?:maya|no)\s+)?(?:(?:waa|weeye|magaca(?:\s+saxda\s+ah)?(?:\s+waa)?)\s+)?",
                    "",
                    answer_raw,
                    flags=re.I,
                ).strip(" .,:;!-")
                corrected_name = re.sub(
                    r"^(?:magaca\s+saxda\s+ah\s+waa|macmiilka\s+saxda\s+ah\s+waa)\s+",
                    "",
                    corrected_name,
                    flags=re.I,
                ).strip(" .,:;!-")
                original_pending_message = str(pending_payment.get("original_message") or "").strip()
                if (
                    len(corrected_name) >= 2
                    and len(corrected_name) <= 120
                    and not re.search(r"\d", corrected_name)
                    and normalize_customer_name(corrected_name) not in {
                        "waxba", "lacag", "jooji", "cancel", "deyn", "dayn",
                        "lacag bixin", "haa", "maya", "ok"
                    }
                ):
                    original_direction = classify_transaction_direction(original_pending_message)
                    if original_pending_message and original_direction == "ADD":
                        # The pending payment was a false interpretation of a clear
                        # amaah/debt message. Keep the verified amount, correct the name,
                        # and preserve a clearly supplied phone/item detail.
                        rejected_ok, rejected_value = _reject_pending_payment_confirmation(
                            pending_payment["id"], sender_phone
                        )
                        if not rejected_ok:
                            send_whatsapp(sender_phone, rejected_value)
                            return {"status": "mistaken_payment_rejection_failed"}
                        try:
                            replay_amount = float(pending_payment.get("amount") or 0)
                        except (TypeError, ValueError):
                            replay_amount = 0
                        if not math.isfinite(replay_amount) or replay_amount <= 0:
                            send_whatsapp(sender_phone, "Lacagtii hore si sax ah looma aqoonsan. Fadlan deynta mar kale u dir magaca iyo lacagta. Waxba lama kaydin.")
                            return {"status": "corrected_debt_amount_invalid"}

                        replay_phone = None
                        for source_line in original_pending_message.splitlines():
                            candidate_digits = re.sub(r"\D", "", source_line)
                            if (
                                re.fullmatch(r"\s*\+?[\d\s().-]+\s*", source_line)
                                and 7 <= len(candidate_digits) <= 15
                            ):
                                replay_phone = candidate_digits
                                break
                        replay_description = None
                        if re.search(r"\bmobile\b[\s\n]+a?\s*15\b|\ba\s*15\b[\s\n]+mobile\b", original_pending_message, re.I):
                            replay_description = "Mobile A15"

                        pending_payment_replay_entry = {
                            "action": "ADD",
                            "customer_name": corrected_name,
                            "amount": replay_amount,
                            "customer_phone": replay_phone,
                            "new_phone": replay_phone,
                            "promised_date": None,
                            "days_until_due": None,
                            "transaction_date": None,
                            "payment_type": None,
                            "description": replay_description,
                            "_source_amount_verified": True,
                        }
                        message_text = original_pending_message
                        GUIDED_SESSIONS.pop(sender_phone, None)
                        CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
                        print(
                            "🔁 Replaying mistaken payment as ADD after customer correction: "
                            f"name={corrected_name!r}, amount={replay_amount:.2f}, "
                            f"phone_present={bool(replay_phone)}, description={replay_description!r}"
                        )
                    else:
                        # For a genuine payment, resolve the corrected name against
                        # this shop and update the still-pending proposal only when
                        # exactly one unpaid debt is found.
                        corrected_matches = find_debtor_matches(business_user_id, corrected_name)
                        corrected_matches = [
                            row for row in corrected_matches
                            if row.get("is_paid") is not True and _safe_money(row.get("amount")) > 0
                        ]
                        if not corrected_matches:
                            # Do not keep asking for HAA/MAYA when the corrected
                            # customer has no open debt. Cancel the mistaken payment
                            # proposal and explain how to resend it as a new debt.
                            rejected_ok, rejected_value = _reject_pending_payment_confirmation(
                                pending_payment["id"], sender_phone
                            )
                            if not rejected_ok:
                                send_whatsapp(sender_phone, rejected_value)
                                return {"status": "payment_customer_correction_cancel_failed"}
                            send_whatsapp(
                                sender_phone,
                                f"Waad saxday: *{corrected_name}* lagama helin dayn furan oo lacagta laga jaro. "
                                "Lacag-bixintii khaldanayd waa la joojiyey; waxba lama kaydin.\n\n"
                                "Haddii tani tahay *deyn cusub*, dib u dir xogta adigoo ku bilaabaya "
                                "*DEYN CUSUB*, tusaale: *DEYN CUSUB Hinda $123*."
                            )
                            return {"status": "payment_correction_cancelled_no_open_debt"}
                        if len(corrected_matches) > 1:
                            send_whatsapp(
                                sender_phone,
                                "Waxaan helay in ka badan hal deyn oo magacaas leh. Fadlan qor magaca buuxa "
                                "ama faahfaahin kale. Lacag-bixintii hore weli lama diiwaangelin; "
                                "qor *MAYA* si aad u joojiso."
                            )
                            return {"status": "payment_customer_correction_needs_clarification"}
                        corrected_debtor = corrected_matches[0]
                        corrected_amount = _safe_money(pending_payment.get("amount"))
                        corrected_balance = _safe_money(corrected_debtor.get("amount"))
                        if corrected_amount <= 0 or corrected_amount - corrected_balance > 0.009:
                            send_whatsapp(
                                sender_phone,
                                f"{corrected_debtor.get('name')} haraagiisu waa ${corrected_balance:.2f}, "
                                f"mana daboolayo lacagta ${corrected_amount:.2f}. Lacag-bixinta lama diiwaangelin."
                            )
                            return {"status": "payment_customer_correction_amount_invalid"}
                        updated_pending = (
                            supabase.table("pending_payment_confirmations")
                            .update({
                                "customer_id": str(corrected_debtor["id"]),
                                "customer_name": str(corrected_debtor.get("name") or corrected_name),
                            })
                            .eq("id", str(pending_payment["id"]))
                            .eq("status", "pending")
                            .select("id")
                            .execute()
                        )
                        if not updated_pending.data:
                            send_whatsapp(sender_phone, "Saxitaanka macmiilka lama kaydin karin. Waxba lama diiwaangelin; fadlan mar kale isku day.")
                            return {"status": "payment_customer_correction_update_failed"}
                        send_whatsapp(
                            sender_phone,
                            "*Macmiilka waa la saxay.*\n\n"
                            f"{corrected_debtor.get('name')} ma wuxuu bixiyay *${corrected_amount:.2f}*?\n\n"
                            "1. *HAA*\n2. *MAYA*\n\n"
                            "Waxba lama kaydin ilaa aad xaqiijiso."
                        )
                        return {"status": "payment_customer_corrected_pending_confirmation"}

            if answer in {"1", "haa", "h", "yes", "y", "ok", "sax"}:
                ok, result_text = _process_pending_payment_confirmation(pending_payment["id"], sender_phone)
                send_whatsapp(sender_phone, result_text)
                return {"status": "payment_confirmed" if ok else "payment_confirmation_failed"}
            if answer in {"2", "maya", "may", "no", "n", "cancel", "jooji"}:
                ok, rejected = _reject_pending_payment_confirmation(pending_payment["id"], sender_phone)
                if not ok:
                    send_whatsapp(sender_phone, rejected)
                    return {"status": "payment_rejection_failed"}
                send_whatsapp(
                    sender_phone,
                    "Lacag-bixinta waa la diiday. Waxba lama kaydin.\n\n"
                    "Haddii magaca ama lacagtu khaldan yihiin, sax oo soo qor: *SAX Axmed $40*."
                )
                if owner_phone:
                    send_whatsapp(
                        owner_phone,
                        "⚠️ *LACAG-BIXIN LA DIIDAY — DIB U EEGIS*\n"
                        f"Dukaan: {business_user_id}\n"
                        f"Macmiil: {rejected.get('customer_name')}\n"
                        f"Lacag: ${float(rejected.get('amount') or 0):.2f}\n"
                        f"Qofka diray: {sender_phone}\n"
                        f"ID: {rejected.get('id')}\n"
                        f"Haddii xogtu sax tahay: APPROVE PAYMENT {rejected.get('id')}"
                    )
                return {"status": "payment_rejected"}
            send_whatsapp(sender_phone, "Fadlan ku jawaab *1 / HAA* ama *2 / MAYA*. Waxba lama kaydin.")
            return {"status": "payment_confirmation_answer_required"}

        # A rejected proposal remains available for a corrected name/amount.
        if re.match(r"^\s*sax\s+", str(message_text or ""), re.I):
            rejected_result = (
                supabase.table("pending_payment_confirmations")
                .select("id, customer_name, business_user_id")
                .eq("sender_phone", sender_phone)
                .eq("business_user_id", str(business_user_id))
                .eq("status", "rejected")
                .order("created_at", desc=True)
                .limit(1).execute()
            )
            correction = re.match(r"^\s*sax\s+(.+?)\s+\$?\s*(\d+(?:[.,]\d{1,2})?)\s*$", str(message_text or ""), re.I)
            if correction and not rejected_result.data:
                send_whatsapp(sender_phone, "Ma jiro lacag-bixin dhowaan la diiday oo la saxayo. Haddii aad rabto inaad beddesho magaca macmiilka, qor *SAX Magaca Hore*; haddii aad rabto wax-ka-beddelka deynta, qor *Magaca ka dhig 25*.")
                return {"status": "no_rejected_payment_to_correct"}
            if rejected_result.data and correction:
                corrected_name = correction.group(1).strip()
                corrected_amount = float(correction.group(2).replace(",", "."))
                corrected_matches = find_debtor_matches(business_user_id, corrected_name)
                corrected_matches = [row for row in corrected_matches if row.get("is_paid") is not True and _safe_money(row.get("amount")) > 0]
                if len(corrected_matches) != 1:
                    send_whatsapp(sender_phone, "Magaca cusub si gaar ah looma aqoonsan. Fadlan qor magaca buuxa ee macmiilka ama la xiriir maamulka. Waxba lama kaydin.")
                    if owner_phone:
                        send_whatsapp(owner_phone, f"⚠️ Saxitaanka lacag-bixinta ee {sender_phone} wuxuu u baahan yahay faragelin: {corrected_name} ${corrected_amount:.2f}.")
                    return {"status": "payment_correction_needs_admin"}
                corrected_debtor = corrected_matches[0]
                corrected_balance = _safe_money(corrected_debtor.get("amount"))
                if corrected_amount <= 0 or corrected_amount - corrected_balance > 0.009:
                    send_whatsapp(sender_phone, f"Lacagta saxda ahi waa inay ka badnaan weydo haraaga ${corrected_balance:.2f}. Waxba lama kaydin.")
                    return {"status": "payment_correction_amount_invalid"}
                inserted = supabase.table("pending_payment_confirmations").insert({
                    "sender_phone": sender_phone,
                    "business_user_id": str(business_user_id),
                    "customer_id": str(corrected_debtor["id"]),
                    "customer_name": str(corrected_debtor.get("name") or corrected_name),
                    "amount": round(corrected_amount, 2),
                    "description": "-",
                    "original_message": str(message_text),
                    "status": "pending",
                    "expires_at": (datetime.now(timezone.utc) + timedelta(minutes=30)).isoformat(),
                }).execute()
                if not inserted.data:
                    send_whatsapp(sender_phone, "Saxitaanka lama diyaarin karin. Waxba lama kaydin.")
                    return {"status": "payment_correction_save_failed"}
                corrected_pending = inserted.data[0]
                send_whatsapp(sender_phone, f"*Xaqiiji saxitaanka*\n\n{corrected_debtor.get('name')} ma wuxuu bixiyay *${corrected_amount:.2f}*?\n\n1. *HAA*\n2. *MAYA*\n\nWaxba lama kaydin ilaa aad xaqiijiso.")
                if owner_phone:
                    send_whatsapp(owner_phone, f"📝 Saxitaan cusub oo sugaya xaqiijin: {corrected_debtor.get('name')} ${corrected_amount:.2f}. ID: {corrected_pending.get('id')}")
                return {"status": "corrected_payment_pending_confirmation"}

    except Exception as db_err:
        print(f"❌ DATABASE ERROR (Business User Lookup): {db_err}")
        return {"status": "business_user_db_error"}

    # DELETE is handled locally and safely before Gemini or other command routing.
    # A name is resolved against this shop; multiple possible names require a choice.
    pending_delete = DELETE_SESSIONS.get(sender_phone)
    explicit_delete_name = parse_explicit_delete_command(message_text)
    if pending_delete:
        # A fresh explicit DELETE command intentionally replaces the previous
        # pending delete request; otherwise continue its name/choice/confirmation step.
        if explicit_delete_name is None:
            delete_result = handle_delete_session(sender_phone, business_user_id, message_text)
            if delete_result is not None:
                return delete_result
    if explicit_delete_name is not None:
        GUIDED_SESSIONS.pop(sender_phone, None)
        CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
        return begin_delete_flow(sender_phone, business_user_id, explicit_delete_name)

    # Friendly onboarding and guided actions. Numeric choices are interpreted
    # only while a menu session is active, so ordinary numbers remain untouched.
    guided_text = str(message_text or "").strip()
    guided = GUIDED_SESSIONS.get(sender_phone)
    if guided:
        expires_at = guided.get("expires_at")
        if not expires_at or datetime.now(timezone.utc) > expires_at:
            GUIDED_SESSIONS.pop(sender_phone, None)
            guided = None

    # Respond to common Somali expressions of confusion with a clear example.
    # Clear an unfinished guided step so the user can restart without stale state.
    if is_somali_confusion_request(guided_text):
        GUIDED_SESSIONS.pop(sender_phone, None)
        send_whatsapp(sender_phone, deynjir_confusion_help_message())
        return {"status": "somali_usage_help_sent"}

    menu_words = {"menu", "start", "hello", "hi", "hey", "help", "caawi", "caawimaad", "bilow"}
    if guided_text.casefold() in menu_words:
        CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
        GUIDED_SESSIONS[sender_phone] = {
            "stage": "menu",
            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
        }
        send_whatsapp(sender_phone, deynjir_main_menu())
        return {"status": "main_menu_sent"}

    if guided_text in {"GUIDED_DEBT", "GUIDED_PAYMENT"}:
        action = "debt" if guided_text == "GUIDED_DEBT" else "payment"
        GUIDED_SESSIONS[sender_phone] = {
            "stage": f"{action}_name",
            "transaction_type": action,
            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
        }
        prompt = "Magaca qofka daynta qaatay?" if action == "debt" else "Magaca qofka lacagta bixiyey?"
        send_whatsapp(sender_phone, prompt + "\n\nQor *JOOJI* haddii aad rabto inaad ka baxdo.")
        return {"status": f"guided_{action}_started"}

    if guided and re.fullmatch(r"\s*(?:jooji|cancel|baaji)\s*", guided_text, re.I):
        GUIDED_SESSIONS.pop(sender_phone, None)
        send_whatsapp(sender_phone, "Waa la joojiyey. Waxba lama beddelin. Qor *MENU* haddii aad caawimaad rabto.")
        return {"status": "guided_action_cancelled"}

    if guided and guided.get("stage") == "menu":
        choice = guided_text.strip()
        if choice == "1":
            guided["stage"] = "debt_name"
            guided["transaction_type"] = "debt"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
            send_whatsapp(sender_phone, "Magaca qofka daynta qaatay?\n\nQor *JOOJI* si aad uga baxdo.")
            return {"status": "guided_debt_name_requested"}
        if choice == "2":
            guided["stage"] = "payment_name"
            guided["transaction_type"] = "payment"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
            send_whatsapp(sender_phone, "Magaca qofka lacagta bixiyey?\n\nQor *JOOJI* si aad uga baxdo.")
            return {"status": "guided_payment_name_requested"}
        if choice == "3":
            GUIDED_SESSIONS.pop(sender_phone, None)
            message_text = "LIISKA DAYNTA"
        elif choice == "4":
            guided["stage"] = "search_name"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
            send_whatsapp(sender_phone, "Qor magaca qofka aad raadinayso.")
            return {"status": "guided_search_name_requested"}
        elif choice == "5":
            GUIDED_SESSIONS.pop(sender_phone, None)
            message_text = "Balamaha Maanta"
        elif choice == "6":
            GUIDED_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, deynjir_help_message())
            return {"status": "help_sent"}
        else:
            # A menu session must not swallow a real text command. For example,
            # "Ballamaha maanta" is option 5 expressed in words, not an invalid
            # numeric choice. Clear the menu state and let normal command parsing
            # handle the user's actual message.
            GUIDED_SESSIONS.pop(sender_phone, None)
            guided = None
            message_text = guided_text

    if guided and guided.get("stage") in {"debt_name", "payment_name"}:
        if is_missing_value(guided_text) or len(guided_text) < 2 or len(guided_text) > 100 or re.search(r"\d", guided_text):
            send_whatsapp(sender_phone, "Fadlan qor magaca qofka oo keliya. Tusaale: *Cali Xasan*.")
            return {"status": "guided_invalid_name"}
        guided["customer_name"] = guided_text.strip()
        guided["stage"] = "debt_amount" if guided.get("stage") == "debt_name" else "payment_amount"
        guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
        send_whatsapp(sender_phone, f"Immisa dollar?\n\nQofka: *{guided['customer_name']}*\nTusaale: *50* ama *$50*.")
        return {"status": "guided_amount_requested"}

    if (
        guided
        and guided.get("stage") == "payment_amount"
        and classify_transaction_direction(guided_text) == "ADD"
    ):
        # A complete new-debt message must not be treated as an answer to an
        # older customer's payment-amount question.
        GUIDED_SESSIONS.pop(sender_phone, None)
        guided = None
        message_text = guided_text
        print(
            "🔁 New ADD message received during a guided payment prompt; "
            "discarded the stale payment context and processing the full message."
        )

    if guided and guided.get("stage") in {"debt_amount", "payment_amount"}:
        # A user may correct a payment assumption in natural Somali instead of
        # entering a number. Handle this BEFORE the numeric-only amount parser.
        # No payment is ever recorded from a denial/correction message.
        if guided.get("stage") == "payment_amount":
            folded_reply = normalize_customer_name(guided_text)
            debt_taken_correction = bool(re.search(
                r"\b(?:deyn|dayn)(?:ta|tii)?\s+(?:ayay|ayuu|ay|bay|buu)?\s*"
                r"(?:qaadatay|qaatay|qaatey)\b|"
                r"\b(?:waxay|wuxuu|wuu|way)\s+(?:qaadatay|qaatay|qaatey)\s+"
                r"(?:deyn|dayn)\b|"
                r"\b(?:deyn|dayn)\s+(?:cusub\s+)?(?:ayay|ayuu|ay|bay|buu)\s+"
                r"(?:qaadatay|qaatay|qaatey)\b",
                folded_reply,
                flags=re.I,
            ))
            no_payment_reply = bool(re.search(
                r"\b(?:waxba|waxba\s+kama\s+helin|wax\s+lacag\s+ah\s+"
                r"kama\s+helin|lacag\s+ma\s+helin|wax\s+lacag\s+ah\s+"
                r"ma\s+helin|lacag\s+ma\s+bixin|ma\s+bixin|ma\s+helin|"
                r"lacag\s+ma\s+jirto|ma\s+jirto\s+lacag)\b",
                folded_reply,
                flags=re.I,
            ))
            if debt_taken_correction:
                # The user clarified that no payment was received and the
                # customer took debt instead. Switch the pending guided action
                # to ADD and ask for the actual amount; do not infer it.
                guided["transaction_type"] = "debt"
                guided["stage"] = "debt_amount"
                guided.pop("payment_declined", None)
                guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
                customer_label = str(guided.get("customer_name") or "macmiilku").strip()
                send_whatsapp(
                    sender_phone,
                    f"Waad mahadsan tahay caddeynta. Lacag-bixin lama diiwaangelin. "
                    f"{customer_label} deyn ayay qaadatay.\n\n"
                    "Immisa ayay qaadatay? Qor lacagta keliya, tusaale: *$50*. "
                    "Qor *JOOJI* haddii aadan rabin inaad diiwaangeliso deyn cusub."
                )
                return {"status": "guided_payment_corrected_to_debt"}
            if no_payment_reply:
                # Keep the short session alive because the user may be about to
                # explain that this was a new debt rather than a payment.
                guided["payment_declined"] = True
                guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
                send_whatsapp(
                    sender_phone,
                    "Hagaag, wax lacag ah lama helin. Lacag-bixin lama diiwaangelin.\n\n"
                    "Haddii macmiilku deyn cusub qaatay, ii sheeg taas iyo lacagta ay qaadatay. "
                    "Haddii kale qor *JOOJI*."
                )
                return {"status": "guided_payment_denied"}
        amount = _guided_amount(guided_text)
        if amount is None:
            send_whatsapp(
                sender_phone,
                "Fadlan qor lacag sax ah. Tusaale: *50* ama *$50*. "
                "Haddii lacag aan la helin, ii sheeg; waxba lama kaydin."
            )
            return {"status": "guided_invalid_amount"}
        guided["amount"] = amount
        # The user has already supplied the name, transaction type and amount.
        # Do not add an unnecessary final "Ma sax baa?" confirmation step.
        name = guided.get("customer_name")
        transaction_type = guided.get("transaction_type")
        if is_missing_value(name):
            guided["stage"] = "debt_name" if transaction_type == "debt" else "payment_name"
            guided.pop("customer_name", None)
            guided.pop("amount", None)
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
            prompt = "Magaca qofka daynta qaatay?" if transaction_type == "debt" else "Magaca qofka lacagta bixiyey?"
            send_whatsapp(sender_phone, prompt)
            return {"status": "guided_customer_name_required"}
        if transaction_type not in {"debt", "payment"}:
            GUIDED_SESSIONS.pop(sender_phone, None)
            activate_guided_menu(sender_phone)
            send_whatsapp(sender_phone, deynjir_unrecognized_message())
            return {"status": "guided_session_invalid"}
        GUIDED_SESSIONS.pop(sender_phone, None)
        saved_description = str(guided.get("description") or "").strip()
        description_part = f" {saved_description}" if saved_description and saved_description != "-" else ""
        message_text = (
            f"{name} ${amount}{description_part} ayuu iga qaatay"
            if transaction_type == "debt"
            else f"{name} ${amount}{description_part} ayuu bixiyay"
        )
        if transaction_type == "debt" and guided.get("existing_account_request"):
            message_text += " ku dar xisaabtii hore"
        print(f"✅ Guided transaction ready: type={transaction_type}, name={name!r}, amount={amount}")

    if guided and guided.get("stage") == "confirm":
        answer = guided_text.casefold().strip()
        if answer in {"1", "haa", "h", "yes", "ok", "sax"}:
            name = guided.get("customer_name")
            amount = guided.get("amount")
            transaction_type = guided.get("transaction_type")
            GUIDED_SESSIONS.pop(sender_phone, None)
            if not name or not amount or transaction_type not in {"debt", "payment"}:
                send_whatsapp(sender_phone, "Wadahadalkii wuu khaldamay. Fadlan mar kale ka bilow *MENU*.")
                return {"status": "guided_session_invalid"}
            # Use natural Somali transaction wording already supported by the
            # deterministic ADD/PAY classifier and local parser.
            message_text = (f"{name} ${amount} ayuu iga qaatay" if transaction_type == "debt"
                            else f"{name} ${amount} ayuu bixiyay")
            print(f"✅ Guided transaction confirmed: type={transaction_type}, name={name!r}, amount={amount}")
        elif answer in {"2", "maya", "no", "cancel", "jooji"}:
            GUIDED_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "Waa la joojiyey. Waxba lama kaydin. Qor *MENU* haddii aad caawimaad rabto.")
            return {"status": "guided_transaction_cancelled"}
        else:
            send_whatsapp(sender_phone, "Fadlan dooro *1* si aad u kaydiso ama *2* si aad u joojiso.")
            return {"status": "guided_confirmation_pending"}

    if guided and guided.get("stage") == "search_name":
        GUIDED_SESSIONS.pop(sender_phone, None)
        message_text = f"search {guided_text.strip()}"

    # Helpful handling for a bare typo/unknown command, rather than a technical error.
    if guided_text.casefold().strip() in {"guid", "inbort", "inport", "lacag bixn"}:
        GUIDED_SESSIONS[sender_phone] = {
            "stage": "menu",
            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
        }
        send_whatsapp(sender_phone, "Waxaan kuu fududayn karaa isticmaalka Deynjir.\n\n" + deynjir_main_menu())
        return {"status": "friendly_guidance_sent"}

    # Shop-wide payment history and date-range Excel/PDF exports.
    payment_text = str(message_text or "").strip()
    pending_payment_export = PAYMENT_EXPORT_SESSIONS.get(sender_phone)
    if pending_payment_export and pending_payment_export.get("business_user_id") == business_user_id:
        if re.fullmatch(r"\s*(?:cancel|jooji)\s*", payment_text, re.I):
            PAYMENT_EXPORT_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "✅ Warbixinta lacag-bixinta waa la joojiyey.")
            return {"status": "payment_export_cancelled"}
        if re.fullmatch(r"\s*(?:excel|xlsx)\s*", payment_text, re.I):
            fmt = "excel"
        elif re.fullmatch(r"\s*(?:pdf)\s*", payment_text, re.I):
            fmt = "pdf"
        else:
            fmt = None
        if fmt:
            try:
                start_date = pending_payment_export["start_date"]
                end_date = pending_payment_export["end_date"]
                records = _load_shop_payments(business_user_id, start_date, end_date)
                if not records:
                    export_status = "no_payments_for_period"
                    period_label = pending_payment_export.get("period_label") or (
                        start_date.strftime("%d/%m/%Y") if start_date == end_date
                        else f"{start_date:%d/%m/%Y} – {end_date:%d/%m/%Y}"
                    )
                    send_whatsapp(sender_phone, f"Ma jiraan wax lacag bixin ah ({period_label}).")
                else:
                    export_status = "payment_export_sent"
                    if fmt == "excel":
                        content = _build_payment_excel(records, start_date, end_date)
                        filename = f"deynjir_lacag_bixin_{start_date:%Y%m%d}_{end_date:%Y%m%d}.xlsx"
                        mime = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
                    else:
                        content = _build_payment_pdf(records, start_date, end_date, business_user.get("name"))
                        filename = f"deynjir_lacag_bixin_{start_date:%Y%m%d}_{end_date:%Y%m%d}.pdf"
                        mime = "application/pdf"
                    total = sum(r["amount"] for r in records)
                    send_whatsapp_file(sender_phone, filename, content, mime,
                        f"💵 Liiska lacag-bixinta: {start_date:%d/%m/%Y} – {end_date:%d/%m/%Y}\nWadarta: ${total:.2f}")
                PAYMENT_EXPORT_SESSIONS.pop(sender_phone, None)
                return {"status": export_status, "format": fmt}
            except Exception as exc:
                print(f"❌ Payment export failed: {type(exc).__name__}: {exc}")
                send_whatsapp(sender_phone, "❌ Warbixinta lama diyaarin. Hubi taariikhaha oo mar kale isku day.")
                PAYMENT_EXPORT_SESSIONS.pop(sender_phone, None)
                return {"status": "payment_export_error"}
        send_whatsapp(sender_phone, "Dooro *EXCEL* ama *PDF*. Qor *CANCEL* si aad u joojiso.")
        return {"status": "payment_export_waiting_format"}

    # Command: LIISKA LACAG BIXINTA [NOV | 03/11/2026 - 07/11/2026]
    payment_list_match = re.fullmatch(
        rf"\s*(?:liiska\s+)?lacag\s*bixinta(?:\s+({PAYMENT_REPORT_MONTH_PATTERN}|"
        rf"((?:{PAYMENT_REPORT_DATE_PATTERN}))(?:\s*(?:-|ilaa|to)\s*((?:{PAYMENT_REPORT_DATE_PATTERN})))?))?\s*",
        payment_text, re.I)
    if payment_list_match:
        try:
            month_token = payment_list_match.group(1)
            range_start = payment_list_match.group(2)
            range_end = payment_list_match.group(3)
            if month_token and not range_start:
                month_number = {
                    "jan": 1, "january": 1, "feb": 2, "february": 2,
                    "mar": 3, "march": 3, "apr": 4, "april": 4,
                    "may": 5, "jun": 6, "june": 6, "jul": 7,
                    "july": 7, "aug": 8, "august": 8, "sep": 9,
                    "sept": 9, "september": 9, "oct": 10, "october": 10,
                    "nov": 11, "november": 11, "dec": 12, "december": 12,
                }[month_token.lower()]
                report_year = today_eat().year
                start_date = datetime(report_year, month_number, 1).date()
                if month_number == 12:
                    end_date = datetime(report_year + 1, 1, 1).date() - timedelta(days=1)
                else:
                    end_date = datetime(report_year, month_number + 1, 1).date() - timedelta(days=1)
            elif range_start:
                start_date = _parse_payment_report_date(range_start)
                end_date = (
                    _parse_payment_report_date(range_end, start_date.year)
                    if range_end else start_date
                )
                if end_date < start_date:
                    raise ValueError("Taariikhda dhammaadka ayaa ka horreysa bilowga")
            else:
                start_date = end_date = None

            if start_date and end_date:
                # Check for matching payments BEFORE asking the user to choose
                # Excel/PDF. This avoids creating an export session for an
                # empty date/month/range.
                records = _load_shop_payments(business_user_id, start_date, end_date)
                if not records:
                    if month_token and not range_start:
                        period_label = f"{month_token.title()} {start_date.year}"
                    elif start_date == end_date:
                        period_label = start_date.strftime("%d/%m/%Y")
                    else:
                        period_label = f"{start_date:%d/%m/%Y} – {end_date:%d/%m/%Y}"
                    PAYMENT_EXPORT_SESSIONS.pop(sender_phone, None)
                    send_whatsapp(sender_phone, f"Ma jiraan wax lacag bixin ah ({period_label}).")
                    return {"status": "no_payments_for_period", "start_date": start_date.isoformat(), "end_date": end_date.isoformat()}

                if month_token and not range_start:
                    period_label = f"{month_token.title()} {start_date.year}"
                elif start_date == end_date:
                    period_label = start_date.strftime("%d/%m/%Y")
                else:
                    period_label = f"{start_date:%d/%m/%Y} – {end_date:%d/%m/%Y}"
                PAYMENT_EXPORT_SESSIONS[sender_phone] = {
                    "business_user_id": business_user_id,
                    "start_date": start_date,
                    "end_date": end_date,
                    "period_label": period_label,
                }
                send_whatsapp(sender_phone,
                    f"💵 *LIISKA LACAG BIXINTA*\n📅 {start_date:%d/%m/%Y} – {end_date:%d/%m/%Y}\n\n"
                    "Dooro nooca faylka: *EXCEL* ama *PDF*.\nQor *CANCEL* si aad u joojiso.")
                return {"status": "payment_export_format_requested"}

            records = _load_shop_payments(business_user_id)
            if not records:
                send_whatsapp(sender_phone, "✅ Weli ma jiraan lacag-bixinno la diiwaangeliyay.")
                return {"status": "no_shop_payments"}
            lines = ["💵 *LIISKA LACAG BIXINTA*", ""]
            for index, record in enumerate(records[-40:], 1):
                lines.append(f"{index}. {record['date_text']} — {record['name']} — ${record['amount']:.2f}")
            lines.extend(["", "━━━━━━━━━━━━", f"Wadarta: *${sum(r['amount'] for r in records):.2f}*", f"Tirada lacag-bixinnada: *{len(records)}*"])
            send_whatsapp(sender_phone, "\n".join(lines))
            return {"status": "shop_payment_list_sent", "count": len(records)}
        except Exception as exc:
            print(f"❌ Shop payment list error: {type(exc).__name__}: {exc}")
            send_whatsapp(sender_phone, "❌ Taariikhda lama fahmin. Tusaale: LIISKA LACAG BIXINTA NOV ama LIISKA LACAG BIXINTA 03/11/2026 - 07/11/2026")
            return {"status": "shop_payment_list_error"}

    # Explicit balance-edit wording takes priority over an unfinished name-rename
    # prompt. For example, "Muna ka dhig 25" must never become a new customer name.
    local_amount_edit_entry = parse_somali_amount_edit(message_text)
    if local_amount_edit_entry:
        RENAME_SESSIONS.pop(sender_phone, None)
        print(f"✏️ Local Somali balance edit parsed: {local_amount_edit_entry['customer_name']!r} -> {local_amount_edit_entry['new_amount']}")

    # Two-step SAX flow. Explicit "SAX old -> new" continues through the
    # existing immediate-rename path; "SAX old" asks for the corrected name.
    rename_state = None if local_amount_edit_entry else RENAME_SESSIONS.get(sender_phone)
    if rename_state and rename_state.get("business_user_id") == business_user_id:
        if datetime.now(timezone.utc) > rename_state.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
            RENAME_SESSIONS.pop(sender_phone, None)
            rename_state = None
        elif re.fullmatch(r"\s*(?:cancel|jooji)\s*", str(message_text or ""), re.I):
            RENAME_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "✅ Saxidda magaca waa la joojiyey.")
            return {"status": "rename_cancelled"}
        elif rename_state.get("stage") == "new_name":
            proposed = str(message_text or "").strip()
            if len(proposed) < 2 or len(proposed) > 120:
                send_whatsapp(sender_phone, "Magaca cusub si sax ah u qor, ama CANCEL.")
                return {"status": "rename_new_name_invalid"}
            rename_state["new_name"] = proposed
            rename_state["stage"] = "confirm"
            rename_state["expires_at"] = datetime.now(timezone.utc) + timedelta(minutes=10)
            send_whatsapp(sender_phone, f"Hubi magaca cusub:\n\nMagac Hore: *{rename_state['old_name']}*\nMagaca Cusub: *{proposed}*\n\nQor *OK* si loo beddelo ama *CANCEL* si loo joojiyo.")
            return {"status": "rename_confirmation_required"}
        elif rename_state.get("stage") == "confirm":
            if re.fullmatch(r"\s*OK\s*", str(message_text or ""), re.I):
                old_name = rename_state["old_name"]
                new_name = rename_state["new_name"]
                try:
                    collision = (supabase.table("customers").select("id, name")
                        .eq("business_user_id", business_user_id).eq("is_archived", False).eq("name", new_name).limit(1).execute())
                    if collision.data and normalize_customer_name(collision.data[0].get("name")) != normalize_customer_name(old_name):
                        send_whatsapp(sender_phone, f"⚠️ Magaca *{new_name}* hore ayuu dukaanka uga jiraa. Magaca lama beddelin.")
                        RENAME_SESSIONS.pop(sender_phone, None)
                        return {"status": "rename_name_collision"}
                    updated = (supabase.table("customers").update({"name": new_name})
                        .eq("business_user_id", business_user_id).eq("is_archived", False).eq("name", old_name).select("id").execute())
                    RENAME_SESSIONS.pop(sender_phone, None)
                    if not updated.data:
                        send_whatsapp(sender_phone, "❌ Magaca lama helin ama lama beddelin.")
                        return {"status": "rename_no_rows"}
                    send_whatsapp(sender_phone, f"✅ Magaca waa la saxay: *{old_name}* → *{new_name}*\nDiiwaannada la cusboonaysiiyay: {len(updated.data)}")
                    return {"status": "rename_confirmed", "updated": len(updated.data)}
                except Exception as exc:
                    print(f"❌ Two-step rename failed: {exc}")
                    send_whatsapp(sender_phone, "❌ Magaca lama beddelin. Mar kale isku day.")
                    return {"status": "rename_error"}
            send_whatsapp(sender_phone, "Qor *OK* si loo beddelo ama *CANCEL* si loo joojiyo.")
            return {"status": "rename_waiting_confirmation"}

    sax_old_name = parse_sax_name_only(message_text)
    if sax_old_name:
        try:
            sax_matches = find_debtor_matches(business_user_id, sax_old_name)
            if not sax_matches:
                send_whatsapp(sender_phone, f"❌ Ma hayo *{sax_old_name}*. Hubi magaca.")
                return {"status": "rename_customer_not_found"}
            distinct = {str(row.get("name") or "").strip() for row in sax_matches}
            if len(distinct) != 1:
                send_whatsapp(sender_phone, "Magaca si cad looma kala saari karin. Fadlan qor magaca oo buuxa.")
                return {"status": "rename_name_ambiguous"}
            old_stored_name = next(iter(distinct))
            RENAME_SESSIONS[sender_phone] = {
                "business_user_id": business_user_id,
                "old_name": old_stored_name,
                "stage": "new_name",
                "expires_at": datetime.now(timezone.utc) + timedelta(minutes=10),
            }
            send_whatsapp(sender_phone, f"Magaca cusub ee *{old_stored_name}* waa maxay?\nQor magaca cusub ama *CANCEL*.")
            return {"status": "rename_new_name_requested"}
        except Exception as exc:
            print(f"❌ SAX lookup failed: {exc}")
            send_whatsapp(sender_phone, "❌ Magaca lama hubin karin. Mar kale isku day.")
            return {"status": "rename_lookup_error"}

    # Resolve a pending customer identity before parsing another message. The
    # saved transaction is replayed only after a clear selection; no money is
    # changed while this session is waiting.
    customer_match_resume_entry = None
    customer_match_resume_remaining = []
    customer_match_resume_forced_action = None
    customer_match_state = CUSTOMER_MATCH_SESSIONS.get(sender_phone)
    if customer_match_state:
        if customer_match_state.get("business_user_id") != str(business_user_id):
            CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
            customer_match_state = None
        elif datetime.now(timezone.utc) > customer_match_state.get(
            "expires_at", datetime.min.replace(tzinfo=timezone.utc)
        ):
            CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "⌛ Xulashadii macmiilka way dhacday. Waxba lama diiwaangelin. Fadlan macaamilka mar kale dir.")
            return {"status": "customer_match_session_expired"}

    if customer_match_state:
        answer = str(message_text or "").strip()
        answer_folded = normalize_customer_name(answer)
        if re.fullmatch(r"(?:jooji|cancel|baaji|stop)", answer, re.I):
            CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "Waa la joojiyey. Waxba lama diiwaangelin.")
            return {"status": "customer_match_cancelled"}

        stage = customer_match_state.get("stage")
        candidate_names = customer_match_state.get("candidate_names") or []
        entry = dict(customer_match_state.get("entry") or {})
        selected_name = None
        force_new = False

        if stage == "choose":
            if answer_folded == "cusub" and customer_match_state.get("allow_new"):
                force_new = True
            elif answer_folded == "cusub":
                send_whatsapp(sender_phone, "Codsigan wuxuu u baahan yahay macmiil hore u jiray. Fadlan dooro lambarka ama qor magaca buuxa.")
                return {"status": "customer_match_new_not_allowed"}
            elif re.fullmatch(r"\d+", answer):
                selected_index = int(answer)
                if 1 <= selected_index <= min(len(candidate_names), 10):
                    selected_name = candidate_names[selected_index - 1]
                else:
                    send_whatsapp(sender_phone, "Lambarkaasi sax ma aha. Fadlan dooro mid ka mid ah lambarrada liiska.")
                    return {"status": "customer_match_invalid_choice"}
            elif answer_folded:
                # A full name typed instead of a number is treated as a fresh
                # lookup, not as permission to create a customer.
                entry["customer_name"] = answer
                entry["_existing_account_lookup_attempted"] = bool(
                    is_existing_account_add_request(customer_match_state.get("original_message"))
                )
                entry["_customer_match_confirmed"] = False
                selected_name = answer
            else:
                send_whatsapp(sender_phone, "Fadlan dooro lambarka macmiilka, ama qor magaca oo buuxa.")
                return {"status": "customer_match_choice_pending"}
        elif stage == "confirm_single":
            if answer_folded in {"haa", "h", "yes", "y", "ok", "sax", "1"}:
                selected_name = candidate_names[0] if candidate_names else entry.get("customer_name")
            elif answer_folded == "cusub" and customer_match_state.get("allow_new"):
                force_new = True
            elif answer_folded in {"maya", "no", "n", "2"}:
                customer_match_state["stage"] = "enter_full_name"
                customer_match_state["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
                send_whatsapp(sender_phone, "Hagaag. Fadlan qor magaca buuxa ee macmiilka aad ula jeeddo.\nQor *CUSUB* haddii aad rabto macmiil cusub, ama *JOOJI*.")
                return {"status": "customer_match_full_name_requested"}
            else:
                send_whatsapp(sender_phone, "Fadlan ku jawaab *HAA* ama *MAYA*.")
                return {"status": "customer_match_confirmation_pending"}
        elif stage == "enter_full_name":
            if answer_folded == "cusub" and customer_match_state.get("allow_new"):
                force_new = True
            elif answer_folded == "cusub":
                send_whatsapp(sender_phone, "Halkan waxaa loo baahan yahay magaca macmiilka jira. Fadlan qor magaca buuxa ama *JOOJI*.")
                return {"status": "customer_match_new_not_allowed"}
            elif len(answer) >= 2 and len(answer) <= 120 and not re.fullmatch(r"\d+", answer):
                selected_name = answer
                entry["_existing_account_lookup_attempted"] = bool(
                    is_existing_account_add_request(customer_match_state.get("original_message"))
                )
                entry["_customer_match_confirmed"] = False
            else:
                send_whatsapp(sender_phone, "Fadlan qor magaca buuxa, ama *JOOJI*.")
                return {"status": "customer_match_full_name_invalid"}

        if force_new:
            entry["_force_new_customer"] = True
            entry["_customer_match_confirmed"] = True
            if entry.get("amount") is not None:
                entry["_source_amount_verified"] = True
        elif selected_name:
            entry["customer_name"] = selected_name
            entry["_customer_match_confirmed"] = True
            if entry.get("amount") is not None:
                # The original transaction passed source-amount validation before
                # this identity prompt; retain that validation after the name changes.
                entry["_source_amount_verified"] = True

        CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
        customer_match_resume_entry = entry
        customer_match_resume_remaining = customer_match_state.get("remaining_entries") or []
        customer_match_resume_forced_action = str(entry.get("action") or "").upper()
        message_text = customer_match_state.get("original_message") or message_text
        print(
            f"✅ Customer match resolved: action={customer_match_resume_forced_action}, "
            f"name={entry.get('customer_name')!r}, new_customer={force_new}"
        )

    # A pending transaction clarification is persisted in Supabase so it survives
    # Render restarts. The original message is replayed only after a clear answer.
    pending_clarification = None
    forced_transaction_action = None
    pending_new_transaction_entries = None
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
                supabase.table("pending_transaction_clarifications").delete().eq("sender_phone", sender_phone).eq("business_user_id", business_user_id).execute()
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

                # Keep optional product/detail information from the clarification
                # reply, while preserving the saved customer and amount.
                if clarification_action == "ADD":
                    detail_match = re.search(
                        r"\boo\s+(.+?)\s*$",
                        normalize_customer_name(str(message_text or "")),
                        re.I,
                    )
                    if detail_match:
                        clarification_detail = detail_match.group(1).strip(" .,:;-")
                        for saved_entry in entries:
                            if isinstance(saved_entry, dict) and saved_entry.get("action") in {"ADD", "PAY"}:
                                saved_entry["description"] = clarification_detail[:160]
                                break

                message_text = pending_clarification.get("original_message") or message_text
                supabase.table("pending_transaction_clarifications").delete().eq("sender_phone", sender_phone).eq("business_user_id", business_user_id).execute()
                print(f"✅ Clarification received; replaying saved message as {forced_transaction_action}")
            except Exception as pending_err:
                print(f"❌ Pending clarification restore failed: {pending_err}")
                send_whatsapp(sender_phone, "❌ Fariintii hore dib looma soo celin karo. Fadlan mar kale dir.")
                return {"status": "pending_clarification_restore_error"}
        else:
            # A new, fully specified transaction supersedes the stale pending
            # clarification. Never replay the previous customer's transaction.
            fresh_entries = local_fallback_parse(message_text)
            fresh_financial_entries = [
                item for item in (fresh_entries or [])
                if isinstance(item, dict)
                and str(item.get("action") or "").upper() in {"ADD", "PAY"}
                and item.get("customer_name")
                and item.get("amount") is not None
            ]
            if fresh_financial_entries and classify_transaction_direction(message_text) in {"ADD", "PAY"}:
                try:
                    supabase.table("pending_transaction_clarifications").delete().eq("sender_phone", sender_phone).eq("business_user_id", business_user_id).execute()
                except Exception as pending_err:
                    print(f"❌ Could not replace old pending clarification: {pending_err}")
                    send_whatsapp(sender_phone, "❌ Fariintii hore lama nadiifin. Waxba lama beddelin; fadlan mar kale dir fariinta.")
                    return {"status": "pending_clarification_replace_error"}
                pending_new_transaction_entries = fresh_financial_entries
                pending_clarification = None
                print(f"🔄 New explicit transaction superseded stale clarification: {fresh_financial_entries!r}")
            else:
                send_whatsapp(sender_phone, "Deyn cusub baa mise lacag-bixin?\n\nSoo qor *DEYN CUSUB* ama *LACAG BIXIN*. Qor *JOOJI* haddii aad rabto inaad ka baxdo.")
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
                .eq("is_archived", False)
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
                        .eq("is_archived", False)
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
                                # Persistent reminder history distinguishes first from repeat reminders.
                                # Requires the customer_reminder_history table documented in the deployment notes.
                                reminder_count = 0
                                try:
                                    history_result = (supabase.table("customer_reminder_history")
                                        .select("id", count="exact")
                                        .eq("business_user_id", business_user_id)
                                        .eq("customer_key", normalize_customer_name(fresh.get("name")))
                                        .execute())
                                    reminder_count = int(getattr(history_result, "count", 0) or len(history_result.data or []))
                                except Exception as history_err:
                                    print(f"❌ Reminder history lookup failed for customer {fresh.get('id')}: {history_err}")
                                    raise RuntimeError("customer_reminder_history table is missing or unavailable")

                                send_ok = send_whatsapp(
                                    target_phone,
                                    build_debt_reminder(
                                        fresh,
                                        business_user.get("name"),
                                        business_user.get("phone_number") or sender_phone,
                                        is_repeat=(reminder_count >= 1),
                                    ),
                                )

                                if send_ok is False:
                                    failed_count += 1
                                    status_message = "Xusuusintan lama dirin."
                                else:
                                    supabase.table("customer_reminder_history").insert({
                                        "business_user_id": business_user_id,
                                        "customer_key": normalize_customer_name(fresh.get("name")),
                                    }).execute()
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

    # A standalone FAAHFAAHIN command refers to the most recently added,
    # searched, or opened customer for this sender and shop. It must not ask
    # for a name again when that context is already known.
    standalone_detail_request = bool(re.fullmatch(
        r"\s*(?:faahfaahin(?:ta)?|description|history|taariikh|statement|xisaab(?:ta)?)\s*[.!?]*\s*",
        str(message_text or ""),
        flags=re.IGNORECASE,
    ))
    standalone_detail_customer = None
    if standalone_detail_request:
        recent_customer = LAST_SELECTED_CUSTOMERS.get(sender_phone) or LAST_HISTORY_REQUESTS.get(sender_phone)
        if recent_customer and recent_customer.get("business_user_id") == business_user_id:
            standalone_detail_customer = recent_customer.get("customer_name")
        if standalone_detail_customer:
            print(f"📒 Standalone FAAHFAAHIN using last selected customer: {standalone_detail_customer!r}")
        else:
            send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca ii sheeg. Tusaale: *FAAHFAAHIN Sakariye*.")
            return {"status": "history_customer_name_required"}

    # If the user confirms a deletion but the delete session has expired or is
    # missing, do not let Gemini/local parsing treat "Haa tirtir" as a customer
    # name. Ask the user to start a new delete request instead.
    if (
        re.fullmatch(
            r"\s*(?:haa\s*,?\s*tirtir|tirtir|confirm\s+delete|yes\s+delete)\s*[.!]?\s*",
            str(message_text or ""),
            flags=re.IGNORECASE,
        )
        and not DELETE_SESSIONS.get(sender_phone)
    ):
        send_whatsapp(
            sender_phone,
            "Ma hayo macmiilka aad doonayso in la tirtiro.\n\n"
            "Qor *DELETE [magaca macmiilka]* si aad u bilowdo tirtirid cusub."
        )
        return {"status": "orphan_delete_confirmation_ignored"}

    # Explicit customer rename is parsed locally; it must not depend on Gemini.
    rename_request = parse_customer_rename_command(message_text)
    phone_update_entries = parse_customer_phone_update(message_text)

    # Fast read-only command matching: avoid a Gemini request for debt lists.
    fuzzy_list_requested = is_fuzzy_debt_list_command(message_text)
    multiline_transaction = parse_multiline_menu_transaction(message_text)

    today_str = today_eat().isoformat()
    dynamic_system_prompt = (
        f"{SYSTEM_PROMPT}\nToday's date is strictly: {today_str}. "
        "Use this to calculate calendar targets or relative days offsets like 'berri'.\n\n"
        "NATURAL SOMALI UNDERSTANDING: Interpret the user's intended meaning, not just exact keywords. "
        "Understand messy everyday Somali writing, informal and regional wording, phonetic spelling, "
        "missing or extra letters, repeated letters, joined or separated words, omitted subjects, pronouns, "
        "word-order changes, missing punctuation, and mixed Somali/English. Do not require exact command phrases. "
        "Use the surrounding sentence to identify whether the user means a new debt, a payment, a date change, "
        "a search, or another supported action. If meaning is genuinely unclear, ask one short clarification; "
        "never guess transaction direction or invent amounts. "
        "Examples: 'Aamina waxay bixisay 20', 'Aamina 20 ayay bixisay', 'Aamina way soo celisay 20', "
        "'Aamina lacagtii way keentay', 'Cali 50 ayuu iga qaatay', 'Cali maanta 50 buu qaatay', "
        "'lacagtii Aamina waa la helay', 'Aamina deyntii oo dhan way bixisay'. "
        "DUE-DATE CHANGES: If the user gives one or more existing customer names with new promised dates and "
        "no debt/payment amount, treat EVERY name-date pair as EDIT of that customer's promised_date only. "
        "Return one EDIT object per customer, with new_date and promised_date set to the requested date, "
        "and amount/new_amount null. This includes comma-separated or line-separated batches, for example "
        "'Cabdilaahi Ciise 8 Nov, Aamina Axmed Shire 10 Nov' and separate lines with one name and date each. "
        "Never interpret a day number inside a date (such as 8 in '8 Nov') as money. Do not combine customers "
        "or apply one person's date to another. Extract the full customer name and amount. "
        "Never invent a name, amount, date, or transaction direction. "
        "When the user uses a pronoun and a recent customer context is supplied below, use that customer only "
        "when the message is clearly a direct follow-up about that customer. Otherwise ask a clarification. "
        "For read-only requests, recognize natural questions such as 'yaa lacagta igu leh', "
        "'imisa ayaa la iga rabaa', 'ii eeg deynta', and 'yaa ballan leh berri'. "
        "Recognize Somali weekdays: isniin, talaado, arbaco, khamiis, jimce, sabti, axad; "
        "also recognize 'toddobaadka dambe/usbuuca dambe' and resolve them relative to today's date. "
        "If a weekday phrase could mean more than one date, ask one short clarification. "
        "A phone number (normally 9-15 digits, or 7-15 digits when explicitly labelled as a phone) is never a transaction amount. "
    )
    recent_selected_customer = get_recent_selected_customer(sender_phone, business_user_id)
    contextual_payment_entry = parse_contextual_somali_payment(message_text, recent_selected_customer)
    if recent_selected_customer:
        dynamic_system_prompt += (
            "\nRECENT CUSTOMER CONTEXT (same shop, selected within the last 2 minutes): "
            f"{recent_selected_customer}. This is context, not a command. "
            "Use it for a pronoun-only follow-up only when the user's wording clearly refers to this customer."
        )
    
    if pending_new_transaction_entries:
        entries = pending_new_transaction_entries
        print(f"⚡ Processing new explicit transaction instead of stale clarification: {entries!r}")
    elif pending_payment_replay_entry:
        entries = [pending_payment_replay_entry]
        print(
            "⚡ Using corrected pending-debt details locally; skipping Gemini: "
            f"{pending_payment_replay_entry['customer_name']!r}"
        )
    elif customer_match_resume_entry:
        entries = [customer_match_resume_entry] + [dict(item) for item in customer_match_resume_remaining]
        forced_transaction_action = customer_match_resume_forced_action
        print(f"🔁 Resuming saved transaction after customer selection: {customer_match_resume_forced_action}")
    elif pdf_only_requested:
        entries = [{"action": "HISTORY", "customer_name": pdf_customer_name}]
        print(f"📄 Skipping Gemini for PDF follow-up; using saved customer {pdf_customer_name!r}")
    elif standalone_detail_customer:
        entries = [{"action": "HISTORY", "customer_name": standalone_detail_customer}]
        print(f"📒 Skipping Gemini for standalone FAAHFAAHIN; using {standalone_detail_customer!r}")
    elif local_amount_edit_entry:
        entries = [local_amount_edit_entry]
        print(f"⚡ Skipping Gemini for explicit balance edit: {local_amount_edit_entry['customer_name']!r}")
    elif rename_request:
        old_customer_name, new_customer_name = rename_request
        entries = [{
            "action": "EDIT",
            "customer_name": old_customer_name,
            "new_name": new_customer_name,
            "amount": None,
            "new_amount": None,
            "promised_date": None,
            "new_date": None,
        }]
        print(f"✏️ Explicit customer rename detected: {old_customer_name!r} -> {new_customer_name!r}")
    elif phone_update_entries:
        entries = phone_update_entries
        print(f"📱 Customer phone-only update parsed locally: {entries[0]['customer_name']!r}; skipping Gemini")
    elif forced_transaction_action:
        print(f"🔁 Using saved entries with confirmed action {forced_transaction_action}")
    elif contextual_payment_entry:
        entries = [contextual_payment_entry]
        print(
            "🧠 Contextual Somali payment follow-up resolved to recently selected customer: "
            f"{contextual_payment_entry['customer_name']!r}"
        )
    elif (direct_somali_entries := local_fallback_parse(message_text)) and any(
        isinstance(item, dict)
        and str(item.get("action") or "").upper() in {"ADD", "PAY"}
        and item.get("customer_name")
        and item.get("amount") is not None
        for item in direct_somali_entries
    ) and classify_transaction_direction(message_text) in {"ADD", "PAY"}:
        entries = direct_somali_entries
        print(f"⚡ Explicit Somali transaction parsed locally before Gemini: {entries!r}")
    elif (structured_entries := parse_structured_somali_transaction(message_text)):
        entries = structured_entries
        print(f"⚡ Structured Somali transaction parsed locally: {entries}")
    elif fuzzy_list_requested:
        entries = [{
            "action": "LIST",
            "customer_name": None,
            "amount": None,
            "filter_date": None,
            "filter_type": None,
        }]
        print(f"⚡ Fuzzy debt-list command recognized locally: {message_text!r}; skipping Gemini")
    elif multiline_transaction:
        entries = multiline_transaction
        print(
            f"⚡ Multi-line menu transaction recognized locally: {message_text!r}; "
            "skipping Gemini"
        )
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
                GUIDED_SESSIONS[sender_phone] = {
                    "stage": "menu",
                    "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                }
                if is_rate_limited:
                    send_whatsapp(
                        sender_phone,
                        "⏳ Adeegga fahamka fariinta hadda waa mashquul. Waxba lama beddelin.\n\n"
                        "Waxaad dooran kartaa mid ka mid ah hawlahan: \n" + deynjir_main_menu()
                    )
                    return {"status": "gemini_rate_limited_guidance_sent"}
                activate_guided_menu(sender_phone)
                send_whatsapp(sender_phone, deynjir_unrecognized_message())
                return {"status": "friendly_fallback_sent"}

    # Normalize action labels once, including saved clarification entries, so
    # downstream routing never depends on Gemini's capitalization.
    if isinstance(entries, list):
        for parsed_item in entries:
            if isinstance(parsed_item, dict) and parsed_item.get("action") is not None:
                parsed_item["action"] = str(parsed_item["action"]).upper()

    # Reject invalid/empty AI intents before they can reach database handlers.
    # Gemini sometimes labels meaningless text as SEARCH with customer_name=null.
    valid_actions = {"ADD", "PAY", "LIST", "SEARCH", "EDIT", "DELETE", "HISTORY", "REPORT", "EXPORT"}
    if not pdf_only_requested and not rename_request and not forced_transaction_action:
        usable_entries = [
            item for item in entries
            if isinstance(item, dict) and str(item.get("action") or "").upper() in valid_actions
        ]
        if not usable_entries:
            print(f"⚠️ No usable intent extracted; message={message_text!r}; entries={entries!r}")
            activate_guided_menu(sender_phone)
            send_whatsapp(sender_phone, deynjir_unrecognized_message())
            return {"status": "unrecognized_message"}
        entries = usable_entries
        for parsed_item in entries:
            parsed_item["action"] = str(parsed_item.get("action") or "").upper()

        # Do not let Gemini turn unrelated text such as "none" into a debt list.
        # Keep short, established list commands such as "deyn" working.
        if any(item.get("action") == "LIST" for item in entries) and not is_explicit_list_request(message_text):
            print(f"⚠️ Rejected LIST intent without an explicit list command: {message_text!r}")
            activate_guided_menu(sender_phone)
            send_whatsapp(sender_phone, deynjir_unrecognized_message())
            return {"status": "unrecognized_message"}

        # Treat literal null-like names exactly like missing names.
        for parsed_item in entries:
            if "customer_name" in parsed_item and is_missing_value(parsed_item.get("customer_name")):
                parsed_item["customer_name"] = None

        # A SEARCH action without a name is not a search. Ask for the name only
        # when the user actually issued a search command; otherwise treat the
        # model's empty SEARCH classification as an unrecognized message.
        for item in entries:
            action = str(item.get("action") or "").upper()
            if action == "SEARCH" and is_missing_value(item.get("customer_name")):
                explicit_search = bool(re.match(
                    r"^\s*(?:search|find|lookup|look\s+up|raadi|raadso)\b",
                    str(message_text or ""), flags=re.IGNORECASE
                ))
                if explicit_search:
                    send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca ii sheeg.")
                    return {"status": "search_name_required"}
                print(
                    f"⚠️ Rejected empty SEARCH intent for unrecognized text: "
                    f"{message_text!r}"
                )
                activate_guided_menu(sender_phone)
                send_whatsapp(sender_phone, deynjir_unrecognized_message())
                return {"status": "unrecognized_message"}

    # If the user answered the pending question, apply that answer to every
    # entry extracted from the saved original message. Otherwise require an
    # explicit direction before any ADD/PAY financial operation.
    if forced_transaction_action:
        for parsed_entry in entries:
            if parsed_entry.get("action") in {"ADD", "PAY"}:
                parsed_entry["action"] = forced_transaction_action
    elif not pdf_only_requested:
        # In this multiline menu format, option 1 explicitly means a new
        # debt. Do not ask the ADD/PAY clarification a second time.
        explicit_direction = (
            "ADD" if multiline_transaction else
            classify_transaction_direction(message_text)
        )
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
                "*Hadii aad ula jeedo*\n\n"
                "*DEYN CUSUB* - Taabo 1\n\n"
                "*LACAG BIXIN* - Taabo 2.\n\n"
                "Soo qor *JOOJI* haddii aad rabto inaad ka baxdo.\n\n"
                "Waxba lama diiwaangelinayo ilaa aad kala caddeyso."
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
        "history", "taariikh", "statement", "xisaab", "faahfaahin", "faahfaahinta", "description"
    ))
    detail_prefix = re.match(
        r"^\s*(?:faahfaahin(?:ta)?|description|history|taariikh|statement|xisaab(?:ta)?)\b\s*[:,-]?\s*(.+?)\s*$",
        original_text,
        flags=re.IGNORECASE,
    )
    if detail_prefix:
        explicit_history_name = detail_prefix.group(1).strip()
        if explicit_history_name:
            print(f"📒 Explicit transaction-detail request detected: {explicit_history_name!r}")
            entries = [{"action": "HISTORY", "customer_name": explicit_history_name}]

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
    
    for entry_index, entry in enumerate(entries):
        action = str(entry.get("action", "ADD") or "ADD").upper()
        name = entry.get("customer_name")
        amount = entry.get("amount")
        promised_date = entry.get("promised_date")
        days_until_due = entry.get("days_until_due")
        customer_phone = entry.get("customer_phone")
        new_amount = entry.get("new_amount")
        new_date = entry.get("new_date")
        # Structured transaction phone numbers belong to the new debt row too.
        new_phone = entry.get("new_phone") or customer_phone
        description = str(entry.get("description") or "").strip() or None
        transaction_date = entry.get("transaction_date")
        payment_type = str(entry.get("payment_type") or "UNKNOWN").upper()
        filter_date = entry.get("filter_date")
        filter_type = entry.get("filter_type")

        date_only_update = False
        # If a message has a customer name + due date but NO amount, treat it as
        # a request to update that customer's existing debt date, not create a
        # second debt with amount 0. Example: existing debt is $4 with no due
        # date; "C/SAMAD SANDHEERE oct 10" should update its date to Oct 10.
        source_has_amount = bool(entry.get("_source_amount_verified")) or (message_has_explicit_amount_for_name(message_text, name) if name else False)
        if action == "ADD" and amount is not None and not source_has_amount:
            # The model may hallucinate/copy a balance not present in the user's
            # message. Never apply that amount as a financial transaction.
            print(f"⚠️ Ignoring AI amount not present in source message for {name!r}: {amount!r}")
            amount = None
            entry["amount"] = None
        # If the user gave a due date but no amount in their own message, treat
        # this as a date-only edit even if the AI hallucinated/copied an amount.
        # Gemini sometimes labels a bare "Customer 8 nov" as transaction_date;
        # for a name + date with no source amount, recover that date as promised_date.
        if (
            action == "ADD"
            and not source_has_amount
            and promised_date is None
            and transaction_date
            and re.search(
                r"\b(?:jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|"
                r"jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|"
                r"oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)\b|"
                r"\b\d{1,2}[/-]\d{1,2}(?:[/-]\d{2,4})?\b",
                str(message_text or ""),
                re.I,
            )
        ):
            promised_date = transaction_date
            entry["promised_date"] = promised_date
            print(f"🗓️ Recovered date-only request as promised_date for {name!r}: {promised_date}")

        # Models may return EDIT directly for a date-only request. Mark it as a
        # date-only update too, so the safe unique-debt selection rules apply.
        if (
            action == "EDIT"
            and not source_has_amount
            and amount is None
            and new_amount is None
            and (new_date is not None or promised_date is not None)
        ):
            date_only_update = True
            new_date = new_date or promised_date
            amount = None
            new_amount = None
            entry["amount"] = None
            entry["new_amount"] = None
            entry["new_date"] = new_date
            print(f"🗓️ Date-only EDIT recognized for {name!r}: {new_date} (balance preserved)")

        date_intent_without_amount = (
            (promised_date is not None or new_date is not None or days_until_due is not None)
            and not source_has_amount
        )
        # Reject missing/null-like customer names before any amount prompt or write.
        if action not in {"LIST", "REPORT", "EXPORT"} and is_missing_value(name):
            print(f"⚠️ Missing/invalid customer name; action={action!r}; value={name!r}; message={message_text!r}")
            send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca macmiilka ii sheeg.")
            continue
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
                # Preserve this customer's transaction while asking for its amount.
                GUIDED_SESSIONS[sender_phone] = {
                    "stage": "debt_amount" if action == "ADD" else "payment_amount",
                    "transaction_type": "debt" if action == "ADD" else "payment",
                    "customer_name": str(name).strip(),
                    "description": description or "-",
                    "existing_account_request": is_existing_account_add_request(message_text) if action == "ADD" else False,
                    "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                }
                send_whatsapp(
                    sender_phone,
                    f"{name}, lacag intee le'eg ayuu qaatay ama bixiyay?\n\n"
                    "Qor lacagta keliya, tusaale: *$4*. Waxba lama diiwaangelin weli. "
                    "Qor *JOOJI* haddii aad rabto inaad ka baxdo."
                )
                print(f"⚠️ Amount missing; saved pending transaction context: action={action}, customer={name!r}; message={message_text!r}")
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
        
        if is_missing_value(name) and action not in ["LIST", "REPORT", "EXPORT"]:
            print(f"⚠️ Transaction skipped because customer name is missing: action={action!r}; message={message_text!r}")
            if action in {"ADD", "PAY"}:
                clear_direction = classify_transaction_direction(message_text)
                explicit_transaction_command = bool(re.match(
                    r"^\s*(?:add|lacag\s*bixin|pay|deyn\s+c cusub|deyn\s+cusub|dayn\s+cusub)\b",
                    str(message_text or ""), flags=re.I
                ))
                if clear_direction is None and not explicit_transaction_command:
                    activate_guided_menu(sender_phone)
                    send_whatsapp(sender_phone, deynjir_unrecognized_message())
                    return {"status": "unrecognized_message"}
            send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca macmiilka ii sheeg.")
            continue
        
        if action == "ADD":
            try:
                if amount is not None:
                    amount = float(amount)
                    if not math.isfinite(amount) or amount <= 0:
                        send_whatsapp(sender_phone, "❌ Lacagta deynta waa inay noqotaa tiro sax ah oo ka weyn $0.")
                        failed_inserts.append({"name": name, "reason": "ADD amount must be finite and positive"})
                        continue
                if amount is None and (not new_phone or entry.get("_structured_somali_transaction")):
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "debt_amount",
                        "transaction_type": "debt",
                        "customer_name": str(name).strip(),
                        "description": description or "-",
                        "existing_account_request": is_existing_account_add_request(message_text),
                        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                    }
                    send_whatsapp(
                        sender_phone,
                        f"{name}, lacag intee le'eg ayuu qaatay?\n\n"
                        "Qor lacagta keliya, tusaale: *$4*. Waxba lama diiwaangelin weli. "
                        "Qor *JOOJI* haddii aad rabto inaad ka baxdo."
                    )
                    print(f"⚠️ Amount missing for ADD; saved pending transaction context: customer={name!r}; message={message_text!r}")
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
                                   .eq("business_user_id", business_user_id).eq("is_archived", False).eq("name", matched_name).execute())
                        if updated.data:
                            send_whatsapp(sender_phone, f"✅ Lambarka *{matched_name}* waa la kaydiyey.\n📱 {new_phone}")
                            successful_inserts.append(entry)
                        else:
                            send_whatsapp(sender_phone, f"❌ Lambarka *{matched_name}* lama kaydin. Fadlan mar kale isku day.")
                            failed_inserts.append({"name": name, "reason": "Phone update returned no rows"})
                        continue
                    else:
                        send_whatsapp(sender_phone, f"❌ Ma helin {name} si lambarkiisa aan u kaydiyo.")
                        failed_inserts.append({"name": name, "reason": "Debtor not found for phone update"})
                        continue
                
                # Amounts without an explicit EDIT / "ka dhig" are additive.
                # If this customer already has exactly one active debt, update
                # that row instead of creating a duplicate debtor/debt record.
                # If the name is ambiguous or multiple active rows exist, ask
                # the user rather than changing the wrong balance.
                if amount is not None:
                    force_new_customer = bool(entry.get("_force_new_customer"))
                    matches = [] if force_new_customer else find_debtor_matches(business_user_id, name)
                    distinct_names = _unique_customer_names(matches)
                    existing_account_request = is_existing_account_add_request(message_text)

                    if len(distinct_names) > 1 and not entry.get("_customer_match_confirmed"):
                        start_customer_match_session(
                            sender_phone, business_user_id, entry, message_text, matches,
                            "choose", entries[entry_index + 1:],
                            allow_new=not existing_account_request
                        )
                        break

                    if len(distinct_names) == 1 and not entry.get("_customer_match_confirmed"):
                        matched_name = distinct_names[0]
                        if normalize_customer_name(name) != normalize_customer_name(matched_name):
                            start_customer_match_session(
                                sender_phone, business_user_id, entry, message_text, matches,
                                "confirm_single", entries[entry_index + 1:],
                                allow_new=not existing_account_request
                            )
                            break

                    if not matches and existing_account_request and not force_new_customer:
                        if entry.get("_existing_account_lookup_attempted"):
                            send_whatsapp(
                                sender_phone,
                                f"❌ Ma helin macmiil jira oo la yiraahdo *{name}*. "
                                "Waxba laguma darin. Hubi magaca macmiilka oo mar kale dir."
                            )
                            failed_inserts.append({"name": name, "reason": "Existing customer requested but no match found"})
                            break
                        start_customer_match_session(
                            sender_phone, business_user_id, entry, message_text, [],
                            "enter_full_name", entries[entry_index + 1:], allow_new=False
                        )
                        break

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
                        if not math.isfinite(add_amount) or add_amount <= 0:
                            send_whatsapp(sender_phone, "❌ Lacagta lagu darayo waa inay noqotaa tiro sax ah oo ka weyn $0.")
                            failed_inserts.append({"name": name, "reason": "Additive amount must be positive"})
                            continue

                        old_amount = float(existing.get("amount") or 0)
                        if promised_date:
                            try:
                                promised_date = datetime.strptime(str(promised_date), "%Y-%m-%d").date().isoformat()
                            except (TypeError, ValueError):
                                send_whatsapp(sender_phone, "❌ Taariikh khaldan. Isticmaal YYYY-MM-DD.")
                                continue
                        parsed_created_at = None
                        if transaction_date:
                            parsed_transaction_date = _parse_somali_date(transaction_date)
                            if parsed_transaction_date is None:
                                send_whatsapp(sender_phone, "❌ Taariikhda macaamilka ma saxna. Isticmaal DD/MM/YYYY.")
                                failed_inserts.append({"name": name, "reason": "Invalid transaction date"})
                                continue
                            parsed_created_at = datetime.combine(
                                parsed_transaction_date, datetime.min.time(), tzinfo=EAT
                            ).isoformat()

                        updated_result = supabase.rpc("record_debt_addition", {
                            "p_customer_id": str(existing["id"]),
                            "p_business_user_id": str(business_user_id),
                            "p_name": str(existing.get("name") or name),
                            "p_amount": round(add_amount, 2),
                            "p_description": description or "-",
                            "p_promised_date": promised_date,
                            "p_phone_number": new_phone,
                            "p_created_at": parsed_created_at,
                        }).execute()
                        updated_data = updated_result.data
                        if isinstance(updated_data, list):
                            updated_data = updated_data[0] if updated_data else None
                        if not isinstance(updated_data, dict) or not updated_data.get("id"):
                            send_whatsapp(sender_phone, "❌ Lacagta laguma darin. Database-ku wax jawaab ah ma soo celin.")
                            failed_inserts.append({"name": name, "reason": "record_debt_addition returned no customer row"})
                            continue

                        updated = updated_data
                        credit_used = float(updated.get("credit_used") or 0)
                        credit_balance = float(updated.get("credit_balance") or 0)
                        credit_note = (
                            f"\n💰 Dhigaal laga isticmaalay: ${credit_used:.2f}"
                            f"\nHaraaga dhigaalka: ${credit_balance:.2f}"
                            if credit_used > 0 else ""
                        )
                        send_whatsapp(
                            sender_phone,
                            f"✅ Deynta {updated['name']} waa la cusboonaysiiyey. "
                            f"Lacagta lagu daray: ${add_amount:.2f}. "
                            f"Haraaga cusub: ${float(updated.get('amount') or 0):.2f}."
                            f"{credit_note}"
                        )
                        remember_selected_customer(sender_phone, business_user_id, updated.get("name") or name)
                        entry["action"] = "ADJUST"
                        successful_inserts.append(entry)
                        continue

                    # If matching records exist but all are paid, start a new
                    # debt row using the canonical stored spelling.
                    if matches:
                        name = matches[0].get("name") or name
                        entry["customer_name"] = name

                parsed_created_at = None
                if transaction_date:
                    parsed_transaction_date = _parse_somali_date(transaction_date)
                    if parsed_transaction_date is None:
                        send_whatsapp(sender_phone, "❌ Taariikhda macaamilka ma saxna. Isticmaal DD/MM/YYYY.")
                        failed_inserts.append({"name": name, "reason": "Invalid transaction date"})
                        continue
                    parsed_created_at = datetime.combine(
                        parsed_transaction_date, datetime.min.time(), tzinfo=EAT
                    ).isoformat()

                result = supabase.rpc("record_debt_addition", {
                    "p_customer_id": None,
                    "p_business_user_id": str(business_user_id),
                    "p_name": str(name),
                    "p_amount": round(float(amount), 2) if amount is not None else 0,
                    "p_description": description or "-",
                    "p_promised_date": promised_date,
                    "p_phone_number": new_phone,
                    "p_created_at": parsed_created_at,
                }).execute()
                if not result.data:
                    send_whatsapp(sender_phone, f"❌ Deynta {name} lama diiwaangelin. Database-ku wax jawaab ah ma soo celin.")
                    failed_inserts.append({"name": name, "reason": "record_debt_addition returned no rows"})
                    continue
                created_customer = result.data[0] if isinstance(result.data, list) else result.data
                remember_selected_customer(sender_phone, business_user_id, (created_customer or {}).get("name") or name)
                credit_used = float((created_customer or {}).get("credit_used") or 0)
                if credit_used > 0:
                    entry["credit_used"] = credit_used
                    entry["credit_balance"] = float((created_customer or {}).get("credit_balance") or 0)
                    entry["remaining_balance"] = float((created_customer or {}).get("amount") or 0)
                successful_inserts.append(entry)
                
            except Exception as e:
                print(f"❌ Debt registration error for {name!r}: {type(e).__name__}: {e}")
                send_whatsapp(
                    sender_phone,
                    f"❌ Deynta {name} lama diiwaangelin. Fadlan hubi xogta oo mar kale isku day."
                )
                failed_inserts.append({"name": name, "reason": str(e)})

        elif action == "PAY":
            try:
                payment_amount = entry.get("amount")
                payment_type = str(entry.get("payment_type") or "UNKNOWN").upper()
                matches = find_debtor_matches(business_user_id, name)
                distinct_names = _unique_customer_names(matches)

                if len(matches) == 0:
                    send_whatsapp(
                        sender_phone,
                        f"❌ Lama helin macmiil deyn ku leh oo la yiraahdo *{name}*. "
                        "Lacag-bixin lama diiwaangelin. Hubi magaca macmiilka."
                    )
                    failed_inserts.append({
                        "name": name,
                        "reason": "Unpaid debtor not found"
                    })
                    continue

                if len(distinct_names) > 1 and not entry.get("_customer_match_confirmed"):
                    start_customer_match_session(
                        sender_phone, business_user_id, entry, message_text, matches,
                        "choose", entries[entry_index + 1:], allow_new=False
                    )
                    break

                if len(distinct_names) == 1 and not entry.get("_customer_match_confirmed"):
                    matched_name = distinct_names[0]
                    if normalize_customer_name(name) != normalize_customer_name(matched_name):
                        start_customer_match_session(
                            sender_phone, business_user_id, entry, message_text, matches,
                            "confirm_single", entries[entry_index + 1:], allow_new=False
                        )
                        break

                if len(matches) > 1:
                    # Same display name with multiple unpaid debt rows cannot be
                    # safely distinguished by a name-only selection.
                    ask_for_full_name(sender_phone, matches, "PAY")
                    continue

                debtor = matches[0]
                current_balance = float(debtor.get("amount") or 0)
                if not math.isfinite(current_balance):
                    raise ValueError("Deynta hadda jirta waxay leedahay haraag aan sax ahayn.")

                if current_balance <= 0 or debtor.get("is_paid") is True:
                    send_whatsapp(sender_phone, f"✅ {debtor['name']} hore ayuu u bixiyay deyntiisa.")
                    continue

                # A missing amount is a full payment ONLY when the AI explicitly says FULL.
                if payment_amount is None and payment_type != "FULL":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "payment_amount",
                        "transaction_type": "payment",
                        "customer_name": str(debtor.get("name") or name).strip(),
                        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                    }
                    send_whatsapp(
                        sender_phone,
                        f"💵 {debtor['name']} lacag intee le'eg ayaad ka heshay?\n"
                        "Qor lacagta keliya, tusaale: *$10*. "
                        "Qor *JOOJI* haddii aad rabto inaad ka baxdo."
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

                if not math.isfinite(float(payment_amount)) or float(payment_amount) <= 0:
                    send_whatsapp(sender_phone, "❌ Lacagta la bixiyay waa inay noqotaa tiro sax ah oo ka weyn $0.")
                    continue

                if payment_amount - current_balance > 0.009:
                    # Send the detailed customer statement first. This is read-only:
                    # an overpayment is never saved as a normal payment.
                    try:
                        pdf_sent = send_customer_statement_pdf(
                            sender_phone,
                            business_user_id,
                            debtor.get("name") or name,
                            business_user.get("name"),
                        )
                        if not pdf_sent:
                            print(
                                "⚠️ Overpayment statement PDF could not be sent for "
                                f"customer={debtor.get('name') or name!r}"
                            )
                    except Exception as statement_error:
                        print(
                            "⚠️ Overpayment statement PDF generation failed: "
                            f"{type(statement_error).__name__}: {statement_error}"
                        )

                    send_whatsapp(
                        sender_phone,
                        f"⚠️ Wadarta deynta macmiilkan ee nidaamka ku jirta waa "
                        f"${current_balance:.2f}, adiguna waxaad soo qortay in laga jaro "
                        f"${payment_amount:.2f}. Fadlan sax lacagta si aan haraaga looga "
                        "dhigin tiro taban. Haddii aad ula jeeddo lacag uu sii dhiganayo, "
                        "soo qor *DHIGAAL*."
                    )
                    continue
                actual_payment = round(payment_amount, 2)
                new_balance = round(max(0.0, current_balance - actual_payment), 2)
                is_now_paid = new_balance <= 0

                # AI-interpreted payments always require explicit human confirmation.
                # Store the proposal in Supabase first; do not alter the debt balance here.
                try:
                    existing_pending = (
                        supabase.table("pending_payment_confirmations")
                        .select("id, customer_name, amount, status")
                        .eq("sender_phone", sender_phone)
                        .eq("business_user_id", business_user_id)
                        .in_("status", ["pending", "processing"])
                        .limit(1)
                        .execute()
                    )
                    if existing_pending.data:
                        pending_item = existing_pending.data[0]
                        send_whatsapp(
                            sender_phone,
                            f"Waxaa jira lacag-bixin kale oo sugaysa xaqiijin: "
                            f"{pending_item.get('customer_name')} ${float(pending_item.get('amount') or 0):.2f}.\n"
                            "Marka hore ka jawaab xaqiijintaas (1/HAA ama 2/MAYA)."
                        )
                        continue
                    expires_at = (datetime.now(timezone.utc) + timedelta(minutes=30)).isoformat()
                    pending_insert = supabase.table("pending_payment_confirmations").insert({
                        "sender_phone": sender_phone,
                        "business_user_id": str(business_user_id),
                        "customer_id": str(debtor["id"]),
                        "customer_name": str(debtor.get("name") or name),
                        "amount": actual_payment,
                        "description": description or "-",
                        "original_message": str(message_text or ""),
                        "status": "pending",
                        "expires_at": expires_at,
                    }).execute()
                    pending_row = pending_insert.data[0] if pending_insert.data else None
                    if not pending_row or not pending_row.get("id"):
                        raise RuntimeError("Pending payment row was not created")
                    send_whatsapp(
                        sender_phone,
                        "*Xaqiiji lacag-bixinta*\n\n"
                        f"{debtor.get('name') or name} ma wuxuu bixiyay *${actual_payment:.2f}*?\n\n"
                        "1. *HAA*\n"
                        "2. *MAYA*\n\n"
                        "Waxba lama kaydin ilaa aad xaqiijiso."
                    )
                    continue
                except Exception as pending_payment_error:
                    print(f"❌ Could not stage payment confirmation: {pending_payment_error}")
                    send_whatsapp(
                        sender_phone,
                        "❌ Xaqiijinta lacag-bixinta lama diyaarin karin. Waxba lama kaydin. Fadlan mar kale isku day."
                    )
                    failed_inserts.append({"name": name, "reason": "Could not stage payment confirmation"})
                    continue

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
                    .eq("is_archived", False)
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
                        try:
                            display_date = datetime.strptime(
                                str(filter_date), "%Y-%m-%d"
                            ).strftime("%d-%m-%Y")
                        except (TypeError, ValueError):
                            display_date = str(filter_date)
                        message_title = f"📋 *Balamaha {display_date}*"

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
                            "✅ Ma jirto deyn aan la bixin."
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
                                        f" ⚠️ Mudo dhaaf "
                                        f"({abs(days_left)} maalin)"
                                    )
                                    overdue_count += 1
                                elif days_left == 0:
                                    status = ""
                                elif not filter_date:
                                    # Keep individual dates when showing a mixed-date list.
                                    status = f" {due_date}"

                            except (TypeError, ValueError):
                                if not filter_date:
                                    status = f" {due_date}"

                        debt_list.append(
                            f"{index}. {debtor_name} — "
                            f"${debtor_amount:,.2f}{status}"
                        )
                    else:
                        debt_list.append(
                            f"{index}. {debtor_name} — "
                            f"${debtor_amount:,.2f}"
                        )

                message = (
                    f"{message_title} "
                    f"({len(debts_query.data)} macmiil):\n\n"
                    + "\n".join(debt_list)
                )

                if wants_due_dates and overdue_count > 0:
                    message = (
                        f"⚠️ {overdue_count} Macmiil ayaa mudo dhaaf ah:\n\n"
                        + message
                    )

                message += (
                    f"\n\n💰 Total: "
                    f"${total:,.2f}"
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
                continue

        elif action == "EDIT":
            try:
                matches = find_debtor_matches(business_user_id, name)

                if len(matches) == 0:
                    send_whatsapp(sender_phone, f"❌ Ma hayo deynta aan weli la bixin ee {name}.")
                    failed_inserts.append({"name": name, "reason": "Debtor not found"})
                    continue

                # A name-only EDIT/SAX request renames every debt row belonging
                # to the same exact stored customer name. It does not alter
                # amounts, due dates, payment records, or customer IDs.
                requested_new_name = str(entry.get("new_name") or "").strip()
                if requested_new_name:
                    distinct_old_names = {
                        str(row.get("name") or "").strip() for row in matches
                    }
                    if len(distinct_old_names) != 1:
                        ask_for_full_name(sender_phone, matches, "EDIT")
                        continue
                    old_stored_name = next(iter(distinct_old_names))
                    if not requested_new_name or len(requested_new_name) > 120:
                        send_whatsapp(sender_phone, "❌ Magaca cusub ma saxna. Fadlan isticmaal magac ka yar 120 xaraf.")
                        continue
                    # Do not merge two different customers by overwriting a name
                    # that is already used by another customer in this shop.
                    collision = (
                        supabase.table("customers")
                        .select("id, name")
                        .eq("business_user_id", business_user_id)
                        .eq("is_archived", False)
                        .eq("name", requested_new_name)
                        .limit(1)
                        .execute()
                    )
                    if collision.data and normalize_customer_name(collision.data[0].get("name")) != normalize_customer_name(old_stored_name):
                        send_whatsapp(
                            sender_phone,
                            f"⚠️ Magaca *{requested_new_name}* hore ayuu uga diiwaangashan yahay dukaankan. "
                            "Magacyada lama isku dari karo."
                        )
                        continue
                    renamed = (
                        supabase.table("customers")
                        .update({"name": requested_new_name})
                        .eq("business_user_id", business_user_id)
                        .eq("is_archived", False)
                        .eq("name", old_stored_name)
                        .select("id, name")
                        .execute()
                    )
                    if not renamed.data:
                        send_whatsapp(sender_phone, "❌ Magaca lama beddelin. Fadlan mar kale isku day.")
                        failed_inserts.append({"name": old_stored_name, "reason": "Rename returned no rows"})
                        continue
                    send_whatsapp(
                        sender_phone,
                        f"✅ Magaca macmiilka waa la saxay:\n*{old_stored_name}* → *{requested_new_name}*\n"
                        f"📁 Diiwaannada deynta ee la cusboonaysiiyay: {len(renamed.data)}"
                    )
                    successful_inserts.append(entry)
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
                    if not math.isfinite(amount_to_set) or amount_to_set < 0:
                        send_whatsapp(sender_phone, "❌ Lacagtu waa inay noqotaa tiro sax ah oo aan tabanayn.")
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

                if "amount" in update_data:
                    try:
                        payment_history = (supabase.table("payments").select("customer_id")
                            .eq("business_user_id", str(business_user_id))
                            .eq("customer_id", str(debtor["id"]))
                            .limit(1).execute())
                        transaction_history = (supabase.table("customer_transactions").select("customer_id")
                            .eq("business_user_id", str(business_user_id))
                            .eq("customer_id", str(debtor["id"]))
                            .limit(1).execute())
                    except Exception as history_check_error:
                        print(f"❌ Could not verify ledger before amount edit: {history_check_error}")
                        send_whatsapp(sender_phone, "❌ Taariikhda macaamilka lama hubin karin. Lacagta lama beddelin si loo ilaaliyo xisaabta.")
                        continue
                    if payment_history.data or transaction_history.data:
                        send_whatsapp(sender_phone, "⚠️ Macmiilkani wuxuu leeyahay taariikh macaamil/lacag-bixin. Si aan taariikhda iyo haraaga isugu khaldin, si toos ah looma beddeli karo lacagta. Waxba lama beddelin. Haddii lacag-bixin hore khaldan tahay, isticmaal *SAX magaca lacagta*; haddii deyn cusub jirto, ku dar macaamil cusub.")
                        continue
                    AMOUNT_EDIT_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id),
                        "customer_id": str(debtor["id"]),
                        "customer_name": str(debtor.get("name") or name),
                        "old_amount": _safe_money(debtor.get("amount")),
                        "update_data": dict(update_data),
                        "expires_at": datetime.now(timezone.utc) + timedelta(minutes=10),
                    }
                    change_lines = []
                    if "amount" in update_data:
                        change_lines.append(f"💵 Lacag: ${_safe_money(debtor.get('amount')):.2f} → ${float(update_data['amount']):.2f}")
                    if "promised_date" in update_data:
                        change_lines.append(f"📅 Ballan cusub: {update_data['promised_date']}")
                    send_whatsapp(sender_phone, "*Xaqiiji wax-ka-beddelka*\n\n" + str(debtor.get("name") or name) + "\n" + "\n".join(change_lines) + "\n\nQor *HAA* si loo kaydiyo ama *MAYA* si loo joojiyo.\nWaxba lama beddelin ilaa aad xaqiijiso.")
                    continue

                result = (
                    supabase.table("customers")
                    .update(update_data)
                    .eq("id", debtor["id"])
                    .eq("business_user_id", business_user_id)
                    .eq("is_archived", False)
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
            # Fallback for AI-recognized DELETE phrasing: it must still pass
            # through exact-name resolution and the explicit confirmation step.
            try:
                begin_delete_flow(sender_phone, business_user_id, name)
            except Exception as e:
                print(f"❌ Delete confirmation setup error: {type(e).__name__}: {e}")
                send_whatsapp(sender_phone, "❌ Macmiilka lama xaqiijin karin. Waxba lama tirtirin.")
                failed_inserts.append({"name": name, "reason": f"Delete setup error: {e}"})
        
        elif action == "SEARCH":
            if not str(name or "").strip():
                print(f"⚠️ Blocked SEARCH with missing customer_name: message={message_text!r}")
                send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca ii sheeg.")
                continue
            try:
                search_matches = find_debtor_matches(business_user_id, name)
                if not search_matches:
                    explicit_search_request = bool(re.match(
                        r"^\s*(?:search|find|lookup|look\s+up|raadi|raadso)\b",
                        str(message_text or ""), flags=re.IGNORECASE
                    ))
                    if explicit_search_request:
                        send_whatsapp(sender_phone, "Ma heli karo qofkan. Hubi magaciisa?")
                    else:
                        print(
                            f"⚠️ Bare-word SEARCH did not match a customer; treating as unrecognized text: "
                            f"{message_text!r}"
                        )
                        activate_guided_menu(sender_phone)
                        send_whatsapp(sender_phone, deynjir_unrecognized_message())
                    continue

                distinct_search_names = {
                    normalize_customer_name(d.get("name"))
                    for d in search_matches
                }

                if len(distinct_search_names) > 1:
                    ask_for_full_name(sender_phone, search_matches, "SEARCH")
                    continue

                matched_name = search_matches[0].get("name", name)
                remember_selected_customer(sender_phone, business_user_id, matched_name)

                total_debt = sum(
                    float(d.get("amount") or 0)
                    for d in search_matches
                    if not d.get("is_paid")
                )

                active_rows = [
                    d for d in search_matches
                    if d.get("is_paid") is not True and _safe_money(d.get("amount")) > 0
                ]
                paid_count = sum(1 for d in search_matches if d.get("is_paid") is True)
                due_dates = []
                for debt_row in active_rows:
                    raw_due = debt_row.get("promised_date")
                    if raw_due:
                        try:
                            due_dates.append(datetime.strptime(str(raw_due)[:10], "%Y-%m-%d").date())
                        except (TypeError, ValueError):
                            pass
                nearest_due = min(due_dates).isoformat() if due_dates else None

                message = (
                    f"🔎 *Natiijada raadinta: {matched_name}*\n\n"
                    f"💰 Deynta hadhsan: *${total_debt:.2f}*\n"
                    f"📋 Deyn aan weli la bixin: *{len(active_rows)}*\n"
                    f"✅ Diiwaanno hore loo bixiyey: *{paid_count}*"
                )
                if nearest_due:
                    message += f"\n📅 Ballanta ugu dhow: *{nearest_due}*"

                
                send_whatsapp(sender_phone, message)
                
            except Exception as e:
                print(f"❌ Search error: {type(e).__name__}: {e}")
                send_whatsapp(sender_phone, "❌ Khalad ayaa dhacay. Fadlan isku day inaad saxdo magaca.")
                failed_inserts.append({"name": name, "reason": f"Search error: {type(e).__name__}: {e}"})

       
        elif action == "HISTORY":
            try:
                # Full customer statement: debt records, payment events, and current outstanding balance.
                history_matches = find_debtor_matches(business_user_id, name, include_archived=True)

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

                    total_balance = sum(
                        max(float(debt.get("amount") or 0), 0.0)
                        for debt in history_matches
                    )
                    total_paid = sum(float(payment.get("amount") or 0) for payment in payment_rows)

                    original_total = 0.0
                    for debt in history_matches:
                        debt_id = str(debt.get("id"))
                        debt_payments = payments_by_debt.get(debt_id, [])
                        paid_for_debt = sum(
                            float(payment.get("amount") or 0)
                            for payment in debt_payments
                        )
                        current_amount = max(float(debt.get("amount") or 0), 0.0)
                        stored_original = debt.get("original_amount")
                        if stored_original is None:
                            stored_original = current_amount + paid_for_debt
                        original_total += max(float(stored_original or 0), current_amount)

                    matched_display_name = history_matches[0].get("name", name)
                    message = (
                        f"📒 *Xisaabta {matched_display_name}:* "
                        f"Wadarta deynta ${original_total:.2f}, "
                        f"lacagta uu bixiyay ${total_paid:.2f}, "
                        f"haraaga hadda ${total_balance:.2f}."
                    )

                    matched_customer_name = history_matches[0].get(
                        "name",
                        name
                    )

                    LAST_HISTORY_REQUESTS[sender_phone] = {
                        "business_user_id": business_user_id,
                        "customer_name": matched_customer_name,
                    }
                    remember_selected_customer(sender_phone, business_user_id, matched_customer_name)

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
                    .eq("is_archived", False)
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
                    .eq("is_archived", False)
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
                success_message = (
                    f"✅ Deynta {entry.get('customer_name') or 'macmiilka'} "
                    f"waa la diiwaangeliyey: ${float(entry.get('amount') or 0):.2f}."
                )
                if entry.get("promised_date"):
                    success_message += f" Ballanta: {entry.get('promised_date')}."
                if float(entry.get("credit_used") or 0) > 0:
                    success_message += (
                        f" Dhigaal laga isticmaalay: ${float(entry.get('credit_used')):.2f}. "
                        f"Haraaga dhigaalka: ${float(entry.get('credit_balance') or 0):.2f}. "
                        f"Haraaga deynta: ${float(entry.get('remaining_balance') or 0):.2f}."
                    )
            else:
                success_message = "✅ Deymaha waa la diiwaangeliyey: " + "; ".join(
                    f"{entry.get('customer_name') or 'Macmiil'} "
                    f"${float(entry.get('amount') or 0):.2f}"
                    + (
                        f" (dhigaal la isticmaalay ${float(entry.get('credit_used') or 0):.2f}; "
                        f"haraaga dhigaalka ${float(entry.get('credit_balance') or 0):.2f})"
                        if float(entry.get("credit_used") or 0) > 0 else ""
                    )
                    for entry in add_entries
                ) + "."
            send_whatsapp(sender_phone, success_message)

    if failed_inserts:
        # Specific handlers already explain the failure. Do not send a second,
        # confusing generic menu after an actionable error.
        print(f"❌ Transaction failures ({len(failed_inserts)}): {failed_inserts}")
    
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


def _parse_payment_report_date(raw, default_year=None):
    """Parse report dates in DD/MM/YYYY, YYYY-MM-DD, or day-month-name form."""
    value = str(raw or "").strip().replace(".", "/")
    if not value:
        raise ValueError("Taariikh maqan")
    for fmt in ("%d/%m/%Y", "%Y-%m-%d", "%d-%m-%Y", "%d/%m"):
        try:
            parsed = datetime.strptime(value, fmt).date()
            if fmt == "%d/%m":
                parsed = parsed.replace(year=default_year or today_eat().year)
            return parsed
        except ValueError:
            pass
    months = {"jan":1,"january":1,"feb":2,"february":2,"mar":3,"march":3,"apr":4,"april":4,"may":5,"jun":6,"june":6,"jul":7,"july":7,"aug":8,"august":8,"sep":9,"sept":9,"september":9,"oct":10,"october":10,"nov":11,"november":11,"dec":12,"december":12}
    year = default_year or today_eat().year
    m = re.fullmatch(r"(\d{1,2})\s+([A-Za-z]+)(?:\s+(\d{4}))?", value)
    if m and m.group(2).lower() in months:
        return datetime(int(m.group(3) or year), months[m.group(2).lower()], int(m.group(1))).date()
    m = re.fullmatch(r"([A-Za-z]+)\s+(\d{1,2})(?:,?\s+(\d{4}))?", value)
    if m and m.group(1).lower() in months:
        return datetime(int(m.group(3) or year), months[m.group(1).lower()], int(m.group(2))).date()
    raise ValueError("Taariikhda lama fahmin")


def _load_shop_payments(business_user_id, start_date=None, end_date=None):
    query = (supabase.table("payments")
        .select("amount, paid_at, customer_id")
        .eq("business_user_id", business_user_id)
        .order("paid_at", desc=False))
    if start_date:
        query = query.gte("paid_at", datetime.combine(start_date, datetime.min.time(), tzinfo=EAT).astimezone(timezone.utc).isoformat())
    if end_date:
        next_day = end_date + timedelta(days=1)
        query = query.lt("paid_at", datetime.combine(next_day, datetime.min.time(), tzinfo=EAT).astimezone(timezone.utc).isoformat())
    rows = query.execute().data or []
    ids = list({str(row.get("customer_id")) for row in rows if row.get("customer_id")})
    names = {}
    if ids:
        customer_rows = (supabase.table("customers")
            .select("id, name")
            .eq("business_user_id", business_user_id)
            .in_("id", ids).execute().data or [])
        names = {str(row.get("id")): row.get("name") or "Macmiil" for row in customer_rows}
    records = []
    for row in rows:
        paid_at = row.get("paid_at")
        date_text = str(paid_at or "")[:10]
        try:
            payment_date = datetime.strptime(date_text, "%Y-%m-%d").date()
        except ValueError:
            payment_date = None
        records.append({
            "date": payment_date,
            "date_text": payment_date.strftime("%d/%m/%Y") if payment_date else date_text,
            "name": names.get(str(row.get("customer_id")), "Macmiil"),
            "amount": _safe_money(row.get("amount")),
        })
    return records


def _build_payment_excel(records, start_date, end_date):
    frame = pd.DataFrame([{"Taariikhda": r["date_text"], "Magaca macmiilka": r["name"], "Lacagta la bixiyay ($)": r["amount"]} for r in records])
    if frame.empty:
        frame = pd.DataFrame(columns=["Taariikhda", "Magaca macmiilka", "Lacagta la bixiyay ($)"])
    output = BytesIO()
    with pd.ExcelWriter(output, engine="openpyxl") as writer:
        frame.to_excel(writer, index=False, sheet_name="Lacag bixinta")
        sheet = writer.sheets["Lacag bixinta"]
        sheet.freeze_panes = "A2"
        sheet.auto_filter.ref = sheet.dimensions
        for column, width in {"A":16,"B":32,"C":22}.items():
            sheet.column_dimensions[column].width = width
        total_row = len(frame) + 3
        sheet.cell(total_row, 2, "Wadarta")
        sheet.cell(total_row, 3, sum(r["amount"] for r in records))
        sheet.cell(total_row + 1, 2, "Tirada diiwaannada")
        sheet.cell(total_row + 1, 3, len(records))
    return output.getvalue()


def _build_payment_pdf(records, start_date, end_date, shop_name):
    output = BytesIO()
    doc = SimpleDocTemplate(output, pagesize=A4, rightMargin=36, leftMargin=36, topMargin=36, bottomMargin=36)
    styles = getSampleStyleSheet()
    story = [Paragraph("DEYNJIR — LIISKA LACAG BIXINTA", styles["Title"]), Spacer(1, 8)]
    if shop_name:
        story.append(Paragraph(escape(str(shop_name)), styles["Heading2"]))
    story.append(Paragraph(f"Muddada: {start_date.strftime('%d/%m/%Y')} – {end_date.strftime('%d/%m/%Y')}", styles["Normal"]))
    story.append(Spacer(1, 12))
    data = [["Taariikhda", "Magaca macmiilka", "Lacagta ($)"]]
    data.extend([[r["date_text"], r["name"], f"${r['amount']:.2f}"] for r in records])
    data.append(["", "Wadarta", f"${sum(r['amount'] for r in records):.2f}"])
    data.append(["", "Tirada diiwaannada", str(len(records))])
    table = Table(data, colWidths=[105, 260, 105], repeatRows=1)
    table.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#E8EEF5")),
        ("FONTNAME", (0,0), (-1,0), "Helvetica-Bold"),
        ("GRID", (0,0), (-1,-3), 0.35, colors.grey),
        ("ALIGN", (-1,1), (-1,-1), "RIGHT"),
        ("FONTNAME", (1,-2), (-1,-1), "Helvetica-Bold"),
        ("TOPPADDING", (0,0), (-1,-1), 7), ("BOTTOMPADDING", (0,0), (-1,-1), 7),
    ]))
    story.append(table)
    doc.build(story)
    return output.getvalue()


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
                .eq("is_archived", False)
                .eq("is_paid", False)
                .order("promised_date", desc=False)
                .execute()
            )
            debts = debts_result.data or []

            overdue_items = []
            today_items = []
            today_date = today_eat()
            for debt in debts:
                raw_due_date = debt.get("promised_date")
                if not raw_due_date:
                    continue
                try:
                    due_date = datetime.strptime(str(raw_due_date)[:10], "%Y-%m-%d").date()
                except (TypeError, ValueError):
                    print(f"⚠️ Invalid promised_date for {debt.get('name')}: {raw_due_date!r}")
                    continue
                amount_text = f"${_safe_money(debt.get('amount')):.2f}"
                customer_name = debt.get("name") or "Macmiil"
                if due_date < today_date:
                    overdue_days = (today_date - due_date).days
                    overdue_items.append(
                        f"• {customer_name}: {amount_text} — ⚠️ Mudo dhaaf ({overdue_days} maalin)"
                    )
                elif due_date == today_date:
                    today_items.append(f"• {customer_name}: {amount_text} — 🔴 Maanta")

            all_items = overdue_items + today_items
            print(f"📅 Daily digest user={business_user_id}: overdue={len(overdue_items)}, due_today={len(today_items)}")
            if not all_items:
                skipped_count += 1
                continue

            max_items = 40
            shown_overdue = overdue_items[:max_items]
            remaining_slots = max(0, max_items - len(shown_overdue))
            shown_today = today_items[:remaining_slots]
            omitted = len(all_items) - len(shown_overdue) - len(shown_today)
            message_lines = ["☀️ *Xasuusin* ☀️", ""]
            if shown_overdue:
                message_lines.extend(["⚠️ *DEYMAHA BALAN DHAAFKA AH*", *shown_overdue, ""])
            if shown_today:
                message_lines.extend(["🔴 *BALANTA MAANTA*", *shown_today])
            if omitted > 0:
                message_lines.extend(["", f"➕ {omitted} kale ayaa jira. Qor *LIISKA DAYNTA* si aad u aragto dhammaan."])

            if name:
                message_lines.insert(1, f"👤 *{name}*")

            ok = send_whatsapp(phone, "\n".join(message_lines))
            if ok:
                sent_count += 1
                print(f"✅ Daily digest sent: user={business_user_id}, overdue={len(overdue_items)}, due_today={len(today_items)}")
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


def _report_period_utc_boundaries(start_date, end_date):
    """Convert inclusive EAT calendar dates into UTC [start, end) boundaries."""
    start_local = datetime.combine(start_date, datetime.min.time(), tzinfo=EAT)
    end_local = datetime.combine(end_date + timedelta(days=1), datetime.min.time(), tzinfo=EAT)
    return start_local.astimezone(timezone.utc).isoformat(), end_local.astimezone(timezone.utc).isoformat()


def _report_period_data(business_user_id, start_date, end_date):
    """Load period activity and current outstanding balances for one shop."""
    start_iso, end_iso = _report_period_utc_boundaries(start_date, end_date)
    debts_result = (supabase.table("customers")
        .select("id, name, amount, original_amount, promised_date, is_paid, created_at")
        .eq("business_user_id", business_user_id)
        .gte("created_at", start_iso).lt("created_at", end_iso).execute())
    new_debts = debts_result.data or []

    payments_result = (supabase.table("payments")
        .select("id, amount, paid_at, customer_id")
        .eq("business_user_id", business_user_id)
        .gte("paid_at", start_iso).lt("paid_at", end_iso).execute())
    payments = payments_result.data or []

    current_result = (supabase.table("customers")
        .select("id, amount, promised_date, is_paid")
        .eq("business_user_id", business_user_id)
        .eq("is_archived", False)
        .eq("is_paid", False).execute())
    current_open = [row for row in (current_result.data or []) if _safe_money(row.get("amount")) > 0]

    today = today_eat()
    overdue_count = 0
    for row in current_open:
        raw_due = row.get("promised_date")
        if not raw_due:
            continue
        try:
            due = datetime.strptime(str(raw_due)[:10], "%Y-%m-%d").date()
            if due < today:
                overdue_count += 1
        except ValueError:
            continue

    new_debt_total = sum(_safe_money(row.get("original_amount") if row.get("original_amount") is not None else row.get("amount")) for row in new_debts)
    payment_total = sum(_safe_money(row.get("amount")) for row in payments)
    return {
        "new_debt_total": new_debt_total,
        "new_debt_count": len(new_debts),
        "new_customer_count": len({str(row.get("name") or "").strip().casefold() for row in new_debts if str(row.get("name") or "").strip()}),
        "payment_total": payment_total,
        "payment_count": len(payments),
        "net_change": new_debt_total - payment_total,
        "outstanding_total": sum(_safe_money(row.get("amount")) for row in current_open),
        "outstanding_count": len(current_open),
        "overdue_count": overdue_count,
    }


def _format_business_activity_report(report_type, start_date, end_date, data, shop_name=None):
    if report_type == "daily":
        heading, period_label = "📊 *Warbixinta Maanta*", start_date.strftime("%d/%m/%Y")
    elif report_type == "weekly":
        heading = "📊 *Warbixinta Toddobaadka*"
        period_label = f"{start_date.strftime('%d/%m/%Y')} – {end_date.strftime('%d/%m/%Y')}"
    else:
        somali_months = ["Janaayo", "Febraayo", "Maarso", "Abriil", "Maajo", "Juun", "Luulyo", "Agoosto", "Sebtembar", "Oktoobar", "Nofeembar", "Diseembar"]
        heading, period_label = "📊 *Warbixinta Bisha*", f"{somali_months[start_date.month - 1]} {start_date.year}"

    lines = [heading, f"📅 {period_label}"]
    if shop_name:
        lines.append(f"🏪 {shop_name}")
    lines.extend([
        "",
        f"🆕 Deyn cusub: *${data['new_debt_total']:.2f}* ({data['new_debt_count']} diiwaan)",
        f"👥 Tirada Macaamiisha deynta cusub qaatay: *{data['new_customer_count']}*",
        f"💵 Lacagta la bixiyey: *${data['payment_total']:.2f}* ({data['payment_count']} lacag-bixin)",
        "",
        f"📒 Totalka Daynta hadda taagan: *${data['outstanding_total']:.2f}*",
        f"👤 Tirada Macaamiisha weli lagu leeyahay: *{data['outstanding_count']}*",
        f"⚠️ Tirada Dadka balan dhaafka ah: *{data['overdue_count']}*",
    ])
    if data["new_debt_count"] == 0 and data["payment_count"] == 0:
        lines.extend(["", "Ma jirin deyn cusub ama lacag-bixin muddadan."])
    return "\n".join(lines)


def _reserve_report_send(business_user_id, report_type, start_date, end_date):
    """Reserve a unique period; cron_report_logs has a unique period constraint."""
    payload = {
        "business_user_id": str(business_user_id), "report_type": report_type,
        "period_start": start_date.isoformat(), "period_end": end_date.isoformat(),
    }
    result = supabase.table("cron_report_logs").insert(payload).select("id").execute()
    return bool(result.data)


def _release_report_reservation(business_user_id, report_type, start_date, end_date):
    try:
        (supabase.table("cron_report_logs").delete()
         .eq("business_user_id", str(business_user_id)).eq("report_type", report_type)
         .eq("period_start", start_date.isoformat()).eq("period_end", end_date.isoformat()).execute())
    except Exception as exc:
        print(f"⚠️ Could not release report reservation: {type(exc).__name__}: {exc}")


async def _send_period_report(report_type, start_date, end_date):
    sent_count = skipped_count = error_count = 0
    users_result = (supabase.table("business_users")
        .select("id, phone_number, name").eq("approval_status", "approved").execute())
    users = users_result.data or []
    print(f"👥 {report_type.upper()} report: approved shops={len(users)}")

    for user in users:
        business_user_id = user.get("id")
        phone = str(user.get("phone_number") or "").strip()
        shop_name = str(user.get("name") or "").strip()
        if not business_user_id or not phone:
            skipped_count += 1
            continue
        reserved = False
        try:
            reserved = _reserve_report_send(business_user_id, report_type, start_date, end_date)
            if not reserved:
                skipped_count += 1
                print(f"⏭️ Duplicate {report_type} report skipped: shop={business_user_id}")
                continue
            data = _report_period_data(business_user_id, start_date, end_date)
            message = _format_business_activity_report(report_type, start_date, end_date, data, shop_name)
            if send_whatsapp(phone, message):
                sent_count += 1
                print(f"✅ {report_type} report sent: shop={business_user_id}, debts={data['new_debt_count']}/${data['new_debt_total']:.2f}, payments={data['payment_count']}/${data['payment_total']:.2f}")
            else:
                error_count += 1
                _release_report_reservation(business_user_id, report_type, start_date, end_date)
                print(f"❌ {report_type} report WhatsApp failed: shop={business_user_id}")
        except Exception as exc:
            error_count += 1
            if reserved:
                _release_report_reservation(business_user_id, report_type, start_date, end_date)
            print(f"❌ {report_type} report failed: shop={business_user_id}, {type(exc).__name__}: {exc}")
    return {"sent": sent_count, "skipped": skipped_count, "errors": error_count}


@app.get("/cron/evening-checkin")
async def evening_checkin(request: Request):
    """Send the daily business activity report at 20:00 Somalia time."""
    if not cron_authorized(request):
        from fastapi import HTTPException
        raise HTTPException(status_code=401, detail="Unauthorized cron request")
    today = today_eat()
    print(f"🌙 DAILY BUSINESS REPORT STARTED: {today.isoformat()}")
    try:
        result = await _send_period_report("daily", today, today)
    except Exception as exc:
        print(f"❌ DAILY REPORT failed to load shops: {type(exc).__name__}: {exc}")
        return {"status": "database_error", "detail": str(exc)}
    print(f"🏁 DAILY REPORT FINISHED: sent={result['sent']}, skipped={result['skipped']}, errors={result['errors']}")
    return {"status": "done", **result, "date": today.isoformat()}


@app.get("/cron/periodic-reports")
async def periodic_reports(request: Request):
    """Run weekly on Fridays and monthly on each month's final calendar day."""
    if not cron_authorized(request):
        from fastapi import HTTPException
        raise HTTPException(status_code=401, detail="Unauthorized cron request")
    today = today_eat()
    results = {}
    if today.weekday() == 4:
        try:
            results["weekly"] = await _send_period_report("weekly", today - timedelta(days=6), today)
        except Exception as exc:
            print(f"❌ WEEKLY REPORT failed: {type(exc).__name__}: {exc}")
            results["weekly"] = {"status": "error", "detail": str(exc)}
    else:
        results["weekly"] = {"status": "not_scheduled_today"}

    tomorrow = today + timedelta(days=1)
    if tomorrow.month != today.month:
        try:
            results["monthly"] = await _send_period_report("monthly", today.replace(day=1), today)
        except Exception as exc:
            print(f"❌ MONTHLY REPORT failed: {type(exc).__name__}: {exc}")
            results["monthly"] = {"status": "error", "detail": str(exc)}
    else:
        results["monthly"] = {"status": "not_scheduled_today"}
    return {"status": "done", "date": today.isoformat(), **results}


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


@app.get("/cron/all-scheduled")
async def all_scheduled_tasks(request: Request):
    """Single scheduler entry point for all existing Deynjir cron tasks.

    Call this endpoint at 04:00, 15:00 and 17:00 UTC (07:00, 18:00 and
    20:00 Somalia time). Keeping one Render Cron Job service avoids creating
    separate paid Cron Job services for each task.
    """
    if not cron_authorized(request):
        from fastapi import HTTPException
        raise HTTPException(status_code=401, detail="Unauthorized cron request")

    now = now_eat()
    hour = now.hour
    results = {"status": "done", "somalia_time": now.isoformat(), "tasks": {}}

    # 07:00 Somalia time — daily due/overdue customer digest.
    if hour == 7:
        print("🕖 SCHEDULER: running daily digest")
        try:
            results["tasks"]["daily_digest"] = await daily_digest(request)
        except Exception as exc:
            print(f"❌ SCHEDULER daily digest failed: {type(exc).__name__}: {exc}")
            results["tasks"]["daily_digest"] = {"status": "error", "detail": str(exc)}

    # 18:00 Somalia time — inactivity reminder (only shops with no activity).
    elif hour == 18:
        print("🕕 SCHEDULER: running inactivity check-in")
        try:
            results["tasks"]["inactivity_checkin"] = await inactivity_checkin(request)
        except Exception as exc:
            print(f"❌ SCHEDULER inactivity check-in failed: {type(exc).__name__}: {exc}")
            results["tasks"]["inactivity_checkin"] = {"status": "error", "detail": str(exc)}

    # 20:00 Somalia time — daily report, plus Friday/month-end reports.
    elif hour == 20:
        print("🕗 SCHEDULER: running daily and periodic reports")
        try:
            results["tasks"]["daily_report"] = await evening_checkin(request)
        except Exception as exc:
            print(f"❌ SCHEDULER daily report failed: {type(exc).__name__}: {exc}")
            results["tasks"]["daily_report"] = {"status": "error", "detail": str(exc)}
        try:
            results["tasks"]["periodic_reports"] = await periodic_reports(request)
        except Exception as exc:
            print(f"❌ SCHEDULER periodic reports failed: {type(exc).__name__}: {exc}")
            results["tasks"]["periodic_reports"] = {"status": "error", "detail": str(exc)}
    else:
        results["status"] = "no_task_for_this_hour"
        results["message"] = "Run this endpoint at 07:00, 18:00 or 20:00 Somalia time."

    return results

if __name__ == "__main__":
    import uvicorn
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
