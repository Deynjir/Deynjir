import os
import asyncio
import re
import json
import csv
import hmac
import time
import secrets
import math
import hashlib
from contextvars import ContextVar
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


def fetch_all_supabase_rows(query_factory, page_size=1000):
    """Fetch every matching Supabase row in stable pages, not just the first page."""
    all_rows = []
    offset = 0
    while True:
        result = query_factory().range(offset, offset + page_size - 1).execute()
        page = result.data or []
        all_rows.extend(page)
        if len(page) < page_size:
            break
        offset += page_size
    return all_rows

# Setup the core application framework
app = FastAPI()

# Remembers the most recent customer statement so the user can request its PDF
# by sending "PDF" as a follow-up WhatsApp message. Cleared on server restart.
LAST_HISTORY_REQUESTS = {}
# Remembers the last customer added, searched, or opened for this sender.
# Used for short-lived, same-shop follow-ups that clearly refer to that customer.
LAST_SELECTED_CUSTOMERS = {}
# Remembers the last appointment-list date so terse follow-ups can repeat the result.
LAST_APPOINTMENT_LIST_REQUESTS = {}
# First-contact onboarding choices are temporary per-sender conversations.
ONBOARDING_SESSIONS = {}
# Admin-triggered, deterministic first-debt onboarding; independent of Gemini/chat AI.
FIRST_DEBT_SESSIONS = {}
FIRST_DEBT_SESSION_TTL = timedelta(minutes=30)
# Short-lived conversational context for natural follow-ups (not financial state).
CONVERSATION_SESSIONS = {}
CONVERSATION_SESSION_TTL = timedelta(minutes=30)
# One-shot reminder for an unanswered workflow prompt; any new user message cancels it.
PENDING_REPLY_REMINDER_TASKS = {}
PENDING_REPLY_INBOUND_SNAPSHOTS = {}
PENDING_REPLY_REMINDER_DELAY_SECONDS = 180
# Follow-up nudges are opt-in; default off avoids unsolicited repeated messages.
PENDING_REPLY_REMINDER_ENABLED = os.getenv("PENDING_REPLY_REMINDER_ENABLED", "false").strip().casefold() in {
    "1", "true", "yes", "on",
}

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
# Guided transaction/search workflows expire quickly; an explicitly displayed
# menu remains selectable for 24 hours so delayed numeric replies route correctly.
GUIDED_SESSIONS = {}
PAUSED_GUIDED_SESSIONS = {}
GUIDED_SESSION_TTL = timedelta(minutes=15)
GUIDED_MENU_SESSION_TTL = timedelta(hours=24)
# Pending ADD/PAY customer identity confirmations. No transaction is saved until resolved.
CUSTOMER_MATCH_SESSIONS = {}
# A PAY request for a customer with no outstanding debt may become a confirmed deposit.
DEPOSIT_OFFER_SESSIONS = {}
DEPOSIT_OFFER_TTL = timedelta(minutes=5)
# Confirmed correction of the immediately preceding ADD/PAY transaction.
CORRECTION_SESSIONS = {}
CORRECTION_SESSION_TTL = timedelta(minutes=5)
# Explicit, confirmed DELETE workflow; sender/shop scoped and temporary.
DELETE_SESSIONS = {}
DELETE_SESSION_TTL = timedelta(minutes=15)
# Short-lived, sender/shop-scoped confirmation before reversing a financial transaction.
UNDO_CONFIRMATION_SESSIONS = {}
UNDO_CONFIRMATION_TTL = timedelta(minutes=5)
# Only a transaction actually recorded by this sender can trigger disagreement follow-up.
LAST_TRANSACTION_CONTEXT = {}
# Short-lived, sender/shop-scoped context for safely undoing the most recent committed batch.
LAST_BATCH_CONTEXT = {}
# After a short search result, remembers whether the shopkeeper wants the full customer statement.
SEARCH_DETAIL_SESSIONS = {}

# Central registry for sender-scoped workflows. Lifecycle checks and cleanup
# use the same registry so new workflows cannot be omitted from interruption logic.
WORKFLOW_SESSION_MAPS = (
    IMPORT_SESSIONS, PAYMENT_EXPORT_SESSIONS, REMINDER_SESSIONS,
    RENAME_SESSIONS, AMOUNT_EDIT_SESSIONS, GUIDED_SESSIONS,
    PAUSED_GUIDED_SESSIONS, CUSTOMER_MATCH_SESSIONS, DELETE_SESSIONS,
    FIRST_DEBT_SESSIONS,
    UNDO_CONFIRMATION_SESSIONS, SEARCH_DETAIL_SESSIONS,
    DEPOSIT_OFFER_SESSIONS, CORRECTION_SESSIONS,
)

# Database-backed workflow recovery. These maps contain JSON-serializable
# conversation state; asyncio tasks and transient inbound snapshots are excluded.
PERSISTED_SESSION_MAPS = {
    "last_history": LAST_HISTORY_REQUESTS,
    "last_selected": LAST_SELECTED_CUSTOMERS,
    "onboarding": ONBOARDING_SESSIONS,
    "first_debt": FIRST_DEBT_SESSIONS,
    "conversation": CONVERSATION_SESSIONS,
    "reminder": REMINDER_SESSIONS,
    "rename": RENAME_SESSIONS,
    "amount_edit": AMOUNT_EDIT_SESSIONS,
    "import": IMPORT_SESSIONS,
    "payment_export": PAYMENT_EXPORT_SESSIONS,
    "guided": GUIDED_SESSIONS,
    "paused_guided": PAUSED_GUIDED_SESSIONS,
    "customer_match": CUSTOMER_MATCH_SESSIONS,
    "deposit_offer": DEPOSIT_OFFER_SESSIONS,
    "correction": CORRECTION_SESSIONS,
    "delete": DELETE_SESSIONS,
    "undo": UNDO_CONFIRMATION_SESSIONS,
    "last_transaction": LAST_TRANSACTION_CONTEXT,
    "last_batch": LAST_BATCH_CONTEXT,
    "search_detail": SEARCH_DETAIL_SESSIONS,
}


def _session_json_default(value):
    if isinstance(value, (datetime,)):
        return value.isoformat()
    if hasattr(value, "isoformat") and callable(value.isoformat):
        return value.isoformat()
    if isinstance(value, (set, tuple)):
        return list(value)
    if isinstance(value, (bytes, bytearray)):
        import base64
        return {"__deynjir_bytes__": base64.b64encode(bytes(value)).decode("ascii")}
    raise TypeError(f"Unsupported workflow session value: {type(value).__name__}")


def _restore_session_value(value, key=""):
    if isinstance(value, dict):
        if set(value) == {"__deynjir_bytes__"}:
            import base64
            try:
                return base64.b64decode(value["__deynjir_bytes__"])
            except Exception:
                return b""
        return {k: _restore_session_value(v, k) for k, v in value.items()}
    if isinstance(value, list):
        return [_restore_session_value(v, key) for v in value]
    if isinstance(value, str) and (key.endswith("_at") or key == "expires_at"):
        try:
            parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
            if parsed.tzinfo is None:
                parsed = parsed.replace(tzinfo=timezone.utc)
            return parsed
        except (TypeError, ValueError):
            return value
    return value


def _load_persisted_workflow_sessions(sender_phone):
    """Restore this sender's unfinished conversations after a process restart."""
    try:
        result = (supabase.table("deynjir_workflow_sessions")
            .select("session_name, payload, expires_at")
            .eq("sender_phone", str(sender_phone)).execute())
        now = datetime.now(timezone.utc)
        for row in result.data or []:
            name = row.get("session_name")
            target = PERSISTED_SESSION_MAPS.get(name)
            payload = row.get("payload")
            if target is None or not isinstance(payload, dict):
                continue
            expiry = row.get("expires_at")
            if expiry:
                try:
                    exp_dt = datetime.fromisoformat(str(expiry).replace("Z", "+00:00"))
                    if exp_dt.tzinfo is None:
                        exp_dt = exp_dt.replace(tzinfo=timezone.utc)
                    if exp_dt <= now:
                        target.pop(sender_phone, None)
                        continue
                except ValueError:
                    pass
            target[sender_phone] = _restore_session_value(payload)
    except Exception as exc:
        # Financial operations remain guarded by idempotent RPCs. Session
        # persistence failures are logged; the active process can still proceed.
        print(f"⚠️ Workflow session restore failed: {type(exc).__name__}: {exc}")


def _save_persisted_workflow_sessions(sender_phone):
    """Upsert or remove all persisted workflow state for one sender."""
    rows = []
    try:
        for name, mapping in PERSISTED_SESSION_MAPS.items():
            value = mapping.get(sender_phone)
            if value is None:
                continue
            payload = json.loads(json.dumps(value, default=_session_json_default, ensure_ascii=False))
            expiry = value.get("expires_at") if isinstance(value, dict) else None
            if isinstance(expiry, datetime):
                expiry = expiry.isoformat()
            rows.append({
                "sender_phone": str(sender_phone), "session_name": name,
                "payload": payload, "expires_at": expiry,
                "updated_at": datetime.now(timezone.utc).isoformat(),
            })
        # Replace the sender snapshot as a single logical save. Rows absent from
        # this snapshot are removed so completed/cancelled flows do not return.
        (supabase.table("deynjir_workflow_sessions").delete()
            .eq("sender_phone", str(sender_phone)).execute())
        if rows:
            supabase.table("deynjir_workflow_sessions").upsert(
                rows, on_conflict="sender_phone,session_name").execute()
    except Exception as exc:
        print(f"⚠️ Workflow session save failed: {type(exc).__name__}: {exc}")


def deynjir_main_menu():
    """Text fallback for the three main WhatsApp actions."""
    return (
        "👋 *Ku soo dhawoow Deynjir!*\n\n"
        "Maxaad rabtaa inaad qabato?\n\n"
        "1️⃣ Deyn cusub\n"
        "2️⃣ Dayn soo xarootay\n"
        "3️⃣ Adeeg kale\n\n"
        "Dooro badhanka hoose ama soo dir 1, 2 ama 3."
    )


def deynjir_other_services_menu():
    """Text menu shown only after the user chooses Adeeg kale."""
    return (
        "📋 *ADEEGYADA KALE*\n\n"
        "Dooro adeegga aad rabto:\n\n"
        "1️⃣ Liiska daynta\n"
        "2️⃣ Raadi macmiil\n"
        "3️⃣ Ballamaha maanta\n"
        "4️⃣ Caawimaad\n"
        "5️⃣ Soo geli daymo hore (IMPORT)\n"
        "6️⃣ Liiska lacag-bixinta\n\n"
        "Soo dir lambarka adeegga (1–6)."
    )


def send_deynjir_other_services_menu(to_phone, page=1):
    """Send the six services across three WhatsApp-compatible button pages."""
    pages = {
        1: (
            "📋 ADEEGYADA KALE (1/3)\n\nDooro adeegga:",
            [("OTHER_DEBT_LIST", "Liiska daynta"),
             ("OTHER_SEARCH", "Raadi macmiil"),
             ("OTHER_NEXT", "Adeegyada xiga")],
            "1️⃣ Liiska daynta\n2️⃣ Raadi macmiil\n3️⃣ Adeegyada xiga"
        ),
        2: (
            "📋 ADEEGYADA KALE (2/3)\n\nDooro adeegga:",
            [("OTHER_APPOINTMENTS", "Ballamaha maanta"),
             ("OTHER_HELP", "Caawimaad"),
             ("OTHER_NEXT", "Adeegyada xiga")],
            "3️⃣ Ballamaha maanta\n4️⃣ Caawimaad\n5️⃣ Adeegyada xiga"
        ),
        3: (
            "📋 ADEEGYADA KALE (3/3)\n\nDooro adeegga:",
            [("OTHER_IMPORT", "Soo geli daymo hore"),
             ("OTHER_PAYMENTS", "Liiska lacag-bixinta"),
             ("OTHER_BACK", "Ku noqo adeegyada hore")],
            "5️⃣ Soo geli daymo hore (IMPORT)\n6️⃣ Liiska lacag-bixinta\n7️⃣ Ku noqo"
        ),
    }
    body, buttons, fallback_lines = pages.get(page, pages[1])
    return send_deynjir_choice_buttons(
        to_phone, body, buttons,
        fallback_lines + "\n\nSoo dir lambarka adeegga."
    )


def send_deynjir_choice_buttons(to_phone, body, buttons, fallback_text):
    """Send contextual WhatsApp reply buttons; preserve a text fallback."""
    clean_phone = str(to_phone).replace("+", "").split("@")[0].strip()
    if GREEN_API_TOKEN:
        url = f"{GREEN_API_BASE}/waInstance{INSTANCE_ID}/sendInteractiveButtonsReply/{GREEN_API_TOKEN}"
        payload = {
            "chatId": f"{clean_phone}@c.us",
            "header": "Deynjir",
            "body": body,
            "footer": "Dooro badhanka hoose",
            "buttons": [
                {"buttonId": str(button_id), "buttonText": str(button_text)}
                for button_id, button_text in buttons
            ],
        }
        try:
            response = requests.post(url, json=payload, timeout=10)
            print(f"📡 Green-API contextual buttons: {response.status_code} - {response.text}")
            if response.ok and response.json().get("idMessage"):
                return True
        except Exception as exc:
            print(f"⚠️ Contextual buttons unavailable; using text fallback: {type(exc).__name__}: {exc}")
    send_whatsapp(to_phone, fallback_text)
    return False


def send_deynjir_main_menu(to_phone):
    """Send exactly three WhatsApp reply buttons; use text if API sending fails."""
    clean_phone = str(to_phone).replace("+", "").split("@")[0].strip()
    if GREEN_API_TOKEN:
        url = f"{GREEN_API_BASE}/waInstance{INSTANCE_ID}/sendInteractiveButtonsReply/{GREEN_API_TOKEN}"
        payload = {
            "chatId": f"{clean_phone}@c.us",
            "header": "Deynjir",
            "body": "Maxaad rabtaa inaad qabato?",
            "footer": "Dooro mid ka mid ah adeegyada",
            "buttons": [
                {"buttonId": "1", "buttonText": "Deyn cusub"},
                {"buttonId": "2", "buttonText": "Dayn soo xarootay"},
                {"buttonId": "3", "buttonText": "Adeeg kale"},
            ],
        }
        try:
            response = requests.post(url, json=payload, timeout=10)
            print(f"📡 Green-API interactive menu: {response.status_code} - {response.text}")
            if response.ok and response.json().get("idMessage"):
                try:
                    schedule_pending_reply_reminder(clean_phone, "Maxaad rabtaa inaad qabato?")
                except Exception as reminder_error:
                    print(f"⚠️ Menu reminder scheduling failed: {reminder_error}")
                return True
        except Exception as exc:
            print(f"⚠️ Interactive menu unavailable; using text fallback: {type(exc).__name__}: {exc}")
    return send_whatsapp(to_phone, deynjir_main_menu())

def deynjir_recovery_menu_message(intro=None):
    """Recovery prompt aligned with the same three-choice menu routing."""
    prefix = (str(intro).strip() + "\n\n") if intro else ""
    return prefix + deynjir_main_menu()

def deynjir_unrecognized_message():
    """One concise clarification; never display a menu or create hidden menu state."""
    return "Ma fahmin fariintaas. Ma ii caddayn kartaa waxa aad rabto?"


def pause_guided_session_for_replacement(sender_phone):
    """End the previous guided flow when a new one starts; do not stack workflows."""
    GUIDED_SESSIONS.pop(sender_phone, None)
    PAUSED_GUIDED_SESSIONS.pop(sender_phone, None)


def restore_paused_guided_session(sender_phone):
    """Legacy compatibility: discard old paused state instead of resurrecting it."""
    PAUSED_GUIDED_SESSIONS.pop(sender_phone, None)


def activate_guided_menu(sender_phone):
    """Make the next numeric reply a valid choice after showing the action menu."""
    pause_guided_session_for_replacement(sender_phone)
    GUIDED_SESSIONS[sender_phone] = {
        "stage": "menu",
        "expires_at": datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL,
    }


def deynjir_help_message():
    return (
        "ℹ️ *Raac Tilmaamahan*\n\n"
        "• Deyn cusub: qor *Cali $50 deyn cusub* ama *ADD Cali $50*\n"
        "• Lacag bixin: qor *Cali $20 ayuu bixiyey* ama *Lacag bixin Cali $20*\n"
        "• Daymihii hore: qor *IMPORT* (sawir, Excel ama qoraal)\n"
        "• Liiska daynta: qor *LIISKA DAYNTA*\n"
        "• Raadi qof: qor *Raadi Cali*\n"
        "• Faahfaahin: qor *FAAHFAAHIN Cali*\n"
        "• Ballamaha: qor *Balamaha Maanta* ama *Balamaha Berri*\n"
        "• Soo geli sawir/Excel: qor *IMPORT*\n"
        "• Dhigaal macmiil: qor *DHIGAAL Cali $100*\n"
        "• Ka noqo macaamilkii ugu dambeeyay: qor *UNDO Cali*\n\n"
        "Soo Qor *MENU* marka aad u baahato hagid."
    )


def deynjir_confusion_help_message():
    return (
        "*Dhib ma leh, waan ku caawinayaa*.\n\n"
        "Nidaamkan wuxuu kaa Sahlayaa inaad\n"
        "diiwaangeliso daymaha, lacag-bixinta iyo balamaha Ganacsigaaga.\n\n"
        "Tusaale:\n"
        "Waxaad Dayn $10 ku leedahay Qof lagu magacaabo Cali.\n"
        "si aad Nidaamka ugu darto soo Qor:\n"
        "*ADD Cali $10*\n\n"
        "Haddii Cali bixiyay $5, soo qor:\n\n"
        "*Lacag bixin Cali $5*"
    )


def is_somali_confusion_request(message_text):
    """Recognize first-time/help requests despite common Somali spelling variations."""
    text = normalize_customer_name(str(message_text or "")).strip()
    if not text:
        return False
    patterns = (
        r"\bbarnaamijka\s+(?:waxba\s+)?ma\s+fahmin\b",
        r"\bbarnaamijka\s+waxba\s+kama\s+fahmin\b",
        # Accept natural variants/typos such as isticmaalmo, isticmaalain, isticmalin.
        r"\b(?:anigu\s+)?(?:horay|hore)\s+uma\s+istic\w*\b",
        r"\b(?:anigu\s+)?(?:waligay|weligay)\s+ma\s+istic\w*\b",
        r"\b(?:anigu\s+)?ma\s+istic\w*\b",
        r"\bmarkii\s+ugu\s+horraysay\s+ayaan\s+istic\w*\b",
        r"\b(?:waxba\s+kama\s+fahmin|ma\s+fahmin|ma\s+garanayo|ma\s+aqaan)\b",
        r"\bsidee\s+(?:loo\s+)?istic\w*\b",
        r"\bmaxaan\s+sameeyaa\b",
        r"\bii\s+sharax\b",
        r"\bi\s+fahan(?:\s+dee)?\b",
        r"\bi\s+fahamsii(?:\s+dee)?\b",
        r"\bii\s+fahan(?:\s+dee)?\b",
        r"\bma\s+i\s+fahmin\b",
    )
    if any(re.search(pattern, text, flags=re.I) for pattern in patterns):
        return True
    # Catch short misspellings of the common first-time phrase without matching
    # unrelated transaction messages.
    compact = re.sub(r"[^a-z]", "", text.casefold())
    return (
        "horay" in text
        and "uma" in text
        and difflib.SequenceMatcher(None, compact, "aniguhorayum isticmaalin".replace(" ", "")).ratio() >= 0.78
    )



def is_explicit_exit_or_block_request(message_text):
    """Detect clear requests to leave/stop/block before customer-name or AI parsing."""
    text = normalize_customer_name(str(message_text or "")).strip()
    exact_phrases = {
        "naga tag", "naga daa", "iga tag", "bax", "ka bax", "iska daa",
        "i dhaaf", "block", "block garee", "i block garee", "block me",
        "leave me alone", "stop messaging", "stop contacting me",
        "ha ii soo qorin", "ha i soo qorin", "ha ii soo dirin",
        "jooji wada hadalka", "jooji isticmaalka",
    }
    return text in exact_phrases or bool(re.fullmatch(
        r"(?:fadlan\s+)?(?:naga\s+tag|iga\s+tag|i\s+dhaaf|ka\s+bax|"
        r"block(?:\s+garee)?|i\s+block\s+garee|leave\s+me\s+alone|"
        r"stop\s+(?:messaging|contacting\s+me)|ha\s+(?:ii|i)\s+soo\s+(?:qorin|dirin))",
        text, re.I
    ))


def is_user_frustrated(message_text):
    """Conservative frustration detector; does not treat every 'maya' as anger."""
    text = normalize_customer_name(str(message_text or ""))
    patterns = (
        r"\bwaan\s+xanaaqay\b", r"\bwaan\s+ku\s+daalay\b",
        r"\bwaad\s+i\s+wareerisay\b", r"\bi\s+wareerisay\b",
        r"\bwaan\s+ku\s+wareeray\b", r"\bnidaamku\s+wuu\s+i\s+wareeriyay\b",
        r"\bway\s+igu\s+adagtahay\b", r"\bwaa\s+igu\s+adag\b",
        r"\bma\s+shaqeynayo\b", r"\bma\s+shaqaynayo\b",
        r"\bwaxba\s+ma\s+shaqeeyaan\b", r"\bwaxba\s+ma\s+shaqeynayaan\b",
        r"\bwaxba\s+ma\s+shaqaynayaan\b", r"\bma\s+fahmaysid\b",
        r"\bwaad\s+fahmi\s+la\s+dahay\b", r"\bwaa\s+iga\s+wareer\b",
    )
    return any(re.search(pattern, text, re.I) for pattern in patterns)


def clear_sender_workflow_sessions(sender_phone):
    """Clear only unfinished conversations; never touch committed financial records."""
    for session_map in WORKFLOW_SESSION_MAPS:
        session_map.pop(sender_phone, None)
    LAST_TRANSACTION_CONTEXT.pop(sender_phone, None)
    LAST_BATCH_CONTEXT.pop(sender_phone, None)
    LAST_SELECTED_CUSTOMERS.pop(sender_phone, None)
    LAST_HISTORY_REQUESTS.pop(sender_phone, None)


def cancel_sender_pending_database_work(sender_phone, business_user_id):
    """Cancel uncommitted payment/transaction proposals for this sender and shop."""
    try:
        (supabase.table("pending_payment_confirmations")
            .update({
                "status": "rejected",
                "actor_phone": str(sender_phone),
                "processed_at": datetime.now(timezone.utc).isoformat(),
            })
            .eq("sender_phone", str(sender_phone))
            .eq("business_user_id", str(business_user_id))
            .eq("status", "pending")
            .execute())
    except Exception as exc:
        print(f"⚠️ Could not cancel pending payment proposals for exit request: {exc}")
    try:
        (supabase.table("pending_transaction_clarifications")
            .delete()
            .eq("sender_phone", str(sender_phone))
            .eq("business_user_id", str(business_user_id))
            .execute())
    except Exception as exc:
        print(f"⚠️ Could not clear pending transaction clarification for exit request: {exc}")


def normalize_easy_command(value):
    """Normalize a small, explicit set of common Somali typing mistakes."""
    raw = " ".join(str(value or "").strip().split())
    folded = raw.casefold().strip(" .!؟?")
    aliases = {
        "inbort": "IMPORT", "inport": "IMPORT", "importi": "IMPORT",
        "menu": "MENU", "manu": "MENU", "menyu": "MENU", "menue": "MENU",
        "caawi": "HELP", "caawimaad": "HELP",
        "help me": "HELP",
        "lacag bixn": "GUIDED_PAYMENT",
        "lacag bixinta": "LIISKA LACAG BIXINTA",
        "ku dar deyn": "GUIDED_DEBT", "ku dar dayn": "GUIDED_DEBT",
        "balanta beri": "BALAMAHA BERRI", "ballanta beri": "BALAMAHA BERRI",
        "balamaha beri": "BALAMAHA BERRI", "ballamaha beri": "BALAMAHA BERRI",
        "balanta berri": "BALAMAHA BERRI", "ballanta berri": "BALAMAHA BERRI",
        "balamaha berri": "BALAMAHA BERRI", "ballamaha berri": "BALAMAHA BERRI",

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
# Financial request context is isolated per async webhook request.
# The same Green-API event ID produces the same request IDs when retried.
_FINANCIAL_REQUEST_CONTEXT = ContextVar("deynjir_financial_request_context", default=None)

_FINANCIAL_RPC_MAP = {
    "record_debt_addition": "record_debt_addition_idempotent",
    "record_debt_payment_with_history": "record_debt_payment_idempotent",
    "record_customer_credit_deposit": "record_customer_credit_deposit_idempotent",
    "create_customer_with_credit_deposit": "create_customer_with_credit_deposit_idempotent",
    "correct_customer_transaction_amount": "correct_customer_transaction_amount_idempotent",
    "undo_customer_transaction_confirmed": "undo_customer_transaction_confirmed_idempotent",
    "undo_debt_batch_confirmed": "undo_debt_batch_confirmed_idempotent",
    "record_debt_addition_batch": "record_debt_addition_batch_idempotent",
    "record_debt_payment_batch_with_history": "record_debt_payment_batch_idempotent",
}

def _financial_request_id(operation, explicit_id=None):
    if explicit_id:
        return str(explicit_id)[:240]
    context = _FINANCIAL_REQUEST_CONTEXT.get() or {}
    event_id = str(context.get("event_id") or "")
    if not event_id:
        # Non-webhook callers should pass an explicit durable ID whenever they
        # can retry. A random fallback avoids accidental collisions but cannot
        # make an ID-less external delivery retry-safe.
        return f"adhoc:{operation}:{secrets.token_urlsafe(18)}"
    counts = context.setdefault("counts", {})
    index = counts.get(operation, 0) + 1
    counts[operation] = index
    digest = hashlib.sha256(event_id.encode("utf-8")).hexdigest()
    return f"wa:{digest}:{operation}:{index}"

def _financial_rpc(function_name, params, request_id=None):
    """Call an idempotent SQL wrapper for every financial write."""
    wrapper = _FINANCIAL_RPC_MAP.get(function_name)
    if not wrapper:
        raise ValueError(f"No idempotent SQL wrapper configured for {function_name}")
    payload = dict(params or {})
    explicit_id = request_id or payload.pop("__request_id", None)
    payload["p_request_id"] = _financial_request_id(function_name, explicit_id)
    return supabase.rpc(wrapper, payload)

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
- Never include transaction wording in customer_name. In particular, remove "deyn cusub", "dayn cusub", "oo", "ah", and action phrases such as "wuxuu qaatay" from the END of a name. Examples: "omar wuxuu qaatay deyn cusub oo $35 ah" -> customer_name="omar", amount=35; "Cumar 35" -> customer_name="Cumar", amount=35; "Omar $35" -> customer_name="Omar", amount=35. Never save "omar deyn cusub oo" as a customer name.
- Negative/no-activity statements are status information, not transactions. Understand natural variations of negated activity wording (for example, no money was received, no customer repaid, no new debt, or nothing happened today), including informal word order and spelling. Do not create ADD or PAY from them. If a guided workflow is waiting, interpret the reply against that stage; if it clearly reports no activity, end the unfinished flow without saving. If the user says the previous reply was not a name, never use that sentence as a customer name.
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

DEYNJIR_ASSISTANT_PROMPT = """You are Deynjir, a concise, friendly Somali-speaking assistant for a shopkeeper's business.
You are speaking to the BUSINESS OWNER, not to a customer. Deynjir helps the shopkeeper record customer debts, record money customers pay back, view unpaid customer debts, search customer balances and payment history, manage promised payment dates, reminders, and import customer debt/payment lists from Excel or images.

BUSINESS PERSPECTIVE:
- The shopkeeper is the creditor. Customers may owe money to the shop.
- ADD means a customer takes goods/money on credit; the shop's receivable increases.
- PAY means the customer pays money back to the shop; the receivable decreases.
- "Deymaha maqan" means outstanding customer debts owed to the shop.
- In this Deynjir business context, "Yaan weli deyn ku leeyahay?" is a request to view outstanding customer debts.
- Never say that the shopkeeper owes customers money unless the user explicitly describes that separate situation.

HOW TO RESPOND:
- Reply in natural, correct, simple Somali unless the user writes in another language.
- Be warm, respectful, short, and practical. Do not give a numbered command menu unless the user explicitly asks for the menu.
- Keep EVERY reply extremely short: one or two sentences, ideally 10-20 words total, and never more than 220 characters.
- Answer only what the user asked. Do not repeat the user's question, introduce yourself again, list features, or add examples unless needed.
- If a user is new, give just one simple next step and at most one short example.
- If confused or frustrated, acknowledge briefly and give one helpful next step. No menus.
- If the user says "haye", "ok", "okay", "waa hagaag", "mahadsanid", or another acknowledgement, reply naturally and briefly. Do not start a new debt/payment workflow unless the user clearly asks.
- After a debt or payment is successfully recorded, do not assume the user wants to record another one. A simple acknowledgement means acknowledge and wait.
- When describing money owed to the shop, use natural wording such as "lacagta lagu leeyahay" or "deynta lagu leeyahay"; avoid reversing the shopkeeper/customer perspective.
- If the user's intent is unclear, ask one short question. Do not invent a transaction or turn an acknowledgement into ADD/PAY.
- If the user reports no activity in natural or misspelled wording, acknowledge briefly; do not ask for an amount, treat the statement as a customer name, open another workflow, or claim database facts.
- If the user corrects that a reply was not a name, ask for the actual customer name only when a name is currently required.
- Do not claim that a debt/payment was saved. Python handles all financial writes and confirmations.
- Do not invent balances, customer names, counts, payment records, due dates, or capabilities.
- For live business data, answer only after the application has routed the request to its database handler. Otherwise ask one short clarification.
- Never output JSON, action labels, headings, feature lists, or internal implementation details.
"""


def generate_deynjir_conversation_reply(message_text, fallback=None, sender_phone=None):
    """Generate a short, context-aware reply; this helper cannot write financial data."""
    if not GEMINI_API_KEY:
        if sender_phone and fallback:
            now = datetime.now(timezone.utc)
            previous = CONVERSATION_SESSIONS.get(str(sender_phone), {})
            history = list(previous.get("history") or [])
            history.extend([
                {"role": "user", "text": str(message_text or "")[:1500]},
                {"role": "model", "text": str(fallback)[:220]},
            ])
            CONVERSATION_SESSIONS[str(sender_phone)] = {
                "history": history[-8:],
                "expires_at": now + CONVERSATION_SESSION_TTL,
            }
        return fallback
    try:
        now = datetime.now(timezone.utc)
        session = CONVERSATION_SESSIONS.get(str(sender_phone)) if sender_phone else None
        if session and (not session.get("expires_at") or now > session["expires_at"]):
            CONVERSATION_SESSIONS.pop(str(sender_phone), None)
            session = None

        history = list((session or {}).get("history") or [])[-8:]
        contents = []
        for turn in history:
            role = turn.get("role")
            text_value = str(turn.get("text") or "").strip()
            if role in {"user", "model"} and text_value:
                contents.append({"role": role, "parts": [{"text": text_value[:700]}]})
        current_text = str(message_text or "").strip()[:1500]
        contents.append({"role": "user", "parts": [{"text": current_text}]})

        contextual_prompt = DEYNJIR_ASSISTANT_PROMPT + """

CONVERSATION CONTINUITY:
- You receive recent messages in chronological order. The last user message is the one to answer.
- Resolve short or indirect follow-ups from the preceding conversation, including references such as 'that', 'it', 'how?', 'tell me', 'what else?', 'no', and 'yes'.
- Keep the same topic when the user is following up; change topic when the user clearly introduces a new one.
- Do not ask the user to repeat context that is already in the conversation.
- If the meaning is genuinely unclear, ask one brief clarifying question instead of showing a menu.
- Never treat conversational context as authorization to create, edit, delete, or pay a financial record.
"""
        url = (
            "https://generativelanguage.googleapis.com/v1beta/"
            f"models/{GEMINI_MODEL}:generateContent"
        )
        response = requests.post(
            url,
            headers={
                "x-goog-api-key": GEMINI_API_KEY,
                "Content-Type": "application/json",
            },
            json={
                "systemInstruction": {"parts": [{"text": contextual_prompt}]},
                "contents": contents,
                "generationConfig": {"temperature": 0.2, "maxOutputTokens": 80},
            },
            timeout=20,
        )
        response.raise_for_status()
        data = response.json()
        parts = data.get("candidates", [{}])[0].get("content", {}).get("parts", [])
        answer = " ".join(
            str(part.get("text") or "").strip()
            for part in parts if isinstance(part, dict) and part.get("text")
        ).strip()
        if not answer:
            return fallback
        answer = answer.strip().strip('"')
        if answer.startswith("[") or answer.startswith("{"):
            return fallback
        sentence_parts = re.split(r"(?<=[.!?؟])\s+", answer)
        answer = " ".join(part.strip() for part in sentence_parts[:2] if part.strip())
        if len(answer) > 220:
            shortened = answer[:217].rsplit(" ", 1)[0].rstrip(" ,;:-")
            answer = (shortened or answer[:217].rstrip()) + "…"

        if sender_phone:
            updated_history = history + [
                {"role": "user", "text": current_text},
                {"role": "model", "text": answer},
            ]
            CONVERSATION_SESSIONS[str(sender_phone)] = {
                "history": updated_history[-8:],
                "expires_at": now + CONVERSATION_SESSION_TTL,
            }
        return answer
    except Exception as exc:
        print(f"⚠️ Deynjir conversational assistant unavailable: {type(exc).__name__}: {exc}")
        if sender_phone and fallback:
            now = datetime.now(timezone.utc)
            previous = CONVERSATION_SESSIONS.get(str(sender_phone), {})
            history = list(previous.get("history") or [])
            history.extend([
                {"role": "user", "text": str(message_text or "")[:1500]},
                {"role": "model", "text": str(fallback)[:220]},
            ])
            CONVERSATION_SESSIONS[str(sender_phone)] = {
                "history": history[-8:],
                "expires_at": now + CONVERSATION_SESSION_TTL,
            }
        return fallback


def remember_conversation_outcome(sender_phone, user_message, bot_message):
    """Keep the latest committed result as context for short natural follow-ups."""
    key = str(sender_phone)
    now = datetime.now(timezone.utc)
    previous = CONVERSATION_SESSIONS.get(key, {})
    history = list(previous.get("history") or [])
    user_text = str(user_message or "").strip()[:1500]
    bot_text = str(bot_message or "").strip()[:220]
    if user_text:
        history.append({"role": "user", "text": user_text})
    if bot_text:
        history.append({"role": "model", "text": bot_text})
    CONVERSATION_SESSIONS[key] = {
        "history": history[-8:],
        "expires_at": now + CONVERSATION_SESSION_TTL,
    }


def is_simple_acknowledgement(message_text):
    """Recognize brief acknowledgements and common Somali refusal spellings."""
    text = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
    return text in {
        "haye", "haaaye", "ok", "okay", "oke", "wa hagaag", "waa hagaag",
        "hagaag", "sax", "fiican", "mahadsanid", "mahadsanidiin",
        "haa", "yes", "yep", "maya", "may", "no", "nah",
        "thanks", "thank you", "thx", "noted", "understood", "alright",
        "good", "waa sax", "waa hagaag mahadsanid",
    }


def is_user_declining_help(message_text):
    """Recognize common Somali refusals without treating them as financial commands."""
    text = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
    exact = {
        "midna ma rabo", "waxba ma rabo", "ma rabo",
        "midna ma doonayo", "waxba ma doonayo", "ma doonayo",
        "midna uma baahni", "uma baahni",
        "maya", "may", "mayaa", "no", "nah", "maya mahadsanid", "may mahadsanid",
        "maya mahadsanidiin", "may mahadsanidiin",
        "may ma rabo", "maya ma rabo", "may ayaan ku idhi",
        "maya ayaan ku idhi", "may ayaan ku iri", "maya ayaan ku iri",
    }
    if text in exact:
        return True
    return bool(re.fullmatch(
        r"(?:(?:may|maya|mayaa)\s+)?(?:midna\s+)?"
        r"(?:ma\s+rabo|ma\s+doonayo|uma\s+baahni|"
        r"ayaan\s+ku\s+(?:idhi|iri)|baan\s+ku\s+(?:idhi|iri))",
        text, flags=re.I,
    ))


def is_contextual_followup(message_text, sender_phone):
    """Identify a short natural follow-up only when a recent chat context exists."""
    session = CONVERSATION_SESSIONS.get(str(sender_phone))
    if not session or not session.get("history"):
        return False
    expires_at = session.get("expires_at")
    if expires_at and datetime.now(timezone.utc) > expires_at:
        CONVERSATION_SESSIONS.pop(str(sender_phone), None)
        return False
    text = str(message_text or "").strip()
    if not text or len(text) > 140:
        return False
    normalized = normalize_customer_name(text).strip(" .!?؟")
    # Never intercept numeric menu choices, financial entries, or explicit commands.
    if re.fullmatch(r"\d+", normalized):
        return False
    if re.search(r"\$\s*\d|\b\d+(?:[.,]\d{1,2})?\s*(?:dollar|doolar|shilin)?\b", normalized, re.I):
        return False
    if re.match(r"^(?:add|pay|deyn|lacag bixin|liiska|raadi|search|faahfaahin|history|report|export|import|undo|delete|edit|dhigaal|menu|start|help)\b", normalized, re.I):
        return False
    # Very short turns are often contextual; longer turns need a clear conversational cue.
    short_turn = len(normalized.split()) <= 6
    followup_cue = bool(re.search(
        r"\b(sidee|haddaba|markaas|marka|haddii|sidaas|taas|taasi|isaga|iyada|kuwaas|maxaa kale|ka waran|ii sheeg|ii sharax|ii faahfaahi|tusaale|faahfaahi|ma fahmin|maxaad ula jeeddaa|maxay ka dhigan tahay|ma ii sharxi kartaa|sax miyaa|run miyaa|haye|maya|haa|how|why|what about|what if|tell me more|explain|what do you mean|and then)\b",
        normalized, re.I
    ))
    return short_turn or followup_cue


def is_natural_top_debt_question(message_text):
    text = normalize_customer_name(str(message_text or ""))
    patterns = (
        r"yaa ugu badan dadka lacagta igu leh",
        r"yaa ugu badan lacagta igu leh",
        r"qofkee lacagta ugu badan igu leh",
        r"qofka lacagta ugu badan igu leh",
        r"yaa deynta ugu badan leh",
        r"yaa ugu deyn badan",
        r"macmiilkee deynta ugu badan leh",
        r"qofkee ugu badan deyn igu leh",
    )
    return any(re.search(pattern, text, re.I) for pattern in patterns)


def is_natural_today_payment_question(message_text):
    text = normalize_customer_name(str(message_text or ""))
    has_today = bool(re.search(r"\b(maanta|today)\b", text, re.I))
    has_payment = bool(re.search(
        r"(lacag(?:aha|ihii|ta)?|lacag bixin(?:ta|no)?|bixiyay|qabtay|soo xarootay)",
        text, re.I
    ))
    return has_today and has_payment and bool(re.search(
        r"(ogaado|ogaan|ii sheeg|imisa|inte[e]?|liis|lacagihii|lacagaha|qabtay|soo xarootay)",
        text, re.I
    ))


def classify_no_activity_statement(message_text):
    """Classify a non-transaction statement; never infer or create a transaction.

    Uses broad negation/activity grammar rather than a closed list of exact
    example sentences. The result is acknowledgement-only, never a DB action.
    """
    text = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
    if not text:
        return None

    payment_patterns = (
        r"\b(?:maanta\s+)?waxba\s+ma\s+(?:bixin|bixinin|keenin|helin)\b",
        r"\b(?:deyn|dayn|lacag)\b.{0,35}\b(?:igama|iigama|iima|ima)\b.{0,25}\b(?:bixin|bixinin|keenin|soo\s+celin|helin)\b",
        r"\b(?:igama|iima|ima)\s+(?:bixin|bixinin|keenin|soo\s+celin|helin)\b",
        r"\b(?:ma|lama)\s+(?:bixin|bixinin|keenin|soo\s+celin|helin|soo\s+gelin|soo\s+xaroon)\b",
        r"\b(?:wali\s+)?(?:[a-z]+\s+){0,4}(?:ma\s+bixin|ma\s+keenin|ma\s+soo\s+celin)\b",
        r"\b(?:lacag|lacagta|lacagtii)\b.{0,45}\b(?:ma\s+(?:bixin|soo\s+gelin|soo\s+xaroon|helin|jirto|jiraan)|lama\s+(?:bixin|helin)|baxday\s+ma\s+jirto)\b",
        r"\b(?:cidna|cidina|qofna|macmiilna)\b.{0,35}\b(?:waxba\s+)?(?:ma\s+bixin|ima\s+soo\s+celin|ma\s+keenin)\b",
        r"\b(?:waxba|wax\s+lacag\s+ah)\s+(?:lama\s+helin|ma\s+(?:soo\s+gelin|soo\s+xaroon|iman))\b",
        r"\b(?:lacag\s+bixin|lacagtii?\s+hore)\s+ma\s*(?:jirto|jiraan|dhicin)\b",
    )
    debt_patterns = (
        r"\b(?:deyn|dayn)\s+(?:cusub\s+)?ma\s*(?:jirto|jiraan|dhicin)\b",
        r"\bwax\s+(?:deyn|dayn)\s+(?:cusub\s+)?ah\s+ma\s*(?:jirto|jiraan)\b",
    )
    general_patterns = (
        r"\bmaanta\s+waxba\s+ma\s+(?:jiraan|dhicin)\b",
        r"\bwaxba\s+ma\s+(?:jiraan|dhicin)\b",
        r"\bwax\s+dhaqdhaqaaq\s+ah\s+ma\s+jiro\b",
        r"\bmaanta\s+(?:wax\s+)?dhaqdhaqaaq\s+ma\s+jiro\b",
    )
    if any(re.search(pattern, text, re.I) for pattern in payment_patterns):
        return "payment"
    if any(re.search(pattern, text, re.I) for pattern in debt_patterns):
        return "debt"
    if any(re.search(pattern, text, re.I) for pattern in general_patterns):
        return "general"
    return None


def is_no_activity_reply(message_text):
    """True when the user reports no activity, not a financial transaction."""
    return classify_no_activity_statement(message_text) is not None


def is_guided_name_correction(message_text):
    """Recognize that the previous reply was not a customer name."""
    text = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
    return bool(re.search(
        r"^(?:(?:taasi|taas|kan|ta)\s+)?(?:magac(?:a)?\s+)?"
        r"(?:maaha|ma\s+aha|ma\s+ahan)(?:\s+magac)?$|"
        r"^ma\s+aha\s+magac$",
        text, re.I,
    ))


def is_deynjir_greeting(message_text):
    text = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
    exact = {"salaan", "waan ku salaamay", "waan ku salaamay walaal", "asalaamu calaykum", "assalamu alaikum", "asc", "subax wanaagsan", "galab wanaagsan", "habeen wanaagsan", "hello", "hi", "hey", "good morning", "good afternoon", "good evening"}
    return text in exact or bool(re.fullmatch(r"waan\s+ku\s+salaamay(?:\s+walaal)?", text, re.I))


def parse_customer_account_request(message_text):
    """Recognize a request for a customer's full account/statement and extract its name if supplied.

    Returns (is_account_request, customer_name). A missing name is never guessed.
    """
    raw = " ".join(str(message_text or "").strip().split())
    text = normalize_customer_name(raw).strip(" .!?؟")
    if not text:
        return False, None

    has_account_word = bool(re.search(
        r"\b(?:xisaab(?:ta|tiisa|teeda)?|faahfaahin(?:ta)?|statement|account)\b",
        text, re.I,
    ))
    has_customer_word = bool(re.search(r"\b(?:macmiil(?:ka|kaas|kiisa|keeda)?|customer|client)\b", text, re.I))
    has_account_intent = has_account_word and (
        has_customer_word
        or bool(re.search(r"\b(?:rabaa|rabo|doonayaa|doonayso|ii\s+sheeg|ii\s+muuji|i\s+tus|sidee|sideen|hel[a]?a?|heli)\b", text, re.I))
        or text.startswith(("xisaabta ", "xisaab ", "faahfaahinta ", "statement ", "account "))
    )
    if not has_account_intent:
        return False, None

    # Remove request wording and generic nouns; whatever remains is the name.
    name = text
    name = re.sub(
        r"\b(?:waxaan|waxan|waan|aniga|fadlan|hadda|rabaa|rabo|doonayaa|doonayso|"
        r"sidee|sideen|ku|u|helaa|hela|heli|helayaa|helikaraa|ka|ii|i|sheeg|muuji|tus|"
        r"xisaabta|xisaab|xisaabtiisa|xisaabteeda|faahfaahinta|faahfaahin|statement|account|"
        r"macmiilka|macmiil|customer|client)\b",
        " ", name, flags=re.I,
    )
    name = re.sub(r"[^\w\s'-]", " ", name, flags=re.UNICODE)
    name = " ".join(name.split()).strip(" -_'")
    if name.casefold() in {"", "ka", "macmiil", "macmiilka", "customer", "client"}:
        name = ""
    return True, (name or None)


def is_privacy_question(message_text):
    text = normalize_customer_name(str(message_text or ""))
    patterns = (
        r"\b(?:xogtayda|xogteyda|xogtayada|xogta\s+aan\s+leeyahay|macluumaadkayga)\b.*\b(?:yaa|cid|arki|arkaya|arag|heli|geli|wadaag)\b",
        r"\b(?:yaa|cid)\b.*\b(?:xogta|macluumaadka)\b.*\b(?:arki|arkaya|arag|heli|geli|wadaag)\b",
        r"\b(?:amniga|ammaanka|amnigiisa|amnigeeda|security|privacy)\b",
        r"\b(?:xogtayda|xogta)\b.*\b(?:ammaan|amn|secure|safe)\w*\b",
    )
    return any(re.search(pattern, text, re.I) for pattern in patterns)


def is_bare_ambiguous_debt_request(message_text):
    return normalize_customer_name(str(message_text or "")).strip(" .!?؟") in {"deyn", "dayn"}


def is_postponing_guided_task(message_text):
    text = normalize_customer_name(str(message_text or ""))
    testing = bool(re.search(r"\b(?:waan\s+)?tijaabin(?:ayay|ayayey|ayayay|ayay)\b", text))
    later = bool(re.search(r"\b(?:hadhow|mar\s+dambe)\b", text))
    task = bool(re.search(r"\b(?:deyn|dayn|xareyn|diiwaangelin|gelin)\b", text))
    return testing or (later and task)


def is_deynjir_general_question(message_text):
    text = normalize_customer_name(str(message_text or ""))
    patterns = (
        r"\bmaxaad\s+(?:ii\s+)?qaban kartaa\b",
        r"\bmaxaad\s+qabataa\b",
        r"\bmaxaad\s+samaysaa\b",
        r"\bmaxaad\s+(?:ii\s+)?tartaa\b",
        r"\bmaxaad tahay\b",
        r"\b(?:adigu\s+)?yaad\s+tahay\b",
        r"\badeeg(?:ga)?(?:una)?\s*(?:waa\s+)?(?:maxay|noocma)?\b",
        r"\bsystem(?:kan|kani|kaani)?\s+(?:waa\s+)?nooc(?:ma|kee)?\b",
        r"\bnidaam(?:kan|kani)?\s+(?:waa\s+)?nooc(?:ma|kee)?\b",
        r"\bsidee(?:\s+bu[u]?|\s+baa)?\s+(?:(?:nidaam(?:kani|kan|ku|ka|kuba)?|deynjir)\s+)?(?:u\s+)?shaqeey\w*\b",
        r"\bsidee\s+(?:bu[u]?\s+)?u\s+shaqeey\w*\b",
        r"\bwaa maxay deynjir\b",
        r"\bmaxaan kaa heli karaa\b",
        r"\bmaxaa la sameeyaa\b",
        r"\bma khasab baa inaan amarro qoro\b",
        r"\bma khasab baa amarro\b",
        r"\bsidee baan ku bilaabaa\b",
        r"\bsideen ku bilaabaa\b",
    )
    return any(re.search(pattern, text, re.I) for pattern in patterns)


def send_top_outstanding_debtors(sender_phone, business_user_id, limit=1):
    """Read-only ranking of customers with the largest unpaid balances."""
    result = (supabase.table("customers")
        .select("name, amount, is_paid")
        .eq("business_user_id", str(business_user_id))
        .eq("is_archived", False)
        .eq("is_paid", False)
        .execute())
    totals = {}
    display_names = {}
    for row in result.data or []:
        amount = float(row.get("amount") or 0)
        if not math.isfinite(amount) or amount <= 0:
            continue
        name = str(row.get("name") or "Macmiil").strip()
        key = normalize_customer_name(name) or name.casefold()
        totals[key] = totals.get(key, 0.0) + amount
        display_names.setdefault(key, name)
    ranked = sorted(totals.items(), key=lambda item: item[1], reverse=True)
    if not ranked:
        send_whatsapp(sender_phone, "✅ Hadda ma jiraan macaamiil leh deyn furan oo la diiwaangeliyey.")
        return {"status": "no_outstanding_debtors"}
    lines = ["🏆 *Macmiilka deynta ugu badan kugu leh*", ""]
    for index, (key, amount) in enumerate(ranked[:limit], 1):
        lines.append(f"{index}. {display_names[key]} — *${amount:,.2f}*")
    if len(ranked) > 1:
        lines.extend(["", "Haddii aad rabto, waxaan kuu soo bandhigi karaa macaamiisha kale ee deynta ugu badan leh."])
    send_whatsapp(sender_phone, "\n".join(lines))
    return {"status": "top_outstanding_debtors_sent", "count": len(ranked)}


def send_today_payment_summary(sender_phone, business_user_id):
    """Read-only summary of today's actual payments from the payment ledger."""
    today = today_eat()
    records = _load_shop_payments(business_user_id, today, today)
    if not records:
        send_whatsapp(sender_phone, "Maanta weli wax lacag-bixin ah laguma diiwaangelin.")
        return {"status": "no_payments_today"}
    total = sum(float(row.get("amount") or 0) for row in records)
    lines = [f"💵 *Lacag-bixintii maanta ({today:%d/%m/%Y})*", ""]
    for index, row in enumerate(records, 1):
        lines.append(f"{index}. {row.get('name') or 'Macmiil'} — *${float(row.get('amount') or 0):,.2f}*")
    lines.extend(["", f"💰 Wadarta maanta: *${total:,.2f}*", f"📋 Tirada lacag-bixinta: *{len(records)}*"])
    send_whatsapp(sender_phone, "\n".join(lines))
    return {"status": "today_payment_summary_sent", "count": len(records), "total": total}



def is_clear_new_supported_request(message_text, include_transactions=True):
    """Conservative pre-router: identify a new supported request, not a bare answer/name."""
    raw = " ".join(str(message_text or "").strip().split())
    if not raw:
        return False
    folded = normalize_customer_name(raw).strip(" .!?؟")
    if is_no_activity_reply(raw) or is_guided_name_correction(raw):
        return False
    if parse_transaction_clarification(raw) in {"ADD", "PAY", "CANCEL"}:
        return False
    if folded in {
        "haa", "h", "yes", "y", "ok", "okay", "sax", "maya", "may", "no", "n",
        "jooji", "cancel", "baaji", "stop", "1", "2", "3", "haa tirtir",
        "haa dir", "ok dir", "cusub", "deyn", "dayn",
    }:
        return False

    # Existing deterministic handlers and read-only requests.
    try:
        if (
            is_explicit_list_request(raw)
            or is_fuzzy_debt_list_command(raw)
            or is_payment_report_command(raw)
            or is_reminder_start_command(raw)
            or is_natural_top_debt_question(raw)
            or is_natural_today_payment_question(raw)
            or parse_explicit_delete_command(raw) is not None
            or parse_customer_rename_command(raw) is not None
            or parse_somali_amount_edit(raw) is not None
            or parse_customer_phone_update(raw)
        ):
            return True
    except Exception:
        pass

    # Explicit operation words/phrases, including requests that still need a name.
    command_patterns = (
        r"^(?:add|pay|deyn\s+cusub|lacag\s*bixin|liiska|raadi|raadso|search|find|"
        r"faahfaahin|history|taariikh|statement|report|warbixin|export|download|"
        r"import|delete|remove|tirtir|tirtiraan|edit|sax|dhigaal|undo|"
        r"xusuusin|remind|balamaha|ballamaha|balanta|ballanta|menu|help|caawi)\b",
        r"\b(?:liiska\s+daymaha|liiska\s+deynta|daymaha\s+oo\s+dhan|deymaha\s+oo\s+dhan)\b",
        r"\b(?:tirtir|tirtiraan|delete|remove)\b",
        r"\b(?:warbixin|report|liiska\s+lacag\s*bixinta|lacagihii\s+maanta)\b",
    )
    if any(re.search(pattern, folded, re.I) for pattern in command_patterns):
        return True

    # Natural-language questions/features should be allowed through while a workflow waits.
    question_cues = (
        r"\b(?:sidee|xagee|halkee|maxaan|maxaad|maxay|yaa|imisa|inte[e]?|"
        r"ii\s+(?:muuji|sheeg|raadi|sharax|soo\s+dir)|i\s+(?:tus|muuji)|"
        r"waxaan\s+rabaa|ma\s+(?:heli|arki|tirtiri|sameyn|samayn)|"
        r"caawi|caawimaad|help|menu)\b"
    )
    if re.search(question_cues, folded, re.I):
        return True

    if include_transactions:
        try:
            parsed = local_fallback_parse(raw) or parse_structured_somali_transaction(raw)
            if isinstance(parsed, list) and any(
                isinstance(item, dict)
                and str(item.get("action") or "").upper() in {"ADD", "PAY", "EDIT", "DELETE", "SEARCH", "HISTORY", "LIST", "REPORT", "EXPORT"}
                and (
                    item.get("customer_name")
                    or item.get("amount") is not None
                    or str(item.get("action") or "").upper() in {"LIST", "REPORT", "EXPORT"}
                )
                for item in parsed
            ):
                return True
        except Exception:
            pass
    return False


def is_explicit_operation_request(message_text):
    """Identify actionable feature requests that must reach Python handlers, not chat-only AI."""
    raw = " ".join(str(message_text or "").strip().split())
    if not raw:
        return False
    try:
        if (
            is_explicit_list_request(raw)
            or is_fuzzy_debt_list_command(raw)
            or is_payment_report_command(raw)
            or is_reminder_start_command(raw)
            or parse_explicit_delete_command(raw) is not None
            or parse_customer_rename_command(raw) is not None
            or parse_somali_amount_edit(raw) is not None
            or parse_customer_phone_update(raw)
        ):
            return True
        parsed = local_fallback_parse(raw) or parse_structured_somali_transaction(raw)
        if isinstance(parsed, list) and any(
            isinstance(item, dict)
            and str(item.get("action") or "").upper() in {"ADD", "PAY", "EDIT", "DELETE", "SEARCH", "HISTORY", "LIST", "REPORT", "EXPORT"}
            and (
                item.get("customer_name")
                or item.get("amount") is not None
                or str(item.get("action") or "").upper() in {"LIST", "REPORT", "EXPORT"}
            )
            for item in parsed
        ):
            return True
    except Exception:
        pass
    folded = normalize_customer_name(raw).strip(" .!?؟")
    return bool(re.search(
        r"^(?:add|pay|deyn\s+cusub|dayn\s+cusub|lacag\s*bixin|liiska|raadi|raadso|"
        r"search|find|faahfaahin|history|taariikh|statement|report|warbixin|export|download|"
        r"import|delete|remove|tirtir|tirtiraan|edit|sax|dhigaal|undo|xusuusin|remind|"
        r"ku\s+dar|deyn\s+ku\s+dar|diiwaangeli|xaree|ka\s+jar|balamaha|ballamaha)\b",
        folded, re.I
    ))


def _has_active_in_memory_workflow(sender_phone):
    """Whether this sender has a resumable multi-step workflow awaiting an answer."""
    return any(sender_phone in session_map for session_map in WORKFLOW_SESSION_MAPS)


def _pending_workflow_snapshot(sender_phone):
    """Capture the stages/data that were waiting when the latest user message arrived."""
    snapshot = []
    session_maps = (
        ("guided", GUIDED_SESSIONS), ("paused_guided", PAUSED_GUIDED_SESSIONS), ("customer_match", CUSTOMER_MATCH_SESSIONS),
        ("first_debt", FIRST_DEBT_SESSIONS),
        ("delete", DELETE_SESSIONS), ("undo", UNDO_CONFIRMATION_SESSIONS),
        ("amount_edit", AMOUNT_EDIT_SESSIONS), ("rename", RENAME_SESSIONS),
        ("import", IMPORT_SESSIONS), ("payment_export", PAYMENT_EXPORT_SESSIONS),
        ("reminder", REMINDER_SESSIONS), ("search_detail", SEARCH_DETAIL_SESSIONS),
        ("deposit_offer", DEPOSIT_OFFER_SESSIONS), ("correction", CORRECTION_SESSIONS),
    )
    for label, session_map in session_maps:
        state = session_map.get(sender_phone)
        if not state:
            continue
        if label == "paused_guided":
            snapshot.append((label, repr([
                (
                    item.get("stage"), item.get("transaction_type"),
                    item.get("customer_name"), item.get("amount"),
                    item.get("expires_at"),
                )
                for item in state if isinstance(item, dict)
            ])))
            continue
        snapshot.append((
            label,
            repr(state.get("stage")),
            repr(state.get("transaction_type")),
            repr(state.get("customer_name")),
            repr(state.get("amount")),
            repr(state.get("expires_at")),
        ))
    return tuple(snapshot)


def cancel_pending_reply_reminder(sender_phone):
    """Any inbound user message counts as a response and cancels the one-shot reminder."""
    task = PENDING_REPLY_REMINDER_TASKS.pop(str(sender_phone), None)
    if task and not task.done():
        task.cancel()


def _pending_reply_reminder_text(sender_phone, original_prompt):
    """Build one short reminder from the newest workflow that is actually waiting."""
    raw_prompt = str(original_prompt or "")
    prompt_norm = normalize_customer_name(raw_prompt)
    asks_for_reply = (
        "?" in raw_prompt
        or bool(re.search(r"\b(?:soo\s+qor|qor|dooro|door|immisa|xaqiiji|ii\s+sheeg|fadlan)\b", prompt_norm, re.I))
    )
    if not asks_for_reply:
        return None

    session_specs = (
        ("guided", GUIDED_SESSIONS),
        ("delete", DELETE_SESSIONS),
        ("customer_match", CUSTOMER_MATCH_SESSIONS),
        ("amount_edit", AMOUNT_EDIT_SESSIONS),
        ("undo", UNDO_CONFIRMATION_SESSIONS),
        ("rename", RENAME_SESSIONS),
        ("import", IMPORT_SESSIONS),
        ("payment_export", PAYMENT_EXPORT_SESSIONS),
        ("reminder", REMINDER_SESSIONS),
        ("search_detail", SEARCH_DETAIL_SESSIONS),
    )
    active = []
    for label, session_map in session_specs:
        state = session_map.get(sender_phone)
        if not state:
            continue
        stamp = state.get("expires_at") or state.get("created_at")
        try:
            if isinstance(stamp, datetime):
                order = stamp.timestamp()
            elif stamp:
                order = datetime.fromisoformat(str(stamp).replace("Z", "+00:00")).timestamp()
            else:
                order = 0
        except Exception:
            order = 0
        active.append((order, label, state))

    if active:
        _, label, state = max(active, key=lambda item: item[0])
        stage = state.get("stage")
        if label == "guided":
            if stage == "menu":
                return "Waxaan kaa sugayaa doorashada hawsha aad rabto. Soo qor 1 ilaa 6."
            if stage == "debt_name":
                return "Waxaan kaa sugayay magaca macmiilka deynta qaatay. 😊"
            if stage == "payment_name":
                return "Waxaan kaa sugayay magaca macmiilka lacagta bixiyay. 😊"
            if stage == "debt_amount":
                return f"Waxaan kaa sugayay lacagta deynta ee {state.get('customer_name') or 'macmiilka'}. 😊"
            if stage == "payment_amount":
                return f"Waxaan kaa sugayay inta uu {state.get('customer_name') or 'macmiilka'} bixiyay. 😊"
            if stage == "confirm":
                return "Waxaan kaa sugayaa xaqiijinta macaamilka. Soo qor HAA ama MAYA."
            if stage == "search_name":
                return "Waxaan kaa sugayay magaca macmiilka aad raadinayso."
            if stage == "history_name":
                return "Waxaan kaa sugayay magaca macmiilka aad rabto faahfaahintiisa."
        elif label == "delete":
            if stage == "name":
                return "Waxaan kaa sugayay magaca macmiilka aad rabto inaad tirtirto."
            if stage == "choose":
                return "Waxaan kaa sugayay doorashada macmiilka saxda ah."
            if stage == "confirm":
                return "Waxaan kaa sugayaa xaqiijinta tirtiridda. Waxba lama tirtirin."
        elif label == "customer_match":
            if stage == "choose":
                return "Waxaan kaa sugayaa doorashada macmiilka saxda ah."
            if stage == "confirm_single":
                return "Waxaan kaa sugayaa xaqiijinta magaca macmiilka."
            return "Waxaan kaa sugayay magaca buuxa ee macmiilka."
        elif label == "amount_edit":
            return "Waxaan kaa sugayaa xaqiijinta wax-ka-beddelka. Soo qor HAA ama MAYA."
        elif label == "undo":
            return "Waxaan kaa sugayaa xaqiijinta ka-noqoshada macaamilka."
        elif label == "rename":
            return "Waxaan kaa sugayay magaca cusub ee macmiilka." if stage == "new_name" else "Waxaan kaa sugayaa xaqiijinta magaca cusub."
        elif label == "import":
            if stage == "duplicate_choice":
                return "Waxaan kaa sugayaa doorashada 1 ama 2 ee liiska import-ka."
            if state.get("entries"):
                return "Waxaan kaa sugayaa xaqiijinta import-ka. Soo qor OK ama CANCEL."
            if state.get("mode") not in {"debt", "payment"}:
                return "Waxaan kaa sugayaa doorashada DEYN ama LACAG BIXIN."
            return "Waxaan kaa sugayay liiska ama faylka aad rabto inaad soo geliso."
        elif label == "payment_export":
            return "Waxaan kaa sugayay doorashada EXCEL ama PDF."
        elif label == "reminder":
            if stage == "confirming":
                return "Waxaan kaa sugayaa xaqiijinta xusuusinta. Soo qor HAA DIR ama JOOJI."
            return "Waxaan kaa sugayay doorashada macaamiisha aad rabto inaad xusuusiso."
        elif label == "search_detail":
            return "Waxaan kaa sugayaa jawaabta ku saabsan faahfaahinta macmiilka."

    if "deyn cusub baa mise lacag bixin" in prompt_norm:
        return "Waxaan kaa sugayaa inaad caddeyso: DEYN CUSUB mise LACAG BIXIN?"
    if "ma wuxuu bixiyay" in prompt_norm or ("xaqiiji" in prompt_norm and "lacag" in prompt_norm):
        return "Waxaan kaa sugayaa xaqiijinta lacag-bixinta. Soo qor HAA ama MAYA."
    if "magaca" in prompt_norm and "macmiil" in prompt_norm:
        return "Waxaan kaa sugayay magaca macmiilka. 😊"
    if "immisa" in prompt_norm or "lacagta" in prompt_norm:
        return "Waxaan kaa sugayay lacagta si aan hawsha u dhammaystiro. 😊"
    if "door" in prompt_norm or "soo qor" in prompt_norm:
        return "Waxaan kaa sugayaa jawaabta su'aashii hore. 😊"
    return None


async def _send_one_pending_reply_reminder(sender_phone, reminder_text, token):
    try:
        await asyncio.sleep(PENDING_REPLY_REMINDER_DELAY_SECONDS)
        if PENDING_REPLY_REMINDER_TASKS.get(sender_phone) is not token:
            return
        PENDING_REPLY_REMINDER_TASKS.pop(sender_phone, None)
        send_whatsapp(sender_phone, reminder_text, schedule_pending=False)
    except asyncio.CancelledError:
        return
    except Exception as reminder_error:
        print(f"⚠️ Pending reply reminder failed for {sender_phone}: {reminder_error}")


def schedule_pending_reply_reminder(sender_phone, original_prompt):
    """Optionally schedule one reminder; disabled by default to prevent message noise."""
    if not PENDING_REPLY_REMINDER_ENABLED:
        PENDING_REPLY_INBOUND_SNAPSHOTS.pop(str(sender_phone), None)
        return
    sender_phone = str(sender_phone)
    reminder_text = _pending_reply_reminder_text(sender_phone, original_prompt)
    baseline = PENDING_REPLY_INBOUND_SNAPSHOTS.pop(sender_phone, None)
    current = _pending_workflow_snapshot(sender_phone)
    prompt_norm = normalize_customer_name(str(original_prompt or ""))
    database_confirmation_prompt = (
        "deyn cusub baa mise lacag bixin" in prompt_norm
        or ("ma wuxuu bixiyay" in prompt_norm and ("haa" in prompt_norm or "maya" in prompt_norm))
    )
    # A reply to a different request must not restart the old workflow's reminder.
    # A changed stage means the user answered the previous step and a new step is now waiting.
    if baseline is not None and current == baseline and not database_confirmation_prompt:
        return
    if not reminder_text:
        return
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        return
    cancel_pending_reply_reminder(sender_phone)
    token = object()
    task = loop.create_task(_send_one_pending_reply_reminder(str(sender_phone), reminder_text, token))
    PENDING_REPLY_REMINDER_TASKS[str(sender_phone)] = task


def send_whatsapp(to_phone: str, message: str, schedule_pending: bool = True):
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
            sent_ok = bool(body.get("idMessage")) or body.get("status") == "success"
        except Exception:
            sent_ok = res.ok
        if sent_ok and schedule_pending:
            schedule_pending_reply_reminder(clean_phone, message)
        return sent_ok
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
    reclaim_processing = False
    if current_status == "processing":
        processing_raw = pending.get("processing_started_at")
        processing_started = None
        if processing_raw:
            try:
                processing_started = datetime.fromisoformat(str(processing_raw).replace("Z", "+00:00"))
                if processing_started.tzinfo is None:
                    processing_started = processing_started.replace(tzinfo=timezone.utc)
            except (TypeError, ValueError):
                processing_started = None
        if processing_started is None:
            return False, (
                "⚠️ Lacag-bixintan waxay ku hartay xaalad farsamayn oo aan lahayn waqti la xaqiijiyey. "
                "Ha ku celin. Maamulka ha hubiyo diiwaanka Supabase."
            )
        if datetime.now(timezone.utc) - processing_started <= timedelta(minutes=5):
            return False, "Lacag-bixintan weli waa la farsamaynayaa. Sug dhowr daqiiqo."
        reclaim_processing = True
    elif current_status != "pending" and not (admin and current_status == "rejected"):
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

    # Conditional one-time claim. An expired processing lease can be reclaimed;
    # the SQL request ID below makes replay safe if the payment already committed.
    try:
        claim_query = (
            supabase.table("pending_payment_confirmations")
            .update({
                "status": "processing",
                "actor_phone": str(actor_phone),
                "processing_started_at": datetime.now(timezone.utc).isoformat(),
            })
            .eq("id", str(pending_id))
            .eq("status", current_status)
        )
        if reclaim_processing:
            claim_query = claim_query.eq("processing_started_at", str(pending.get("processing_started_at")))
        claimed = claim_query.select("id").execute()
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

        rpc_result = _financial_rpc("record_debt_payment_with_history", {
            "p_customer_id": str(debtor["id"]),
            "p_business_user_id": str(pending.get("business_user_id")),
            "p_amount": round(amount, 2),
            "p_description": str(pending.get("description") or "-").strip() or "-",
        }, request_id=f"pending-payment:{pending_id}").execute()
        rpc_data = rpc_result.data
        if isinstance(rpc_data, list):
            rpc_data = rpc_data[0] if rpc_data else None
        if not isinstance(rpc_data, dict) or not rpc_data.get("id"):
            raise RuntimeError("Payment RPC did not return the updated customer")
        payment_rpc_succeeded = True
        transaction_sender = str(pending.get("sender_phone") or actor_phone)
        remember_selected_customer(transaction_sender, pending.get("business_user_id"), debtor.get("name") or pending.get("customer_name"))
        remember_recent_transaction(transaction_sender, pending.get("business_user_id"), debtor.get("id"), debtor.get("name") or pending.get("customer_name"))
        supabase.table("pending_payment_confirmations").update({
            "status": "confirmed",
            "processed_at": datetime.now(timezone.utc).isoformat(),
        }).eq("id", str(pending_id)).eq("status", "processing").execute()
        success_text = (
            f"✅ Lacag-bixinta waa la diiwaangeliyey.\n"
            f"{rpc_data.get('name') or pending.get('customer_name')}: ${amount:.2f}\n"
            f"Baaqiga: ${float(rpc_data.get('amount') or 0):.2f}"
        )
        if ONBOARDING_SESSIONS.get(transaction_sender, {}).get("stage") == "first_successful_action":
            success_text += (
                "\n\n🎉 *Bilow fiican!* Deynjir hadda wuxuu kuu hayaa diiwaanka macaamilkan. "
                "Waxaad ku dari kartaa macaamiil kale ama lacag-bixintooda. "
                "Haddii daymo hore kuu yaallaan, qor *IMPORT* si aad si fudud ugu soo geliso."
            )
            ONBOARDING_SESSIONS.pop(transaction_sender, None)
        remember_conversation_outcome(
            transaction_sender,
            pending.get("original_message") or f"{pending.get('customer_name')} ${amount}",
            success_text,
        )
        return True, success_text
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

@app.api_route("/", methods=["GET", "HEAD"])
def home():
    return {"status": f"{APP_NAME} Bot Engine is running live.", "app": APP_NAME}
def normalize_customer_name(value):
    """Normalize names for case/punctuation/spacing-insensitive comparison."""
    value = unicodedata.normalize("NFKD", str(value or "").casefold())
    value = "".join(ch for ch in value if not unicodedata.combining(ch))
    value = re.sub(r"[^\w\s]", " ", value)
    return " ".join(value.split())


def clean_extracted_customer_name(value):
    """Remove transaction wording accidentally appended to an extracted name.

    Only trims known action/filler phrases from the END, preserving genuine
    multi-part names and never manufacturing a replacement name.
    """
    name = " ".join(str(value or "").strip().split())
    if not name:
        return None

    # The AI may accidentally return the whole input as the name, including
    # the amount (for example: "cusub Cali $33"). Remove a trailing amount
    # before validating the remaining customer name. Currency markers make
    # this safe without stripping ordinary numeric parts from names.
    name = re.sub(
        r"\s+(?:[$€£]|USD\s*)\s*\d+(?:[.,]\d{1,2})?\s*$",
        "",
        name,
        flags=re.I,
    ).strip(" ,:;.-")

    # Strip command words accidentally included at the START of a name.
    # Examples: "cusub Cali", "dayn Omar", "deyn cusub Axmed".
    leading_patterns = (
        r"^(?:deyn|dayn)\s+cusub\s+",
        r"^(?:deyn|dayn|cusub)\s+",
        r"^(?:lacag\s*bixin|add|pay)\s+",
    )
    previous = None
    while name and name != previous:
        previous = name
        for pattern in leading_patterns:
            name = re.sub(pattern, "", name, flags=re.I).strip(" ,:;.-")

    trailing_patterns = (
        r"\s+(?:(?:wuxuu|wuu|ayuu|ayaa|ayay|waxay|way|ayaan)\s+)?"
        r"(?:qaatay|qaadatay|qaatey|qaateen|qaaty|bixiyay|bixiyey|bixisay|"
        r"bixiyeen|soo\s+celiyay|soo\s+celiyey|celiyay|celiyey|"
        r"keenay|keentay|amaahday|amaah)\b.*$",
        r"\s+(?:deyn|dayn)(?:\s+cusub)?(?:\s+oo)?(?:\s+ah)?\s*$",
        r"\s+(?:cusub\s+oo|oo\s+ah|oo|ah)\s*$",
    )
    previous = None
    while name and name != previous:
        previous = name
        for pattern in trailing_patterns:
            name = re.sub(pattern, "", name, flags=re.I).strip(" ,:;.-")
    if not name or normalize_customer_name(name) in {
        "deyn", "dayn", "deyn cusub", "dayn cusub", "cusub", "oo", "ah"
    }:
        return None
    return name


def customer_name_is_grounded_in_source(customer_name, source_message):
    """True only when the proposed name appears contiguously in the user's message."""
    proposed = normalize_customer_name(customer_name)
    source = normalize_customer_name(source_message)
    if not proposed or not source:
        return False
    return f" {proposed} " in f" {source} "


def is_name_confirmation_interrupt_command(message_text):
    """A real command interrupts name confirmation; a bare reply is a name correction."""
    raw = " ".join(str(message_text or "").strip().split())
    folded = normalize_customer_name(raw).strip(" .!?؟")
    if not folded:
        return False
    command_prefix = (
        r"^(?:menu|start|help|caawi|caawimaad|add|pay|deyn|dayn|"
        r"lacag\s*bixin|import|delete|remove|tirtir|undo|dhigaal|"
        r"liiska|raadi|raadso|search|find|history|taariikh|faahfaahin|"
        r"report|warbixin|export|download|xusuusin|remind|"
        r"balamaha|ballamaha|ballanta|balanta|sax|edit|rename|pdf)\b"
    )
    if re.match(command_prefix, folded, re.I):
        return True
    if parse_transaction_clarification(raw) in {"ADD", "PAY", "CANCEL"}:
        return True
    # A message with an amount is a new transaction, not a name-only correction.
    if re.search(r"(?:\$\s*\d|\b\d+(?:[.,]\d{1,2})?\s*(?:usd|dollar|dollars)\b|(?<!\w)\d+(?:[.,]\d{1,2})?(?!\w))", raw, re.I):
        return True
    return False


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


def parse_contextual_due_date_update(message_text, recent_customer_name):
    """Resolve a clearly labelled date-only follow-up to the recently selected customer."""
    if not recent_customer_name:
        return None
    raw = " ".join(str(message_text or "").strip().split())
    match = re.fullmatch(
        r"(?:mudada|muddo(?:da)?|ballan(?:ta)?|taariikh(?:da)?)(?:\s+(?:waa|ah))?\s+"
        r"(\d{1,2}[/-]\d{1,2}[/-]\d{4}|\d{4}-\d{2}-\d{2})[.!؟]?",
        raw,
        re.I,
    )
    if not match:
        return None
    raw_date = match.group(1)
    try:
        if re.fullmatch(r"\d{4}-\d{2}-\d{2}", raw_date):
            parsed = datetime.strptime(raw_date, "%Y-%m-%d").date()
        else:
            parsed = datetime.strptime(raw_date.replace("-", "/"), "%d/%m/%Y").date()
    except ValueError:
        return None
    return {
        "action": "EDIT",
        "customer_name": str(recent_customer_name).strip(),
        "amount": None,
        "new_amount": None,
        "promised_date": parsed.isoformat(),
        "new_date": parsed.isoformat(),
        "days_until_due": None,
        "description": None,
        "_contextual_due_date_update": True,
    }


def is_explicit_due_date_change(message_text):
    """Only bypass the existing-date confirmation when the user clearly orders a change."""
    return bool(re.search(
        r"\b(?:ka\s+dhig|kadhig|beddel|badal|cusboonaysii|update|change|edit)\b",
        str(message_text or ""),
        re.I,
    ))


def remember_recent_transaction(sender_phone, business_user_id, customer_id, customer_name):
    """Remember a real committed transaction for a brief disagreement follow-up."""
    if not customer_id:
        return
    # A later single transaction supersedes the short-lived batch undo target.
    LAST_BATCH_CONTEXT.pop(str(sender_phone), None)
    LAST_TRANSACTION_CONTEXT[str(sender_phone)] = {
        "business_user_id": str(business_user_id),
        "customer_id": str(customer_id),
        "customer_name": str(customer_name or "Macmiilka"),
        "created_at": datetime.now(timezone.utc),
    }


def is_transaction_disagreement(message_text):
    """Conservative Somali/English disagreement detector; never performs an undo."""
    text = normalize_customer_name(str(message_text or ""))
    patterns = (
        r"\bmaya\b", r"\bkhalad\b", r"\bqalad\b",
        r"\bsidaas\s+ma\s+aha\b", r"\bsax\s+ma\s+aha\b",
        r"\bma\s+saxna\b", r"\bwaa\s+qalad\b",
        r"\bka\s+noqo\b", r"\bka\s+noqon\b", r"\bkanoqoto\b", r"\bkanoqon\b",
        r"\bka\s+laabo\b", r"\bka\s+laabato\b", r"\bkalaabato\b",
        r"\bka\s+laab\b", r"\bdib\s+u\s+celi\b",
        r"\bwaan\s+ka\s+noqday\b", r"\bi\s+ka\s+noqo\b",
        r"\bundo\b", r"\bnot\s+correct\b", r"\bwrong\b",
    )
    return any(re.search(pattern, text, re.I) for pattern in patterns)


def undo_confirmation_answer(message_text):
    """Return yes/no/None for an active undo confirmation response."""
    text = normalize_customer_name(str(message_text or "")).strip(" .!؟?")
    if text in {"1", "haa", "h", "yes", "y", "undo", "ka noqo", "ka noqon", "kanoqoto", "kanoqon", "ka laabo", "ka laabato", "dib u celi", "haa ka noqo", "haa undo"}:
        return "yes"
    if text in {"2", "maya", "no", "n", "sax", "waa sax", "xaree", "hay", "iska daa", "jooji"}:
        return "no"
    return None


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
    return normalize_customer_name(value).strip(" .!?؟") in {
        "", "none", "null", "undefined", "unknown", "n a", "na",
        "ma jiro", "ma jirto", "ma jiraan", "ma jirto qof", "qof ma jiro",
        "qofna ma jiro", "waxba", "waxba ma jiraan", "lacag ma jirto",
        "lacag ma hayo", "ma hayo", "ma aqaan", "ma garanayo",
    }


def parse_local_appointment_list_request(message_text):
    """Recognize natural Somali requests for customers whose debts are due on a date.

    Keep this deterministic: appointment-list requests must not wait for Gemini
    or be interpreted as a new debt/payment.
    """
    raw = normalize_customer_name(message_text).strip(" .!?؟")
    raw = re.sub(r"\s+", " ", raw)
    appointment_word = r"(?:balam(?:aha|a)?|ballam(?:aha|a)?|balan(?:ta|san|s)?|ballan(?:ta|san|s)?)"
    today_word = r"(?:maanta|today|maantaas)"
    tomorrow_word = r"(?:beri|berri|tomorrow)"
    list_action = r"(?:i\s+tus|ii\s+tus|soo\s+saar|soo\s+bixi|i\s+sheeg|ii\s+sheeg|muuji|eeg|liiska|yaa|kuwa)"
    people_word = r"\b(?:kuwa|macaamiisha|dadka|dadkaas|macmiisha)\b"

    target_type = None
    if re.search(today_word, raw, re.I):
        # Require an appointment term plus either a list/show verb or a people
        # reference. This avoids stealing ordinary date edits such as "Cali
        # ballantiisa maanta ka dhig".
        if re.search(appointment_word, raw, re.I) and (
            re.search(list_action, raw, re.I) or re.search(people_word, raw, re.I)
        ):
            target_type = "today"
    elif re.search(tomorrow_word, raw, re.I):
        if re.search(appointment_word, raw, re.I) and (
            re.search(list_action, raw, re.I) or re.search(people_word, raw, re.I)
        ):
            target_type = "tomorrow"

    # Also accept the short canonical commands, independent of word order.
    if target_type is None and re.fullmatch(
        r"(?:balamaha|ballamaha|balanta|ballanta|balan|ballan)\s+(?:maanta|today)", raw, re.I
    ):
        target_type = "today"
    if target_type is None and re.fullmatch(
        r"(?:balamaha|ballamaha|balanta|ballanta|balan|ballan)\s+(?:beri|berri|tomorrow)", raw, re.I
    ):
        target_type = "tomorrow"

    if target_type == "today":
        target_date = today_eat()
    elif target_type == "tomorrow":
        target_date = today_eat() + timedelta(days=1)
    else:
        return None

    return {
        "action": "LIST", "customer_name": None, "amount": None,
        "filter_date": target_date.isoformat(), "filter_type": target_type,
    }



def resolve_contextual_appointment_list_followup(message_text, sender_phone):
    """Reuse the last requested appointment date for clear result-retry phrases."""
    raw = normalize_customer_name(message_text).strip(" .!?؟")
    retry_phrases = {
        "soo saar", "soo bixi", "mar kale soo saar", "sii wad",
        "ilaa intee sugaa", "ilaa intee ayaan sugaa", "maxaan sugaa",
        "wali sugayaa", "soo bandhig",
    }
    if raw not in retry_phrases:
        return None
    saved = LAST_APPOINTMENT_LIST_REQUESTS.get(sender_phone) or {}
    expires_at = saved.get("expires_at")
    if not expires_at or datetime.now(timezone.utc) > expires_at:
        LAST_APPOINTMENT_LIST_REQUESTS.pop(sender_phone, None)
        return None
    return {
        "action": "LIST", "customer_name": None, "amount": None,
        "filter_date": saved.get("filter_date"),
        "filter_type": saved.get("filter_type"),
    }


def is_explicit_appointment_list_request(message_text):
    """Allow appointment-list phrasing with relative or explicit calendar dates."""
    raw = normalize_customer_name(message_text).strip(" .!?؟")
    if not re.match(r"^(?:balamaha|ballamaha|balanta|ballanta|balan(?:ta)?)\b", raw, re.I):
        return False
    return bool(re.search(
        r"\b(?:maanta|beri|berri|today|tomorrow|\d{1,2}(?:st|nd|rd|th)?|"
        r"jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|"
        r"jul(?:y)?|aug(?:ust)?|sep(?:tember)?|oct(?:ober)?|nov(?:ember)?|"
        r"dec(?:ember)?)\b",
        raw, re.I
    ))


def is_explicit_list_request(message_text):
    """Recognize clear debt-list requests without conflating appointment filters."""
    raw = normalize_customer_name(message_text).strip(" .!?؟")
    debt_list_phrases = {
        "liis", "liiska", "liiska deynta", "liiska daynta",
        "liiska daymaha", "liiska deymaha",
        "liiska daymaha oo dhan", "liiska deymaha oo dhan",
        "daymaha", "deymaha", "daymaha oo dhan", "deymaha oo dhan",
        "dhamaan daymaha", "dhammaan daymaha",
        "dhamaan deymaha", "dhammaan deymaha",
        "ii muuji daymaha", "ii muuji deymaha",
        "i tus daymaha", "i tus deymaha",
        "ii tus daymaha", "ii tus deymaha",
        "deynaha liiskooda", "deymaha maqan", "deynta maqan", "deymo maqan",
        "yaan weli deyn ku leeyahay", "yaan deyn ku leeyahay",
        "yaa weli deyn igu leh", "liiska deymaha maqan",
        "list", "list debts", "debt list", "show debts", "show all debts",
        "all debts", "view debts",
    }
    if raw in debt_list_phrases:
        return True
    return bool(re.fullmatch(
        r"(?:liiska\s+)?(?:daymaha|deymaha|deynta|daynta)"
        r"(?:\s+(?:oo\s+dhan|oo\s+idil))|"
        r"(?:liis|liiska|liiska deynta|liiska daynta|"
        r"liiska daynta iyo balamaha|liiska deynta iyo balamaha)",
        raw,
        flags=re.I,
    )) or is_fuzzy_debt_list_command(message_text)


def is_contextual_debt_list_followup(message_text, sender_phone):
    """Resolve short 'where/all' follow-ups as a debt-list request only in list context."""
    session = CONVERSATION_SESSIONS.get(str(sender_phone)) or {}
    expires_at = session.get("expires_at")
    if expires_at and datetime.now(timezone.utc) > expires_at:
        CONVERSATION_SESSIONS.pop(str(sender_phone), None)
        return False

    history = list(session.get("history") or [])
    last_model = next(
        (str(turn.get("text") or "").strip()
         for turn in reversed(history)
         if turn.get("role") == "model" and str(turn.get("text") or "").strip()),
        "",
    )
    if not last_model:
        return False

    previous = normalize_customer_name(last_model)
    list_context = bool(
        re.search(r"\b(?:liiska|daymaha|deymaha)\b", previous, re.I)
        or re.search(r"\bdeynta\b.*\bmacaamiisha", previous, re.I)
        or re.search(r"\bdaynta\b.*\bmacaamiisha", previous, re.I)
    )
    if not list_context:
        return False

    followup = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
    return followup in {
        "dhamaan", "dhammaan", "dhamaan daymaha", "dhammaan daymaha",
        "dhamaan deymaha", "dhammaan deymaha",
        "may dhamaan", "maya dhamaan", "maya dhammaan", "may dhammaan",
        "halkee", "meeye", "meeyaan", "xagee", "xaggee",
        "liiska xagee", "daymaha xagee",
    }


def parse_customer_rename_command(message_text):
    """Parse an explicit customer rename without relying on AI interpretation.

    Supported examples:
      SAX Old customer name -> Correct customer name
      EDIT Old customer name TO Correct customer name
      SAX Old customer name ku beddel Correct customer name
    """
    raw = " ".join(str(message_text or "").strip().split())
    patterns = [
        r"^(?:sax|rename|rename\s+customer|edit\s+name|edit|change\s+name)\s+(?:magaca\s+)?(.+?)\s*(?:->|=>|\bto\b)\s*(.+?)\s*[.!]?$",
        r"^(?:sax|edit)\s+(?:magaca\s+)?(.+?)\s+\b(?:ku\s+bed{1,2}el|u\s+bed{1,2}el|ka\s+dhig|magaca\s+cusub)\b\s+(.+?)\s*[.!]?$",
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
    match = re.match(
        r"^(?:sax|edit\s+name)\s+(?:magaca\s+)?(.+?)\s*[.!]?$",
        raw, re.IGNORECASE,
    )
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
        r"\b(?:ima|uma|igama|iigama|iima)\s+(?:bixin|bixinin|keenin|soo\s+celin|helin)\b",
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


def parse_first_debt_due_date(value):
    """Parse a first-debt onboarding due date without AI. Return date, 'none', or None."""
    original = str(value or "").strip().strip(" .!?؟")
    if not original:
        return None
    # Parse numeric dates before text normalization, which removes separators.
    explicit = _parse_somali_date(original)
    if explicit:
        return explicit
    raw = normalize_customer_name(original).strip(" .!?؟")
    if raw in {"ma hubo", "ma aqaan", "ma garanayo", "ballan ma leh", "balan ma leh",
               "ballan ma jiro", "balan ma jiro", "lama sheegin", "ma jiro", "none", "no date"}:
        return "none"
    today = today_eat()
    if raw in {"maanta", "today", "h maanta"}:
        return today
    if raw in {"berri", "bari", "tomorrow", "maalinta berri"}:
        return today + timedelta(days=1)
    weekday_map = {
        "isniin": 0, "isniinta": 0, "talaado": 1, "talaadada": 1,
        "arbaco": 2, "arbacada": 2, "khamiis": 3, "khamiista": 3,
        "jimco": 4, "jimcaha": 4, "sabti": 5, "sabtida": 5,
        "axad": 6, "axadda": 6,
    }
    for label, weekday in weekday_map.items():
        if re.fullmatch(r"(?:maalinta\s+)?" + re.escape(label), raw):
            return today + timedelta(days=(weekday - today.weekday()) % 7)
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


def parse_transaction_batch_text(message_text):
    """Parse a clear, explicitly directed multi-row ADD/PAY message.

    Supports headers (DEYN CUSUB / LACAG BIXIN), one-row-per-line input,
    semicolon-separated rows, and comma-separated rows when each segment has
    its own unambiguous amount. Every row must parse; nothing is silently lost.
    """
    raw = str(message_text or "").replace("\r", "\n").strip()
    if not raw:
        return None

    # Shopkeepers commonly put the direction and first customer on one line:
    # "dayn Omar $44, Yuunus $21". Treat the leading word as a header, not
    # part of the first customer's name. This is deterministic and Gemini-free.
    inline_mode = None
    inline_header = re.match(
        r"^(?:deyn|dayn)(?:\s+(?:cusub|cusubta))?\s*[:.,-]?\s+",
        raw, re.I,
    )
    if inline_header:
        inline_mode = "debt"
        raw = raw[inline_header.end():].strip()
    else:
        inline_payment_header = re.match(
            r"^(?:lacag\s*bixin(?:ta)?|bixin|payments?)\s*[:.,-]?\s+",
            raw, re.I,
        )
        if inline_payment_header:
            inline_mode = "payment"
            raw = raw[inline_payment_header.end():].strip()
    if not raw:
        return None

    add_header = re.compile(r"^(?:deyn|dayn)(?:\s+(?:cusub|cusubta))?$|^(?:add|new\s+debt)$", re.I)
    pay_header = re.compile(r"^(?:lacag\s*bixin(?:ta)?|bixin|payment(?:s)?)$", re.I)
    date_pattern = r"(?:\d{4}-\d{1,2}-\d{1,2}|\d{1,2}[/-]\d{1,2}[/-]\d{2,4})"
    due_re = re.compile(
        rf"(?:\b(?:ballan(?:ta)?|wakhtiga\s+balanta|waqtiga\s+balanta|due(?:\s+date)?)\s*(?:waa)?\s*[:=-]?\s*)({date_pattern})",
        re.I,
    )
    currency_re = re.compile(
        r"\$\s*(\d+(?:[.,]\d{1,2})?)|(?<![\w/.-])(\d+(?:[.,]\d{1,2})?)\s*\$"
    )
    plain_amount_re = re.compile(r"(?<![\w/.-])(\d{1,7}(?:[.,]\d{1,2})?)(?![\w/.-])")

    def split_line(line):
        line = " ".join(line.split()).strip()
        if not line:
            return []
        if ";" in line:
            return [part.strip() for part in line.split(";") if part.strip()]
        # A comma is a row separator only if every side independently contains
        # exactly one currency-marked amount or a plain amount. Decimal commas
        # are not split because the next character must begin a word/name.
        if re.search(r",\s*[A-Za-z\u0080-\uffff]", line):
            parts = [part.strip() for part in re.split(r",\s*(?=[A-Za-z\u0080-\uffff])", line) if part.strip()]
            if len(parts) > 1:
                valid = True
                for part in parts:
                    stripped = due_re.sub(" ", part)
                    matches = list(currency_re.finditer(stripped))
                    if not matches:
                        matches = list(plain_amount_re.finditer(stripped))
                    if len(matches) != 1:
                        valid = False
                        break
                if valid:
                    return parts
        return [line]

    source_rows = []
    for line in raw.splitlines():
        clean = " ".join(line.split()).strip()
        if not clean:
            continue
        if re.fullmatch(r"(?:menu|liis|liiska)\s*", clean, re.I):
            continue
        source_rows.extend(split_line(clean))

    mode = inline_mode
    rows = []
    for line in source_rows:
        clean = re.sub(r"^\s*(?:[-*•]|\d+[.)])\s*", "", line).strip()
        if add_header.fullmatch(clean):
            if mode == "payment":
                return None
            mode = "debt"
            continue
        if pay_header.fullmatch(clean):
            if mode == "debt":
                return None
            mode = "payment"
            continue
        rows.append(clean)

    if len(rows) < 2:
        return None

    parsed_rows = []
    row_actions = set()
    for row_number, row in enumerate(rows, start=1):
        folded = normalize_customer_name(row)
        add_mark = bool(re.search(
            r"\b(?:deyn(?:ta)?\s+(?:cusub|qaato|qaatay|qaadatay|qaatey)|"
            r"iga\s+qaatay|ayuu\s+qaatay|wuxuu\s+iga\s+qaatay|amaah|dayn\s+qaatay)\b",
            folded, re.I))
        pay_mark = bool(re.search(
            r"\b(?:lacag\s*bixin(?:ta)?|bixiyay|bixiyey|bixisay|bixiyeen|"
            r"soo\s+celiyay|soo\s+celiyey|celiyay|celiyey|keenay|keentay|"
            r"ii\s+keenay|lacagtii\s+waa\s+la\s+helay)\b",
            folded, re.I))
        row_action = "debt" if add_mark and not pay_mark else ("payment" if pay_mark and not add_mark else None)
        if add_mark and pay_mark:
            return None
        if row_action:
            row_actions.add(row_action)
        effective_mode = row_action or mode
        if effective_mode not in {"debt", "payment"}:
            return None
        if mode and row_action and row_action != mode:
            return None

        due_match = due_re.search(row)
        due_date = None
        row_without_date = row
        if due_match:
            due_date = _import_parse_date(due_match.group(1))
            row_without_date = due_re.sub(" ", row, count=1)

        amount_matches = list(currency_re.finditer(row_without_date))
        if not amount_matches and (mode or row_action):
            amount_matches = list(plain_amount_re.finditer(row_without_date))
        if len(amount_matches) != 1:
            return None
        amount_match = amount_matches[0]
        amount_text = next((group for group in amount_match.groups() if group is not None), None)
        try:
            amount = float(amount_text.replace(",", "."))
        except (TypeError, ValueError):
            return None
        if not math.isfinite(amount) or amount <= 0:
            return None

        name = (row_without_date[:amount_match.start()] + " " + row_without_date[amount_match.end():]).strip()
        name = re.sub(
            r"(?i)\b(?:deyn(?:ta)?|dayn|cusub|lacag|bixin(?:ta)?|bixiyay|bixiyey|bixisay|"
            r"bixiyeen|ayuu|buu|bay|baan|wuxuu|wuu|ayaa|ayay|waxay|way|iga|qaatay|"
            r"qaadatay|qaatey|qaato|soo|celiyay|celiyey|keenay|keentay|amaah|"
            r"usd|dollars?|dollar)\b", " ", name)
        name = re.sub(r"[$]", " ", name)
        name = " ".join(name.split()).strip(" .,:;-")
        if not name or len(name) > 120 or not re.search(r"[A-Za-z\u0080-\uffff]", name):
            return None

        parsed_rows.append({
            "name": name,
            "amount": round(amount, 2),
            "promised_date": due_date if effective_mode == "debt" else None,
            "phone_number": None,
            "description": None,
        })

    if len(row_actions) > 1:
        return None
    if mode is None:
        if len(row_actions) != 1:
            return None
        mode = next(iter(row_actions))
    if row_actions and next(iter(row_actions)) != mode:
        return None
    if len(parsed_rows) < 2 or len(parsed_rows) > 50:
        return None
    return mode, parsed_rows


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

    # First resolve literal stored-name phrases. If both a short name and a
    # longer name occur as substrings (e.g. LOW and IIDLE LOW), choose the
    # longest exact phrase. If two different names of the same longest length
    # are literally present, leave the choice ambiguous.
    exact_candidates = [
        (len(normalized.split()), len(normalized), display, normalized)
        for normalized, display in stored_names.items()
        if f" {normalized} " in normalized_message
    ]
    if exact_candidates:
        longest_words = max(item[0] for item in exact_candidates)
        longest = [item for item in exact_candidates if item[0] == longest_words]
        longest_chars = max(item[1] for item in longest)
        longest = [item for item in longest if item[1] == longest_chars]
        unique_exact = {item[3]: item[2] for item in longest}
        if len(unique_exact) == 1:
            resolved = next(iter(unique_exact.values()))
            print(f"🔎 Recovered longest exact debtor name from original message: {ai_name!r} -> {resolved!r}")
            return resolved
        return None

    # If the customer typed a small spelling variation (e.g. MAT AAN vs MATAN),
    # compare same-length word windows from the original message against names.
    message_parts = normalize_customer_name(message_text).split()
    requested_parts = normalize_customer_name(ai_name).split()
    candidates = []

    for normalized, display in stored_names.items():
        stored_parts = normalized.split()
        if not stored_parts:
            continue
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
        stored_parts = normalized.split()
        # A one-word request such as "Omar" must not fuzzy-match a different
        # multi-word name such as "CABDI CUMAR". Exact token matches were
        # already handled above; fuzzy matching is only safe here when both
        # sides have the same number of name parts.
        if len(requested_parts) != len(stored_parts):
            continue
        score = _name_similarity(requested, normalized)
        if score >= 0.82:
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
        # Show useful context so the shopkeeper can distinguish same-name people
        # and multiple outstanding debt records before choosing.
        shown = (matches or [])[:10]
        for index, debtor in enumerate(shown, start=1):
            due = debtor.get("promised_date") or "ballan lama gelin"
            amount = _safe_money(debtor.get("amount"))
            prompt += f"{index}️⃣ {debtor.get('name') or 'Macmiil'} — ${amount:.2f} — {due}\n"
        prompt += "\nDooro lambarka diiwaanka/macmiilka saxda ah."
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
        f"Macmiilka: *{candidate['name']}*\n"
        f"Wadarta deynta: *${balance:.2f}*\n"
        "Soo qor *HAA, TIRTIR*.\n"
        "ama Qor *JOOJI* si aan loo Tirtirin."
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
    if state.get("stage") in {"name", "choose"} and is_no_activity_reply(answer):
        DELETE_SESSIONS.pop(sender_phone, None)
        send_whatsapp(sender_phone, "Waan fahmay. Hawshii tirtiridda waa la joojiyey; waxba lama tirtirin.")
        return {"status": "delete_no_activity_cancelled"}
    if state.get("stage") == "name" and is_guided_name_correction(answer):
        send_whatsapp(sender_phone, "Waan fahmay—taasi magac ma ahayn. Fadlan qor magaca macmiilka aad rabto inaad tirtirto, ama *JOOJI*.")
        return {"status": "delete_name_correction_requested"}
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
                send_whatsapp(sender_phone, f"✅ *{customer_name}* waa laga saaray liiska Rasmiga ah. Balse Deymihii iyo lacag-bixinnadiisii hore way kaydsan yihiin; waxaad ka heli kartaa markaad codsato xisaabtiisa.")
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
    """Return a requested customer name, or an empty string when deletion needs clarification."""
    raw = " ".join(str(message_text or "").strip().split())
    match = re.match(r"^(?:delete|remove|tirtir)\b\s*[:,-]?\s*(.*?)\s*[.!]?$", raw, re.I)
    if match:
        target = match.group(1).strip(" .,:;")
        target = re.sub(r"^(?:(?:xogta|deynta|daynta|macmiilka)\s+)+", "", target, flags=re.I).strip()
        if target.casefold() in {"xogta", "deynta", "daynta", "macmiilka"}:
            target = ""
        return target or ""

    natural_patterns = (
        r"^(?:waxaan\s+)?inaan\s+tirtir(?:o|to|aan|ayaa|aa)?\s+rabaa$",
        r"^(?:waxaan\s+)?rabaa\s+inaan\s+tirtir(?:o|to|aan|ayaa|aa)?(?:\s+(.*))?$",
        r"^(?:waxaan\s+)?rabaa\s+in\s+la\s+tirtir(?:o|to|aan)?(?:\s+(.*))?$",
        r"^(?:xogta|deynta|daynta|macmiilka)\s+(?:waan\s+)?rabaa\s+inaan\s+tirtir(?:o|to|aan)?(?:\s+(.*))?$",
    )
    for pattern in natural_patterns:
        natural_match = re.match(pattern, raw, re.I)
        if natural_match:
            target = ((natural_match.group(1) if natural_match.lastindex else "") or "").strip(" .,:;")
            target = re.sub(r"^(?:(?:xogta|deynta|daynta|macmiilka)\s+)+", "", target, flags=re.I).strip()
            if target.casefold() in {"xogta", "deynta", "daynta", "macmiilka"}:
                target = ""
            return target or ""
    return None


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
        description = str(entry.get("description") or "").strip()
        if description.lower() in ("nan", "none", "null"):
            description = ""
        clean.append({
            "name": name,
            "amount": round(amount, 2),
            "promised_date": _import_parse_date(entry.get("promised_date") or entry.get("due_date") or entry.get("due")),
            "phone_number": phone or None,
            "description": description[:160] or None,
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
    payload = {"contents":[{"role":"user","parts":[{"text":prompt}]}],
               "generationConfig":{"temperature":0,"responseMimeType":"application/json"}}
    response = _gemini_generate_content(url, payload, timeout=60)
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
    preview_prompt = "\n".join(lines)
    send_deynjir_choice_buttons(
        admin_phone,
        preview_prompt,
        [("IMPORT_CONFIRM_OK", "OK, kaydi"),
         ("IMPORT_CONFIRM_CANCEL", "CANCEL, jooji")],
        preview_prompt
    )


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
    session.setdefault("request_id", secrets.token_urlsafe(24))

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

        # One database function call commits the entire reviewed batch atomically.
        # Apply the matching Deynjir idempotency migration before deploying this code.
        payment_payload = [
            {
                "customer_id": str(debtor["id"]),
                "amount": round(float(item["amount"]), 2),
                "description": str(item.get("description") or "-").strip() or "-",
            }
            for item, debtor in prepared
        ]
        if len(payment_payload) == 1:
            # Preserve compatibility for one-row imports; the batch RPC requires 2+.
            item, debtor = prepared[0]
            rpc_result = _financial_rpc("record_debt_payment_with_history", {
                "p_customer_id": str(debtor["id"]),
                "p_business_user_id": str(business_user_id),
                "p_amount": round(float(item["amount"]), 2),
                "p_description": str(item.get("description") or "-").strip() or "-",
            }, request_id=f"import:{session['request_id']}:payment:0").execute()
            rpc_data = rpc_result.data
            if isinstance(rpc_data, list):
                rpc_data = rpc_data[0] if rpc_data else None
            if not isinstance(rpc_data, dict) or not rpc_data.get("id"):
                raise RuntimeError("record_debt_payment ma xaqiijin lacag-bixinta. Hubi Supabase.")
            saved = 1
        else:
            batch_result = _financial_rpc("record_debt_payment_batch_with_history", {
                "p_business_user_id": str(business_user_id),
                "p_payments": payment_payload,
            }, request_id=f"import:{session['request_id']}:payment:batch").execute()
            batch_data = batch_result.data
            if isinstance(batch_data, list):
                batch_data = batch_data[0] if batch_data else None
            if not isinstance(batch_data, dict) or batch_data.get("success") is not True:
                raise RuntimeError("Supabase ma xaqiijin kaydinta dhammaan lacag-bixinnada.")
            saved = int(batch_data.get("count") or 0)
            if saved != len(payment_payload):
                raise RuntimeError("Tirada lacag-bixinnada la xaqiijiyey ma waafaqsana liiska.")

        total_paid = sum(float(item["amount"]) for item in entries)
        send_whatsapp(
            admin_phone,
            "✅ Import-ka lacag-bixinta waa dhammaaday.\n"
            f"Lacag-bixin la diiwaangeliyay: {saved}\n"
            f"Wadarta lacagta: ${total_paid:.2f}\n"
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
                "✅ *Lacag-bixinnada waa la diiwaangeliyey.*\n\n"
                f"Dukaan: *{shop_name}*\n"
                f"Tirada lacag-bixinnada: *{saved}*\n"
                f"Wadarta lacagta: *${total_paid:.2f}*\n\n"
                "Lacagahan waxaa laga jaray deymaha macaamiisha ee dukaankaaga.\n"
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
    prepared_debts = []

    # Validate and recheck every row before the database write begins.
    for item in entries:
        amount = float(item["amount"])
        if not math.isfinite(amount) or amount <= 0:
            raise ValueError(f"{item.get('name')}: lacagtu ma saxna.")
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
        prepared_debts.append(item)

    # For 2+ rows, one PostgreSQL function call commits the whole debt batch
    # atomically. One-row imports keep using the established single-row RPC.
    if len(prepared_debts) == 1:
        item = prepared_debts[0]
        result = _financial_rpc("record_debt_addition", {
            "p_customer_id": None,
            "p_business_user_id": str(business_user_id),
            "p_name": str(item["name"]),
            "p_amount": round(float(item["amount"]), 2),
            "p_description": str(item.get("description") or "-").strip() or "-",
            "p_promised_date": item.get("promised_date"),
            "p_phone_number": item.get("phone_number"),
            "p_created_at": None,
        }, request_id=f"import:{session['request_id']}:debt:0").execute()
        if not result.data:
            raise RuntimeError(f"Deynta {item['name']} lama xaqiijin in la kaydiyey.")
        added = 1
    elif len(prepared_debts) >= 2:
        debt_payload = [
            {
                "name": str(item["name"]),
                "amount": round(float(item["amount"]), 2),
                "description": str(item.get("description") or "-").strip() or "-",
                "promised_date": item.get("promised_date"),
                "phone_number": item.get("phone_number"),
            }
            for item in prepared_debts
        ]
        batch_result = _financial_rpc("record_debt_addition_batch", {
            "p_business_user_id": str(business_user_id),
            "p_debts": debt_payload,
        }, request_id=f"import:{session['request_id']}:debt:batch").execute()
        batch_data = batch_result.data
        if isinstance(batch_data, list):
            batch_data = batch_data[0] if batch_data else None
        if not isinstance(batch_data, dict) or batch_data.get("success") is not True:
            raise RuntimeError("Supabase ma xaqiijin kaydinta dhammaan deymaha.")
        added = int(batch_data.get("count") or 0)
        if added != len(prepared_debts):
            raise RuntimeError("Tirada deymaha la xaqiijiyey ma waafaqsana liiska.")

        # Capture exact ledger transaction IDs immediately after commit. The
        # batch-undo option is offered only if every row can be tied to one
        # distinct customer and its latest transaction is the expected ADD.
        # This avoids ever undoing a later unrelated transaction.
        try:
            returned_rows = batch_data.get("debts") or []
            batch_transactions = []
            seen_customer_ids = set()
            if len(returned_rows) == len(prepared_debts):
                for returned, prepared in zip(returned_rows, prepared_debts):
                    if not isinstance(returned, dict):
                        raise ValueError("Batch RPC did not return a customer row")
                    customer_id = str(returned.get("id") or returned.get("customer_id") or "").strip()
                    if not customer_id or customer_id in seen_customer_ids:
                        raise ValueError("Batch has missing or repeated customer IDs")
                    seen_customer_ids.add(customer_id)
                    latest_result = supabase.rpc("get_latest_customer_transaction_for_undo", {
                        "p_customer_id": customer_id,
                        "p_business_user_id": str(business_user_id),
                    }).execute()
                    latest = latest_result.data
                    if isinstance(latest, list):
                        latest = latest[0] if latest else None
                    if not isinstance(latest, dict) or not latest.get("transaction_id"):
                        raise ValueError("Could not identify the committed ledger transaction")
                    if str(latest.get("transaction_type") or "").upper() != "ADD":
                        raise ValueError("Latest customer transaction is not a plain debt addition")
                    if abs(float(latest.get("amount") or 0) - float(prepared["amount"])) > 0.009:
                        raise ValueError("Latest ledger amount does not match the imported debt")
                    batch_transactions.append({
                        "customer_id": customer_id,
                        "transaction_id": str(latest["transaction_id"]),
                        "customer_name": str(latest.get("customer_name") or returned.get("name") or prepared["name"]),
                        "amount": round(float(latest.get("amount") or prepared["amount"]), 2),
                    })
            if len(batch_transactions) == len(prepared_debts):
                LAST_BATCH_CONTEXT[admin_phone] = {
                    "business_user_id": str(business_user_id),
                    "mode": "debt",
                    "transactions": batch_transactions,
                    "total": round(sum(float(x["amount"]) for x in batch_transactions), 2),
                    "created_at": datetime.now(timezone.utc),
                    "expires_at": datetime.now(timezone.utc) + UNDO_CONFIRMATION_TTL,
                    "request_id": f"undo-batch:{session['request_id']}",
                }
            else:
                LAST_BATCH_CONTEXT.pop(admin_phone, None)
        except Exception as batch_undo_capture_error:
            LAST_BATCH_CONTEXT.pop(admin_phone, None)
            print(f"⚠️ Batch undo context not available (batch is still saved): {type(batch_undo_capture_error).__name__}: {batch_undo_capture_error}")

    if skipped:
        admin_confirmation = (
            "⚠️ Liiska deynta qayb ahaan ayaa loo diiwaangeliyey.\n\n"
            f"✅ Deymo cusub oo lagu daray: {added}\n"
            f"⏭️ Deymo hore oo laga booday: {skipped}\n\n"
            "Deymaha hore laguma darin mar labaad."
        )
    else:
        admin_confirmation = (
            "✅ Liiska deynta waa la diiwaangeliyey.\n\n"
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
        "✅ *Deyn cusub ayaa lagu daray liiskaaga.*\n\n"
        f"Name: *{shop_name}*\n\n"
        "soo Qor *LIISKA DAYNTA* si aad u aragto dhamaan liiska deymaha."
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
    """Claim a webhook event; stale/failed deliveries can be retried safely."""
    if not event_id:
        return False
    try:
        result = supabase.rpc("claim_webhook_event", {"p_event_id": str(event_id)}).execute()
        value = result.data
        if isinstance(value, list):
            value = value[0] if value else None
        if isinstance(value, dict):
            return value.get("claimed") is not True
        return value is not True
    except Exception as exc:
        print(f"⚠️ Webhook claim unavailable: {type(exc).__name__}: {exc}")
        raise HTTPException(status_code=503, detail="Webhook processing state unavailable; retry delivery.") from exc


async def _whatsapp_webhook_process(request: Request):
    data = await request.json()
    print(f"📥 Green-API webhook received: type={data.get('typeWebhook')}")

    type_webhook = data.get("typeWebhook")

    # Accept contact messages and commands manually sent from the linked
    # WhatsApp handset. Green-API labels handset-originated messages
    # outgoingMessageReceived; keep this enabled because the shopkeeper may
    # operate Deynjir from that same linked phone. Bot/API-sent messages use
    # outgoingAPIMessageReceived and remain ignored to prevent reply loops.
    allowed_types = {
        "incomingMessageReceived",
        "outgoingMessageReceived",
    }

    if type_webhook not in allowed_types:
        return {"status": "ignored"}
    if type_webhook == "outgoingMessageReceived":
        print("📱 Processing a message manually sent from the linked WhatsApp handset")

    sender_data = data.get("senderData", {})
    sender_chat_id = sender_data.get("chatId")

    if not sender_chat_id:
        return {"status": "no_chat_id"}

    sender_phone = sender_chat_id.split("@")[0]
    # Never resurrect an older paused flow on a new inbound message.
    PAUSED_GUIDED_SESSIONS.pop(sender_phone, None)
    PENDING_REPLY_INBOUND_SNAPSHOTS[sender_phone] = _pending_workflow_snapshot(sender_phone)
    cancel_pending_reply_reminder(sender_phone)
    print(f"🔍 SENDER PHONE: {sender_phone}")

    message_data = data.get("messageData", {})
    type_message = message_data.get("typeMessage")

    # Gate every non-text media type before any reply, download, import-session
    # lookup, or AI processing. Unknown/pending/rejected senders stay silent.
    media_message_types = {
        "audioMessage", "pttMessage", "voiceMessage", "voiceNoteMessage",
        "documentMessage", "imageMessage",
    }
    if type_message in media_message_types:
        try:
            media_user_result = (
                supabase.table("business_users")
                .select("id, approval_status")
                .eq("phone_number", sender_phone)
                .limit(1)
                .execute()
            )
            media_user = media_user_result.data[0] if media_user_result.data else None
            media_status = str((media_user or {}).get("approval_status") or "").casefold()
            if not media_user or media_status != "approved":
                ONBOARDING_SESSIONS.pop(sender_phone, None)
                print(
                    f"🔕 UNAPPROVED MEDIA SILENCED: phone={sender_phone}, "
                    f"type={type_message}, status={media_status or 'not_registered'}"
                )
                return {"status": "unapproved_user_silenced"}
        except Exception as media_approval_error:
            # Fail closed: do not process or respond to media if approval
            # cannot be verified from the database.
            print(
                f"⚠️ Media approval lookup failed; media ignored: "
                f"{type(media_approval_error).__name__}: {media_approval_error}"
            )
            return {"status": "media_approval_check_failed"}

    # Voice notes/audio are intentionally not transcribed or sent to Gemini.
    if type_message in {"audioMessage", "pttMessage", "voiceMessage", "voiceNoteMessage"}:
        send_whatsapp(sender_phone, "Fadlan qoraal soo qor.")
        return {"status": "audio_not_supported"}

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
            IMPORT_SESSIONS[sender_phone]["request_id"] = secrets.token_urlsafe(24)
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
            IMPORT_SESSIONS[sender_phone]["request_id"] = secrets.token_urlsafe(24)
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
        elif type_message in {"interactiveButtonReply", "interactiveButtonsResponse"}:
            reply_data = (
                message_data.get("interactiveButtonReply")
                or message_data.get("interactiveButtonsResponse")
                or message_data.get("templateButtonReplyMessage")
                or message_data.get("interactiveButtonReplyMessage")
                or {}
            )
            message_text = str(
                reply_data.get("selectedId")
                or reply_data.get("selectedButtonId")
                or reply_data.get("buttonId")
                or reply_data.get("selectedDisplayText")
                or reply_data.get("selectedButtonText")
                or reply_data.get("buttonText")
                or ""
            )
        else:
            print(f"⚠️ Unsupported incoming message type: {type_message}")
            return {"status": "unsupported_message_type", "type_message": type_message}
    except (KeyError, TypeError) as exc:
        print(f"❌ Could not extract incoming text: {type_message} - {exc}")
        return {"status": "no_text_payload"}

    print(f"📩 INCOMING MESSAGE TYPE: {type_message}")
    print(f"💬 EXTRACTED MESSAGE TEXT: {message_text!r}")
    # Green-API may return either a button ID ("3") or its visible title.
    # Normalize both forms so the same menu routing works for every response shape.
    _button_label = str(message_text or "").strip().casefold()
    _button_label_map = {
        "deyn cusub": "1",
        "dayn cusub": "1",
        "dayn soo xarootay": "2",
        "adeeg kale": "3",
        "tx_add": "1", "deyn cusub (add)": "1",
        "tx_pay": "2", "lacag-bixin": "2", "lacag bixin": "2",
        "tx_cancel": "3", "jooji": "3",
        "import_both": "2", "labadaba geli": "2",
        "import_single": "1", "hal deyn geli": "1",
        "undo_yes": "1", "haa, ka noqo": "1", "haa ka noqo": "1",
        "undo_no": "2", "maya, iska daa": "2", "maya iska daa": "2",
        "other_debt_list": "1", "liiska daynta": "1",
        "other_search": "2", "raadi macmiil": "2",
        "other_appointments": "3", "ballamaha maanta": "3",
        "other_help": "4", "caawimaad": "4",
        "other_import": "5", "soo geli daymo hore": "5",
        "other_payments": "6", "liiska lacag-bixinta": "6",
        "other_next": "7", "adeegyada xiga": "7", "other_back": "8", "ku noqo adeegyada hore": "8",
        "import_mode_debt": "DEYN", "deyn": "DEYN",
        "import_mode_payment": "LACAG BIXIN", "lacag-bixin": "LACAG BIXIN",
        "import_confirm_ok": "OK", "ok": "OK",
        "import_confirm_cancel": "CANCEL", "cancel": "CANCEL",
    }
    message_text = _button_label_map.get(_button_label, message_text)


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


    # Explicit leave/block requests must never be interpreted as customer names.
    # Only approved shop users receive this response; unknown users remain silent.
    if is_explicit_exit_or_block_request(message_text):
        try:
            exit_account = (supabase.table("business_users")
                .select("id, approval_status")
                .eq("phone_number", sender_phone)
                .limit(1).execute())
            if exit_account.data and str(exit_account.data[0].get("approval_status") or "").casefold() == "approved":
                exit_business_id = str(exit_account.data[0]["id"])
                clear_sender_workflow_sessions(sender_phone)
                cancel_sender_pending_database_work(sender_phone, exit_business_id)
                activate_guided_menu(sender_phone)
                send_whatsapp(
                    sender_phone,
                    deynjir_recovery_menu_message(
                        "Waan fahmay. Hawshii socotay waa la joojiyey; waxba cusub lama kaydin."
                    )
                )
                return {"status": "exit_request_handled"}
            return {"status": "unapproved_user_silenced"}
        except Exception as exit_error:
            print(f"⚠️ Exit request handling failed: {type(exit_error).__name__}: {exit_error}")
            # Do not fall through to customer/AI parsing for a clear exit request.
            return {"status": "exit_request_handling_error"}

    # Resolve UNDO only after the approved business account is known.
    undo_match = re.fullmatch(
        r"\s*(?:undo(?:\s+last)?|ka\s*noqo(?:to|n)?|ka\s+laab(?:o|ato)|dib\s+u\s+celi|ka\s+noqo\s+kii\s+ugu\s+dambeeyay|ka\s+noqo\s+tii\s+ugu\s+dambeeysay)(?:\s+(.+?))?\s*[.!]?\s*",
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
    active_import_for_router = IMPORT_SESSIONS.get(sender_phone)
    preempt_import_session = bool(
        active_import_for_router
        and is_clear_new_supported_request(import_text, include_transactions=False)
        and not re.fullmatch(r"\s*(?:OK|CANCEL|JOOJI|BAAJI|DEYN|DAYN|LACAG\s*BIXIN|PAYMENT|PAYMENTS|1|2)\s*", import_text, re.I)
    )
    if (((sender_phone == owner_phone) or (sender_phone in IMPORT_SESSIONS)) and not preempt_import_session or is_import_command) and not (
        is_payment_report_command(import_text) or sender_phone in PAYMENT_EXPORT_SESSIONS
    ):
        if re.fullmatch(r"\s*(?:CANCEL|JOOJI|BAAJI)\s*", import_text, re.I) and sender_phone in IMPORT_SESSIONS:
            IMPORT_SESSIONS.pop(sender_phone, None)
            activate_guided_menu(sender_phone)
            send_whatsapp(
                sender_phone,
                deynjir_recovery_menu_message("✅ Import-ka waa la joojiyey. Waxba lama kaydin.")
            )
            return {"status": "import_cancelled"}
        session_for_choice = IMPORT_SESSIONS.get(sender_phone)
        if session_for_choice and session_for_choice.get("stage") == "duplicate_choice":
            if re.fullmatch(r"\s*2\s*", import_text):
                _apply_import_duplicate_choice(session_for_choice, "2")
                session_for_choice["request_id"] = secrets.token_urlsafe(24)
                session_for_choice["stage"] = "ready"
                send_deynjir_choice_buttons(
                    sender_phone, "✅ Labada deymood waa la kala gelinayaa. Ma kaydinnaa?",
                    [("IMPORT_CONFIRM_OK", "OK, kaydi"), ("IMPORT_CONFIRM_CANCEL", "CANCEL, jooji")],
                    "✅ Labada deymood waa la kala gelinayaa. Soo qor *OK* si loo kaydiyo ama *CANCEL* si loo joojiyo."
                )
                return {"status": "import_duplicates_confirmed_separate"}
            if re.fullmatch(r"\s*1\s*", import_text):
                _apply_import_duplicate_choice(session_for_choice, "1")
                session_for_choice["request_id"] = secrets.token_urlsafe(24)
                session_for_choice["stage"] = "ready"
                send_deynjir_choice_buttons(
                    sender_phone, "✅ Hal deyn oo keliya ayaan kaydinayaa. Ma kaydiyaa?",
                    [("IMPORT_CONFIRM_OK", "OK, kaydi"), ("IMPORT_CONFIRM_CANCEL", "CANCEL, jooji")],
                    "✅ Hal deyn oo keliya ayaan kaydinayaa. Soo qor *OK* si aan u kaydiyo ama *CANCEL* si loo joojiyo."
                )
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
                        prompt = "\n".join(lines)
                        send_deynjir_choice_buttons(
                            sender_phone, prompt,
                            [("IMPORT_BOTH", "Labadaba geli"), ("IMPORT_SINGLE", "Hal deyn geli")],
                            prompt + "\n\nSoo dir *2* ama *1*, ama *CANCEL* si loo joojiyo."
                        )
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
                    "entries": None, "mode": None, "request_id": secrets.token_urlsafe(24),
                    "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL,
                }
                mode_prompt = f"✅ Magaca: {own_shop.get('name') or sender_phone}.\n\nMaxaad rabtaa inaad soo xarayso?"
                send_deynjir_choice_buttons(
                    sender_phone, mode_prompt,
                    [("IMPORT_MODE_DEBT", "DEYN"), ("IMPORT_MODE_PAYMENT", "LACAG BIXIN")],
                    mode_prompt + "\n\n*DEYN* — deymo cusub.\n*LACAG BIXIN* — Deyn soo xarootay.\n\nKadib ii soo dir qoraal, Excel/CSV ama sawir."
                )
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
                    "request_id": secrets.token_urlsafe(24), "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL}
                mode_prompt = f"✅ Dukaanka waa la doortay: {shop.get('name') or target_phone}.\n\nMaxaad rabtaa inaad soo geliso?"
                send_deynjir_choice_buttons(
                    sender_phone, mode_prompt,
                    [("IMPORT_MODE_DEBT", "DEYN"), ("IMPORT_MODE_PAYMENT", "LACAG BIXIN")],
                    mode_prompt + "\n\n*DEYN* — deymo cusub.\n*LACAG BIXIN* — lacagaha laga bixiyay deymaha jira.\n\nKadib ii soo dir qoraal, Excel/CSV ama sawir."
                )
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
                send_whatsapp(sender_phone, "✅ Waxaad dooratay *DEYN*. Soo dir liiska deynta qoraal ahaan, Excel/CSV ama sawir ahaan.")
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
                    if "GEMINI_TEMPORARILY_UNAVAILABLE" in str(exc):
                        send_whatsapp(sender_phone, "⏳ Adeegga akhrinta qoraalka hadda waa mashquul. Waxba lama kaydin. Fadlan dhowr daqiiqo kadib isla liiska mar kale soo dir.")
                        return {"status": "import_text_ai_temporarily_unavailable"}
                    send_whatsapp(sender_phone, "❌ Liiska si sax ah looma akhrin karo. Fadlan caddee magacyada iyo lacagaha, dabadeed mar kale soo dir.")
                    return {"status": "import_text_parse_error"}

    # Owner approves/rejects with: APPROVE 252... or REJECT 252...
    parts = message_text.strip().split(maxsplit=1)
    command = parts[0].upper() if parts else ""

    welcome_match = re.fullmatch(r"\s*WELCOME\s+(\+?\d{8,15})\s*", str(message_text or ""), re.I)
    if welcome_match:
        if sender_phone != owner_phone:
            send_whatsapp(sender_phone, "❌ Amarkan waxaa isticmaali kara maamulka oo keliya.")
            return {"status": "welcome_command_forbidden"}
        target_phone = welcome_match.group(1).replace("+", "").strip()
        try:
            target_result = (supabase.table("business_users")
                .select("id, phone_number, name, approval_status")
                .eq("phone_number", target_phone).limit(1).execute())
            if not target_result.data:
                send_whatsapp(sender_phone, "❌ Lambarkan dukaan kuma jiro systemka. Marka hore diiwaangeli oo ansixi.")
                return {"status": "welcome_target_not_found"}
            target_shop = target_result.data[0]
            if str(target_shop.get("approval_status") or "").casefold() != "approved":
                send_whatsapp(sender_phone, "❌ Dukaankan weli lama ansixin. Marka hore ku ansixi APPROVE 252... kadib dir WELCOME 252...")
                return {"status": "welcome_target_not_approved"}
            FIRST_DEBT_SESSIONS[target_phone] = {
                "business_user_id": str(target_shop["id"]),
                "stage": "entry",
                "request_id": f"first-debt:{secrets.token_urlsafe(18)}",
                "expires_at": datetime.now(timezone.utc) + FIRST_DEBT_SESSION_TTL,
            }
            welcome_sent = send_whatsapp(
                target_phone,
                "Ku soo dhawoow Deynjir! 👋\n\n"
                "Aan kuu diiwaangeliyo Deymaha kaa maqan.\n\n"
                "Ii soo qor magaca qofka iyo lacagta aad ku leedahay.\n",
                schedule_pending=False,
            )
            if not welcome_sent:
                FIRST_DEBT_SESSIONS.pop(target_phone, None)
                send_whatsapp(sender_phone, "❌ WhatsApp-ku ma xaqiijin dirista fariinta. Fadlan hubi Green-API iyo lambarka, kadib mar kale isku day.")
                return {"status": "first_debt_welcome_send_failed"}
            _save_persisted_workflow_sessions(target_phone)
            send_whatsapp(sender_phone, f"✅ Fariinta soo-dhaweynta waxaa loo diray {target_phone}.")
            return {"status": "first_debt_welcome_sent"}
        except Exception as welcome_error:
            print(f"❌ WELCOME command failed: {type(welcome_error).__name__}: {welcome_error}")
            send_whatsapp(sender_phone, "❌ Fariintii lama dirin. Hubi lambarka.")
            return {"status": "first_debt_welcome_error"}

    if sender_phone == owner_phone and command in {"APPROVE", "REJECT"}:
        if len(parts) != 2:
            send_whatsapp(sender_phone, "Isticmaal Qaababkan:\n*APPROVE 252...* — oggolow codsiga.\n*REJECT 252...* — diid codsiga.")
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
            if new_status == "approved":
                ONBOARDING_SESSIONS[applicant_phone] = {
                    "stage": "first_successful_action",
                    "created_at": datetime.now(timezone.utc),
                }
            send_whatsapp(
                applicant_phone,
                (
                    "🎉 *Waxaa lagugu soo daray Nidaamka Deynjir!*\n\n"
                    "Waxaan kaa caawinayaa inaad si fudud ula socoto daymaha iyo balamaha macaamiishaada. Aan ku bilowno hal macaamil oo keliya. \n\n"
                    "*Ii soo qor magaca qofka iyo lacagta aad ku leedahay*"
                )
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

        # Admin-triggered first-debt onboarding. This flow is deterministic and
        # deliberately runs before conversational AI, Gemini parsing, and the
        # general guided transaction system.
        first_debt = FIRST_DEBT_SESSIONS.get(sender_phone)
        if first_debt and first_debt.get("business_user_id") == str(business_user_id):
            expiry = first_debt.get("expires_at")
            if not expiry or datetime.now(timezone.utc) > expiry:
                FIRST_DEBT_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "si aad u xarayso deyn cusub soo qor magaca macmiilka iyo lacagta lagu leeyahay.")
                return {"status": "first_debt_session_expired"}

            first_text = str(message_text or "").strip()
            first_norm = normalize_customer_name(first_text).strip(" .!?؟")
            if first_norm in {"jooji", "cancel", "baaji", "dhamaad", "dhammaad", "done", "finish", "menu"}:
                FIRST_DEBT_SESSIONS.pop(sender_phone, None)
                if first_norm == "menu":
                    send_whatsapp(sender_phone, deynjir_help_message())
                else:
                    send_whatsapp(sender_phone, "Waa hagaag. Habkii diiwaangelinta daynta waa la joojiyey. Markaad diyaar tahay, soo qor MENU.")
                return {"status": "first_debt_onboarding_closed"}

            # Let explicit non-onboarding commands interrupt the flow safely.
            if first_debt.get("stage") != "entry" and re.match(
                r"^(?:liiska|liis|raadi|raadso|search|history|faahfaahin|import|lacag\s*bixin|xusuusin|report|export|delete|tirtir|undo|balamaha|ballamaha)\b",
                first_norm, re.I,
            ):
                FIRST_DEBT_SESSIONS.pop(sender_phone, None)
                first_debt = None
            else:
                stage = first_debt.get("stage")
                if stage == "entry":
                    parsed_first = local_fallback_parse(first_text) or []
                    valid = (
                        isinstance(parsed_first, list) and len(parsed_first) == 1
                        and str(parsed_first[0].get("action") or "").upper() == "ADD"
                        and parsed_first[0].get("customer_name")
                        and parsed_first[0].get("amount") is not None
                        and not parsed_first[0].get("customer_phone")
                    )
                    if not valid:
                        send_whatsapp(sender_phone,
                            "Fadlan ii soo qor magaca qofka iyo lacagta aad ku leedahay.\n"
                            "Tusaale: *Cali $50*.\n\nQor *JOOJI* haddii aad rabto inaad ka baxdo.")
                        return {"status": "first_debt_entry_invalid"}
                    entry = parsed_first[0]
                    amount_value = float(entry["amount"])
                    customer_name = str(entry["customer_name"]).strip()
                    if not customer_name or len(customer_name) > 100 or not math.isfinite(amount_value) or amount_value <= 0:
                        send_whatsapp(sender_phone, "Magaca ama lacagtu sax ma aha. Tusaale ahaan qor: *Cali $50*.")
                        return {"status": "first_debt_entry_invalid"}
                    first_debt.update({"customer_name": customer_name, "amount": round(amount_value, 2), "stage": "due_date"})
                    first_debt["expires_at"] = datetime.now(timezone.utc) + FIRST_DEBT_SESSION_TTL
                    send_whatsapp(sender_phone,
                        f"Goorma ayuu *{customer_name}* ballan qaaday inuu lacagta bixiyo?\n\n"
                        "Haddii uusan ballan lahayn, qor *MA HUBO*.")
                    return {"status": "first_debt_due_date_requested"}

                if stage == "due_date":
                    parsed_due = parse_first_debt_due_date(first_text)
                    if parsed_due is None:
                        send_whatsapp(sender_phone,
                            "Ma fahmin taariikhda. Fadlan soo qor sida *13/11/2026*, *berri*, *Jimcaha*, ama *MA HUBO* haddii uusan ballan lahayn.")
                        return {"status": "first_debt_due_date_invalid"}
                    first_debt["promised_date"] = None if parsed_due == "none" else parsed_due.isoformat()
                    first_debt["stage"] = "confirm"
                    first_debt["expires_at"] = datetime.now(timezone.utc) + FIRST_DEBT_SESSION_TTL
                    due_label = "-" if not first_debt["promised_date"] else parsed_due.strftime("%d/%m/%Y")
                    send_whatsapp(sender_phone,
                        "Hubi xogta daynta:\n\n"
                        f"• Qofka: *{first_debt['customer_name']}*\n"
                        f"• Lacagta: *${first_debt['amount']:.2f}*\n"
                        f"• Ballanta: *{due_label}*\n\n"
                        "Ma diiwaangeliyaa? Soo qor *HAA* ama *MAYA*.\n"
                        "Waxba lama kaydin ilaa aad soo qorto *HAA*.")
                    return {"status": "first_debt_confirmation_requested"}

                if stage == "name_correction":
                    if len(first_text) < 2 or len(first_text) > 100 or re.search(r"\d", first_text):
                        send_whatsapp(sender_phone, "Fadlan soo qor magaca buuxa ee qofka, ama qor JOOJI.")
                        return {"status": "first_debt_name_correction_invalid"}
                    first_debt["customer_name"] = first_text
                    first_debt["stage"] = "confirm"
                    due = first_debt.get("promised_date")
                    due_label = "-" if not due else datetime.strptime(due, "%Y-%m-%d").strftime("%d/%m/%Y")
                    send_whatsapp(sender_phone,
                        "Hubi xogta daynta:\n\n"
                        f"• Qofka: *{first_text}*\n"
                        f"• Lacagta: *${float(first_debt['amount']):.2f}*\n"
                        f"• Ballanta: *{due_label}*\n\n"
                        "Ma diiwaangeliyaa? Soo qor *HAA* ama *MAYA*.")
                    return {"status": "first_debt_name_corrected"}

                if stage == "confirm":
                    if first_norm in {"maya", "may", "no", "2"}:
                        first_debt["stage"] = "due_date"
                        send_whatsapp(sender_phone,
                            "Waa hagaag. Soo qor taariikhda saxda ah, tusaale *13/11/2026* ama *berri*. "
                            "Haddii uusan ballan lahayn, qor *MA HUBO*.")
                        return {"status": "first_debt_due_date_correction_requested"}
                    if first_norm not in {"haa", "h", "yes", "y", "ok", "sax", "1"}:
                        send_whatsapp(sender_phone, "Fadlan ku jawaab *HAA* si loo diiwaangeliyo ama *MAYA* si aad taariikhda u saxdo. Qor *JOOJI* si aad uga baxdo.")
                        return {"status": "first_debt_confirmation_invalid"}

                    customer_name = str(first_debt.get("customer_name") or "").strip()
                    amount_value = float(first_debt.get("amount") or 0)
                    if not customer_name or not math.isfinite(amount_value) or amount_value <= 0:
                        FIRST_DEBT_SESSIONS.pop(sender_phone, None)
                        send_whatsapp(sender_phone, "Xogtii daynta ma dhammaystirnayn. Fadlan mar kale bilow.")
                        return {"status": "first_debt_state_invalid"}

                    try:
                        matches = find_debtor_matches(business_user_id, customer_name)
                        distinct_names = _unique_customer_names(matches)
                        if len(distinct_names) > 1:
                            first_debt["stage"] = "name_correction"
                            send_whatsapp(sender_phone,
                                f"Waxaan helay dhowr qof oo magacyadoodu u egyihiin *{customer_name}*. "
                                "Fadlan soo qor magaca buuxa si aan qofka saxda ah u doorto. Waxba weli lama kaydin.")
                            return {"status": "first_debt_name_disambiguation_requested"}
                        active_matches = [row for row in matches if row.get("is_paid") is not True and float(row.get("amount") or 0) > 0]
                        if len(active_matches) > 1:
                            FIRST_DEBT_SESSIONS.pop(sender_phone, None)
                            send_whatsapp(sender_phone,
                                f"Waxaan helay dhowr deyn oo hore ugu qoran *{customer_name}*. Si aanan u khaldin xisaabta, habkan koowaad waa la joojiyey. "
                                "Fadlan isticmaal habka caadiga ah ee ku darista deynta ama la xiriir maamulka.")
                            return {"status": "first_debt_multiple_active_records"}
                        matched_customer = active_matches[0] if active_matches else None
                        write_result = _financial_rpc("record_debt_addition", {
                            "p_customer_id": str(matched_customer["id"]) if matched_customer else None,
                            "p_business_user_id": str(business_user_id),
                            "p_name": str((matched_customer or {}).get("name") or customer_name),
                            "p_amount": round(amount_value, 2),
                            "p_description": "-",
                            "p_promised_date": first_debt.get("promised_date"),
                            "p_phone_number": None,
                            "p_created_at": None,
                        }, request_id=first_debt.get("request_id")).execute()
                        saved = write_result.data
                        if isinstance(saved, list):
                            saved = saved[0] if saved else None
                        if not isinstance(saved, dict) or not saved.get("id"):
                            raise RuntimeError("record_debt_addition returned no customer row")
                        remember_selected_customer(sender_phone, business_user_id, saved.get("name") or customer_name)
                        remember_recent_transaction(sender_phone, business_user_id, saved.get("id"), saved.get("name") or customer_name)
                        due_saved = saved.get("promised_date") or first_debt.get("promised_date")
                        due_saved_label = "-" if not due_saved else datetime.strptime(str(due_saved), "%Y-%m-%d").strftime("%d/%m/%Y")
                        send_whatsapp(sender_phone,
                            f"✅ Daynta *{saved.get('name') or customer_name}* waa la diiwaangeliyey.\n"
                            f"Lacagta: *${float(saved.get('amount') or amount_value):.2f}*\n"
                            f"Ballanta: *{due_saved_label}*\n\n"
                            "Hadda soo qor qofka ku xiga iyo lacagta aad ku leedahay.\n\n"
                            "Markaad dhamayso, qor *DHAMMAAD* ama *MENU*.")
                        first_debt.update({
                            "stage": "entry", "customer_name": None, "amount": None,
                            "promised_date": None,
                            "request_id": f"first-debt:{secrets.token_urlsafe(18)}",
                            "expires_at": datetime.now(timezone.utc) + FIRST_DEBT_SESSION_TTL,
                        })
                        return {"status": "first_debt_saved"}
                    except Exception as first_debt_error:
                        print(f"❌ First debt onboarding save failed: {type(first_debt_error).__name__}: {first_debt_error}")
                        send_whatsapp(sender_phone,
                            "❌ Daynta lama diiwaangelin. Fadlan mar kale soo qor *HAA* si aan dib ugu hubiyo, "
                            "ama *JOOJI* si aad uga baxdo. Wax kale lama xaqiijin.")
                        return {"status": "first_debt_save_error"}

                # Unknown state: fail closed rather than routing a stale answer into AI.
                FIRST_DEBT_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Wadahadalkii daynta koowaad wuu khaldamay. Fadlan la xiriir maamulka si mar kale laguugu bilaabo.")
                return {"status": "first_debt_unknown_stage"}

        # Active undo/rename sessions own their replies. In particular, "1" and
        # "2" are confirmation answers here, not ADD/PAY direction choices.
        pending_undo = UNDO_CONFIRMATION_SESSIONS.get(sender_phone)
        undo_waiting_for_this_shop = bool(
            pending_undo and pending_undo.get("business_user_id") == str(business_user_id)
        )
        pending_rename = RENAME_SESSIONS.get(sender_phone)
        rename_waiting_for_this_shop = bool(
            pending_rename and pending_rename.get("business_user_id") == str(business_user_id)
        )
        normalized_inbound = normalize_customer_name(message_text).strip(" .!?؟")
        guided_waiting = GUIDED_SESSIONS.get(sender_phone) or {}
        expired_menu_choice = False
        if guided_waiting:
            guided_expiry = guided_waiting.get("expires_at")
            if not guided_expiry or datetime.now(timezone.utc) > guided_expiry:
                expired_menu_choice = (
                    guided_waiting.get("stage") in {"menu", "menu_other", "menu_other_page2", "menu_other_page3"}
                    and str(message_text or "").strip() in {"1", "2", "3", "4", "5", "6"}
                )
                GUIDED_SESSIONS.pop(sender_phone, None)
                guided_waiting = {}
        rename_interrupt = bool(re.match(
            r"^(?:menu|start|help|add|pay|deyn|dayn|lacag\s*bixin|import|delete|remove|"
            r"tirtir|undo|dhigaal|liiska|raadi|search|history|taariikh|faahfaahin|sax)\b",
            normalized_inbound, re.I,
        ))
        pending_new_request = (
            _has_active_in_memory_workflow(sender_phone)
            and not undo_waiting_for_this_shop
            and not (rename_waiting_for_this_shop and not rename_interrupt)
            and is_clear_new_supported_request(message_text, include_transactions=True)
        )
        # CUSUB and help are replies inside an active customer-match workflow,
        # not new financial requests. Keep the saved ADD/PAY entry (name + amount)
        # so rejecting a suggested match never forces the shopkeeper to retype it.
        active_customer_match = CUSTOMER_MATCH_SESSIONS.get(sender_phone) or {}
        customer_match_waiting_for_shop = (
            active_customer_match.get("business_user_id") == str(business_user_id)
        )
        if customer_match_waiting_for_shop and (
            normalized_inbound in {"cusub"}
            or re.search(r"\b(?:caawin|caawi|help)\b", normalized_inbound, re.I)
        ):
            pending_new_request = False
        if (
            customer_match_waiting_for_shop
            and active_customer_match.get("stage") == "confirm_extracted_name"
            and not is_name_confirmation_interrupt_command(message_text)
        ):
            # The next bare message is the requested correction, not a new search.
            pending_new_request = False
        if rename_waiting_for_this_shop and rename_interrupt:
            RENAME_SESSIONS.pop(sender_phone, None)
        direction_reply = parse_transaction_clarification(message_text)
        numeric_reply = str(message_text or "").strip()
        guided_menu_choice = (
            guided_waiting.get("stage") in {"menu", "menu_other", "menu_other_page2", "menu_other_page3"}
            and numeric_reply in {"1", "2", "3", "4", "5", "6", "7", "8"}
        )
        guided_amount_reply = guided_waiting.get("stage") in {"debt_amount", "payment_amount"} and _guided_amount(numeric_reply) is not None
        deposit_waiting = DEPOSIT_OFFER_SESSIONS.get(sender_phone) or {}
        correction_waiting = CORRECTION_SESSIONS.get(sender_phone) or {}
        financial_confirmation_reply = (
            (deposit_waiting.get("business_user_id") == str(business_user_id)
             or correction_waiting.get("business_user_id") == str(business_user_id))
            and normalize_customer_name(numeric_reply).strip(" .!?؟") in {"1", "2", "haa", "h", "yes", "y", "ok", "maya", "may", "no", "n", "cancel", "jooji"}
        )
        delete_waiting = DELETE_SESSIONS.get(sender_phone) or {}
        if guided_menu_choice or guided_amount_reply or financial_confirmation_reply:
            pending_new_request = False
        if delete_waiting.get("stage") == "confirm" and normalize_customer_name(message_text).strip(" .!?؟") == "tirtir":
            pending_new_request = False
        if (
            _has_active_in_memory_workflow(sender_phone)
            and not undo_waiting_for_this_shop
            and not (rename_waiting_for_this_shop and not rename_interrupt)
            and direction_reply in {"ADD", "PAY"}
            and not guided_menu_choice
            and not guided_amount_reply
            and not financial_confirmation_reply
        ):
            pending_new_request = True
        if pending_new_request:
            # A clearly new request replaces an unfinished guided task. Do not
            # leave it hidden in memory where it can intercept a later number.
            if (
                customer_match_waiting_for_shop
                and active_customer_match.get("stage") == "confirm_extracted_name"
            ):
                CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
            GUIDED_SESSIONS.pop(sender_phone, None)
            PAUSED_GUIDED_SESSIONS.pop(sender_phone, None)
            print(
                f"🔀 New supported request replaced the prior guided state for "
                f"{sender_phone}: {message_text!r}"
            )

        # Resolve an already-open UNDO confirmation before interpreting this reply
        # as a new command. Only explicit 1/HAA or 2/MAYA responses are accepted.
        if undo_waiting_for_this_shop and pending_undo and not pending_new_request:
            if datetime.now(timezone.utc) > pending_undo.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
                UNDO_CONFIRMATION_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Waqtigii xaqiijinta ka-noqoshadu wuu dhammaaday. Waxba lama beddelin. Haddii loo baahdo, codsiga mar kale dir.")
                return {"status": "undo_confirmation_expired"}
            answer = undo_confirmation_answer(message_text)
            if answer == "no":
                UNDO_CONFIRMATION_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "✅ Waa hagaag. Macaamilka sidii uu ahaa ayaan u reebay. Waxba lama beddelin.")
                return {"status": "undo_cancelled"}
            if answer == "yes":
                UNDO_CONFIRMATION_SESSIONS.pop(sender_phone, None)
                try:
                    if pending_undo.get("batch_transactions"):
                        undo_result = _financial_rpc("undo_debt_batch_confirmed", {
                            "p_business_user_id": str(business_user_id),
                            "p_transactions": pending_undo["batch_transactions"],
                        }, request_id=pending_undo.get("request_id") or f"undo-batch:{secrets.token_urlsafe(16)}").execute()
                        undo_data = undo_result.data
                        if isinstance(undo_data, list):
                            undo_data = undo_data[0] if undo_data else None
                        if not isinstance(undo_data, dict) or undo_data.get("success") is not True:
                            raise RuntimeError("Database-ku ma xaqiijin ka-noqoshada dhammaan deymaha batch-ka.")
                        LAST_BATCH_CONTEXT.pop(sender_phone, None)
                        LAST_TRANSACTION_CONTEXT.pop(sender_phone, None)
                        send_whatsapp(sender_phone,
                            "✅ *Dhammaan deymaha batch-kii ugu dambeeyay waa laga noqday.*\n\n"
                            f"Tirada macaamiisha: *{int(undo_data.get('count') or len(pending_undo['batch_transactions']))}*\n"
                            f"Wadarta lacagta: *${float(pending_undo.get('total') or 0):.2f}*\n\n"
                            "Taariikhda macaamillada waa la hayey si raad-raac loo helo.")
                        return {"status": "batch_undo_completed"}

                    undo_result = _financial_rpc("undo_customer_transaction_confirmed", {
                        "p_customer_id": pending_undo["customer_id"],
                        "p_business_user_id": str(business_user_id),
                        "p_expected_transaction_id": pending_undo["transaction_id"],
                    }, request_id=pending_undo.get("request_id") or f"undo:{pending_undo['transaction_id']}").execute()
                    undo_data = undo_result.data
                    if isinstance(undo_data, list):
                        undo_data = undo_data[0] if undo_data else None
                    if not isinstance(undo_data, dict) or not undo_data.get("success"):
                        raise RuntimeError("Database-ku ma xaqiijin ka-noqoshada.")
                    customer_after = undo_data.get("customer") or {}
                    undone_type = str(undo_data.get("transaction_type") or "").upper()
                    type_so = {"ADD": "deyn lagu daray", "PAY": "lacag-bixin", "DEPOSIT": "dhigaal", "ADD + DHIGAAL": "deyn iyo isticmaalka dhigaalka"}.get(undone_type, "macaamil")
                    restored_credit = undo_data.get("restored_credit_balance")
                    credit_line = f"\nHaraaga dhigaalka: ${float(restored_credit):.2f}" if restored_credit is not None else ""
                    send_whatsapp(sender_phone,
                        f"✅ Macaamilkii waa laga noqday.\n\nMacmiil: *{customer_after.get('name') or pending_undo.get('customer_name')}*\n"
                        f"Nooca: {type_so}\nLacagta: *${float(undo_data.get('amount') or 0):.2f}*\n"
                        f"Hadhaaga Hada: *${float(customer_after.get('amount') or 0):.2f}*{credit_line}\n\n")
                    LAST_TRANSACTION_CONTEXT.pop(sender_phone, None)
                    return {"status": "undo_completed", "transaction_type": undone_type}
                except Exception as undo_error:
                    print(f"❌ Confirmed UNDO error: {type(undo_error).__name__}: {undo_error}")
                    send_whatsapp(sender_phone, "⚠️ Deyntan lagama noqon. khalad jira awgii.")
                    return {"status": "undo_failed"}
            send_whatsapp(sender_phone, "Fadlan ku jawaab *1* = HAA, ka noqo; ama *2* = MAYA, xaree oo sii hay.\nWaqtigu waa 5 daqiiqo.")
            return {"status": "undo_confirmation_waiting"}

        # An explicitly displayed menu owns its numeric replies. Route these
        # before import/search/AI/session handlers so option 4 or 5 cannot be
        # mistaken for a debt name, amount, or another workflow's answer.
        if expired_menu_choice:
            send_whatsapp(sender_phone, "Waqtigii menu-ga wuu dhammaaday. Soo qor *MENU* si aad u doorato adeegga aad rabto.")
            return {"status": "menu_choice_expired"}

        if guided_menu_choice:
            choice = numeric_reply
            menu_stage = guided_waiting.get("stage")

            # MAIN MENU: 1 = new debt, 2 = received payment, 3 = other services.
            if menu_stage == "menu":
                if choice == "1":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "debt_name",
                        "transaction_type": "debt",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                    }
                    send_whatsapp(
                        sender_phone,
                        "Magaca macmiilka deynta lagu leeyahay?\\n\\n"
                        "Qor *JOOJI* si aad uga baxdo."
                    )
                    return {"status": "guided_debt_name_requested"}

                if choice == "2":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "payment_name",
                        "transaction_type": "payment",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                    }
                    send_whatsapp(
                        sender_phone,
                        "Magaca qofka lacagta bixiyey?\\n\\n"
                        "Qor *JOOJI* si aad uga baxdo."
                    )
                    return {"status": "guided_payment_name_requested"}

                if choice == "3":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "menu_other",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL,
                    }
                    send_deynjir_other_services_menu(sender_phone)
                    return {"status": "other_services_menu_sent"}

            # OTHER SERVICES MENU: numbers are interpreted only in this stage.
            elif menu_stage == "menu_other":
                if choice == "7":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "menu_other_page2",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL,
                    }
                    send_deynjir_other_services_menu(sender_phone, page=2)
                    return {"status": "other_services_page_two_sent"}
                if choice == "1":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    message_text = "LIISKA DAYNTA"

                elif choice == "2":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "search_name",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                    }
                    send_whatsapp(
                        sender_phone,
                        "Qor magaca macmiilka aad raadinayso.\n\n"
                        "Qor *JOOJI* si aad uga baxdo."
                    )
                    return {"status": "guided_search_name_requested"}

                elif choice == "3":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    message_text = "Balamaha Maanta"

                elif choice == "4":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    send_whatsapp(sender_phone, deynjir_help_message())
                    return {"status": "help_sent"}

                elif choice == "5":
                    # Start import directly: the import router runs earlier in this webhook.
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    shop_name = str((business_user or {}).get("name") or sender_phone)
                    IMPORT_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id),
                        "shop_phone": sender_phone,
                        "shop_name": shop_name,
                        "entries": None,
                        "mode": None,
                        "request_id": secrets.token_urlsafe(24),
                        "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL,
                    }
                    mode_prompt = f"✅ Magaca: {shop_name}.\n\nMaxaad rabtaa inaad soo xarayso?"
                    send_deynjir_choice_buttons(
                        sender_phone, mode_prompt,
                        [("IMPORT_MODE_DEBT", "DEYN"), ("IMPORT_MODE_PAYMENT", "LACAG BIXIN")],
                        mode_prompt + "\n\n*DEYN* — deymo cusub.\n*LACAG BIXIN* — Deyn soo xarootay.\n\nKadib ii soo dir qoraal, Excel/CSV ama sawir."
                    )
                    return {"status": "menu_import_started"}

                elif choice == "6":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    message_text = "LIISKA LACAG BIXINTA"

                else:
                    send_whatsapp(
                        sender_phone,
                        "Fadlan dooro lambar u dhexeeya 1 iyo 6.\n\n"
                    )
                    send_deynjir_other_services_menu(sender_phone, page=1)
                    return {"status": "other_services_invalid_choice"}

            elif menu_stage == "menu_other_page2":
                if choice == "3":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    message_text = "Balamaha Maanta"
                elif choice == "4":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    send_whatsapp(sender_phone, deynjir_help_message())
                    return {"status": "help_sent"}
                elif choice == "7":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "menu_other_page3",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL,
                    }
                    send_deynjir_other_services_menu(sender_phone, page=3)
                    return {"status": "other_services_page_three_sent"}
                else:
                    send_deynjir_other_services_menu(sender_phone, page=2)
                    return {"status": "other_services_invalid_choice"}

            elif menu_stage == "menu_other_page3":
                if choice == "5":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    shop_name = str((business_user or {}).get("name") or sender_phone)
                    IMPORT_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id),
                        "shop_phone": sender_phone,
                        "shop_name": shop_name,
                        "entries": None,
                        "mode": None,
                        "request_id": secrets.token_urlsafe(24),
                        "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL,
                    }
                    mode_prompt = f"✅ Magaca: {shop_name}.\n\nMaxaad rabtaa inaad soo xarayso?"
                    send_deynjir_choice_buttons(
                        sender_phone, mode_prompt,
                        [("IMPORT_MODE_DEBT", "DEYN"), ("IMPORT_MODE_PAYMENT", "LACAG BIXIN")],
                        mode_prompt + "\\n\\n*DEYN* — deymo cusub.\\n*LACAG BIXIN* — Deyn soo xarootay.\\n\\nKadib ii soo dir qoraal, Excel/CSV ama sawir."
                    )
                    return {"status": "menu_import_started"}
                if choice == "6":
                    GUIDED_SESSIONS.pop(sender_phone, None)
                    message_text = "LIISKA LACAG BIXINTA"
                elif choice == "8":
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "menu",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL,
                    }
                    send_deynjir_other_services_menu(sender_phone, page=1)
                    return {"status": "other_services_page_one_sent"}
                else:
                    send_deynjir_other_services_menu(sender_phone, page=3)
                    return {"status": "other_services_invalid_choice"}

        # A disagreement shortly after a committed transaction opens a confirmation;
        # the bot never reverses anything based on AI classification alone.
        recent_tx = LAST_TRANSACTION_CONTEXT.get(sender_phone) or {}
        has_other_active_session = any(sender_phone in session_map for session_map in (
            IMPORT_SESSIONS, CUSTOMER_MATCH_SESSIONS, GUIDED_SESSIONS,
            AMOUNT_EDIT_SESSIONS, RENAME_SESSIONS, DELETE_SESSIONS,
            PAYMENT_EXPORT_SESSIONS, REMINDER_SESSIONS,
        ))
        has_active_payment_confirmation = False
        if (recent_tx.get("business_user_id") == str(business_user_id)
                and isinstance(recent_tx.get("created_at"), datetime)
                and datetime.now(timezone.utc) - recent_tx["created_at"] <= UNDO_CONFIRMATION_TTL
                and is_transaction_disagreement(message_text)):
            # Do not steal a HAA/MAYA reply that belongs to the existing PAY confirmation.
            try:
                active_payment_check = (supabase.table("pending_payment_confirmations")
                    .select("id")
                    .eq("sender_phone", sender_phone)
                    .eq("business_user_id", str(business_user_id))
                    .in_("status", ["pending", "processing"])
                    .limit(1).execute())
                has_active_payment_confirmation = bool(active_payment_check.data)
            except Exception as pending_check_error:
                print(f"⚠️ Could not check pending payment before disagreement detection: {pending_check_error}")
                has_active_payment_confirmation = True
        if (not has_other_active_session
                and not has_active_payment_confirmation
                and recent_tx.get("business_user_id") == str(business_user_id)
                and isinstance(recent_tx.get("created_at"), datetime)
                and datetime.now(timezone.utc) - recent_tx["created_at"] <= UNDO_CONFIRMATION_TTL
                and is_transaction_disagreement(message_text)):
            try:
                preview_result = supabase.rpc("get_latest_customer_transaction_for_undo", {
                    "p_customer_id": recent_tx["customer_id"],
                    "p_business_user_id": str(business_user_id),
                }).execute()
                preview = preview_result.data
                if isinstance(preview, list):
                    preview = preview[0] if preview else None
                if isinstance(preview, dict) and preview.get("transaction_id"):
                    UNDO_CONFIRMATION_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id),
                        "customer_id": str(recent_tx["customer_id"]),
                        "customer_name": str(preview.get("customer_name") or recent_tx.get("customer_name")),
                        "transaction_id": str(preview["transaction_id"]),
                        "transaction_type": str(preview.get("transaction_type") or ""),
                        "amount": float(preview.get("amount") or 0),
                        "request_id": f"undo:{secrets.token_urlsafe(18)}",
                        "expires_at": datetime.now(timezone.utc) + UNDO_CONFIRMATION_TTL,
                    }
                    undo_prompt = (
                        f"⚠️ Waxaad u muuqataa inaadan ku qanacsanayn macaamilkii ugu dambeeyay.\n\n"
                        f"Macmiil: *{preview.get('customer_name') or recent_tx.get('customer_name')}*\n"
                        f"Lacagta: *${float(preview.get('amount') or 0):.2f}*\n\n"
                        "*Ma rabtaa inaad ka noqoto macaamilkan?*\n\n"
                        "Waxba lama beddelayo ilaa aad xaqiijiso."
                    )
                    send_deynjir_choice_buttons(
                        sender_phone, undo_prompt,
                        [("UNDO_YES", "Haa, ka noqo"), ("UNDO_NO", "Maya, iska daa")],
                        undo_prompt + "\n\n1️⃣ HAA — Ka noqo (UNDO)\n2️⃣ MAYA — Waa sax, xaree\nKu jawaab 1 ama 2."
                    )
                    return {"status": "undo_confirmation_requested"}
            except Exception as preview_error:
                print(f"⚠️ Could not preview latest transaction for disagreement: {type(preview_error).__name__}: {preview_error}")

        # Privacy/security questions must never be misclassified as EXPORT or another financial action.
        if is_privacy_question(message_text):
            privacy_reply = (
                "Su'aal muhiim ah. Deynjir wuxuu xogta u isticmaalaa maareynta deymaha "
                "dukaankaaga, hawlaha dukaankana wuxuu ku kala saaraa aqoonsiga dukaanka. "
                "Cidda geli karta xogta maamulka waxay ku xiran tahay rukhsadaha database-ka "
                "iyo cidda haysata gelitaanka maamulka. Ma doonayo inaan kuu ballanqaado "
                "in qof kale aanu arki karin anigoon hubin dejinta amniga."
            )
            remember_conversation_outcome(sender_phone, message_text, privacy_reply)
            send_whatsapp(sender_phone, privacy_reply)
            return {"status": "privacy_question_answered"}

        active_guided = GUIDED_SESSIONS.get(sender_phone)
        if is_deynjir_greeting(message_text):
            if active_guided and active_guided.get("stage") not in {"menu"}:
                greeting_reply = (
                    "Wacalaykum salaam! 😊 Wadahadalkii hore weli wuu socdaa. "
                    "Fadlan ka jawaab su'aashii aan ku weydiiyey ama qor *JOOJI*."
                )
            else:
                greeting_reply = "Wacalaykum salaam! 😊 Maxaad rabtaa inaan kaa caawiyo?"
            remember_conversation_outcome(sender_phone, message_text, greeting_reply)
            send_whatsapp(sender_phone, greeting_reply)
            return {"status": "greeting_answered"}

        if is_postponing_guided_task(message_text) and (not active_guided or active_guided.get("stage") in {"menu", "debt_name"}):
            GUIDED_SESSIONS.pop(sender_phone, None)
            postpone_reply = (
                "Dhib ma leh 😊 Tijaabi inta aad rabto. Marka macmiil deyn qaato "
                "ama lacag bixiyo, ii sheeg magaciisa iyo lacagta. Waxba hadda lama diiwaangelin."
            )
            remember_conversation_outcome(sender_phone, message_text, postpone_reply)
            send_whatsapp(sender_phone, postpone_reply)
            return {"status": "guided_task_postponed"}

        # First-time questions should not clear or cancel unrelated financial workflows.
        # Only explicit frustration recovery may clear an unfinished workflow.
        if is_user_frustrated(message_text):
            clear_sender_workflow_sessions(sender_phone)
            cancel_sender_pending_database_work(sender_phone, business_user_id)
            fallback_reply = "Waan ku fahmay, iga raalli noqo. Ii sheeg waxa aad rabto, waan ku hagi doonaa."
            reply = generate_deynjir_conversation_reply(message_text, fallback_reply, sender_phone)
            send_whatsapp(sender_phone, reply or fallback_reply)
            return {"status": "conversational_help_sent"}

        if normalize_customer_name(message_text).strip(" .!?؟") in {"ma garanayo", "ma aqaan"}:
            if active_guided and active_guided.get("stage") in {"debt_name", "payment_name"}:
                GUIDED_SESSIONS.pop(sender_phone, None)
            no_customer_reply = (
                "Dhib ma leh. Hadda waxba ha gelin. Marka macmiil jiro, "
                "ii sheeg magaciisa iyo lacagta."
            )
            remember_conversation_outcome(sender_phone, message_text, no_customer_reply)
            send_whatsapp(sender_phone, no_customer_reply)
            return {"status": "no_customer_yet_helped"}

        if is_somali_confusion_request(message_text):
            fallback_reply = "Ku soo dhawoow Deynjir! 😊 Tusaale ahaan, qor: Cali $20 ayuu deyn qaatay."
            reply = generate_deynjir_conversation_reply(message_text, fallback_reply, sender_phone)
            send_whatsapp(sender_phone, reply or fallback_reply)
            return {"status": "conversational_help_sent"}

        if is_deynjir_general_question(message_text):
            fallback_reply = (
                "Deynjir wuxuu kuu fududeeyaa diiwaangelinta deymaha, lacag-bixinta iyo ballamaha. "
                "Tusaale ahaan, qor Cali $20 marka uu deyn qaato."
            )
            reply = generate_deynjir_conversation_reply(message_text, fallback_reply, sender_phone)
            send_whatsapp(sender_phone, reply or fallback_reply)
            return {"status": "system_question_answered"}

        if undo_match:
            undo_key = str(undo_match.group(1) or "").strip()
            if not undo_key:
                recent_batch = LAST_BATCH_CONTEXT.get(sender_phone) or {}
                batch_expiry = recent_batch.get("expires_at")
                if (str(recent_batch.get("business_user_id") or "") == str(business_user_id)
                        and recent_batch.get("mode") == "debt"
                        and isinstance(batch_expiry, datetime)
                        and datetime.now(timezone.utc) <= batch_expiry
                        and recent_batch.get("transactions")):
                    batch_transactions = list(recent_batch["transactions"])
                    UNDO_CONFIRMATION_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id),
                        "batch_transactions": batch_transactions,
                        "total": float(recent_batch.get("total") or 0),
                        "request_id": f"undo-batch:{secrets.token_urlsafe(18)}",
                        "expires_at": datetime.now(timezone.utc) + UNDO_CONFIRMATION_TTL,
                    }
                    summary = "\n".join(
                        f"• {item['customer_name']} — ${float(item['amount']):.2f}"
                        for item in batch_transactions[:10]
                    )
                    if len(batch_transactions) > 10:
                        summary += f"\n• Iyo {len(batch_transactions) - 10} macaamiil oo kale"
                    undo_prompt = (
                        "⚠️ *Xaqiiji ka-noqoshada batch-kii ugu dambeeyay*\n\n"
                        f"{summary}\n\n"
                        f"Tirada: *{len(batch_transactions)}*\nWadarta: *${float(recent_batch.get('total') or 0):.2f}*\n\n"
                        "Waxba lama beddelin ilaa aad xaqiijiso. (5 daqiiqo)"
                    )
                    send_deynjir_choice_buttons(
                        sender_phone, undo_prompt,
                        [("UNDO_YES", "Haa, ka noqo"), ("UNDO_NO", "Maya, iska daa")],
                        undo_prompt + "\n\n1️⃣ HAA — Ka noqo\n2️⃣ MAYA — Hayso\nKu jawaab 1 ama 2."
                    )
                    return {"status": "batch_undo_confirmation_requested"}
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

                preview_result = supabase.rpc("get_latest_customer_transaction_for_undo", {
                    "p_customer_id": str(undo_customer["id"]),
                    "p_business_user_id": str(business_user_id),
                }).execute()
                preview = preview_result.data
                if isinstance(preview, list):
                    preview = preview[0] if preview else None
                if not isinstance(preview, dict) or not preview.get("transaction_id"):
                    raise RuntimeError("Ma jiro macaamil ammaan ah oo la celin karo.")
                UNDO_CONFIRMATION_SESSIONS[sender_phone] = {
                    "business_user_id": str(business_user_id),
                    "customer_id": str(undo_customer["id"]),
                    "customer_name": str(preview.get("customer_name") or undo_customer.get("name")),
                    "transaction_id": str(preview["transaction_id"]),
                    "transaction_type": str(preview.get("transaction_type") or ""),
                    "amount": float(preview.get("amount") or 0),
                    "request_id": f"undo:{secrets.token_urlsafe(18)}",
                    "expires_at": datetime.now(timezone.utc) + UNDO_CONFIRMATION_TTL,
                }
                undo_prompt = (
                    f"⚠️ *Xaqiiji ka-noqoshada macaamilka*\n\nMacmiil: *{preview.get('customer_name') or undo_customer.get('name')}*\n"
                    f"Nooca: *{preview.get('transaction_type')}*\nLacagta: *${float(preview.get('amount') or 0):.2f}*\n\n"
                    "Waxba lama beddelin ilaa aad xaqiijiso. (5 daqiiqo)"
                )
                send_deynjir_choice_buttons(
                    sender_phone, undo_prompt,
                    [("UNDO_YES", "Haa, ka noqo"), ("UNDO_NO", "Maya, iska daa")],
                    undo_prompt + "\n\n1️⃣ HAA — Ka noqo\n2️⃣ MAYA — Xaree oo sii hay\nKu jawaab 1 ama 2."
                )
                return {"status": "undo_confirmation_requested"}
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
                deposit_result = _financial_rpc("record_customer_credit_deposit", {
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
                remember_selected_customer(sender_phone, business_user_id, customer_row.get("name") or customer_key)
                remember_recent_transaction(sender_phone, business_user_id, customer_row.get("id"), customer_row.get("name") or customer_key)
                send_whatsapp(
                    sender_phone,
                    f"✅ *Dhigaalkan waa la diiwaangeliyey.*\n\n"
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
        if amount_edit_state and amount_edit_state.get("business_user_id") == str(business_user_id) and not pending_new_request:
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
                    update_data = dict(amount_edit_state.get("update_data") or {})
                    if "amount" in update_data:
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
                    update_query = (supabase.table("customers").update(update_data)
                        .eq("id", str(amount_edit_state["customer_id"]))
                        .eq("business_user_id", str(business_user_id))
                        .eq("is_archived", False)
                        .eq("amount", float(amount_edit_state["old_amount"])))
                    if amount_edit_state.get("date_confirmation_only"):
                        old_due = amount_edit_state.get("old_promised_date")
                        if old_due:
                            update_query = update_query.eq("promised_date", str(old_due))
                        else:
                            update_query = update_query.is_("promised_date", "null")
                    updated_result = update_query.select("id, name, amount, promised_date, is_paid").execute()
                    AMOUNT_EDIT_SESSIONS.pop(sender_phone, None)
                    if not updated_result.data:
                        send_whatsapp(sender_phone, "❌ Waxba lama beddelin. Hubi rukhsadaha database-ka (RLS).")
                        return {"status": "amount_edit_update_empty"}
                    updated_customer = updated_result.data[0]
                    lines = []
                    if "amount" in update_data:
                        lines.append(f"💵 Lacag: ${float(current_customer.get('amount') or 0):.2f} → ${float(updated_customer.get('amount') or 0):.2f}")
                    if "promised_date" in update_data:
                        lines.append(f"📅 Ballan: {current_customer.get('promised_date') or '-'} → {updated_customer.get('promised_date')}")
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
        if (pending_payment_result.data and not is_clear_new_supported_request(message_text, include_transactions=True) and parse_transaction_clarification(message_text) not in {"ADD", "PAY"}):
            pending_payment = pending_payment_result.data[0]
            if classify_no_activity_statement(message_text) and pending_payment.get("status") == "pending":
                rejected_ok, rejected_value = _reject_pending_payment_confirmation(
                    pending_payment["id"], sender_phone
                )
                if not rejected_ok:
                    send_whatsapp(sender_phone, rejected_value)
                    return {"status": "payment_no_activity_rejection_failed"}
                send_whatsapp(
                    sender_phone,
                    "Waan fahmay. Lacag-bixintii sugaysay waa la joojiyey. Waxba lama kaydin."
                )
                return {"status": "payment_no_activity_rejected"}
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
    if (
        pending_delete
        and pending_delete.get("stage") == "confirm"
        and normalize_customer_name(message_text).strip(" .!?؟") == "tirtir"
    ):
        explicit_delete_name = None
    if pending_delete and not pending_new_request:
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

    # Resolve a pending deposit offer before interpreting the user's HAA/MAYA reply elsewhere.
    deposit_offer = DEPOSIT_OFFER_SESSIONS.get(sender_phone)
    if deposit_offer:
        if deposit_offer.get("business_user_id") != str(business_user_id):
            DEPOSIT_OFFER_SESSIONS.pop(sender_phone, None)
        elif pending_new_request:
            DEPOSIT_OFFER_SESSIONS.pop(sender_phone, None)
        else:
            expires_at = deposit_offer.get("expires_at")
            if not expires_at or datetime.now(timezone.utc) > expires_at:
                DEPOSIT_OFFER_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Waqtigii xaqiijinta dhigaalku wuu dhammaaday. Waxba lama diiwaangelin.")
                return {"status": "deposit_offer_expired"}
            answer = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
            if answer in {"haa", "h", "yes", "y", "ok", "1"}:
                DEPOSIT_OFFER_SESSIONS.pop(sender_phone, None)
                try:
                    amount = float(deposit_offer.get("amount") or 0)
                    if not math.isfinite(amount) or amount <= 0:
                        raise ValueError("Deposit amount must be positive")
                    if deposit_offer.get("create_customer"):
                        result = _financial_rpc("create_customer_with_credit_deposit", {
                            "p_business_user_id": str(business_user_id),
                            "p_name": str(deposit_offer.get("customer_name") or "").strip(),
                            "p_amount": round(amount, 2),
                            "p_description": "DHIGAAL",
                        }, request_id=deposit_offer.get("request_id")).execute()
                    else:
                        result = _financial_rpc("record_customer_credit_deposit", {
                            "p_customer_id": str(deposit_offer.get("customer_id")),
                            "p_business_user_id": str(business_user_id),
                            "p_amount": round(amount, 2),
                            "p_description": "DHIGAAL",
                        }, request_id=deposit_offer.get("request_id")).execute()
                    data = result.data
                    if isinstance(data, list):
                        data = data[0] if data else None
                    if not isinstance(data, dict) or not data.get("success"):
                        raise RuntimeError("Database did not confirm the deposit")
                    customer_id = str(data.get("customer_id") or deposit_offer.get("customer_id") or "")
                    customer_name = str(data.get("customer_name") or deposit_offer.get("customer_name") or "Macmiilka")
                    remember_selected_customer(sender_phone, business_user_id, customer_name)
                    if customer_id:
                        remember_recent_transaction(sender_phone, business_user_id, customer_id, customer_name)
                    suffix = "\nMacmiilka cusub waa la diiwaangeliyey." if deposit_offer.get("create_customer") else ""
                    send_whatsapp(sender_phone,
                        f"✅ *Dhigaalkan waa la diiwaangeliyey.*\n\nMacmiilka: *{customer_name}*\n"
                        f"Lacagta la dhigay: *${amount:.2f}*\n"
                        f"Haraaga dhigaalka: *${float(data.get('credit_balance') or 0):.2f}*{suffix}")
                    return {"status": "deposit_offer_confirmed", "credit_balance": data.get("credit_balance")}
                except Exception as exc:
                    print(f"❌ Deposit confirmation failed: {type(exc).__name__}: {exc}")
                    send_whatsapp(sender_phone, "❌ Dhigaalka lama diiwaangelin. Waxba lama beddelin. Fadlan mar kale isku day.")
                    return {"status": "deposit_offer_failed"}
            if answer in {"maya", "may", "no", "n", "2", "cancel", "jooji"}:
                DEPOSIT_OFFER_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "✅ Waa la joojiyey. Wax lacag ah lama diiwaangelin.")
                return {"status": "deposit_offer_cancelled"}
            send_whatsapp(sender_phone, "Fadlan ku jawaab *HAA* si dhigaalka loo diiwaangeliyo ama *MAYA* si loo joojiyo. Waxba weli lama kaydin.")
            return {"status": "deposit_offer_confirmation_required"}

    # Resolve a pending amount correction; the SQL RPC reverses and replaces the ledger event atomically.
    correction = CORRECTION_SESSIONS.get(sender_phone)
    if correction:
        if correction.get("business_user_id") != str(business_user_id):
            CORRECTION_SESSIONS.pop(sender_phone, None)
        elif pending_new_request:
            CORRECTION_SESSIONS.pop(sender_phone, None)
        else:
            expires_at = correction.get("expires_at")
            if not expires_at or datetime.now(timezone.utc) > expires_at:
                CORRECTION_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Waqtigii saxitaanka wuu dhammaaday. Macaamilkii hore waxba lagama beddelin.")
                return {"status": "transaction_correction_expired"}
            answer = normalize_customer_name(str(message_text or "")).strip(" .!?؟")
            if answer in {"haa", "h", "yes", "y", "ok", "1"}:
                CORRECTION_SESSIONS.pop(sender_phone, None)
                try:
                    result = _financial_rpc("correct_customer_transaction_amount", {
                        "p_customer_id": str(correction["customer_id"]),
                        "p_business_user_id": str(business_user_id),
                        "p_expected_transaction_id": str(correction["transaction_id"]),
                        "p_new_amount": round(float(correction["new_amount"]), 2),
                    }, request_id=correction.get("request_id") or f"correction:{correction['transaction_id']}").execute()
                    data = result.data
                    if isinstance(data, list):
                        data = data[0] if data else None
                    if not isinstance(data, dict) or not data.get("success"):
                        raise RuntimeError("Database did not confirm the correction")
                    customer = data.get("customer") or {}
                    customer_name = str(customer.get("name") or correction.get("customer_name") or "Macmiilka")
                    customer_id = str(customer.get("id") or correction["customer_id"])
                    remember_recent_transaction(sender_phone, business_user_id, customer_id, customer_name)
                    send_whatsapp(sender_phone,
                        f"✅ *Saxitaanka waa la diiwaangeliyey.*\n\nMacmiil: *{customer_name}*\n"
                        f"Lacagtii hore: *${float(correction['old_amount']):.2f}*\n"
                        f"Lacagta cusub: *${float(correction['new_amount']):.2f}*\n"
                        f"Haraaga hadda: *${float(customer.get('amount') or 0):.2f}*\n\n"
                        "Taariikhdii hore waa la calaamadeeyey, saxitaanka cusubna waa la diiwaangeliyey.")
                    return {"status": "transaction_correction_confirmed"}
                except Exception as exc:
                    print(f"❌ Transaction correction failed: {type(exc).__name__}: {exc}")
                    send_whatsapp(sender_phone, "❌ Saxitaanka lama samayn. Macaamilkii hore isma beddelin. Fadlan dib u eeg liiska macaamilka.")
                    return {"status": "transaction_correction_failed"}
            if answer in {"maya", "may", "no", "n", "2", "cancel", "jooji"}:
                CORRECTION_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "✅ Waa hagaag. Macaamilkii hore sidii uu ahaa ayaan u reebay.")
                return {"status": "transaction_correction_cancelled"}
            send_whatsapp(sender_phone, "Fadlan ku jawaab *HAA* si loo saxo ama *MAYA* si loo ilaaliyo macaamilkii hore. Waxba weli lama beddelin.")
            return {"status": "transaction_correction_confirmation_required"}

    # A bare amount shortly after a committed ADD/PAY may be a correction. Ask first.
    amount_match = re.fullmatch(r"\s*(?:sax\s+)?\$?\s*(\d+(?:[.,]\d{1,2})?)\s*", str(message_text or ""), re.I)
    recent = LAST_TRANSACTION_CONTEXT.get(sender_phone) or {}
    if (amount_match and not _has_active_in_memory_workflow(sender_phone)
            and str(recent.get("business_user_id") or "") == str(business_user_id)
            and isinstance(recent.get("created_at"), datetime)
            and datetime.now(timezone.utc) - recent["created_at"] <= CORRECTION_SESSION_TTL):
        try:
            new_amount = float(amount_match.group(1).replace(",", "."))
            if math.isfinite(new_amount) and new_amount > 0:
                preview_result = supabase.rpc("get_latest_customer_transaction_for_undo", {
                    "p_customer_id": str(recent.get("customer_id")),
                    "p_business_user_id": str(business_user_id),
                }).execute()
                preview = preview_result.data
                if isinstance(preview, list):
                    preview = preview[0] if preview else None
                tx_type = str((preview or {}).get("transaction_type") or "").upper()
                if isinstance(preview, dict) and preview.get("transaction_id") and tx_type in {"ADD", "PAY", "ADD + DHIGAAL"}:
                    old_amount = float(preview.get("amount") or 0)
                    if abs(old_amount - new_amount) > 0.009:
                        CORRECTION_SESSIONS[sender_phone] = {
                            "business_user_id": str(business_user_id),
                            "customer_id": str(recent.get("customer_id")),
                            "customer_name": str(preview.get("customer_name") or recent.get("customer_name") or "Macmiilka"),
                            "transaction_id": str(preview["transaction_id"]),
                            "old_amount": old_amount,
                            "new_amount": round(new_amount, 2),
                            "request_id": f"correction:{secrets.token_urlsafe(18)}",
                            "expires_at": datetime.now(timezone.utc) + CORRECTION_SESSION_TTL,
                        }
                        send_whatsapp(sender_phone,
                            "Ma waxaad rabtaa inaad saxdo lacagtii macaamilkii ugu dambeeyay?\n\n"
                            f"Macmiil: *{preview.get('customer_name') or recent.get('customer_name')}*\n"
                            f"Lacagtii la diiwaangeliyey: *${old_amount:.2f}*\n"
                            f"Lacagta cusub: *${new_amount:.2f}*\n\n"
                            "*HAA* — Xaqiiji saxitaanka\n*MAYA* — Waxba ha beddelin\n\n"
                            "Waxba lama beddelin ilaa aad HAA ku xaqiijiso. (5 daqiiqo)")
                        return {"status": "transaction_correction_requested"}
        except Exception as exc:
            print(f"⚠️ Could not prepare correction proposal: {type(exc).__name__}: {exc}")

    # Friendly onboarding and guided actions. Numeric choices are interpreted
    # only while a menu session is active, so ordinary numbers remain untouched.
    # A guided amount answer is routed deterministically and never reparsed by AI.
    guided_transaction_override = None
    guided_text = str(message_text or "").strip()
    guided = GUIDED_SESSIONS.get(sender_phone)
    if pending_new_request:
        guided = None  # Keep the saved session; route this message as a separate request.
    if guided:
        expires_at = guided.get("expires_at")
        if not expires_at or datetime.now(timezone.utc) > expires_at:
            GUIDED_SESSIONS.pop(sender_phone, None)
            guided = None

    guided_normalized = normalize_customer_name(guided_text).strip(" .!?؟")

    # Stage-aware semantic triage: status statements and name corrections are
    # not customer names or amounts. Resolve them before the guided parser.
    guided_stage = str((guided or {}).get("stage") or "")
    no_activity_kind = classify_no_activity_statement(guided_text)
    if no_activity_kind and guided_stage in {
        "debt_name", "payment_name", "debt_amount", "payment_amount",
    }:
        GUIDED_SESSIONS.pop(sender_phone, None)
        if no_activity_kind == "payment":
            no_activity_reply = (
                "Waan fahmay. Lacag-bixin lama diiwaangelin, hawshiina waa la joojiyey. "
                "Waxba lama kaydin."
            )
        elif no_activity_kind == "debt":
            no_activity_reply = (
                "Waan fahmay. Deyn cusub lama diiwaangelin, hawshiina waa la joojiyey. "
                "Waxba lama kaydin."
            )
        else:
            no_activity_reply = (
                "Waan fahmay. Hawshii hadda lama sii wadin; waxba lama diiwaangelin."
            )
        remember_conversation_outcome(sender_phone, guided_text, no_activity_reply)
        send_whatsapp(sender_phone, no_activity_reply)
        return {"status": "guided_no_activity_cancelled", "kind": no_activity_kind}

    if guided_stage in {"debt_name", "payment_name", "debt_amount", "payment_amount"} and is_guided_name_correction(guided_text):
        expected_name = (
            "macmiilka deynta lagu leeyahay"
            if guided_stage in {"debt_name", "debt_amount"}
            else "macmiilka lacagta bixiyey"
        )
        if guided_stage in {"debt_amount", "payment_amount"} and guided:
            guided["stage"] = "debt_name" if guided_stage == "debt_amount" else "payment_name"
            guided.pop("customer_name", None)
            guided.pop("amount", None)
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
        name_correction_reply = (
            f"Waan fahmay—fariintaasi magac ma ahayn. Fadlan qor magaca {expected_name}, "
            "ama *JOOJI* si aad uga baxdo."
        )
        remember_conversation_outcome(sender_phone, guided_text, name_correction_reply)
        send_whatsapp(sender_phone, name_correction_reply)
        return {"status": "guided_name_correction_requested"}

    # Customer-account requests must enter the real HISTORY/statement workflow,
    # not the conversational fallback. Ask for the customer name when omitted.
    account_request, account_customer_name = parse_customer_account_request(guided_text)
    if account_request:
        if account_customer_name:
            message_text = f"FAAHFAAHIN {account_customer_name}"
            guided_text = message_text
            guided = None
        else:
            pause_guided_session_for_replacement(sender_phone)
            GUIDED_SESSIONS[sender_phone] = {
                "stage": "history_name",
                "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
            }
            account_prompt = "Hagaag 😊 Magaca macmiilka aad xisaabtiisa rabto ii sheeg. Tusaale: *Cali Xasan*."
            remember_conversation_outcome(sender_phone, guided_text, account_prompt)
            send_whatsapp(sender_phone, account_prompt)
            return {"status": "customer_account_name_requested"}
    if guided and guided.get("stage") in {"debt_name", "payment_name"} and guided_normalized in {
        "ma garanayo", "ma aqaan", "qof ma jiro", "qofna ma jiro", "hadda qof ma jiro", "ma jiro qof", "qof ma hayo",
    }:
        GUIDED_SESSIONS.pop(sender_phone, None)
        no_customer_reply = (
            "Dhib ma leh. Hadda waxba ha gelin. Marka macmiil jiro, "
            "ii sheeg magaciisa iyo lacagta. Waxba lama diiwaangelin."
        )
        remember_conversation_outcome(sender_phone, guided_text, no_customer_reply)
        send_whatsapp(sender_phone, no_customer_reply)
        return {"status": "guided_no_customer_yet"}

    if guided and guided.get("stage") in {"menu", "debt_name", "payment_name"} and (
        is_user_declining_help(guided_text) or guided_normalized in {"jooji", "cancel", "baaji", "iska daa"}
    ):
        GUIDED_SESSIONS.pop(sender_phone, None)
        cancel_reply = "Waa hagaag, waan joojiyey. Waxba lama diiwaangelin. Markaad diyaar tahay, ii sheeg."
        remember_conversation_outcome(sender_phone, guided_text, cancel_reply)
        send_whatsapp(sender_phone, cancel_reply)
        return {"status": "guided_action_declined"}

    if is_bare_ambiguous_debt_request(guided_text):
        if guided and guided.get("stage") == "menu":
            GUIDED_SESSIONS.pop(sender_phone, None)
        clarify_debt_reply = "Ma rabtaa inaad *deyn cusub ku darto*, mise inaad *aragto liiska deymaha jira*?"
        remember_conversation_outcome(sender_phone, guided_text, clarify_debt_reply)
        send_whatsapp(sender_phone, clarify_debt_reply)
        return {"status": "ambiguous_debt_request_clarified"}

    if guided_normalized in {"deyn cusub", "dayn cusub", "new debt"} and (not guided or guided.get("stage") == "menu"):
        pause_guided_session_for_replacement(sender_phone)
        GUIDED_SESSIONS[sender_phone] = {
            "stage": "debt_name", "transaction_type": "debt",
            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
        }
        send_whatsapp(sender_phone, "Hagaag 😊 Magaca macmiilka deynta lagu leeyahay ii sheeg. Tusaale: *Cali Xasan*.")
        return {"status": "guided_debt_name_requested"}

    # A short search result can be expanded into the full customer statement.
    pending_search_detail = SEARCH_DETAIL_SESSIONS.get(sender_phone)
    if pending_search_detail and pending_search_detail.get("business_user_id") == str(business_user_id) and not pending_new_request:
        if datetime.now(timezone.utc) > pending_search_detail.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
            SEARCH_DETAIL_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "Waqtigii codsiga xisaabta wuu dhammaaday. Mar kale raadi macmiilka haddii aad u baahan tahay.")
            return {"status": "search_detail_expired"}
        search_answer = normalize_customer_name(guided_text).strip(" .!؟?")
        if search_answer in {"1", "haa", "h", "yes", "y", "xisaab", "xisaabta", "faahfaahin", "faahfaahinta"}:
            customer_for_statement = str(pending_search_detail.get("customer_name") or "").strip()
            SEARCH_DETAIL_SESSIONS.pop(sender_phone, None)
            if customer_for_statement:
                message_text = f"FAAHFAAHIN {customer_for_statement}"
                guided_text = message_text
        elif search_answer in {"2", "maya", "no", "n"}:
            SEARCH_DETAIL_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "Waa hagaag. Haddii aad mar dambe u baahato, qor *FAAHFAAHIN magaca macmiilka*.")
            return {"status": "search_detail_declined"}
        else:
            # A different message starts a new request; it must not be swallowed.
            SEARCH_DETAIL_SESSIONS.pop(sender_phone, None)

    # Convert a conversational "yes" into a real guided debt-entry session.
    # An AI-generated offer cannot create workflow state by itself, so detect
    # the preceding offer and explicitly start the deterministic guided flow.
    conversation_state = CONVERSATION_SESSIONS.get(str(sender_phone), {})
    conversation_history = list(conversation_state.get("history") or [])
    last_model_message = next(
        (
            str(turn.get("text") or "").strip()
            for turn in reversed(conversation_history)
            if turn.get("role") == "model" and str(turn.get("text") or "").strip()
        ),
        "",
    )
    affirmative_reply = normalize_customer_name(guided_text).strip(" .!?؟") in {
        "haa", "h", "1", "yes", "y", "ok", "haye", "waa hagaag", "sax"
    }
    last_model_normalized = normalize_customer_name(last_model_message)
    previous_offer_is_new_debt = bool(
        re.search(
            r"(?:rabtaa.{0,90}diiwaangelin.{0,40}deyn cusub|"
            r"diiwaangelin.{0,40}deyn cusub.{0,90}rabtaa|"
            r"rabtaa.{0,90}deyn cusub)",
            last_model_normalized,
            re.I,
        )
    )
    if not guided and affirmative_reply and previous_offer_is_new_debt:
        CONVERSATION_SESSIONS.pop(str(sender_phone), None)
        pause_guided_session_for_replacement(sender_phone)
        GUIDED_SESSIONS[sender_phone] = {
            "stage": "debt_name",
            "transaction_type": "debt",
            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
        }
        send_whatsapp(
            sender_phone,
            "Hagaag. Fadlan ii qor magaca macmiilka deynta lagu leeyahay."
        )
        return {"status": "guided_debt_started_from_conversation"}

    # First-time users and confused shopkeepers receive one short explanation.
    if is_somali_confusion_request(guided_text):
        if guided and guided.get("stage") == "history_name":
            fallback_reply = (
                "Xisaabta macmiilku waxay muujinaysaa dayntiisa iyo lacag-bixintiisa. "
                "Ii qor magaca macmiilka si aan kuu tuso. Tusaale: *Cali Xasan*."
            )
        else:
            GUIDED_SESSIONS.pop(sender_phone, None)
            fallback_reply = (
                "Dhib ma leh, waan ku hagi doonaa. 😊 Tusaale ahaan, qor: Cali $20 ayuu deyn qaatay."
            )
        reply = generate_deynjir_conversation_reply(guided_text, fallback_reply, sender_phone)
        send_whatsapp(sender_phone, reply or fallback_reply)
        return {"status": "somali_usage_help_sent"}

    if is_deynjir_general_question(guided_text):
        fallback_reply = (
            "Deynjir wuxuu maamulaa deymaha, lacag-bixinta macaamiisha iyo ballamaha ganacsigaaga."
        )
        reply = generate_deynjir_conversation_reply(guided_text, fallback_reply, sender_phone)
        send_whatsapp(sender_phone, reply or fallback_reply)
        return {"status": "system_question_answered"}

    # A clear refusal should end optional guidance instead of restarting the
    # same service-selection question. Do not intercept active financial stages.
    if (not guided or guided.get("stage") == "menu") and is_user_declining_help(guided_text):
        if guided and guided.get("stage") == "menu":
            GUIDED_SESSIONS.pop(sender_phone, None)
        print(f"🔕 Optional help declined silently: {guided_text!r}")
        return {"status": "help_declined_silently"}

    # Acknowledgements are not new financial instructions. Keep the reply short
    # and do not restart ADD/PAY after a completed transaction.
    active_name_confirmation = (
        (CUSTOMER_MATCH_SESSIONS.get(sender_phone) or {}).get("business_user_id") == str(business_user_id)
        and (CUSTOMER_MATCH_SESSIONS.get(sender_phone) or {}).get("stage") == "confirm_extracted_name"
    )
    if not guided and is_simple_acknowledgement(guided_text) and not active_name_confirmation:
        # Acknowledgements should not create another notification or restart a task.
        # Workflow-specific confirmations have already been handled by their owners.
        print(f"🔕 Silent acknowledgement: {guided_text!r}")
        return {"status": "acknowledgement_silenced"}

    # Continue a recent natural conversation instead of sending the recovery menu.
    # Explicit financial commands and amounts are excluded by is_contextual_followup.
    if (
        not guided
        and not is_explicit_operation_request(guided_text)
        and not is_explicit_list_request(guided_text)
        and not is_contextual_debt_list_followup(guided_text, sender_phone)
        and not is_no_activity_reply(guided_text)
        and not is_guided_name_correction(guided_text)
        and is_contextual_followup(guided_text, sender_phone)
    ):
        fallback_reply = "Waan ku fahmay. Qaybtee ayaad rabtaa inaan kuu sii sharaxo?"
        reply = generate_deynjir_conversation_reply(guided_text, fallback_reply, sender_phone)
        send_whatsapp(sender_phone, reply or fallback_reply)
        return {"status": "contextual_followup_answered"}

    menu_words = {"menu", "start", "help", "caawi", "caawimaad", "bilow"}
    if guided_text.casefold() in menu_words:
        CONVERSATION_SESSIONS.pop(sender_phone, None)
        # MENU always starts a fresh menu context, even when it interrupts an old workflow.
        GUIDED_SESSIONS.pop(sender_phone, None)
        PAUSED_GUIDED_SESSIONS.pop(sender_phone, None)
        CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
        GUIDED_SESSIONS[sender_phone] = {
            "stage": "menu",
            "expires_at": datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL,
        }
        send_deynjir_main_menu(sender_phone)
        return {"status": "main_menu_sent"}

    if guided_text in {"GUIDED_DEBT", "GUIDED_PAYMENT"}:
        action = "debt" if guided_text == "GUIDED_DEBT" else "payment"
        pause_guided_session_for_replacement(sender_phone)
        GUIDED_SESSIONS[sender_phone] = {
            "stage": f"{action}_name",
            "transaction_type": action,
            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
        }
        prompt = "Magaca macmiilka deynta lagu leeyahay?" if action == "debt" else "Magaca macmiilka lacagta bixiyey?"
        send_whatsapp(sender_phone, prompt + "\n\nQor *JOOJI* haddii aad rabto inaad ka baxdo.")
        return {"status": f"guided_{action}_started"}

    if guided and re.fullmatch(r"\s*(?:jooji|cancel|baaji)\s*", guided_text, re.I):
        GUIDED_SESSIONS.pop(sender_phone, None)
        activate_guided_menu(sender_phone)
        send_whatsapp(
            sender_phone,
            deynjir_recovery_menu_message("Waa la joojiyey. Waxba lama beddelin.")
        )
        return {"status": "guided_action_cancelled"}

    if guided and guided.get("stage") == "menu":
        choice = guided_text.strip()
        if choice == "1":
            guided["stage"] = "debt_name"
            guided["transaction_type"] = "debt"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
            send_whatsapp(sender_phone, "Magaca macmiilka deynta lagu leeyahay?\n\nQor *JOOJI* si aad uga baxdo.")
            return {"status": "guided_debt_name_requested"}
        if choice == "2":
            guided["stage"] = "payment_name"
            guided["transaction_type"] = "payment"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
            send_whatsapp(sender_phone, "Magaca qofka lacagta bixiyey?\n\nQor *JOOJI* si aad uga baxdo.")
            return {"status": "guided_payment_name_requested"}
        if choice == "3":
            guided["stage"] = "menu_other"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL
            send_whatsapp(sender_phone, deynjir_other_services_menu())
            return {"status": "other_services_menu_sent"}
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

    if guided and guided.get("stage") == "menu_other":
        choice = guided_text.strip()
        if choice == "1":
            GUIDED_SESSIONS.pop(sender_phone, None)
            message_text = "LIISKA DAYNTA"
        elif choice == "2":
            guided["stage"] = "search_name"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
            send_whatsapp(sender_phone, "Qor magaca qofka aad raadinayso.")
            return {"status": "guided_search_name_requested"}
        elif choice == "3":
            GUIDED_SESSIONS.pop(sender_phone, None)
            message_text = "Balamaha Maanta"
        elif choice == "4":
            GUIDED_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, deynjir_help_message())
            return {"status": "help_sent"}
        elif choice == "5":
            GUIDED_SESSIONS.pop(sender_phone, None)
            message_text = "IMPORT"
        elif choice == "6":
            GUIDED_SESSIONS.pop(sender_phone, None)
            message_text = "LIISKA LACAG BIXINTA"
        else:
            send_whatsapp(sender_phone, "Fadlan dooro lambar u dhexeeya 1 iyo 6.\n\n" + deynjir_other_services_menu())
            return {"status": "other_services_invalid_choice"}

    if guided and guided.get("stage") in {"debt_name", "payment_name"}:
        if is_simple_acknowledgement(guided_text):
            send_whatsapp(sender_phone, "Markaad diyaar tahay, qor magaca macmiilka ama *JOOJI* si aad uga baxdo.")
            return {"status": "guided_name_acknowledgement_clarified"}
        if is_missing_value(guided_text):
            GUIDED_SESSIONS.pop(sender_phone, None)
            no_customer_reply = (
                "Waa hagaag. Haddii uusan jirin macmiil ama aadan magac hayn, hawsha waan joojiyey. "
                "Waxba lama diiwaangelin."
            )
            remember_conversation_outcome(sender_phone, guided_text, no_customer_reply)
            send_whatsapp(sender_phone, no_customer_reply)
            return {"status": "guided_missing_customer_cancelled"}
        if len(guided_text) < 2 or len(guided_text) > 100 or re.search(r"\d", guided_text):
            send_whatsapp(sender_phone, "Fadlan qor magaca macmiilka oo keliya, ama *JOOJI*.")
            return {"status": "guided_invalid_name"}
        guided["customer_name"] = guided_text.strip()
        if guided.get("amount") is not None:
            saved_amount = _guided_amount(guided.get("amount"))
            saved_type = guided.get("transaction_type")
            if saved_amount is None or saved_type not in {"debt", "payment"}:
                GUIDED_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Wadahadalkii hore si sax ah looma aqoonsan. Fadlan mar kale dir magaca iyo lacagta.")
                return {"status": "guided_saved_amount_invalid"}
            saved_name = guided["customer_name"]
            saved_description = str(guided.get("description") or "").strip()
            GUIDED_SESSIONS.pop(sender_phone, None)
            description_part = f" {saved_description}" if saved_description and saved_description != "-" else ""
            message_text = (
                f"{saved_name} ${saved_amount}{description_part} ayuu iga qaatay"
                if saved_type == "debt"
                else f"{saved_name} ${saved_amount}{description_part} ayuu bixiyay"
            )
            if saved_type == "debt" and guided.get("existing_account_request"):
                message_text += " ku dar xisaabtii hore"
            guided_transaction_override = {
                "action": "ADD" if saved_type == "debt" else "PAY",
                "customer_name": saved_name,
                "amount": saved_amount,
                "payment_type": "PARTIAL" if saved_type == "payment" else None,
                "description": saved_description or "-",
                "_source_amount_verified": True,
                "_guided_transaction": True,
            }
            guided = None
            print(f"✅ Amount-first guided transaction completed deterministically: type={saved_type}, name={saved_name!r}, amount={saved_amount}")
        else:
            guided["stage"] = "debt_amount" if guided.get("stage") == "debt_name" else "payment_amount"
            guided["expires_at"] = datetime.now(timezone.utc) + GUIDED_SESSION_TTL
        if guided and guided.get("stage") == "debt_amount":
            amount_prompt = (
                f"Immisa lacag ah ayaa *{guided['customer_name']}* lagu leeyahay?\n\n"
                "Qor lacagta oo keliya."
            )
        elif guided and guided.get("stage") == "payment_amount":
            amount_prompt = (
                f"Immisa dollar ayuu *{guided['customer_name']}* bixiyey?\n\n"
                "Qor lacagta oo keliya."
            )
        if guided:
            send_whatsapp(sender_phone, amount_prompt)
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
        no_amount_phrases = {
            "waxba", "ma jiro", "ma jirto", "lacag ma jirto", "lacag ma hayo",
            "wax lacag ah ma jirto", "wax lacag ah ma hayo", "ma hayo lacag",
            "ma hayo", "waxba ma hayo", "lacag ma jirto hadda",
        }
        if guided_normalized in no_amount_phrases or is_missing_value(guided_text):
            GUIDED_SESSIONS.pop(sender_phone, None)
            no_amount_reply = (
                "Waan fahmay. Lacag lama diiwaangelin, hawshiina waa la joojiyey. "
                "Markaad diyaar tahay, mar kale bilow."
            )
            remember_conversation_outcome(sender_phone, guided_text, no_amount_reply)
            send_whatsapp(sender_phone, no_amount_reply)
            return {"status": "guided_no_amount_cancelled"}
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
            no_payment_reply = classify_no_activity_statement(guided_text) == "payment"
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
                    "Immisa ayay qaadatay? Qor lacagta oo keliya. "
                    "Qor *JOOJI* haddii aadan rabin inaad diiwaangeliso deyn cusub."
                )
                return {"status": "guided_payment_corrected_to_debt"}
            if no_payment_reply:
                # A negative statement completes this interaction; do not keep
                # asking for an amount or silently convert it into a new debt.
                GUIDED_SESSIONS.pop(sender_phone, None)
                reply = "Waan fahmay. Lacag-bixin lama diiwaangelin, hawshiina waa la joojiyey. Waxba lama kaydin."
                remember_conversation_outcome(sender_phone, guided_text, reply)
                send_whatsapp(sender_phone, reply)
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
            prompt = "Magaca macmiilka deynta lagu leeyahay?" if transaction_type == "debt" else "Magaca macmiilka lacagta bixiyey?"
            send_whatsapp(sender_phone, prompt)
            return {"status": "guided_customer_name_required"}
        if transaction_type not in {"debt", "payment"}:
            GUIDED_SESSIONS.pop(sender_phone, None)
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
        guided_transaction_override = {
            "action": "ADD" if transaction_type == "debt" else "PAY",
            "customer_name": str(name).strip(),
            "amount": float(amount),
            "payment_type": "PARTIAL" if transaction_type == "payment" else None,
            "description": saved_description or "-",
            "_source_amount_verified": True,
            "_guided_transaction": True,
        }
        print(f"✅ Guided transaction ready deterministically: type={transaction_type}, name={name!r}, amount={amount}")

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
    elif guided and guided.get("stage") == "history_name":
        GUIDED_SESSIONS.pop(sender_phone, None)
        message_text = f"FAAHFAAHIN {guided_text.strip()}"

    # Helpful handling for a bare typo/unknown command, rather than a technical error.
    if guided_text.casefold().strip() in {"guid", "inbort", "inport", "lacag bixn"}:
        pause_guided_session_for_replacement(sender_phone)
        GUIDED_SESSIONS[sender_phone] = {
            "stage": "menu",
            "expires_at": datetime.now(timezone.utc) + GUIDED_MENU_SESSION_TTL,
        }
        send_deynjir_main_menu(sender_phone)
        return {"status": "friendly_guidance_sent"}

    # Shop-wide payment history and date-range Excel/PDF exports.
    payment_text = str(message_text or "").strip()
    pending_payment_export = PAYMENT_EXPORT_SESSIONS.get(sender_phone)
    if pending_payment_export and pending_payment_export.get("business_user_id") == business_user_id and not pending_new_request:
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
                    "created_at": datetime.now(timezone.utc),
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

    # Two-step SAX flow. Explicit "SAX old -> new" uses the immediate rename
    # path; "SAX magaca old" and "SAX old" ask for the corrected name.
    rename_state = None if (local_amount_edit_entry or pending_new_request) else RENAME_SESSIONS.get(sender_phone)
    if rename_state and rename_state.get("business_user_id") == business_user_id:
        if datetime.now(timezone.utc) > rename_state.get("expires_at", datetime.min.replace(tzinfo=timezone.utc)):
            RENAME_SESSIONS.pop(sender_phone, None)
            rename_state = None
        elif re.fullmatch(r"\s*(?:cancel|jooji|maya|no|2|menu|help)\s*", str(message_text or ""), re.I):
            RENAME_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "✅ Saxidda magaca waa la joojiyey. Waxba lama beddelin.")
            return {"status": "rename_cancelled"}
        elif rename_state.get("stage") == "new_name":
            proposed = str(message_text or "").strip()
            if (
                len(proposed) < 2 or len(proposed) > 120
                or re.fullmatch(r"[$]?\s*\d+(?:[.,]\d{1,2})?\s*(?:usd|dollar|dollars)?", proposed, re.I)
            ):
                send_whatsapp(sender_phone, "Fadlan qor magac cusub oo qoraal ah, ee ha qorin lacag. Ama JOOJI.")
                return {"status": "rename_new_name_invalid"}
            rename_state["new_name"] = proposed
            rename_state["stage"] = "confirm"
            rename_state["expires_at"] = datetime.now(timezone.utc) + timedelta(minutes=10)
            send_whatsapp(sender_phone, f"Hubi magaca cusub:\n\nMagac Hore: *{rename_state['old_name']}*\nMagaca Cusub: *{proposed}*\n\nQor *1* ama *HAA* si loo beddelo; *2* ama *MAYA* si loo joojiyo.")
            return {"status": "rename_confirmation_required"}
        elif rename_state.get("stage") == "confirm":
            rename_answer = normalize_customer_name(message_text).strip(" .!?؟")
            if rename_answer in {"ok", "haa", "1", "yes", "y", "confirm"}:
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
            if rename_answer in {"cancel", "jooji", "maya", "2", "no", "n"}:
                RENAME_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "✅ Saxidda magaca waa la joojiyey. Waxba lama beddelin.")
                return {"status": "rename_cancelled"}
            send_whatsapp(sender_phone, "Fadlan ku jawaab *1/HAA* si loo beddelo ama *2/MAYA* si loo joojiyo.")
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

    if customer_match_state and not pending_new_request:
        answer = str(message_text or "").strip()
        answer_folded = normalize_customer_name(answer)
        if re.search(r"\b(?:caawin|caawi|help|menu|adeegyada)\b", answer_folded, re.I):
            send_whatsapp(
                sender_phone,
                deynjir_help_message() + "\n\n" +
                "ℹ️ Xulashadii macmiilka weli way kuu furan tahay. "
                "Ku jawaab *HAA*, *MAYA*, ama *CUSUB* si aad u sii wadato. "
                "Qor *JOOJI* haddii aad rabto inaad ka baxdo."
            )
            return {"status": "help_sent_customer_match_preserved"}
        if classify_no_activity_statement(answer):
            CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "Waan fahmay. Xulashadii macmiilka waa la joojiyey; waxba lama diiwaangelin.")
            return {"status": "customer_match_no_activity_cancelled"}
        if is_guided_name_correction(answer) and customer_match_state.get("stage") in {"enter_full_name", "choose"}:
            send_whatsapp(sender_phone, "Waan fahmay—fariintaasi magac ma ahayn. Fadlan qor magaca buuxa ee macmiilka, ama *JOOJI*.")
            return {"status": "customer_match_name_correction_requested"}
        if re.fullmatch(r"(?:jooji|cancel|baaji|stop)", answer, re.I):
            CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, "Waa la joojiyey. Waxba lama diiwaangelin.")
            return {"status": "customer_match_cancelled"}

        stage = customer_match_state.get("stage")
        candidate_names = customer_match_state.get("candidate_names") or []
        entry = dict(customer_match_state.get("entry") or {})
        selected_name = None
        force_new = False

        if stage == "confirm_extracted_name":
            proposed_name = clean_extracted_customer_name(entry.get("customer_name"))
            if answer_folded in {"ok", "okay", "haa", "sax", "yes", "y", "1"}:
                corrected_name = proposed_name
            elif answer_folded in {"maya", "no", "n", "2"}:
                send_whatsapp(
                    sender_phone,
                    "Fadlan qor magaca saxda ah ee macmiilka. Waxba lama diiwaangelin."
                )
                return {"status": "customer_name_correction_required"}
            else:
                corrected_name = clean_extracted_customer_name(answer)
                if not corrected_name or len(corrected_name) > 120 or re.search(r"\d", corrected_name):
                    send_whatsapp(
                        sender_phone,
                        f"Magaca waxaan u fahmay *{proposed_name or 'magac aan caddayn'}*. "
                        "Haddii uu sax yahay soo qor *OK*; haddii kale soo qor magaca saxda ah."
                    )
                    return {"status": "customer_name_correction_invalid"}

            if not corrected_name:
                CUSTOMER_MATCH_SESSIONS.pop(sender_phone, None)
                send_whatsapp(sender_phone, "Magaca si sax ah looma aqoonsan. Fadlan macaamilka mar kale soo dir. Waxba lama diiwaangelin.")
                return {"status": "customer_name_confirmation_missing"}

            entry["customer_name"] = corrected_name
            entry["_customer_name_source_confirmed"] = True

        elif stage == "choose":
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
                send_whatsapp(sender_phone, "Hagaag. Ma aha macmiilkaas.\n\nQor magaca saxda ah ee macmiilka kale, ama *CUSUB* si aan u sameeyo macmiil cusub anigoo ilaalinaya magaca iyo lacagtii aad markii hore dirtay.\nQor *JOOJI* si aad u baajiso.")
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

    if pending_clarification and not is_clear_new_supported_request(message_text, include_transactions=True):
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
            activate_guided_menu(sender_phone)
            send_whatsapp(
                sender_phone,
                deynjir_recovery_menu_message("Waa la joojiyey. Wax deyn ah lama diiwaangelin.")
            )
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
                clarification_prompt = "Deyn cusub baa mise lacag-bixin?"
                send_deynjir_choice_buttons(
                    sender_phone, clarification_prompt,
                    [("TX_ADD", "Deyn cusub"), ("TX_PAY", "Lacag-bixin"), ("TX_CANCEL", "Jooji")],
                    clarification_prompt + "\n\nSoo qor *DEYN CUSUB*, *LACAG BIXIN* ama *JOOJI*."
                )
                return {"status": "awaiting_transaction_clarification"}

    # A standalone 1-6 outside any active workflow is treated as a menu choice.
    # This protects users whose menu state was lost (for example after a Render
    # restart) and prevents Gemini/customer-search fallback from treating "5"
    # as a customer name. Existing active workflows retain ownership of numeric
    # replies (amounts, confirmations, reminder/import selections, etc.).
    standalone_menu_choice = str(message_text or "").strip()
    if (
        re.fullmatch(r"[1-6]", standalone_menu_choice)
        and not _has_active_in_memory_workflow(sender_phone)
        and pending_clarification is None
    ):
        if standalone_menu_choice == "1":
            pause_guided_session_for_replacement(sender_phone)
            GUIDED_SESSIONS[sender_phone] = {
                "stage": "debt_name",
                "transaction_type": "debt",
                "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
            }
            send_whatsapp(
                sender_phone,
                "Magaca macmiilka deynta lagu leeyahay?\n\nQor *JOOJI* si aad uga baxdo."
            )
            return {"status": "menu_choice_debt_started"}
        if standalone_menu_choice == "2":
            pause_guided_session_for_replacement(sender_phone)
            GUIDED_SESSIONS[sender_phone] = {
                "stage": "payment_name",
                "transaction_type": "payment",
                "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
            }
            send_whatsapp(
                sender_phone,
                "Magaca qofka lacagta bixiyey?\n\nQor *JOOJI* si aad uga baxdo."
            )
            return {"status": "menu_choice_payment_started"}
        if standalone_menu_choice == "3":
            message_text = "LIISKA DAYNTA"
            guided_text = message_text
            print("🧭 Standalone menu choice 3 routed locally to debt list")
        elif standalone_menu_choice == "4":
            pause_guided_session_for_replacement(sender_phone)
            GUIDED_SESSIONS[sender_phone] = {
                "stage": "search_name",
                "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
            }
            send_whatsapp(sender_phone, "Qor magaca macmiilka aad raadinayso.\n\nQor *JOOJI* si aad uga baxdo.")
            return {"status": "menu_choice_search_started"}
        elif standalone_menu_choice == "5":
            message_text = "Balamaha Maanta"
            guided_text = message_text
            print("🧭 Standalone menu choice 5 routed locally to today's appointments")
        elif standalone_menu_choice == "6":
            send_whatsapp(sender_phone, deynjir_help_message())
            return {"status": "menu_choice_help_sent"}

    # Manual debt-reminder workflow: fully rule-based, no Gemini request.
    # Start: XUSUUSIN -> numbered unpaid-customer list -> "1,3" -> confirmation.
    reminder_text = str(message_text or "").strip()
    reminder_state = REMINDER_SESSIONS.get(sender_phone)

    if reminder_state and not pending_new_request:
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

    if reminder_state and reminder_state.get("stage") == "selecting" and not pending_new_request:
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

    if reminder_state and reminder_state.get("stage") == "confirming" and not pending_new_request:
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
            pause_guided_session_for_replacement(sender_phone)
            GUIDED_SESSIONS[sender_phone] = {
                "stage": "history_name",
                "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
            }
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

    # Natural-language business questions are routed to the existing database
    # read paths before Gemini's transaction JSON parser can misclassify them.
    no_activity_kind = classify_no_activity_statement(message_text)
    if no_activity_kind:
        if no_activity_kind == "payment":
            reply = "Waan fahmay. Lacag-bixin lama diiwaangelin. Waxba lama kaydin. 🤝"
        elif no_activity_kind == "debt":
            reply = "Waan fahmay. Deyn cusub lama diiwaangelin. Waxba lama kaydin. 🤝"
        else:
            reply = "Waan fahmay. Wax dhaqdhaqaaq cusub lama diiwaangelin. 🤝"
        send_whatsapp(sender_phone, reply)
        return {"status": "no_activity_reply_acknowledged", "kind": no_activity_kind}

    if is_natural_top_debt_question(message_text):
        try:
            return send_top_outstanding_debtors(sender_phone, business_user_id, limit=1)
        except Exception as ranking_error:
            print(f"❌ Outstanding-debtor ranking failed: {type(ranking_error).__name__}: {ranking_error}")
            send_whatsapp(sender_phone, "Waan fahmay inaad rabto macaamiisha deynta ugu badan kugu leh, balse xogta hadda lama soo saari karin. Fadlan mar kale isku day.")
            return {"status": "top_outstanding_debtors_error"}

    if is_natural_today_payment_question(message_text):
        try:
            return send_today_payment_summary(sender_phone, business_user_id)
        except Exception as payment_summary_error:
            print(f"❌ Today's payment summary failed: {type(payment_summary_error).__name__}: {payment_summary_error}")
            send_whatsapp(sender_phone, "Waan fahmay inaad rabto lacagihii maanta la qabtay, balse xogta hadda lama soo saari karin. Fadlan mar kale isku day.")
            return {"status": "today_payment_summary_error"}

    # Route clear appointment requests before the generic debt-list matcher.
    local_appointment_entry = parse_local_appointment_list_request(message_text)
    if local_appointment_entry is None:
        local_appointment_entry = resolve_contextual_appointment_list_followup(message_text, sender_phone)
    if local_appointment_entry and local_appointment_entry.get("filter_date"):
        LAST_APPOINTMENT_LIST_REQUESTS[sender_phone] = {
            "filter_date": local_appointment_entry["filter_date"],
            "filter_type": local_appointment_entry.get("filter_type"),
            "expires_at": datetime.now(timezone.utc) + timedelta(minutes=10),
        }

    # Fast read-only command matching: avoid a Gemini request for debt lists.
    fuzzy_list_requested = (
        is_fuzzy_debt_list_command(message_text)
        or is_explicit_list_request(message_text)
        or is_contextual_debt_list_followup(message_text, sender_phone)
    )
    multiline_transaction = parse_multiline_menu_transaction(message_text)

    # Direct multi-row text lists use the same preview/OK workflow as Excel and
    # image imports. This avoids the single-customer natural-language parser.
    direct_batch = parse_transaction_batch_text(message_text)
    if direct_batch:
        batch_mode, batch_rows = direct_batch
        try:
            validated_batch = _validate_import_entries(batch_rows)
            IMPORT_SESSIONS[sender_phone] = {
                "business_user_id": str(business_user_id),
                "shop_phone": sender_phone,
                "shop_name": str((business_user or {}).get("name") or sender_phone),
                "entries": validated_batch,
                "mode": batch_mode,
                "request_id": secrets.token_urlsafe(24),
                "stage": "ready",
                "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL,
            }
            _stage_import(sender_phone, validated_batch, batch_mode)
            return {"status": "direct_batch_preview_ready", "mode": batch_mode, "count": len(validated_batch)}
        except Exception as batch_error:
            print(f"❌ Direct batch parse/stage error: {type(batch_error).__name__}: {batch_error}")
            send_whatsapp(sender_phone, f"Liiska si sax ah looma diyaarin karin: {str(batch_error)[:180]}\nWaxba lama kaydin. Fadlan sax safafka oo mar kale dir.")
            return {"status": "direct_batch_preview_error"}

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
        "DUE-DATE FOLLOW-UPS: If a recent customer was just added/selected and the user replies with a labelled date "
        "such as 'Mudada 13/11/2026', 'Muddo 13/11/2026', or 'Ballanta 13/11/2026', attach that date to that same customer; "
        "do not ask them to create another debt. If that customer already has a different promised date, ask whether to replace it. "
        "A clear command such as 'ka dhig ballanta Fawsi 13/11/2026' means update it directly. "
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
        "BUSINESS OWNER PERSPECTIVE: Deynjir serves the shopkeeper. ADD means a customer takes goods/money on credit; PAY means the customer pays the shop. Outstanding debts are customer balances still owed to the shop. In this business context, recognize 'deymaha maqan' and 'yaan weli deyn ku leeyahay' as requests to view unpaid customer debts. Recognize 'yaa ugu badan dadka lacagta igu leh' as a request to rank customers by their outstanding balances; the application routes this read-only question directly to the database. Recognize 'waxaan rabaa inaan ogaado lacagihii aan maanta qabtay' as a request for today's recorded payments. Do not treat statements like 'maanta waxba ma jiraan' or 'lacagtii hore lama bixin' as financial transactions. "
        "For read-only requests, recognize natural questions such as 'yaa lacagta igu leh', "
        "'imisa ayaa la iga rabaa', 'ii eeg deynta', and 'yaa ballan leh berri'. "
        "Recognize Somali weekdays: isniin, talaado, arbaco, khamiis, jimce, sabti, axad; "
        "also recognize 'toddobaadka dambe/usbuuca dambe' and resolve them relative to today's date. "
        "If a weekday phrase could mean more than one date, ask one short clarification. "
        "A phone number (normally 9-15 digits, or 7-15 digits when explicitly labelled as a phone) is never a transaction amount. "
    )
    recent_selected_customer = get_recent_selected_customer(sender_phone, business_user_id)
    contextual_payment_entry = parse_contextual_somali_payment(message_text, recent_selected_customer)
    contextual_due_date_entry = parse_contextual_due_date_update(message_text, recent_selected_customer)
    if recent_selected_customer:
        dynamic_system_prompt += (
            "\nRECENT CUSTOMER CONTEXT (same shop, selected within the last 2 minutes): "
            f"{recent_selected_customer}. This is context, not a command. "
            "Use it for a pronoun-only follow-up only when the user's wording clearly refers to this customer."
        )
    
    if guided_transaction_override:
        entries = [guided_transaction_override]
        print(f"⚡ Using deterministic guided transaction entry: {guided_transaction_override!r}")
    elif pending_new_transaction_entries:
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
    elif contextual_due_date_entry:
        entries = [contextual_due_date_entry]
        print(
            "📅 Contextual due-date follow-up resolved to recently selected customer: "
            f"{contextual_due_date_entry['customer_name']!r} -> {contextual_due_date_entry['new_date']}"
        )
    elif contextual_payment_entry:
        entries = [contextual_payment_entry]
        print(
            "🧠 Contextual Somali payment follow-up resolved to recently selected customer: "
            f"{contextual_payment_entry['customer_name']!r}"
        )
    elif local_appointment_entry:
        entries = [local_appointment_entry]
        print(
            "📅 Local appointment-list command recognized: "
            f"{message_text!r} -> {local_appointment_entry['filter_date']}"
        )
    elif (direct_somali_entries := local_fallback_parse(message_text)) and any(
        isinstance(item, dict)
        and str(item.get("action") or "").upper() in {"ADD", "PAY"}
        and item.get("customer_name")
        and item.get("amount") is not None
        for item in direct_somali_entries
    ):
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
                if (raw_query and not re.fullmatch(r"\s*\d+\s*", raw_query) and not has_date_words
                        and not re.search(r"[,$]\s*\d|\d\s*\$", raw_query)):
                    try:
                        fallback_matches = find_debtor_matches(business_user_id, raw_query)
                    except Exception as fallback_err:
                        print(f"⚠️ Local customer-search fallback failed: {fallback_err}")
                        fallback_matches = []
                    if fallback_matches:
                        entries = [{"action": "SEARCH", "customer_name": raw_query}]
                        print(f"🛟 Local fallback routing known customer name to SEARCH: {raw_query!r}")
            if not entries:
                # An unknown message is not a request to open the menu. Avoid
                # hidden menu state that could capture a later number.
                if is_rate_limited:
                    send_whatsapp(
                        sender_phone,
                        "⏳ Adeegga fahamka fariinta hadda waa mashquul. Waxba lama beddelin. "
                        "Fadlan fariinta mar kale isku day."
                    )
                    return {"status": "gemini_rate_limited_clarification"}
                send_whatsapp(sender_phone, deynjir_unrecognized_message())
                return {"status": "friendly_fallback_sent"}

    # Normalize action labels once, including saved clarification entries, so
    # downstream routing never depends on Gemini's capitalization.
    if isinstance(entries, list):
        for parsed_item in entries:
            if isinstance(parsed_item, dict) and parsed_item.get("action") is not None:
                parsed_item["action"] = str(parsed_item["action"]).upper()
            if isinstance(parsed_item, dict) and parsed_item.get("customer_name"):
                cleaned_name = clean_extracted_customer_name(parsed_item.get("customer_name"))
                parsed_item["customer_name"] = cleaned_name
                if not cleaned_name:
                    print(
                        "⚠️ Rejected transaction with no valid customer name after "
                        f"removing action wording: {parsed_item!r}"
                    )

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
            send_whatsapp(sender_phone, deynjir_unrecognized_message())
            return {"status": "unrecognized_message"}
        entries = usable_entries
        for parsed_item in entries:
            parsed_item["action"] = str(parsed_item.get("action") or "").upper()

        # Do not let Gemini turn unrelated text such as "none" into a debt list.
        # Keep only explicit list commands; a bare "deyn" is clarified earlier.
        if (
            any(item.get("action") == "LIST" for item in entries)
            and not is_explicit_list_request(message_text)
            and not is_explicit_appointment_list_request(message_text)
        ):
            print(f"⚠️ Rejected LIST intent without an explicit list command: {message_text!r}")
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
                    pause_guided_session_for_replacement(sender_phone)
                    GUIDED_SESSIONS[sender_phone] = {
                        "stage": "search_name",
                        "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                    }
                    send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca ii sheeg.")
                    return {"status": "search_name_required"}
                print(
                    f"⚠️ Rejected empty SEARCH intent for unrecognized text: "
                    f"{message_text!r}"
                )
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
            clarification_prompt = (
                "Waxaad soo qortay magac iyo tiro keliya.\n\n"
                "Waxba lama diiwaangelinayo ilaa aad kala caddeyso."
            )
            send_deynjir_choice_buttons(
                sender_phone, clarification_prompt,
                [("TX_ADD", "Deyn cusub"), ("TX_PAY", "Lacag-bixin"), ("TX_CANCEL", "Jooji")],
                clarification_prompt + "\n\n*DEYN CUSUB* — 1\n*LACAG BIXIN* — 2\n*JOOJI* — 3"
            )
            return {"status": "awaiting_transaction_clarification"}
        elif has_financial_entries and explicit_direction:
            for parsed_entry in entries:
                if parsed_entry.get("action") in {"ADD", "PAY"}:
                    parsed_entry["action"] = explicit_direction

    # Any clearly directed multi-customer ADD/PAY message (including rows
    # extracted by Gemini from natural Somali) uses one reviewed batch import.
    # This prevents the ordinary per-customer PAY loop from creating one
    # pending confirmation and then blocking every later payment in the list.
    if len(entries) >= 2 and all(
        isinstance(item, dict)
        and str(item.get("action") or "").upper() in {"ADD", "PAY"}
        and item.get("customer_name")
        and item.get("amount") is not None
        for item in entries
    ):
        batch_actions = {str(item.get("action") or "").upper() for item in entries}
        if len(batch_actions) != 1:
            send_whatsapp(
                sender_phone,
                "Liiska wuxuu isku daray deyn iyo lacag-bixin. Fadlan laba liis u kala dir; waxba lama kaydin."
            )
            return {"status": "mixed_transaction_batch_rejected"}
        batch_action = next(iter(batch_actions))
        batch_mode = "debt" if batch_action == "ADD" else "payment"
        try:
            batch_rows = _validate_import_entries([
                {
                    "name": item.get("customer_name"),
                    "amount": item.get("amount"),
                    "promised_date": item.get("promised_date"),
                    "phone_number": item.get("new_phone") or item.get("customer_phone"),
                    "description": item.get("description"),
                }
                for item in entries
            ])
            IMPORT_SESSIONS[sender_phone] = {
                "business_user_id": str(business_user_id),
                "shop_phone": sender_phone,
                "shop_name": str((business_user or {}).get("name") or sender_phone),
                "entries": batch_rows,
                "mode": batch_mode,
                "request_id": secrets.token_urlsafe(24),
                "stage": "ready",
                "expires_at": datetime.now(timezone.utc) + IMPORT_SESSION_TTL,
            }
            _stage_import(sender_phone, batch_rows, batch_mode)
            return {
                "status": "ai_batch_preview_ready",
                "mode": batch_mode,
                "count": len(batch_rows),
            }
        except Exception as batch_error:
            print(f"❌ AI multi-row batch staging failed: {type(batch_error).__name__}: {batch_error}")
            send_whatsapp(
                sender_phone,
                f"Liiska si sax ah looma diyaarin karin: {str(batch_error)[:160]}\nWaxba lama kaydin. Fadlan sax safafka oo mar kale dir."
            )
            return {"status": "ai_batch_preview_error"}

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
            if action == "HISTORY":
                pause_guided_session_for_replacement(sender_phone)
                GUIDED_SESSIONS[sender_phone] = {
                    "stage": "history_name",
                    "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                }
                send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca macmiilka aad rabto faahfaahintiisa ii sheeg.")
                return {"status": "history_customer_name_required"}
            if action in {"ADD", "PAY"}:
                transaction_type = "debt" if action == "ADD" else "payment"
                stage = "debt_name" if action == "ADD" else "payment_name"
                pending_state = {
                    "stage": stage,
                    "transaction_type": transaction_type,
                    "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                }
                if amount is not None:
                    pending_state["amount"] = amount
                    pending_state["description"] = description or "-"
                    pending_state["existing_account_request"] = is_existing_account_add_request(message_text) if action == "ADD" else False
                pause_guided_session_for_replacement(sender_phone)
                GUIDED_SESSIONS[sender_phone] = pending_state
                if amount is not None:
                    prompt = (
                        f"Waxaan helay lacagta *${float(amount):.2f}*. Fadlan ii sheeg magaca macmiilka deynta qaatay."
                        if action == "ADD"
                        else f"Waxaan helay lacagta *${float(amount):.2f}*. Fadlan ii sheeg magaca macmiilka lacagta bixiyay."
                    )
                else:
                    prompt = "Fadlan ii sheeg magaca macmiilka deynta lagu leeyahay." if action == "ADD" else "Fadlan ii sheeg magaca macmiilka lacagta bixiyay."
                send_whatsapp(sender_phone, prompt)
                return {"status": "guided_customer_name_required", "action": action, "amount_collected": amount is not None}
            send_whatsapp(sender_phone, "Waa qofkee? Fadlan magaca macmiilka ii sheeg.")
            continue

        # Never save a model-supplied ADD/PAY name unless its words occur in
        # the user's message or the user explicitly approved/corrected it.
        if (
            action in {"ADD", "PAY"}
            and name
            and not entry.get("_customer_name_source_confirmed")
        ):
            grounded_name = clean_extracted_customer_name(name)
            if not grounded_name:
                send_whatsapp(
                    sender_phone,
                    "Magaca macmiilka si cad uma fahmin. Fadlan mar kale ii qor magaca. Waxba lama diiwaangelin."
                )
                return {"status": "customer_name_not_understood"}
            name = grounded_name
            entry["customer_name"] = grounded_name
            if not customer_name_is_grounded_in_source(grounded_name, message_text):
                CUSTOMER_MATCH_SESSIONS[sender_phone] = {
                    "business_user_id": str(business_user_id),
                    "entry": dict(entry),
                    "original_message": str(message_text or ""),
                    "candidate_names": [],
                    "stage": "confirm_extracted_name",
                    "remaining_entries": [dict(item) for item in entries[entry_index + 1:]],
                    "allow_new": False,
                    "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                }
                send_whatsapp(
                    sender_phone,
                    f"Magaca waxaan u fahmay *{grounded_name}*. "
                    "Haddii uu sax yahay soo qor *OK*; haddii kale soo qor magaca saxda ah.\\n\\n"
                    "Waxba lama diiwaangelin ilaa magaca la xaqiijiyo. Qor *JOOJI* si aad u baajiso."
                )
                return {"status": "customer_name_confirmation_pending"}

        if action in {"ADD", "PAY"} and not new_phone and (amount is None or (action == "ADD" and date_intent_without_amount)):
            date_only = promised_date if action == "ADD" else None
            if action == "ADD" and not date_only and days_until_due is not None:
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
                pause_guided_session_for_replacement(sender_phone)
                GUIDED_SESSIONS[sender_phone] = {
                    "stage": "debt_amount" if action == "ADD" else "payment_amount",
                    "transaction_type": "debt" if action == "ADD" else "payment",
                    "customer_name": str(name).strip(),
                    "description": description or "-",
                    "existing_account_request": is_existing_account_add_request(message_text) if action == "ADD" else False,
                    "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                }
                amount_question = (
                    f"{name}, immisa lacag ah ayaa lagu leeyahay?"
                    if action == "ADD"
                    else f"{name}, immisa dollar ayuu bixiyey?"
                )
                send_whatsapp(
                    sender_phone,
                    f"{amount_question}\n\nQor lacagta oo keliya. Hada Waxba lama diiwaangelin. "
                    "Qor *JOOJI* haddii aad rabto inaad ka baxdo."
                )
                print(f"⚠️ Amount missing; saved pending transaction context: action={action}, customer={name!r}; message={message_text!r}")
                continue

        # Recover the full stored name from the original WhatsApp message if AI shortened it.
        if name and action in {"ADD", "PAY", "EDIT", "DELETE", "HISTORY", "SEARCH"}:
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
                    pause_guided_session_for_replacement(sender_phone)
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
                        f"{name}, immisa lacag ah ayaa lagu leeyahay?\n\n"
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
                        send_whatsapp(sender_phone, f"❌ Kuma hayo liiska {name} si lambarkiisa aan u kaydiyo.")
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
                                f"❌ Ma helin macmiil Liiska ku jira oo la yiraahdo *{name}*. "
                                "Hubi magaca macmiilka oo mar kale soo dir."
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

                        updated_result = _financial_rpc("record_debt_addition", {
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
                        remember_recent_transaction(sender_phone, business_user_id, updated.get("id"), updated.get("name") or name)
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

                result = _financial_rpc("record_debt_addition", {
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
                remember_recent_transaction(sender_phone, business_user_id, (created_customer or {}).get("id"), (created_customer or {}).get("name") or name)
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
                    if payment_amount is None:
                        pause_guided_session_for_replacement(sender_phone)
                        GUIDED_SESSIONS[sender_phone] = {
                            "stage": "payment_amount", "transaction_type": "payment",
                            "customer_name": str(name).strip(),
                            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                        }
                        send_whatsapp(sender_phone, f"{name}, immisa lacag ah ayuu kuu keenay? Qor lacagta keliya, tusaale: *$17*.")
                        break
                    try:
                        proposed_deposit = float(payment_amount)
                    except (TypeError, ValueError):
                        proposed_deposit = 0
                    if not math.isfinite(proposed_deposit) or proposed_deposit <= 0:
                        send_whatsapp(sender_phone, "Lacagtu waa inay ka weyn tahay $0. Fadlan sax lacagta.")
                        break
                    DEPOSIT_OFFER_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id), "customer_name": str(name).strip(),
                        "customer_id": None, "create_customer": True,
                        "amount": round(proposed_deposit, 2),
                        "request_id": f"deposit-offer:{secrets.token_urlsafe(18)}",
                        "expires_at": datetime.now(timezone.utc) + DEPOSIT_OFFER_TTL,
                    }
                    send_whatsapp(sender_phone,
                        f"⚠️ *{name}* kuma jiro liiska macaamiishaada, mana laha deyn diiwaangashan.\n\n"
                        f"Ma rabtaa in ${proposed_deposit:.2f} loogu diiwaangeliyo *dhigaal* ahaan?\n\n"
                        "*HAA* — Dhigaal samee\n*MAYA* — Jooji\n\n"
                        "Waxba lama kaydin ilaa aad HAA ku xaqiijiso.")
                    break

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
                    if payment_amount is None:
                        pause_guided_session_for_replacement(sender_phone)
                        GUIDED_SESSIONS[sender_phone] = {
                            "stage": "payment_amount", "transaction_type": "payment",
                            "customer_name": str(debtor.get("name") or name).strip(),
                            "expires_at": datetime.now(timezone.utc) + GUIDED_SESSION_TTL,
                        }
                        send_whatsapp(sender_phone, f"{debtor.get('name') or name}, immisa lacag ah ayuu kuu keenay? Qor lacagta keliya, tusaale: *$17*.")
                        break
                    try:
                        proposed_deposit = float(payment_amount)
                    except (TypeError, ValueError):
                        proposed_deposit = 0
                    if not math.isfinite(proposed_deposit) or proposed_deposit <= 0:
                        send_whatsapp(sender_phone, "Lacagtu waa inay ka weyn tahay $0. Fadlan sax lacagta.")
                        break
                    DEPOSIT_OFFER_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id),
                        "customer_name": str(debtor.get("name") or name).strip(),
                        "customer_id": str(debtor.get("id")), "create_customer": False,
                        "amount": round(proposed_deposit, 2),
                        "request_id": f"deposit-offer:{secrets.token_urlsafe(18)}",
                        "expires_at": datetime.now(timezone.utc) + DEPOSIT_OFFER_TTL,
                    }
                    send_whatsapp(sender_phone,
                        f"ℹ️ *{debtor.get('name') or name}* wax dayn ah kuma laha liiskaaga.\n\n"
                        f"Ma rabtaa in ${proposed_deposit:.2f} loogu diiwaangeliyo *dhigaal* ahaan?\n\n"
                        "*HAA* — Dhigaal samee\n*MAYA* — Jooji\n\n"
                        "Waxba lama kaydin ilaa aad HAA ku xaqiijiso.")
                    break

                # A missing amount is a full payment ONLY when the AI explicitly says FULL.
                if payment_amount is None and payment_type != "FULL":
                    pause_guided_session_for_replacement(sender_phone)
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

                # Build a fresh query for each range so Supabase's default row
                # limit cannot silently hide customers from the full debt list.
                if filter_date:
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
                    if wants_due_dates:
                        message_title = "📋 *Liiska Deynta iyo Balamaha*"
                    else:
                        message_title = "📋 *Liiska Deynta*"

                def build_debt_list_query():
                    query = (
                        supabase.table("customers")
                        .select("*")
                        .eq("business_user_id", business_user_id)
                        .eq("is_archived", False)
                        .eq("is_paid", False)
                    )
                    if filter_date:
                        query = query.eq("promised_date", filter_date)
                    query = query.order("promised_date", desc=False).order("id", desc=False)
                    return query

                debt_rows = fetch_all_supabase_rows(build_debt_list_query)

                if not debt_rows:
                    if filter_date:
                        date_label = "maanta" if filter_type == "today" else "berri" if filter_type == "tomorrow" else filter_date
                        empty_due_reply = f"✅ Ma jiraan macaamiil leh ballan {date_label} ({filter_date})."
                        send_whatsapp(sender_phone, empty_due_reply)
                        remember_conversation_outcome(
                            sender_phone, message_text,
                            f"Liiska ballamaha ee {filter_date} waa madhan."
                        )
                        send_due_list_followup(sender_phone)
                    else:
                        empty_list_reply = "✅ Ma jirto deyn aan la bixin."
                        send_whatsapp(sender_phone, empty_list_reply)
                        remember_conversation_outcome(
                            sender_phone, message_text,
                            "Liiska deymaha waa madhan; ma jiraan deymo aan la bixin."
                        )
                    continue

                debt_list = []
                total = 0
                overdue_count = 0
                today = today_eat()

                for index, debt in enumerate(debt_rows, start=1):
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
                    f"({len(debt_rows)} macmiil):\n\n"
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

                # Send the complete debt register as one WhatsApp message.
                # Do not split a normal shop debt list into separate pages.
                send_whatsapp(sender_phone, message)

                remember_conversation_outcome(
                    sender_phone, message_text,
                    f"Liiska deymaha oo dhan waa la soo bandhigay ({len(debt_rows)} macmiil)."
                )

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

                # If a date already exists, do not silently overwrite it when the
                # user merely supplies another date. Ask once; explicit change
                # commands (e.g. "ka dhig ballanta ...") are clear authorization.
                if (
                    date_only_update
                    and "promised_date" in update_data
                    and debtor.get("promised_date")
                    and str(debtor.get("promised_date")) != str(update_data["promised_date"])
                    and not is_explicit_due_date_change(message_text)
                ):
                    old_due = str(debtor.get("promised_date"))
                    new_due = str(update_data["promised_date"])
                    try:
                        old_due_display = datetime.strptime(old_due, "%Y-%m-%d").strftime("%d/%m/%Y")
                    except ValueError:
                        old_due_display = old_due
                    try:
                        new_due_display = datetime.strptime(new_due, "%Y-%m-%d").strftime("%d/%m/%Y")
                    except ValueError:
                        new_due_display = new_due
                    AMOUNT_EDIT_SESSIONS[sender_phone] = {
                        "business_user_id": str(business_user_id),
                        "customer_id": str(debtor["id"]),
                        "customer_name": str(debtor.get("name") or name),
                        "old_amount": _safe_money(debtor.get("amount")),
                        "old_promised_date": old_due,
                        "update_data": dict(update_data),
                        "date_confirmation_only": True,
                        "expires_at": datetime.now(timezone.utc) + timedelta(minutes=10),
                    }
                    send_whatsapp(
                        sender_phone,
                        f"📅 *{debtor.get('name') or name}* wuxuu hore u lahaa ballan *{old_due_display}*.\n\n"
                        f"Ma ku beddelaa *{new_due_display}*?\n\n"
                        "Qor *HAA* si loo beddelo ama *MAYA* si loo daayo. Waxba lama beddelin weli."
                    )
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
                    changes.append(f"📅 Ballan: {debtor.get('promised_date') or '-'} → {updated['promised_date']}")

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
                        send_whatsapp(sender_phone, "Ma helin macmiilkaas. Fadlan hubi magaca.")
                        failed_inserts.append({"name": name, "reason": "Customer search returned no match"})
                    else:
                        print(
                            f"⚠️ Bare-word SEARCH did not match a customer; treating as unrecognized text: "
                            f"{message_text!r}"
                        )
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

                SEARCH_DETAIL_SESSIONS[sender_phone] = {
                    "business_user_id": str(business_user_id),
                    "customer_name": str(matched_name),
                    "expires_at": datetime.now(timezone.utc) + timedelta(minutes=5),
                }
                message = (
                    f"🔎 *{matched_name}*\n"
                    f"💰 Deyn hadhsan: *${total_debt:.2f}*\n\n"
                    "Ma rabtaa xisaabta macmiilka oo faahfaahsan?\n"
                    "1️⃣ Haa\n"
                    "2️⃣ Maya"
                )
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
                        f"❌ {name} Kuma jiro Liiska Deynta."
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
                    f"waan diiwaangeliyey: ${float(entry.get('amount') or 0):.2f}."
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
            if ONBOARDING_SESSIONS.get(sender_phone, {}).get("stage") == "first_successful_action":
                success_message += (
                    "\n\n🎉 *Bilow fiican!* Deynjir hadda wuxuu kuu hayaa diiwaanka macaamilkan. "
                    "Waxaad ku dari kartaa macaamiil kale ama lacag-bixintooda. "
                    "Haddii daymo hore kuu yaallaan, qor *IMPORT* si aad si fudud ugu soo geliso."
                )
                ONBOARDING_SESSIONS.pop(sender_phone, None)
            send_whatsapp(sender_phone, success_message)
            remember_conversation_outcome(sender_phone, message_text, success_message)

    if failed_inserts:
        # Failure branches already send their specific reply. Never append a second generic menu.
        print(f"❌ Transaction failures ({len(failed_inserts)}): {failed_inserts}")
    
    return {"status": "success"}


@app.post("/webhook")
async def whatsapp_webhook(request: Request):
    """Claim webhook delivery, process it, then mark completion/failure."""
    try:
        payload = await request.json()
    except Exception as exc:
        raise HTTPException(status_code=400, detail="Invalid webhook JSON") from exc
    if not isinstance(payload, dict):
        raise HTTPException(status_code=400, detail="Webhook payload must be a JSON object")
    message_data = payload.get("messageData") or {}
    if not isinstance(message_data, dict):
        message_data = {}
    event_id = (
        payload.get("id") or payload.get("eventId") or payload.get("idMessage")
        or message_data.get("idMessage") or message_data.get("id")
    )
    event_type = payload.get("typeWebhook")
    if event_type in {"incomingMessageReceived", "outgoingMessageReceived"} and not event_id:
        # Never process a financial command without a stable provider event ID:
        # doing so would make a retry indistinguishable from a new transaction.
        print(
            "❌ Webhook rejected: stable Green-API message ID missing; "
            f"type={event_type!r}, top_level_keys={sorted(payload.keys())}, "
            f"messageData_keys={sorted(message_data.keys())}"
        )
        raise HTTPException(status_code=503, detail="Missing stable Green-API message ID; retry delivery.")
    if event_id:
        event_id = str(event_id).strip()
        if not event_id or len(event_id) > 300:
            print(f"❌ Webhook rejected: invalid event ID length; type={event_type!r}")
            raise HTTPException(status_code=400, detail="Invalid Green-API message ID")
    if event_id and is_duplicate_webhook(event_id):
        return {"status": "duplicate_webhook_ignored"}
    sender_data = payload.get("senderData") or {}
    sender_chat_id = str(sender_data.get("chatId") or "")
    session_sender = sender_chat_id.split("@")[0] if sender_chat_id else ""
    if session_sender:
        _load_persisted_workflow_sessions(session_sender)
    token = _FINANCIAL_REQUEST_CONTEXT.set({"event_id": str(event_id or secrets.token_urlsafe(24)), "counts": {}})
    try:
        result = await _whatsapp_webhook_process(request)
        if event_id:
            result_status = str((result or {}).get("status") or "") if isinstance(result, dict) else ""
            if result_status.endswith(("_error", "_failed")) or result_status in {"error", "failed"}:
                supabase.rpc("fail_webhook_event", {"p_event_id": str(event_id)}).execute()
            else:
                supabase.rpc("complete_webhook_event", {"p_event_id": str(event_id)}).execute()
        return result
    except Exception as webhook_exc:
        print(
            "❌ Webhook processing failed: "
            f"type={type(webhook_exc).__name__}, event_id={str(event_id or '')[:80]}, "
            f"error={webhook_exc}"
        )
        if event_id:
            try:
                supabase.rpc("fail_webhook_event", {"p_event_id": str(event_id)}).execute()
            except Exception as mark_error:
                print(
                    "⚠️ Could not mark webhook failed: "
                    f"{type(mark_error).__name__}: {mark_error}"
                )
        raise
    finally:
        if session_sender:
            _save_persisted_workflow_sessions(session_sender)
        _FINANCIAL_REQUEST_CONTEXT.reset(token)


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
            def build_daily_digest_query():
                return (
                    supabase.table("customers")
                    .select("name, amount, promised_date, id")
                    .eq("business_user_id", business_user_id)
                    .eq("is_archived", False)
                    .eq("is_paid", False)
                    .order("promised_date", desc=False)
                    .order("id", desc=False)
                )

            # Fetch every unpaid customer with a due date, across all database
            # pages. The reminder below includes every overdue and due-today row.
            debts = fetch_all_supabase_rows(build_daily_digest_query)

            overdue_items = []
            today_items = []
            overdue_total = 0.0
            today_total = 0.0
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
                        f"{len(overdue_items) + 1}. {customer_name}: {amount_text} — ⚠️ Mudo dhaaf ({overdue_days} maalin)"
                    )
                    overdue_total += _safe_money(debt.get("amount"))
                elif due_date == today_date:
                    today_items.append(
                        f"{len(today_items) + 1}. {customer_name}: {amount_text} — 🔴 Maanta"
                    )
                    today_total += _safe_money(debt.get("amount"))

            all_items = overdue_items + today_items
            print(f"📅 Daily digest user={business_user_id}: overdue={len(overdue_items)}, due_today={len(today_items)}")
            if not all_items:
                skipped_count += 1
                continue

            # Include every overdue and due-today customer. No 40-item cap and
            # no "more customers" omission notice: this is the complete reminder.
            message_lines = ["☀️ *Xusuusinta Subaxnimo* ☀️", ""]
            if overdue_items:
                message_lines.extend([
                    f"⚠️ *DEYMAHA BALAN DHAAFKA AH ({len(overdue_items)})*",
                    *overdue_items,
                    "",
                ])
            if today_items:
                message_lines.extend([
                    f"🔴 *BALANTA MAANTA ({len(today_items)})*",
                    *today_items,
                ])
            message_lines.extend([
                "",
                f"💰 Wadarta guud: ${overdue_total + today_total:,.2f}",
            ])

            ok = send_whatsapp(phone, "\n".join(message_lines))
            if ok:
                sent_count += 1
                print(f"✅ Complete daily digest sent: user={business_user_id}, overdue={len(overdue_items)}, due_today={len(today_items)}, total={len(all_items)}")
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
