"""Průběžné výsledky voleb do zastupitelstva města Louny (9.-10. 10. 2026).

Skript stáhne oficiální XML z otevřených dat ČSÚ (volby.gov.cz), spočítá
rozdělení mandátů a vygeneruje index.html.

- Dokud ČSÚ nemá sečtené všechny okrsky, mandáty nepřiděluje. Skript proto
  ukazuje vlastní PRŮBĚŽNÝ ODHAD z dosud sečtených hlasů.
- Jakmile je sečteno vše (JE_SPOCTENO="1"), zobrazí se OFICIÁLNÍ počty
  mandátů přímo z dat ČSÚ.

Použití:
    python3 election_tracker.py                # stáhne živá data
    python3 election_tracker.py --file x.xml   # načte XML ze souboru (test)

Nepotřebuje žádné knihovny mimo standardní Python 3.9+.
"""

import argparse
import hashlib
import html
import os
import re
import sys
import time
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime
from fractions import Fraction
from zoneinfo import ZoneInfo

# --- Nastavení -------------------------------------------------------------

KOD_ZASTUPITELSTVA = "565971"  # Louny
DATA_URL = (
    "https://volby.gov.cz/appdata/kv2026/20261009/odata/zastup/"
    f"vysledky_obec_{KOD_ZASTUPITELSTVA}.xml"
)
OFICIALNI_STRANKA = "https://volby.gov.cz/"
OUTPUT_FILE = "index.html"
KLAUZULE_PROCENT = 5

# Klíčem je vylosované číslo strany na hlasovacím lístku.
# Zkratku a emoji si můžete libovolně změnit.
PARTIES = {
    1: {"short": "KSČM", "emoji": "🟪"},
    2: {"short": "USZ", "emoji": "🟩"},
    3: {"short": "ODS (VIZE)", "emoji": "🟨"},
    4: {"short": "SOCDEM", "emoji": "🟧"},
    5: {"short": "LS", "emoji": "⬛"},
    6: {"short": "ANO", "emoji": "🟦"},
    7: {"short": "SPD", "emoji": "🟫"},
    8: {"short": "LOPAT", "emoji": "🟥"},
    9: {"short": "PLL", "emoji": "🩷"},
}
NEZNAMA_STRANA = {"short": None, "emoji": "⬜"}


# --- Načtení dat -----------------------------------------------------------

def download_xml(url, attempts=3):
    last_error = None
    for attempt in range(attempts):
        try:
            request = urllib.request.Request(
                url, headers={"User-Agent": "volby-louny-tracker/1.0"}
            )
            with urllib.request.urlopen(request, timeout=30) as response:
                return response.read()
        except Exception as error:  # síťová chyba, timeout, HTTP chyba
            last_error = error
            time.sleep(5 * (attempt + 1))
    raise RuntimeError(f"Data z {url} se nepodařilo stáhnout: {last_error}")


def strip_namespaces(root):
    for element in root.iter():
        if "}" in element.tag:
            element.tag = element.tag.split("}", 1)[1]


def to_int(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def parse_results(xml_bytes):
    root = ET.fromstring(xml_bytes)
    strip_namespaces(root)

    obec = root.find(".//OBEC")
    if obec is None:
        raise RuntimeError("XML neobsahuje element OBEC (chyba na straně ČSÚ?).")
    ucast = obec.find(".//UCAST")
    if ucast is None:
        raise RuntimeError("XML neobsahuje element UCAST.")

    parties = []
    for element in obec.iter("VOLEBNI_STRANA"):
        number = to_int(element.get("POR_STR_HLAS_LIST"))
        config = PARTIES.get(number, NEZNAMA_STRANA)
        full_name = element.get("NAZEV_STRANY", f"Strana č. {number}")

        elected = []
        for child in element:
            if child.get("PRIJMENI"):
                name = " ".join(
                    part
                    for part in (
                        child.get("TITULPRED"),
                        child.get("JMENO"),
                        child.get("PRIJMENI"),
                        child.get("TITULZA"),
                    )
                    if part
                )
                elected.append(name)

        parties.append(
            {
                "number": number,
                "short": config["short"] or full_name,
                "name": full_name,
                "emoji": config["emoji"],
                "votes": to_int(element.get("HLASY")),
                "votes_pct": element.get("HLASY_PROC", "0.00"),
                "candidates": to_int(element.get("KANDIDATU_POCET")),
                "official_mandates": to_int(element.get("ZASTUPITELE_POCET")),
                "elected": elected,
                "mandates": 0,
            }
        )

    return {
        "name": obec.get("NAZEVZAST", "Louny"),
        "seats": to_int(obec.get("VOLENO_ZASTUP")),
        "final": obec.get("JE_SPOCTENO") == "1",
        "generated": root.get("DATUM_CAS_GENEROVANI", ""),
        "districts_total": to_int(ucast.get("OKRSKY_CELKEM")),
        "districts_done": to_int(ucast.get("OKRSKY_ZPRAC")),
        "districts_pct": ucast.get("OKRSKY_ZPRAC_PROC", "0.00"),
        "turnout_pct": ucast.get("UCAST_PROC", "0.00"),
        "voters": to_int(ucast.get("ZAPSANI_VOLICI")),
        "envelopes": to_int(ucast.get("VYDANE_OBALKY")),
        "valid_votes": to_int(ucast.get("PLATNE_HLASY")),
        "parties": parties,
    }


# --- Výpočet mandátů (§ 45 zákona č. 491/2001 Sb.) -------------------------

def allocate_mandates(parties, seats, clause_pct=KLAUZULE_PROCENT):
    """Vrátí ({číslo strany: mandáty}, použitá klauzule v %).

    1. Do skrutinia postoupí strany s alespoň 5 % hlasů. Základ se u strany
       s méně kandidáty, než je volených zastupitelů, poměrně snižuje.
    2. Nepostoupí-li aspoň dvě strany, klauzule se snižuje po 1 procentním bodu.
    3. Hlasy postupujících stran se dělí čísly 1, 2, 3... (nejvýše tolikrát,
       kolik má strana kandidátů) a mandáty dostanou nejvyšší podíly.
       Při shodě podílů rozhoduje vyšší celkový počet hlasů strany, pak los
       (zde nahrazen číslem strany, aby byl výsledek při každém běhu stejný).
    """
    result = {party["number"]: 0 for party in parties}
    total = sum(party["votes"] for party in parties)
    if total == 0 or seats <= 0:
        return result, clause_pct

    def passes(party, pct):
        base = Fraction(total * min(party["candidates"], seats), seats)
        return party["votes"] > 0 and party["votes"] * 100 >= pct * base

    pct = clause_pct
    while True:
        qualified = [party for party in parties if passes(party, pct)]
        if len(qualified) >= 2 or pct == 0:
            break
        pct -= 1

    quotients = []
    for party in qualified:
        for divisor in range(1, party["candidates"] + 1):
            quotients.append(
                (Fraction(party["votes"], divisor), party["votes"], -party["number"])
            )
    quotients.sort(reverse=True)

    for _, _, negative_number in quotients[:seats]:
        result[-negative_number] += 1
    return result, pct


def apply_mandates(data):
    """Doplní stranám mandáty a vrátí režim: 'final', 'estimate' nebo 'waiting'."""
    if data["final"]:
        for party in data["parties"]:
            party["mandates"] = party["official_mandates"]
        return "final"

    total = sum(party["votes"] for party in data["parties"])
    if data["districts_done"] == 0 or total == 0:
        return "waiting"

    mandates, _ = allocate_mandates(data["parties"], data["seats"])
    for party in data["parties"]:
        party["mandates"] = mandates[party["number"]]
    return "estimate"


# --- Generování stránky ----------------------------------------------------

def number(value):
    return f"{value:,}".replace(",", "\u00a0")


def data_signature(data, mode):
    parts = [mode, str(data["districts_done"]), str(data["districts_total"])]
    for party in sorted(data["parties"], key=lambda p: p["number"]):
        parts.append(f'{party["number"]}:{party["votes"]}:{party["mandates"]}')
        parts.extend(party["elected"])
    return hashlib.sha256("|".join(parts).encode("utf-8")).hexdigest()[:16]


def format_csu_time(value):
    try:
        return datetime.fromisoformat(value).strftime("%d.%m.%Y %H:%M:%S")
    except ValueError:
        return value or "neuvedeno"


def generate_html(data, mode, signature):
    esc = html.escape
    seats = data["seats"]
    majority = seats // 2 + 1
    now = datetime.now(ZoneInfo("Europe/Prague")).strftime("%d.%m.%Y %H:%M:%S")

    if mode == "final":
        status_class = "final"
        status_text = (
            "<strong>Konečný výsledek.</strong> Sečteny všechny okrsky, "
            "počty mandátů jsou oficiální údaje ČSÚ."
        )
    elif mode == "estimate":
        status_class = "estimate"
        status_text = (
            f"<strong>Průběžný odhad.</strong> Sečteno {data['districts_done']} "
            f"z {data['districts_total']} okrsků ({esc(data['districts_pct'])} %). "
            "Mandáty jsou přepočtené z dosud sečtených hlasů a ještě se mohou změnit."
        )
    else:
        status_class = "waiting"
        status_text = (
            "<strong>Sčítání ještě nezačalo.</strong> Volební místnosti se zavírají "
            "v sobotu 10. 10. 2026 ve 14:00, první výsledky se objeví krátce poté."
        )

    by_mandates = sorted(
        data["parties"], key=lambda p: (-p["mandates"], -p["votes"], p["number"])
    )
    by_votes = sorted(data["parties"], key=lambda p: (-p["votes"], p["number"]))

    if mode == "waiting":
        hall = '<span class="empty">' + "⬜ " * seats + "</span>"
    else:
        hall = "".join(
            f'<span title="{esc(party["short"])}: {party["mandates"]}">'
            + (party["emoji"] + " ") * party["mandates"]
            + "</span>"
            for party in by_mandates
            if party["mandates"] > 0
        )

    rows = ""
    for party in by_votes:
        mandates = "–" if mode == "waiting" else str(party["mandates"])
        rows += (
            "<tr>"
            f'<td class="num">{party["number"]}</td>'
            f'<td>{party["emoji"]} <strong>{esc(party["short"])}</strong>'
            f'<br><small>{esc(party["name"])}</small></td>'
            f'<td class="num">{number(party["votes"])}</td>'
            f'<td class="num">{esc(party["votes_pct"])} %</td>'
            f'<td class="num"><strong>{mandates}</strong></td>'
            "</tr>\n"
        )

    elected_html = ""
    if mode == "final" and any(party["elected"] for party in data["parties"]):
        elected_html = "<h2>Zvolení zastupitelé</h2>\n"
        for party in by_mandates:
            if party["elected"]:
                names = ", ".join(esc(name) for name in party["elected"])
                elected_html += (
                    f'<p>{party["emoji"]} <strong>{esc(party["short"])}</strong>: '
                    f"{names}</p>\n"
                )

    mandates_label = "Mandáty" if mode == "final" else "Mandáty (odhad)"

    return f"""<!DOCTYPE html>
<html lang="cs">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta http-equiv="refresh" content="60">
    <!-- data-signature:{signature} -->
    <title>Volby {esc(data["name"])} 2026 - průběžné výsledky</title>
    <style>
        body {{ font-family: Arial, sans-serif; max-width: 800px; margin: 0 auto; padding: 20px; color: #222; }}
        h1 {{ color: #333; margin-bottom: 4px; }}
        small {{ color: #666; }}
        .update-time {{ color: #666; font-size: 0.9em; }}
        .status {{ padding: 12px 16px; border-radius: 8px; margin: 16px 0; border-left: 6px solid; }}
        .status.waiting {{ background: #f0f0f0; border-color: #999; }}
        .status.estimate {{ background: #fff6d6; border-color: #e0a800; }}
        .status.final {{ background: #e2f5e5; border-color: #2e9e44; }}
        .sal {{ font-size: 24px; line-height: 1.5; margin: 12px 0; background: #f5f5f5; padding: 20px; border-radius: 8px; word-break: break-word; }}
        .sal .empty {{ opacity: 0.35; }}
        .facts {{ display: flex; flex-wrap: wrap; gap: 8px 24px; margin: 12px 0; }}
        table {{ width: 100%; border-collapse: collapse; margin-top: 12px; }}
        th, td {{ padding: 10px; border-bottom: 1px solid #ddd; text-align: left; vertical-align: top; }}
        th {{ background-color: #f2f2f2; }}
        .num {{ text-align: right; white-space: nowrap; }}
        footer {{ margin-top: 24px; color: #666; font-size: 0.85em; }}
    </style>
</head>
<body>
    <h1>{esc(data["name"])}: výsledky voleb do zastupitelstva 2026</h1>
    <p class="update-time">Poslední změna dat: {now} &middot; údaj ČSÚ z {esc(format_csu_time(data["generated"]))}</p>

    <div class="status {status_class}">{status_text}</div>

    <div class="facts">
        <span>Sečtené okrsky: <strong>{data["districts_done"]} / {data["districts_total"]}</strong></span>
        <span>Volební účast: <strong>{esc(data["turnout_pct"])} %</strong></span>
        <span>Platné hlasy: <strong>{number(data["valid_votes"])}</strong></span>
    </div>

    <h2>Složení zastupitelstva ({seats} křesel, většina {majority})</h2>
    <div class="sal">{hall}</div>

    <h2>Hlasy a mandáty</h2>
    <table>
        <tr><th class="num">Č.</th><th>Strana</th><th class="num">Hlasy</th><th class="num">Podíl</th><th class="num">{mandates_label}</th></tr>
{rows}    </table>

    {elected_html}
    <footer>
        Zdroj dat: Český statistický úřad, <a href="{OFICIALNI_STRANKA}">volby.gov.cz</a> (otevřená data).
        Stránka kontroluje nová data přibližně každých 5 až 15 minut a přepíše se jen při změně.
        Průběžný odhad mandátů je vlastní výpočet podle § 45 zákona č. 491/2001 Sb., závazné jsou až výsledky ČSÚ.
    </footer>
</body>
</html>
"""


def existing_signature(path):
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as file:
        match = re.search(r"data-signature:([0-9a-f]+)", file.read())
    return match.group(1) if match else None


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--file", help="načíst XML z místního souboru místo stažení")
    parser.add_argument("--output", default=OUTPUT_FILE, help="výstupní HTML soubor")
    args = parser.parse_args()

    try:
        if args.file:
            with open(args.file, "rb") as file:
                xml_bytes = file.read()
        else:
            xml_bytes = download_xml(DATA_URL)
        data = parse_results(xml_bytes)
    except Exception as error:
        # Stará stránka zůstane beze změny, běh v GitHub Actions neselže.
        print(f"::warning::Aktualizace přeskočena: {error}")
        return 0

    mode = apply_mandates(data)
    signature = data_signature(data, mode)

    if existing_signature(args.output) == signature:
        print("Data se od posledního běhu nezměnila, stránka zůstává.")
        return 0

    with open(args.output, "w", encoding="utf-8") as file:
        file.write(generate_html(data, mode, signature))

    summary = ", ".join(
        f'{party["short"]} {party["mandates"]}'
        for party in sorted(data["parties"], key=lambda p: -p["mandates"])
        if party["mandates"]
    )
    print(
        f"Vygenerován {args.output} ({mode}): okrsky "
        f'{data["districts_done"]}/{data["districts_total"]}. {summary}'
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
