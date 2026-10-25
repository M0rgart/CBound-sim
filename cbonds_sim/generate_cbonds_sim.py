#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Генератор синтетических данных в стиле Cbonds (облигационный рынок).

Скрипт создаёт правдоподобный, но полностью искусственный набор данных:
эмитенты, выпуски облигаций, купонные графики, дневные котировки,
индексы и рейтинговые события. Никакие реальные данные Cbonds не
используются и не копируются.

Запуск:
    py -3 generate_cbonds_sim.py --out data
    py -3 generate_cbonds_sim.py --out data --seed 7 --bonds 500

Зависимости: только стандартная библиотека Python 3.9+.
"""

from __future__ import annotations

import argparse
import calendar
import csv
import math
import os
import random
import statistics
import sys
from collections import defaultdict
from datetime import date, timedelta

# ---------------------------------------------------------------------------
# Константы рынка
# ---------------------------------------------------------------------------

START_DATE = date(2024, 1, 2)
END_DATE = date(2024, 12, 30)
VALUATION_DATE = date(2024, 12, 30)

RATINGS = ["AAA", "AA+", "AA", "AA-", "A+", "A", "A-",
           "BBB+", "BBB", "BBB-", "BB+", "BB", "BB-",
           "B+", "B", "B-", "CCC"]

RATING_SPREAD_BP = {
    "AAA": 40, "AA+": 60, "AA": 85, "AA-": 110,
    "A+": 140, "A": 175, "A-": 210,
    "BBB+": 260, "BBB": 320, "BBB-": 400,
    "BB+": 500, "BB": 620, "BB-": 760,
    "B+": 950, "B": 1200, "B-": 1500, "CCC": 2200,
}

RATING_WEIGHTS = {
    "AAA": 2, "AA+": 3, "AA": 5, "AA-": 6,
    "A+": 9, "A": 10, "A-": 9,
    "BBB+": 8, "BBB": 8, "BBB-": 6,
    "BB+": 6, "BB": 5, "BB-": 4,
    "B+": 4, "B": 3, "B-": 2, "CCC": 1,
}

RATING_AGENCY = {
    "AAA": "АКРА", "AA+": "АКРА", "AA": "АКРА", "AA-": "АКРА",
    "A+": "Эксперт РА", "A": "Эксперт РА", "A-": "Эксперт РА",
    "BBB+": "Эксперт РА", "BBB": "Эксперт РА", "BBB-": "Эксперт РА",
    "BB+": "АКРА", "BB": "АКРА", "BB-": "АКРА",
    "B+": "Эксперт РА", "B": "Эксперт РА", "B-": "Эксперт РА",
    "CCC": "Эксперт РА",
}

# Кривая бескупонной доходности (Nelson-Siegel) на начало и конец года.
# (b0, b1, b2, tau): y(t) = b0 + b1*NS1 + b2*(NS1 - exp(-t/tau))
GOV_CURVES = {
    "RUB": ((11.7, 3.9, -1.2, 1.6), (13.8, 8.0, -1.5, 1.5)),
    "USD": ((4.55, 0.05, -0.35, 2.0), (4.70, -0.25, -0.30, 2.0)),
    "CNY": ((2.55, 0.15, -0.10, 1.8), (2.70, 0.05, -0.10, 1.8)),
}

FX_TO_RUB = {"RUB": 1.0, "USD": 92.5, "CNY": 12.7}

# sector -> (спред к ОФЗ, бп; допустимые рейтинги; вес)
SECTORS = [
    ("Нефть и газ", -10, ["AAA", "AA", "AA-", "A+", "A", "A-"], 0.10),
    ("Металлургия", -5, ["AA-", "A+", "A", "A-", "BBB+", "BB+"], 0.07),
    ("Банки", -20, ["AA+", "AA", "AA-", "A+", "A", "A-", "BBB+", "BBB", "BB+"], 0.15),
    ("Телеком", 0, ["AA-", "A+", "A", "A-", "BBB+", "BB+"], 0.06),
    ("Ритейл", 30, ["A+", "A", "A-", "BBB+", "BBB", "BBB-", "BB+", "BB"], 0.08),
    ("Электроэнергетика", 10, ["AA", "AA-", "A+", "A", "A-", "BBB+", "BB+"], 0.07),
    ("Транспорт и логистика", 20, ["AA-", "A+", "A", "A-", "BBB+", "BBB", "BB+"], 0.07),
    ("Строительство и девелопмент", 50, ["A", "A-", "BBB+", "BBB", "BBB-", "BB+", "BB", "BB-"], 0.07),
    ("МФО", 150, ["A", "A-", "BBB+", "BBB", "BBB-", "BB+", "BB", "BB-", "B+", "B", "B-"], 0.06),
    ("Химия и удобрения", 10, ["AA-", "A+", "A", "A-", "BBB+", "BB+"], 0.05),
    ("Машиностроение", 30, ["A", "A-", "BBB+", "BBB", "BB+", "BB"], 0.04),
    ("Финансовые компании", 40, ["AA-", "A+", "A", "A-", "BBB+", "BBB", "BB+", "BB"], 0.06),
    ("Квазигосударственные", -30, ["AAA", "AA+", "AA", "AA-"], 0.06),
    ("Субфедеральные образования", 40, ["AA", "AA-", "A+", "A", "A-", "BBB+"], 0.05),
]

NAME_PREFIXES = ["Северный", "Волжский", "Уральский", "Сибирский", "Балтийский",
                 "Южный", "Каспийский", "Дальневосточный", "Центральный",
                 "Приморский", "Амурский", "Окский", "Донской", "Камский",
                 "Полярный", "Онежский", "Енисейский", "Ленский"]

SECTOR_NOUNS = {
    "Нефть и газ": ["Нефтегаз", "Петролеум", "Энергоресурс", "Нефть", "Газохим"],
    "Металлургия": ["Металл", "Сталь", "Прокат", "Рудник", "Сплав"],
    "Банки": ["Банк", "Кредит", "Финанс", "Капитал", "Банкир"],
    "Телеком": ["Телеком", "Связь", "Телекоммуникации", "Медиа", "Сети"],
    "Ритейл": ["Торг", "Ритейл", "Маркет", "Продукт", "Универмаг"],
    "Электроэнергетика": ["Энерго", "Электросети", "Генерация", "Энергосбыт", "Теплоэнерго"],
    "Транспорт и логистика": ["Логистика", "Транспорт", "Порт", "Терминал", "Экспедиция"],
    "Строительство и девелопмент": ["Строй", "Девелопмент", "Недвижимость", "Стройинвест", "Квартал"],
    "МФО": ["Микрокредит", "Займ", "Финанс", "Кредит", "Деньги"],
    "Химия и удобрения": ["Химия", "Удобрения", "Полимер", "Химзавод", "Реагент"],
    "Машиностроение": ["Машины", "Завод", "Техника", "Двигатель", "Станкостроение"],
    "Финансовые компании": ["Лизинг", "Инвест", "Капитал", "Финанс", "Актив"],
    "Квазигосударственные": ["Развитие", "Инфраструктура", "Проект", "Фонд", "Корпорация"],
    "Субфедеральные образования": ["Область", "Край", "Республика", "Округ"],
}

REGIONS = ["Самарская", "Нижегородская", "Свердловская", "Новосибирская",
           "Ростовская", "Тюменская", "Иркутская", "Омская", "Томская",
           "Белгородская", "Воронежская", "Ярославская", "Красноярский",
           "Пермский", "Ставропольский", "Хабаровский", "Приморский"]

LEGAL_FORMS = ["ПАО", "АО", "ООО"]


# ---------------------------------------------------------------------------
# Вспомогательные функции
# ---------------------------------------------------------------------------

def add_months(d: date, n: int) -> date:
    y = d.year + (d.month - 1 + n) // 12
    m = (d.month - 1 + n) % 12 + 1
    day = min(d.day, calendar.monthrange(y, m)[1])
    return date(y, m, day)


def trading_days(start: date, end: date) -> list[date]:
    days, d = [], start
    while d <= end:
        if d.weekday() < 5:
            days.append(d)
        d += timedelta(days=1)
    return days


def ns_yield(t: float, p: tuple[float, float, float, float]) -> float:
    b0, b1, b2, tau = p
    t = max(t, 0.08)
    x = t / tau
    ns1 = (1.0 - math.exp(-x)) / x
    return b0 + b1 * ns1 + b2 * (ns1 - math.exp(-x))


def interpolate_params(p0, p1, f):
    return tuple(a + (b - a) * f for a, b in zip(p0, p1))


def coupon_schedule(issue: date, maturity: date, freq: int) -> list[date]:
    step = 12 // freq
    dates, d = [], maturity
    while d > issue:
        dates.append(d)
        d = add_months(d, -step)
    dates.reverse()
    return dates


def accrued_fraction(schedule, t0: date) -> float:
    prev = max((d for d in schedule if d <= t0), default=None)
    nxt = min((d for d in schedule if d > t0), default=None)
    if nxt is None:
        return 0.0
    if prev is None:
        prev = add_months(nxt, -1)
    span = max((nxt - prev).days, 1)
    return min(max((t0 - prev).days / span, 0.0), 1.0)


def bond_metrics(schedule, t0: date, face: float, coupon_rate: float,
                 freq: int, ytm: float):
    """Возвращает (clean, accrued, dirty, mac_duration, mod_duration, n_left)."""
    future = [d for d in schedule if d > t0]
    if not future:
        return None
    per = coupon_rate * face / freq
    w = accrued_fraction(schedule, t0)
    accrued = per * w
    t_first = max((future[0] - t0).days, 1) / 365.25
    dirty = 0.0
    weighted_t = 0.0
    for i, d in enumerate(future):
        t = t_first + i / freq
        cf = per + (face if i == len(future) - 1 else 0.0)
        pv = cf * (1.0 + ytm / freq) ** (-freq * t)
        dirty += pv
        weighted_t += t * pv
    if dirty <= 0:
        return None
    mac = weighted_t / dirty
    mod = mac / (1.0 + ytm / freq)
    return dirty - accrued, accrued, dirty, mac, mod, len(future)


def clamp(x, lo, hi):
    return max(lo, min(hi, x))


def fmt(x, nd=4):
    return "" if x is None else f"{x:.{nd}f}"


# ---------------------------------------------------------------------------
# Генерация справочников
# ---------------------------------------------------------------------------

def make_issuers(rng: random.Random, n_issuers: int) -> list[dict]:
    sectors = [(name, adj, ratings, weight) for name, adj, ratings, weight in SECTORS]
    total_w = sum(s[3] for s in sectors)
    issuers = []

    # ОФЗ — отдельный "эмитент"
    issuers.append({
        "issuer_id": "ISS0000",
        "name": "Министерство финансов РФ",
        "short_name": "Минфин России",
        "sector": "Государственные облигации",
        "group": "government",
        "rating": "AAA",
        "agency": "АКРА",
        "region": "Россия",
        "inn": "7700000000",
    })

    for i in range(1, n_issuers + 1):
        r = rng.random() * total_w
        acc = 0.0
        sector, adj, ratings, _ = sectors[0]
        for s in sectors:
            acc += s[3]
            if r <= acc:
                sector, adj, ratings, _ = s
                break
        if sector == "Субфедеральные образования":
            region = rng.choice(REGIONS)
            name = f"{region} область"
            short = name
            legal = ""
            rating = rng.choices(ratings, weights=[RATING_WEIGHTS[r] for r in ratings], k=1)[0]
        else:
            legal = rng.choice(LEGAL_FORMS if sector != "Банки" else ["ПАО", "АО"])
            noun = rng.choice(SECTOR_NOUNS[sector])
            name = f"{legal} «{rng.choice(NAME_PREFIXES)} {noun}»"
            short = f"{rng.choice(NAME_PREFIXES)} {noun}"
            rating = rng.choices(ratings, weights=[RATING_WEIGHTS[r] for r in ratings], k=1)[0]
        issuers.append({
            "issuer_id": f"ISS{i:04d}",
            "name": name,
            "short_name": short,
            "sector": sector,
            "group": ("bank" if sector == "Банки" else
                      "mfo" if sector == "МФО" else
                      "sub_sovereign" if sector == "Субфедеральные образования" else
                      "quasi_sovereign" if sector == "Квазигосударственные" else
                      "corporate"),
            "rating": rating,
            "agency": RATING_AGENCY[rating],
            "region": rng.choice(REGIONS) if sector != "Субфедеральные образования" else name,
            "inn": f"{rng.randint(1, 9)}{rng.randint(0, 999999999):09d}",
        })
    return issuers


def make_bonds(rng, issuers, n_bonds):
    """Создаёт выпуски: ОФЗ + корпоративные/субфедеральные/квазигосударственные."""
    bonds: list[dict] = []
    gov = next(i for i in issuers if i["group"] == "government")
    corporates = [i for i in issuers if i["group"] != "government"]
    seq = defaultdict(int)
    used_isin: set[str] = set()

    def new_isin() -> str:
        while True:
            isin = "RU000A" + "".join(rng.choice("0123456789ABCDEFGHJKLMNPQRSTUVWXYZ")
                                      for _ in range(6))
            if isin not in used_isin:
                used_isin.add(isin)
                return isin

    def build(issuer, is_ofz, ccy, ctype, freq, issue, maturity, size, status, num,
              coupon_override=None):
        tenor_years = max((maturity - issue).days / 365.25, 0.3)
        adj = next((s[1] for s in SECTORS if s[0] == issuer["sector"]), 0)
        base = ns_yield(tenor_years, GOV_CURVES[ccy][1])
        if is_ofz:
            spread = 0
        else:
            spread = RATING_SPREAD_BP[issuer["rating"]] + adj
            if ccy == "USD":
                spread += 30
        ytm_issue = (base + spread / 10000.0) / 100.0 + rng.gauss(0, 0.0025)

        if ctype == "zero":
            coupon_rate = 0.0
        elif ctype == "floater":
            coupon_rate = round(clamp(base / 100.0 + rng.uniform(0.005, 0.02),
                                      0.01, 0.40) * 100, 2)
        elif coupon_override is not None:
            coupon_rate = coupon_override
        else:
            coupon_rate = round(clamp(ytm_issue * 100 + rng.gauss(0, 0.35), 0.1, 35.0), 2)

        face = 1000.0
        outstanding = size / face
        if status == "Погашена":
            outstanding *= rng.uniform(0.0, 0.05)

        if is_ofz:
            series = f"ОФЗ-{'ПД' if ctype == 'fixed' else 'ПК'} {num}"
        elif ccy != "RUB":
            series = f"{num:02d}"
        else:
            series = rng.choice(["БО", "001P", "002P"]) + f"-{num:02d}"

        return {
            "isin": new_isin(),
            "issuer_id": issuer["issuer_id"],
            "name": f"{issuer['short_name']} {series}",
            "series": series,
            "currency": ccy,
            "sector": issuer["sector"],
            "group": issuer["group"],
            "rating": issuer["rating"],
            "coupon_type": {"fixed": "Фиксированный",
                            "floater": "Плавающий",
                            "zero": "Бескупонный"}[ctype],
            "coupon_freq": freq,
            "coupon_rate": coupon_rate,
            "issue_date": issue,
            "maturity_date": maturity,
            "offer_date": (add_months(issue, rng.choice([36, 60, 84]))
                           if status == "Оферта" else None),
            "face_value": face,
            "outstanding": outstanding * face,
            "status": status,
            "listing": ("МосБиржа, 1 уровень" if is_ofz else
                        rng.choice(["МосБиржа, 1 уровень", "МосБиржа, 2 уровень",
                                    "МосБиржа, 3 уровень", "Вне списка"])),
            "amortization": rng.random() < 0.12,
            "spread_base_bp": spread,
            "is_ofz": is_ofz,
            "_ctype_raw": ctype,
        }

    # --- ОФЗ: 10 выпусков с разными сроками -------------------------------
    ofz_offsets = [3, 9, 18, 30, 48, 66, 90, 126, 168, 216]
    for k, off in enumerate(ofz_offsets):
        maturity = add_months(VALUATION_DATE, off)
        issue = add_months(VALUATION_DATE, -rng.choice([12, 24, 36, 60, 84, 120]))
        is_fixed = (k % 3 != 2)
        ctype = "fixed" if is_fixed else "floater"
        freq = 2 if is_fixed else 4
        num = (26200 + k) if is_fixed else (29000 + k)
        size = rng.choice([350, 400, 500, 600, 700, 800]) * 1e9
        coupon = round(clamp(ns_yield((maturity - issue).days / 365.25,
                                      GOV_CURVES["RUB"][0]), 5.0, 12.5), 2)
        bonds.append(build(gov, True, "RUB", ctype, freq, issue, maturity,
                           size, "В обращении", num, coupon_override=coupon))

    # --- Корпоративные выпуски -------------------------------------------
    tries = 0
    while len(bonds) < n_bonds and tries < n_bonds * 40:
        tries += 1
        issuer = rng.choice(corporates)

        r = rng.random()
        if r < 0.82:
            ccy = "RUB"
        elif r < 0.95:
            ccy = "USD"
        else:
            ccy = "CNY"

        rc = rng.random()
        if rc < 0.68:
            ctype = "fixed"
        elif rc < 0.90:
            ctype = "floater"
        else:
            ctype = "zero"

        if ctype == "zero":
            freq = 2
        elif ctype == "fixed":
            freq = 2 if rng.random() < 0.4 else (4 if rng.random() < 0.85 else 12)
        else:
            freq = 4 if rng.random() < 0.85 else 12

        # даты: ~92% выпусков в обращении, ~8% уже погашены
        if rng.random() < 0.08:
            maturity = VALUATION_DATE - timedelta(days=rng.randint(30, 1500))
        else:
            maturity = VALUATION_DATE + timedelta(days=rng.choice(
                [90, 180, 270, 365, 540, 730, 1095, 1460, 1825, 2550, 3650, 5475]))
        issue = add_months(maturity, -rng.choice([12, 24, 36, 60, 84, 120, 180]))
        if issue > VALUATION_DATE - timedelta(days=90):
            issue = VALUATION_DATE - timedelta(days=rng.randint(90, 400))
        if issue < date(2015, 1, 1):
            issue = date(2015, 1, 1) + timedelta(days=rng.randint(0, 700))
        if issue >= maturity - timedelta(days=180):
            continue

        if maturity <= VALUATION_DATE:
            status = "Погашена"
        else:
            rstat = rng.random()
            if rstat < 0.02:
                status = "Дефолт"
            elif rstat < 0.07:
                status = "Оферта"
            else:
                status = "В обращении"

        size = rng.choice([3, 5, 10, 15, 20, 30, 50]) * 1e9
        if ccy != "RUB":
            size /= FX_TO_RUB[ccy]

        seq[(issuer["issuer_id"], ctype, ccy)] += 1
        num = seq[(issuer["issuer_id"], ctype, ccy)]
        bonds.append(build(issuer, False, ccy, ctype, freq, issue, maturity,
                           size, status, num))

    return bonds[:n_bonds]



# ---------------------------------------------------------------------------
# Дневная симуляция
# ---------------------------------------------------------------------------

def simulate(bonds, issuers_by_id, rng, days):
    by_isin = {b["isin"]: b for b in bonds}
    schedules = {}
    for b in bonds:
        schedules[b["isin"]] = coupon_schedule(b["issue_date"], b["maturity_date"],
                                               b["coupon_freq"])

    # OU-процессы идемпотентности
    level_noise = {"RUB": 0.0, "USD": 0.0, "CNY": 0.0}
    idio = {b["isin"]: (rng.gauss(0, 0.0003) if b["is_ofz"] else rng.gauss(0, 0.0025))
            for b in bonds}

    price_rows = []
    index_acc = []
    prev_dirty = {}
    prev_acc = {}
    prev_clean = {}
    prev_date = {}
    index_levels = defaultdict(lambda: 100.0)
    index_tr = defaultdict(lambda: 100.0)

    for k, day in enumerate(days):
        f = k / max(len(days) - 1, 1)

        # общий сдвиг кривой
        for ccy in level_noise:
            level_noise[ccy] = 0.85 * level_noise[ccy] + rng.gauss(0, 0.012)
        curves = {}
        for ccy, (p0, p1) in GOV_CURVES.items():
            b0, b1, b2, tau = interpolate_params(p0, p1, f)
            curves[ccy] = (b0 + level_noise[ccy], b1, b2, tau)

        bucket = defaultdict(lambda: {"w": 0.0, "ret": 0.0, "pret": 0.0, "ytm": [],
                                      "dur": [], "gs": [], "turn": 0.0})

        for b in bonds:
            isin = b["isin"]
            if day > b["maturity_date"] or b["status"] == "Погашена":
                continue
            if day < b["issue_date"]:
                continue

            tenor = max((b["maturity_date"] - day).days / 365.25, 0.02)
            gov_y = ns_yield(tenor, curves[b["currency"]])

            # индивидуальный кредитный шум (OU)
            sig = 0.0004 if b["is_ofz"] else 0.0022
            idio[isin] = 0.9 * idio[isin] + rng.gauss(0, sig)
            spread_bp = b["spread_base_bp"]
            if b["status"] == "Дефолт":
                spread_bp = max(spread_bp, 2500)
            elif b["status"] == "Оферта":
                spread_bp *= 1.05

            ytm = gov_y / 100.0 + (spread_bp / 10000.0) + idio[isin]
            ytm = clamp(ytm, 0.005, 0.60)

            ctype = b["_ctype_raw"]
            if ctype == "floater":
                coupon_now = clamp(gov_y / 100.0 + spread_bp / 10000.0, 0.0, 0.45)
                price_clean = clamp(100.0 + rng.gauss(0, 0.35), 92.0, 108.0)
                acc = coupon_now * 100.0 / b["coupon_freq"] * \
                    accrued_fraction(schedules[isin], day)
                dirty = price_clean + acc
                mod = max((min((d for d in schedules[isin] if d > day),
                               default=day + timedelta(days=90)) - day).days / 365.25, 0.02)
            else:
                metrics = bond_metrics(schedules[isin], day, 100.0,
                                       b["coupon_rate"] / 100.0, b["coupon_freq"], ytm)
                if metrics is None:
                    continue
                price_clean, acc, dirty, mac, mod, nleft = metrics
                if not (0.5 < price_clean < 250.0):
                    continue
                dirty = price_clean + acc

            g_spread_bp = (ytm - gov_y / 100.0) * 10000.0

            # оборот
            out_rub = b["outstanding"] * FX_TO_RUB[b["currency"]] * price_clean / 100.0
            turnover = out_rub * clamp(rng.lognormvariate(-5.2, 0.9), 0.0, 0.25)
            trades = max(0, int(turnover / max(2.0e6, out_rub * 1e-4)))

            price_rows.append({
                "date": day.isoformat(),
                "isin": isin,
                "currency": b["currency"],
                "price_clean": round(price_clean, 4),
                "accrued_int": round(acc, 4),
                "price_dirty": round(dirty, 4),
                "ytm": round(ytm * 100, 4),
                "current_yield": round((b["coupon_rate"] / price_clean) if price_clean else 0, 4),
                "g_spread_bp": round(g_spread_bp, 2),
                "mod_duration": round(mod, 4),
                "turnover_rub": round(turnover, 2),
                "trades": trades,
            })

            # индексы
            cats = []
            if b["currency"] == "RUB":
                if b["is_ofz"]:
                    cats += ["IFX_CBONDS", "CBONDS_RUB_GOV"]
                else:
                    cats.append("IFX_CBONDS")
                    if RATINGS.index(b["rating"]) <= RATINGS.index("BBB-"):
                        cats.append("CBONDS_RUB_CORP_IG")
                    else:
                        cats.append("CBONDS_RUB_CORP_HY")
            elif b["currency"] == "USD" and not b["is_ofz"]:
                cats.append("CBONDS_USD_CORP")

            # доходность за день: изменение «грязной» цены + выплаченный купон
            pd = prev_dirty.get(isin)
            pday = prev_date.get(isin)
            ret = 0.0
            if pd and pd > 0:
                paid = 0.0
                if pday is not None and any(pday < cd <= day for cd in schedules[isin]):
                    paid = prev_acc.get(isin, 0.0)
                ret = (dirty + paid) / pd - 1.0
            prev_dirty[isin] = dirty
            prev_acc[isin] = acc
            prev_date[isin] = day

            pc = prev_clean.get(isin)
            price_ret = (price_clean / pc - 1.0) if pc and pc > 0 else 0.0
            prev_clean[isin] = price_clean

            w = out_rub
            for c in cats:
                bb = bucket[c]
                bb["w"] += w
                bb["ret"] += w * ret
                bb["pret"] += w * price_ret
                bb["ytm"].append(ytm * 100)
                bb["dur"].append(mod)
                bb["gs"].append(g_spread_bp)
                bb["turn"] += turnover

        # уровни индексов: PI — по чистым ценам, TR — полная доходность
        for code, bb in bucket.items():
            if bb["w"] <= 0:
                continue
            r = clamp(bb["ret"] / bb["w"], -0.15, 0.15)
            pr = clamp(bb["pret"] / bb["w"], -0.15, 0.15)
            index_levels[code] *= (1.0 + pr)
            index_tr[code] *= (1.0 + r)
            index_acc.append({
                "date": day.isoformat(),
                "index_code": code,
                "bonds_count": len(bb["ytm"]),
                "level": round(index_levels[code], 4),
                "level_tr": round(index_tr[code], 4),
                "avg_ytm": round(statistics.fmean(bb["ytm"]), 3),
                "avg_duration": round(statistics.fmean(bb["dur"]), 3),
                "avg_g_spread_bp": round(statistics.fmean(bb["gs"]), 1),
                "turnover_rub": round(bb["turn"], 2),
            })

    return price_rows, index_acc, schedules


# ---------------------------------------------------------------------------
# Экспорт
# ---------------------------------------------------------------------------

def write_csv(path, rows, fields):
    with open(path, "w", newline="", encoding="utf-8-sig") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore", delimiter=";")
        w.writeheader()
        w.writerows(rows)


def build_valuation_rows(bonds, schedules, price_rows):
    last = {}
    for r in price_rows:
        last[r["isin"]] = r
    out = []
    for b in bonds:
        r = last.get(b["isin"])
        row = {
            "isin": b["isin"],
            "name": b["name"],
            "issuer_id": b["issuer_id"],
            "issuer": "",
            "sector": b["sector"],
            "group": b["group"],
            "rating": b["rating"],
            "currency": b["currency"],
            "coupon_type": b["coupon_type"],
            "coupon_freq": b["coupon_freq"],
            "coupon_rate": b["coupon_rate"],
            "issue_date": b["issue_date"].isoformat(),
            "maturity_date": b["maturity_date"].isoformat(),
            "offer_date": b["offer_date"].isoformat() if b["offer_date"] else "",
            "face_value": b["face_value"],
            "outstanding": round(b["outstanding"], 2),
            "status": b["status"],
            "listing": b["listing"],
            "amortization": "да" if b["amortization"] else "нет",
            "price_clean": r["price_clean"] if r else "",
            "accrued_int": r["accrued_int"] if r else "",
            "price_dirty": r["price_dirty"] if r else "",
            "ytm": r["ytm"] if r else "",
            "current_yield": r["current_yield"] if r else "",
            "g_spread_bp": r["g_spread_bp"] if r else "",
            "mod_duration": r["mod_duration"] if r else "",
            "turnover_rub": r["turnover_rub"] if r else 0,
            "trades": r["trades"] if r else 0,
        }
        out.append(row)
    return out


def build_rating_events(rng, valuation_rows, n_events=90):
    rows = []
    for _ in range(n_events):
        b = rng.choice([r for r in valuation_rows if r["status"] != "Погашена"])
        idx = RATINGS.index(b["rating"])
        action = rng.choices(
            ["Подтверждение", "Повышение", "Понижение", "Дефолт"],
            weights=[60, 15, 22, 3], k=1)[0]
        if action == "Повышение" and idx > 0:
            new = RATINGS[idx - 1]
        elif action == "Понижение" and idx < len(RATINGS) - 1:
            new = RATINGS[idx + 1]
        elif action == "Дефолт":
            new = "D"
        else:
            new = b["rating"]
            action = "Подтверждение"
        d = START_DATE + timedelta(days=rng.randint(0, (VALUATION_DATE - START_DATE).days))
        rows.append({
            "date": d.isoformat(),
            "isin": b["isin"],
            "issuer": b["issuer"],
            "agency": rng.choice(["АКРА", "Эксперт РА", "НРА"]),
            "action": action,
            "rating_from": b["rating"] if action != "Подтверждение" else b["rating"],
            "rating_to": new,
            "outlook": rng.choice(["Стабильный", "Позитивный", "Негативный", "Развивающийся"]),
        })
    rows.sort(key=lambda r: r["date"])
    return rows


def main():
    ap = argparse.ArgumentParser(description="Синтетические данные в стиле Cbonds")
    ap.add_argument("--out", default="data", help="каталог для CSV")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--issuers", type=int, default=55)
    ap.add_argument("--bonds", type=int, default=360)
    args = ap.parse_args()

    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

    rng = random.Random(args.seed)
    os.makedirs(args.out, exist_ok=True)

    days = trading_days(START_DATE, END_DATE)

    print(f"Генерация: seed={args.seed}, эмитентов={args.issuers}, выпусков={args.bonds}, дней={len(days)}")
    issuers = make_issuers(rng, args.issuers)
    issuers_by_id = {i["issuer_id"]: i for i in issuers}
    bonds = make_bonds(rng, issuers, args.bonds)
    print(f"Создано выпусков: {len(bonds)}")

    price_rows, index_rows, schedules = simulate(bonds, issuers_by_id, rng, days)
    print(f"Строк дневных котировок: {len(price_rows)}")

    # bonds.csv
    valuation = build_valuation_rows(bonds, schedules, price_rows)
    for r in valuation:
        r["issuer"] = issuers_by_id[r["issuer_id"]]["name"]

    # coupon schedule
    coupon_rows = []
    for b in bonds:
        for d in schedules[b["isin"]]:
            coupon_rows.append({
                "isin": b["isin"],
                "coupon_date": d.isoformat(),
                "coupon_per_100": round(b["coupon_rate"], 4),
                "coupon_amount": round(b["coupon_rate"] / 100 * b["face_value"]
                                       / b["coupon_freq"], 2),
                "currency": b["currency"],
            })

    rating_rows = build_rating_events(rng, valuation)

    iss_fields = ["issuer_id", "name", "short_name", "sector", "group",
                  "rating", "agency", "region", "inn"]
    bond_fields = ["isin", "name", "issuer_id", "issuer", "sector", "group", "rating",
                   "currency", "coupon_type", "coupon_freq", "coupon_rate",
                   "issue_date", "maturity_date", "offer_date", "face_value",
                   "outstanding", "status", "listing", "amortization",
                   "price_clean", "accrued_int", "price_dirty", "ytm",
                   "current_yield", "g_spread_bp", "mod_duration",
                   "turnover_rub", "trades"]
    price_fields = ["date", "isin", "currency", "price_clean", "accrued_int",
                    "price_dirty", "ytm", "current_yield", "g_spread_bp",
                    "mod_duration", "turnover_rub", "trades"]
    index_fields = ["date", "index_code", "bonds_count", "level", "level_tr",
                    "avg_ytm", "avg_duration", "avg_g_spread_bp", "turnover_rub"]
    coupon_fields = ["isin", "coupon_date", "coupon_per_100", "coupon_amount", "currency"]
    rating_fields = ["date", "isin", "issuer", "agency", "action", "rating_from",
                     "rating_to", "outlook"]

    write_csv(os.path.join(args.out, "issuers.csv"), issuers, iss_fields)
    write_csv(os.path.join(args.out, "bonds.csv"), valuation, bond_fields)
    write_csv(os.path.join(args.out, "prices_daily.csv"), price_rows, price_fields)
    write_csv(os.path.join(args.out, "coupons.csv"), coupon_rows, coupon_fields)
    write_csv(os.path.join(args.out, "indices_daily.csv"), index_rows, index_fields)
    write_csv(os.path.join(args.out, "rating_events.csv"), rating_rows, rating_fields)

    # сводка
    in_issue = [r for r in valuation if r["status"] != "Погашена" and r["ytm"] != ""]
    print(f"В обращении: {len(in_issue)} выпусков")
    if in_issue:
        print(f"Средняя доходность: {statistics.fmean(float(r['ytm']) for r in in_issue):.2f}%")
        print(f"Средняя дюрация:    {statistics.fmean(float(r['mod_duration']) for r in in_issue):.2f} лет")
        print(f"Суммарный объём:    {sum(float(r['outstanding']) * FX_TO_RUB[r['currency']] for r in in_issue) / 1e12:.2f} трлн ₽")
    if index_rows:
        last = {}
        for r in index_rows:
            last[r["index_code"]] = r
        print("Индексы на конец периода:")
        for code, r in sorted(last.items()):
            print(f"  {code:22s} level={r['level']:8.2f}  tr={r['level_tr']:8.2f}  ytm={r['avg_ytm']:.2f}%")

    print(f"Файлы записаны в: {os.path.abspath(args.out)}")


if __name__ == "__main__":
    main()
