#!/usr/bin/env python3
"""Check that every problem-sheet question has at least one tagged level.

Usage: python3 scripts/check_coverage.py
Exits non-zero if a question is missing, or a tagged level lacks an @answer block.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
# Number of questions on each MT2026 sheet.
QUESTIONS = {1: 13, 2: 10, 3: 11, 4: 12, 5: 6, 6: 5, 7: 9, 8: 7, 9: 8, 10: 8}
TAG = re.compile(r"^--\s*@sheet\s+(\d+)\s+Q(\d+)(\S*)", re.M)

found, no_answer = {}, []
for f in sorted((ROOT / "Game" / "Levels").rglob("*.lean")):
    src = f.read_text()
    for m in TAG.finditer(src):
        sheet, q, part = int(m.group(1)), int(m.group(2)), m.group(3)
        found.setdefault((sheet, q), []).append(f"Q{q}{part} ({f.relative_to(ROOT)})")
        if "@answer" not in src:
            no_answer.append(f"S{sheet} Q{q}{part}: {f.relative_to(ROOT)}")

missing = [f"S{s} Q{q}" for s, n in QUESTIONS.items() for q in range(1, n + 1) if (s, q) not in found]
total = sum(QUESTIONS.values())
print(f"{total - len(missing)}/{total} sheet questions have a level "
      f"({sum(len(v) for v in found.values())} tagged levels).")
for s in QUESTIONS:
    have = sum(1 for q in range(1, QUESTIONS[s] + 1) if (s, q) in found)
    print(f"  Sheet {s:>2}: {have}/{QUESTIONS[s]}")
if missing:
    print("Missing:", ", ".join(missing))
if no_answer:
    print("Tagged levels without an @answer block:\n  " + "\n  ".join(no_answer))
sys.exit(1 if missing or no_answer else 0)
