#!/usr/bin/env python3
"""Flag tactics and proof syntax that a level needs but never explains.

For each level in game order:
- every tactic in its NewTactic line must be mentioned (in backticks) in that level's
  Introduction or hints;
- for each syntax pattern, at the FIRST level whose sample proof uses it, the level's
  Introduction or hints must mention it.
A player can't use what nobody told them exists.
"""
import re, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEVELS = ROOT / "Game" / "Levels"
order = re.findall(r"^import Game\.Levels\.(\w+)$", (ROOT / "Game.lean").read_text(), re.M)
SYNTAX = {  # name: (regex on proof, regex that counts as an explanation in intro/hints)
    "anonymous constructor ⟨a, b⟩ as a term": (r"(exact|refine|use|:=)\s*⟨", r"⟨"),
    "fun x => …": (r"\bfun\b", r"\bfun\b|λ"),
    "projections .1/.2/.mp/.mpr": (r"[\w)⟩]\.(1|2|mp|mpr)\b", r"\.(1|2|mp|mpr)\b"),
    ".symm / .trans / .le": (r"[\w)]\.(symm|trans|le|ne'|ne)\b", r"\.(symm|trans|le|ne)\b"),
    "<;> (apply to all goals)": (r"<;>", r"<;>"),
    "▸ (rewrite term)": (r"▸", r"▸"),
    "nested `by` inside a step": (r"(:=|\()\s*by\b", r"`[^`]*\bby\b[^`]*`"),
    "named arguments (h := …)": (r"\(\w+\s*:=", r"\(\w+\s*:="),
    "underscore placeholder _": (r"(exact|apply|refine)[^\n]*\s_[\s)]", r"\b_\b|`_`"),
    "@ explicit arguments": (r"@\w", r"@"),
    "calc block": (r"\bcalc\b", r"calc"),
    "show": (r"^\s*show\b", r"\bshow\b"),
    "all_goals / any_goals": (r"\b(all_goals|any_goals)\b", r"all_goals|any_goals"),
}

def parts(src):
    m = re.search(r"^Statement.*?(?=^Conclusion|\Z)", src, re.S | re.M)
    proof = m.group(0) if m else ""
    proof = proof.split(":= by", 1)[1] if ":= by" in proof else proof   # skip the statement line
    hints = " ".join(re.findall(r'Hint[^"\n]*"((?:[^"\\]|\\.)*)"', proof, re.S))
    proof_wo = re.sub(r'Hint[^"\n]*"(?:[^"\\]|\\.)*"', "", proof, flags=re.S)
    intro = re.search(r'Introduction\s+"((?:[^"\\]|\\.)*)"', src, re.S)
    return proof_wo, (intro.group(1) if intro else "") + " " + hints

first_seen = {}
problems = []
for w in order:
    for f in sorted((LEVELS / w).glob("L*.lean")):
        src = f.read_text()
        proof, text = parts(src)
        rel = f.relative_to(LEVELS)
        for line in re.findall(r"^NewTactic (.*)$", src, re.M):
            for t in line.split():
                t = t.strip("«»")
                if not re.search(r"`[^`]*\b" + re.escape(t) + r"\b[^`]*`", text):
                    problems.append((str(rel), f"tactic `{t}` unlocked but not explained"))
        for name, (use, expl) in SYNTAX.items():
            if name in first_seen:
                continue
            if re.search(use, proof, re.M):
                first_seen[name] = str(rel)
                if not re.search(expl, text):
                    problems.append((str(rel), f"first use of {name} — not explained"))
for rel, msg in problems:
    print(f"{rel}: {msg}")
print(f"{len(problems)} teaching gaps")
