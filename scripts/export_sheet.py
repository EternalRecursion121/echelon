#!/usr/bin/env python3
"""Export every level tagged `-- @sheet N Qk` as a tutorial answer pack.

Usage: python3 scripts/export_sheet.py N [--out exports/] [--progress my-progress.json]
                                           [--hand-in] [--pdf] [--name "Your Name"]

With --progress (the JSON from the game's "Download progress" button, which works on the
public server), each question shows YOUR proof from the game instead of the sample proof,
marks unsolved questions, and notes how many hidden hints you opened.

--hand-in (needs --progress) produces what you submit: each question, your explanation
(any `-- Explain:` comment block in your proof), your Lean proof and the hint count —
and no model answers. --pdf also renders the Markdown to PDF (pandoc + lualatex).

For each tagged level it emits, informal-first: the question (level Introduction), the
tutorial answer (a `/-! @answer ... -/` block in the level file, falling back to the
Conclusion), then the Lean certificate — the statement and sample proof with game-only
lines (Hint/Branch) stripped. Levels are ordered by question number.
"""
import json, re, subprocess, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
TAG = re.compile(r"^--\s*@sheet\s+(\d+)\s+Q(\S+)", re.M)


def string_block(src, keyword):
    m = re.search(keyword + r'\s+"((?:[^"\\]|\\.)*)"', src, re.S)
    return m.group(1).replace('\\\\', '\\').strip() if m else ""


def proof_block(src):
    m = re.search(r"(/--.*?-/\s*)?(Statement.*?:= by\n)(.*?)(?=\n(?:end |Conclusion|/--|\S))", src, re.S)
    if not m:
        return "", ""
    doc = (m.group(1) or "").strip().removeprefix("/--").removesuffix("-/").strip()
    lines, skip, in_str = [], None, False
    for line in (m.group(2) + m.group(3)).splitlines():
        quotes = len(re.findall(r'(?<!\\)"', line))
        if in_str:                        # continuation of a multi-line Hint string
            in_str = quotes % 2 == 0
            continue
        indent = len(line) - len(line.lstrip())
        if skip is not None and indent > skip:
            continue                      # body of a Branch
        skip = None
        if re.match(r"\s*(Hint|Branch)\b", line):
            skip = indent
            in_str = quotes % 2 == 1
            continue
        lines.append(line)
    return doc, "\n".join(lines).rstrip()


def answer_block(src):
    m = re.search(r"/-!\s*@answer\s*(.*?)-/", src, re.S)
    return m.group(1).strip() if m else ""


def world_level(src):
    w = re.search(r'^World\s+"([^"]+)"', src, re.M)
    l = re.search(r"^Level\s+(\d+)", src, re.M)
    return (w.group(1), l.group(1)) if w and l else (None, None)


def player_proof(progress, world, level):
    """(code, completed, hints_opened) from a downloaded GameProgress JSON, or None."""
    lv = progress.get("data", {}).get(world, {}).get(level)
    if not lv:
        return None
    return lv.get("code", "").strip(), lv.get("completed", False), len(lv.get("help", []))


def qkey(q):
    m = re.match(r"(\d+)(.*)", q)
    return (int(m.group(1)), m.group(2)) if m else (999, q)


def main():
    sheet = int(sys.argv[1])
    out = ROOT / (sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else "exports")
    progress = None
    if "--progress" in sys.argv:
        progress = json.loads(pathlib.Path(sys.argv[sys.argv.index("--progress") + 1]).read_text())
    entries = []
    for f in sorted((ROOT / "Game" / "Levels").rglob("*.lean")):
        src = f.read_text()
        for m in TAG.finditer(src):
            if int(m.group(1)) == sheet:
                doc, proof = proof_block(src)
                note = ""
                if progress is not None:
                    mine = player_proof(progress, *world_level(src))
                    if mine and mine[0]:
                        code, done, hints = mine
                        header = proof.split(":= by")[0] + ":= by"
                        proof = header + "\n" + "\n".join("  " + l for l in code.splitlines())
                        note = ("✓ solved in the game" if done else "✗ not yet solved in the game") + \
                               (f" · {hints} hidden hint(s) opened" if hints else " · no hidden hints")
                    else:
                        proof, note = "-- not attempted yet", "✗ not attempted in the game"
                entries.append((m.group(2), f.relative_to(ROOT), string_block(src, "Introduction"),
                                doc, proof, answer_block(src) or string_block(src, "Conclusion"), note))
    entries.sort(key=lambda e: qkey(e[0]))
    hand_in = "--hand-in" in sys.argv
    if hand_in and progress is None:
        sys.exit("--hand-in needs --progress <file> (download it from the game's menu)")
    name = sys.argv[sys.argv.index("--name") + 1] if "--name" in sys.argv else ""
    out.mkdir(exist_ok=True)
    stem = f"sheet{sheet}" + ("-hand-in" if hand_in else "")
    if hand_in:
        md = [f"# Linear Algebra MT2026 — Problem Sheet {sheet}" + (f" — {name}" if name else ""), "",
              "Proofs written and checked in Lean 4 (Mathlib) in the *Echelon* game.", ""]
        for q, path, intro, doc, proof, concl, note in entries:
            md += [f"## Question {q}", "", intro, "", f"*{note}*", ""]
            expl = explanation(proof)
            if expl:
                md += ["**Explanation.** " + expl, ""]
            md += [f"*Claim.* {doc}" if doc else "", "", "```lean", proof, "```", ""]
    else:
        md = [f"# Problem Sheet {sheet} — worked answers (Lean-checked)\n"]
        for q, path, intro, doc, proof, concl, note in entries:
            md += [f"## Question {q}\n", intro, "",
                   ("### Model answer (check yours against it)\n" if progress is not None else "### Answer\n"),
                   concl, "",
                   "### Lean certificate" + (" (my proof)" if progress is not None else "") + "\n",
                   f"*{note}*" if note else "", f"*Claim.* {doc}" if doc else "",
                   "", "```lean", proof, "```", "", f"<sub>source: `{path}`</sub>", ""]
    target = out / f"{stem}.md"
    target.write_text("\n".join(md))
    print(f"wrote {target} ({len(entries)} questions)")
    if "--pdf" in sys.argv:
        pdf = out / f"{stem}.pdf"
        subprocess.run(["pandoc", str(target), "-o", str(pdf), "--pdf-engine=lualatex",
                        "-V", "geometry:margin=2.2cm", "-V", "mainfont=STIX Two Text",
                        "-V", "mathfont=STIX Two Math", "-H", str(ROOT / "scripts" / "pdf-header.tex")],
                       check=True)
        print(f"wrote {pdf}")


def explanation(proof):
    """The player's `-- Explain:` comment block, joined into one paragraph."""
    lines, on = [], False
    for line in proof.splitlines():
        t = line.strip()
        if t.startswith("-- Explain:"):
            on, t = True, t[len("-- Explain:"):]
        elif on and t.startswith("--"):
            t = t[2:]
        elif on:
            break
        else:
            continue
        lines.append(t.strip())
    return " ".join(l for l in lines if l)


if __name__ == "__main__":
    main()
