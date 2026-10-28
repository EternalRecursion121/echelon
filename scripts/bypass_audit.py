#!/usr/bin/env python3
"""Flag levels that a single automation tactic solves outright.

For each level, writes a scratch file that imports the level's own imports and states the
level's goal once per tactic as an `example ... := by <tac>`; compiles it, and reports which
tactics succeed and whether the level disables them. A success that is not disabled is a
potential bypass (judge by hand: sometimes a one-liner is fine, e.g. a final arithmetic check).

Usage: python3 scripts/bypass_audit.py [WorldId ...] [--jobs 6]
"""
import concurrent.futures as cf, os, re, subprocess, sys, pathlib, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
TACTICS = ["simp", "norm_num", "linarith", "nlinarith", "positivity", "decide", "omega",
           "ring", "module", "field_simp", "eval_det", "simp_all"]
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])


def statement(src):
    m = re.search(r"^Statement\s+(.*?):=\s*by\s*$", src, re.S | re.M)
    if not m:
        return None
    head = m.group(1)
    head = re.sub(r"^\(preamble\s*:=.*?\)\s*", "", head, flags=re.S)
    first = head.split(None, 1)
    if first and not first[0][0] in "({[:⦃" and len(first) > 1:
        head = first[1]                                    # drop the statement's name
    return head.strip()


def audit(path):
    src = path.read_text()
    head = statement(src)
    if head is None:
        return path, None, []
    imports = re.findall(r"^import .*$", src, re.M)
    opens = re.findall(r"^open [^\n]*?(?: in)?$", src, re.M)
    disabled = set()
    for line in re.findall(r"^DisabledTactic (.*)$", src, re.M):
        disabled |= set(line.split())
    body = "\n".join(imports) + "\nopen LinearAlgebraGame\n" + \
        "\n".join(o for o in opens if not o.endswith(" in")) + "\n\n"
    for t in TACTICS:
        body += f"-- TACTIC {t}\nexample {head} := by\n  {t}\n\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir="/tmp") as fh:
        fh.write(body)
        name = fh.name
    out = subprocess.run(["lake", "env", "lean", name], cwd=ROOT, env=ENV,
                         capture_output=True, text=True).stdout
    os.unlink(name)
    # lines of the file with errors -> which examples failed
    err_lines = {int(m.group(1)) for m in re.finditer(r":(\d+):\d+: error", out)}
    lines = body.splitlines()
    markers = [i for i, l in enumerate(lines, 1) if l.startswith("-- TACTIC ")] + [len(lines) + 1]
    succeeded = []
    for start, end in zip(markers, markers[1:]):
        t = lines[start - 1].split()[-1]
        # each example spans from its marker to the next marker (statements can be long)
        if not any(start < e < end for e in err_lines):
            succeeded.append(t)
    return path, disabled, succeeded


def world_order():
    """Ancestors of each world from the `Dependency` lines in Game.lean."""
    parents = {}
    for line in re.findall(r"^Dependency (.*)$", (ROOT / "Game.lean").read_text(), re.M):
        chain = [w.strip() for w in line.split("→")]
        for a, b in zip(chain, chain[1:]):
            parents.setdefault(b, set()).add(a)
    def anc(w, seen=None):
        seen = set() if seen is None else seen
        for p in parents.get(w, ()):
            if p not in seen:
                seen.add(p); anc(p, seen)
        return seen
    return anc


def unlocked_tactics(world, level_file, anc):
    """Tactics introduced in ancestor worlds, plus in this world up to and including this level."""
    tac = set()
    levels = ROOT / "Game" / "Levels"
    for w in anc(world):
        for f in (levels / w).glob("L*.lean"):
            for line in re.findall(r"^New(?:Hidden)?Tactic (.*)$", f.read_text(), re.M):
                tac |= {t.strip("«»") for t in line.split()}
    for f in sorted((levels / world).glob("L*.lean")):
        if f.name > level_file.name:
            break
        for line in re.findall(r"^New(?:Hidden)?Tactic (.*)$", f.read_text(), re.M):
            tac |= {t.strip("«»") for t in line.split()}
    return tac


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 6
    if "--jobs" in sys.argv:
        args = [a for a in args if a != str(jobs)]
    worlds = args or [p.name for p in (ROOT / "Game" / "Levels").iterdir() if p.is_dir()]
    files = [f for w in worlds for f in sorted((ROOT / "Game" / "Levels" / w).glob("L*.lean"))]
    flagged = 0
    anc = world_order()
    with cf.ThreadPoolExecutor(jobs) as ex:
        for path, disabled, ok in ex.map(audit, files):
            rel = path.relative_to(ROOT)
            if disabled is None:
                print(f"?  {rel}: no Statement found"); continue
            avail = unlocked_tactics(path.parent.name, path, anc)
            live = [t for t in ok if t not in disabled and t in avail]
            if live:
                flagged += 1
                print(f"⚠  {rel}: solved by {', '.join(live)}" +
                      (f" (disabled: {', '.join(t for t in ok if t in disabled)})" if len(live) < len(ok) else ""))
    print(f"{len(files)} levels audited, {flagged} flagged.")


if __name__ == "__main__":
    main()
