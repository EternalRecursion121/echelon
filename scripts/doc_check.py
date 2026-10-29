"""For each level, each NewTheorem/NewDefinition item must have a doc in a module the level
imports (transitively). Docs now live in Game/Doc/Theorems.lean (imported by Game.Metadata)."""
import re, pathlib, collections
ROOT = pathlib.Path(__file__).resolve().parent.parent
def mod_path(m): return ROOT / (m.replace('.', '/') + '.lean')
docs = collections.defaultdict(list)   # module -> names
allfiles = list((ROOT/'Game').rglob('*.lean')) + [ROOT/'Game.lean']
for f in allfiles:
    for kind, name in re.findall(r'^(TheoremDoc|DefinitionDoc)\s+(\S+)', f.read_text(), re.M):
        docs[f].append((kind, name))
    # a named Statement documents itself (its docstring becomes the inventory doc)
    for name in re.findall(r'^Statement\s+([^\s({:]+)', f.read_text(), re.M):
        docs[f].append(('TheoremDoc', 'LinearAlgebraGame.' + name))
dupes = collections.Counter((k, n) for g, v in docs.items() if 'Levels' not in str(g) for k, n in v)
print('duplicate docs:', [k for k, c in dupes.items() if c > 1])
cache = {}
def closure(f):
    if f in cache: return cache[f]
    out = {f}
    for m in re.findall(r'^import (Game\S*)', f.read_text(), re.M):
        p = mod_path(m)
        if p.exists(): out |= closure(p)
    cache[f] = out
    return out
bad = 0
for f in sorted((ROOT/'Game/Levels').rglob('L*.lean')):
    src = f.read_text()
    avail = {(k, n) for g in closure(f) for k, n in docs.get(g, [])}
    for kind, line in re.findall(r'^(NewTheorem|NewDefinition) (.*)$', src, re.M):
        dk = 'TheoremDoc' if kind == 'NewTheorem' else 'DefinitionDoc'
        for it in line.split():
            if (dk, it) not in avail:
                bad += 1; print(f.relative_to(ROOT), kind, it)
print(bad, 'items without a doc in the import closure')
