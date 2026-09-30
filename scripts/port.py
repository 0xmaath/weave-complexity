#!/usr/bin/env python3
"""Port the three Lax submissions into a single Complexity/ tree.

For each source repo:
  * concepts/<N>/**.lean  -> Complexity/<T>/**.lean      (definitions; axioms removed)
  * proofs/<NP>/**.lean   -> Complexity/<TP>/**.lean     (proofs; aliases added)
Every `axiom` of a concept package is replaced by an `alias` (placed right after the
annotated proof theorem) that re-exposes the proof under the concept's original name.
"""
import os, re, sys, json, subprocess, shutil, glob

SRC = os.environ.get('PORT_SRC', '/tmp/claude-0/-home-user-weave-complexity/1ebe0456-a2cf-5409-a1b1-6e3f73cdcb71/scratchpad/src')
DST = os.environ.get('PORT_DST', '/home/user/weave-complexity')

REPOS = [
    # (dir, concept ns, proof ns, target concept ns, target proof ns, github, authors)
    ('classical-complexity', 'Lax434930', 'Lax434930Proofs', 'Complexity.Classes', 'Complexity.ClassesProofs',
     'https://github.com/EdouardBonnet/classical-complexity', 'Édouard Bonnet, Codex 5.6 and 6', 'lax-434930'),
    ('cook-levin', 'Lax429075', 'Lax429075Proofs', 'Complexity.CookLevin', 'Complexity.CookLevinProofs',
     'https://github.com/EdouardBonnet/cook-levin', 'Édouard Bonnet, Codex 5.6 and 6', 'lax-429075'),
    ('arc-kayles', 'Lax689614', 'Lax689614Proofs', 'Complexity.ArcKayles', 'Complexity.ArcKaylesProofs',
     'https://github.com/EdouardBonnet/arc-kayles', 'Édouard Bonnet, gpt-6-astra', 'lax-689614'),
]
DROP_MODULES = {'Lax434930.PVersusNP'}   # open question stated as an axiom: not ported

RENAMES = []
for d, n, np_, t, tp, *_ in REPOS:
    RENAMES.append((np_, tp))
    RENAMES.append((n, t))
RENAMES.sort(key=lambda p: -len(p[0]))

def rename(text):
    for old, new in RENAMES:
        text = re.sub(r'(?<![\w.])' + re.escape(old) + r'(?![\w])', new, text)
    return text

def commit_of(repo):
    return subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=f'{SRC}/{repo}').decode().strip()

# ---------- collect files ----------
files = []   # dicts: src path, rel path, module (old), module(new), kind, repo
for d, n, np_, t, tp, gh, authors, laxid in REPOS:
    for kind, ns, tns in (('concepts', n, t), ('proofs', np_, tp)):
        base = f'{SRC}/{d}/{kind}'
        for p in sorted(glob.glob(f'{base}/**/*.lean', recursive=True)):
            if '/.lake/' in p:
                continue
            rel = os.path.relpath(p, base)               # Lax434930/Foo.lean or Lax434930.lean
            mod = rel[:-5].replace('/', '.')
            assert mod == ns or mod.startswith(ns + '.'), (mod, ns)
            newmod = tns + mod[len(ns):]
            files.append(dict(src=p, rel=rel, mod=mod, newmod=newmod, kind=kind, repo=d,
                              gh=gh, authors=authors, laxid=laxid, commit=commit_of(d)))
files = [f for f in files if f['mod'] not in DROP_MODULES]
bymod = {f['mod']: f for f in files}

def strip_comments(t):
    t = re.sub(r'/-.*?-/', ' ', t, flags=re.S)
    t = re.sub(r'--[^\n]*', ' ', t)
    return t

# ---------- concept axioms ----------
axioms = []   # dict(mod, ns, name, full, text, binders_type)
for f in files:
    if f['kind'] != 'concepts':
        continue
    t = open(f['src']).read()
    lines = t.split('\n')
    out = []
    i = 0
    cur = []
    while i < len(lines):
        line = lines[i]
        m = re.match(r'^namespace (\S+)', line)
        if m: cur.append(m.group(1))
        m = re.match(r'^end (\S+)', line)
        if m and cur and cur[-1] == m.group(1): cur.pop()
        m = re.match(r'^axiom (\S+)(.*)$', line)
        if m:
            name = m.group(1)
            body = [line[len('axiom '):]]
            j = i + 1
            while j < len(lines) and lines[j].strip() != '' and lines[j][0] in ' \t':
                body.append(lines[j]); j += 1
            # remove preceding docstring
            k = len(out) - 1
            while k >= 0 and out[k].strip() == '': k -= 1
            doc = None
            if k >= 0 and out[k].rstrip().endswith('-/'):
                k2 = k
                while k2 >= 0 and not out[k2].lstrip().startswith('/--'): k2 -= 1
                doc = '\n'.join(out[k2:k+1])
                del out[k2:]
            # drop trailing blank lines before the removed block
            while out and out[-1].strip() == '': out.pop()
            full = '.'.join(cur + [name])
            axioms.append(dict(mod=f['mod'], ns='.'.join(cur), name=name, full=full,
                               decl='\n'.join(body), doc=doc, file=f))
            i = j
            # also eat blank lines that followed
            while i < len(lines) and lines[i].strip() == '': i += 1
            out.append('')
            out.append(f'<<AXIOM {full}>>')
            out.append('')
            continue
        out.append(line)
        i += 1
    f['text'] = '\n'.join(out).rstrip('\n') + '\n'
    # sanity: blank line before 'end'
    f['text'] = re.sub(r'\n\n\n+', '\n\n', f['text'])

axiom_by_full = {a['full']: a for a in axioms}
print(f'{len(axioms)} concept axioms removed', file=sys.stderr)

# ---------- proof aliases ----------
alias_of = {}   # concept full name -> (proof module, proof full name)
for f in files:
    if f['kind'] != 'proofs':
        continue
    t = open(f['src']).read()
    lines = t.split('\n')
    cur = []
    insertions = []   # (line index to insert before, text)
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r'^namespace (\S+)', line)
        if m: cur.append(m.group(1))
        m = re.match(r'^end (\S+)', line)
        if m and cur and cur[-1] == m.group(1): cur.pop()
        m = re.match(r'^conclusion:\s*(\S+)\s*$', line)
        if m:
            concl = m.group(1)
            # find declaration after docstring end
            j = i
            while not lines[j].rstrip().endswith('-/'): j += 1
            j += 1
            dm = re.match(r'^(?:protected |noncomputable )*(theorem|lemma) (\S+)', lines[j])
            assert dm, (f['src'], lines[j])
            pname = dm.group(2)
            pfull = '.'.join(cur + [pname])
            # end of declaration: next non-blank column-0 line
            k = j + 1
            while k < len(lines) and (lines[k].strip() == '' or lines[k][0] in ' \t'):
                k += 1
            assert concl in axiom_by_full, concl
            assert concl not in alias_of, concl
            alias_of[concl] = (f['mod'], pfull)
            a = axiom_by_full[concl]
            doc = a['doc']
            docline = (doc + '\n') if doc else ''
            insertions.append((k, f"{docline}alias _root_.{rename(concl)} := {pname}\n\n"))
            i = j + 1
            continue
        i += 1
    # apply insertions from the end; make sure the `alias` command is available
    if insertions and 'import Batteries.Tactic.Alias' not in t:
        last = max(i for i, l in enumerate(lines) if l.startswith('import '))
        lines.insert(last + 1, 'import Batteries.Tactic.Alias')
        insertions = [(k + 1, text) for k, text in insertions]
    for k, text in sorted(insertions, key=lambda x: -x[0]):
        # ensure blank line separation
        block = ('' if (k > 0 and lines[k-1].strip() == '') else '\n') + text
        lines.insert(k, block.rstrip('\n') + '\n')
    f['text'] = '\n'.join(lines)

for f in files:
    if f['kind'] != 'concepts':
        continue
    def repl(m):
        full = m.group(1)
        pmod, pfull = alias_of[full]
        short = full.split('.')[-1]
        return (f"/- The archived concept stated `{short}` here as an `axiom`. In this port it is a\n"
                f"theorem: it is proved as `{pfull}` in `{pmod}`, which\n"
                f"re-exports it under the name `{full}` via `alias`. -/")
    f['text'] = re.sub(r'<<AXIOM (\S+)>>', repl, f['text'])

missing = [a['full'] for a in axioms if a['full'] not in alias_of]
assert not missing, missing
print(f'{len(alias_of)} aliases inserted', file=sys.stderr)

# ---------- imports for statement users ----------
def uses_statement(text_nc, full, ns, name, mod):
    # full name or any suffix ending with the namespace's last component(s)
    parts = full.split('.')
    for k in range(0, len(parts) - 1):
        q = '.'.join(parts[k:])
        if re.search(r'(?<![\w.])' + re.escape(q) + r'(?![\w])', text_nc):
            return True
    # bare name: only if the namespace is opened or we are inside it
    if re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w])', text_nc):
        if re.search(r'^open\b[^\n]*(?<![\w.])' + re.escape(ns) + r'(?![\w.])', text_nc, re.M):
            return True
        if re.search(r'^namespace ' + re.escape(ns) + r'(\.|\s|$)', text_nc, re.M):
            return True
    return False

added_imports = {}
for f in files:
    t = f['text']
    imports = set(re.findall(r'^import (\S+)', t, re.M))
    nc = strip_comments(t)
    need = set()
    for full, (pmod, pfull) in alias_of.items():
        if pmod == f['mod']:
            continue
        a = axiom_by_full[full]
        if uses_statement(nc, full, a['ns'], a['name'], f['mod']):
            need.add(pmod)
    need -= imports
    if need:
        added_imports[f['mod']] = sorted(need)
        # insert after the last import line
        lines = t.split('\n')
        last = max(i for i, l in enumerate(lines) if l.startswith('import '))
        for pm in sorted(need, reverse=True):
            lines.insert(last + 1, f'import {pm}')
        f['text'] = '\n'.join(lines)
for m, ims in added_imports.items():
    print(f'  {m} += {ims}', file=sys.stderr)

# drop imports of dropped modules
for f in files:
    for dm in DROP_MODULES:
        f['text'] = re.sub(r'^import ' + re.escape(dm) + r'\n', '', f['text'], flags=re.M)

# ---------- cycle check on the new import graph ----------
graph = {}
for f in files:
    graph[f['mod']] = [m for m in re.findall(r'^import (\S+)', f['text'], re.M) if m in bymod]
state = {}
def visit(m, stack):
    if state.get(m) == 2: return
    if state.get(m) == 1:
        raise SystemExit(f'import cycle: {" -> ".join(stack + [m])}')
    state[m] = 1
    for d in graph[m]: visit(d, stack + [m])
    state[m] = 2
for m in graph: visit(m, [])
print('import graph acyclic', file=sys.stderr)

# ---------- write files ----------
def header(f):
    return f"""/-
Ported from {f['gh']} (Lax submission {f['laxid']}, commit {f['commit'][:12]}),
file `{f['kind']}/{f['rel']}`.
Original authors: {f['authors']}. Licensed under the Apache License, Version 2.0;
see `LICENSES/{f['repo']}.LICENSE`. Modifications for this port: module and namespace
renamed from `{f['mod']}` to `{f['newmod']}`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
"""

# Remove only the ported package trees; other modules under Complexity/ are hand-written.
for _, _, _, t, tp, *_ in REPOS:
    for m in (t, tp):
        shutil.rmtree(f"{DST}/{m.replace('.', '/')}", ignore_errors=True)
        try:
            os.remove(f"{DST}/{m.replace('.', '/')}.lean")
        except FileNotFoundError:
            pass
for f in files:
    path = f"{DST}/{f['newmod'].replace('.', '/')}.lean"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as out:
        out.write(header(f) + rename(f['text']).rstrip('\n') + '\n')

os.makedirs(f'{DST}/LICENSES', exist_ok=True)
for d, *_ in REPOS:
    shutil.copy(f'{SRC}/{d}/LICENSE', f'{DST}/LICENSES/{d}.LICENSE')

# root module (ported packages plus the hand-written milestone modules)
roots = [tp for _, _, _, t, tp, *_ in REPOS] + [t for _, _, _, t, tp, *_ in REPOS]
with open(f'{DST}/Complexity.lean', 'w') as out:
    out.write('/-\nRoot module of the Complexity library. Imports every ported definition and proof.\n-/\n')
    for r in sorted(roots):
        out.write(f'import {r}\n')
    for r in ['Complexity.Savitch', 'Complexity.Games.Membership', 'Complexity.QBF.Completeness',
              'Complexity.Modular.QExpansion']:
        out.write(f'import {r}\n')

# ---------- statement-fidelity check file ----------
# For every removed axiom, restate its original signature (in the original concept-file
# context) as a Pi type and check that the alias has exactly that type.
def split_decl(decl):
    """'name binders : type' -> (binders, type), splitting at the first depth-0 colon."""
    depth = 0
    opens_, closes_ = '([{⦃⟨', ')]}⦄⟩'
    for i, ch in enumerate(decl):
        if ch in opens_: depth += 1
        elif ch in closes_: depth -= 1
        elif ch == ':' and depth == 0 and decl[i:i+2] != ':=':
            return decl[:i], decl[i+1:]
    raise SystemExit('cannot split ' + decl)

chk = ['/-', 'Generated by the port script: every removed concept axiom is restated verbatim',
       'here (binders and statement copied from the archived concept file) and checked against',
       'the theorem that now carries its name. If a ported proof ever proved a different',
       'statement than the archived concept, this file fails to build.', '-/', 'import Complexity', '']
for a in axioms:
    f = a['file']
    ctx = rename(f['text'])
    opens = re.findall(r'^open [^\n]*$', ctx, re.M)
    decl = rename(a['decl'])
    binders, ty = split_decl(decl[len(a['name']):])
    full = rename(a['full'])
    ns = rename(a['ns'])
    binders = ' '.join(binders.split())
    ty = ' '.join(ty.split())
    chk.append(f'namespace {ns}')
    chk += opens
    if binders:
        chk.append(f"example : ∀ {binders},\n    {ty} :=\n  @{full}")
    else:
        chk.append(f"example : {ty} :=\n  @{full}")
    chk.append(f'end {ns}')
    chk.append('')
with open(f'{DST}/Complexity/StatementCheck.lean', 'w') as out:
    out.write('\n'.join(chk))
    # Hand-maintained restatements of later milestones' theorems.
    extra_path = f'{DST}/scripts/StatementCheckExtra.lean'
    if os.path.exists(extra_path):
        out.write('\n' + open(extra_path).read())
os.makedirs(f'{DST}/scripts', exist_ok=True)
names = sorted(rename(a['full']) for a in axioms)
with open(f'{DST}/scripts/AxiomCheck.lean', 'w') as out:
    out.write('''/-
Generated by the port script. Run with `lake env lean scripts/AxiomCheck.lean`.
For every ported top-level statement (each former concept-package axiom, now a theorem)
this prints `#print axioms` and fails unless the axioms used are among
`propext`, `Classical.choice` and `Quot.sound`.
-/
import Complexity
import Complexity.StatementCheck

open Lean Elab Command in
elab "#check_standard_axioms " ids:ident* : command => do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Array Name) := #[]
  for id in ids do
    let n ← resolveGlobalConstNoOverload id
    let axs ← collectAxioms n
    let extra := axs.filter fun a => !allowed.contains a
    logInfo m!"{n} depends on axioms: {axs.toList}"
    if !extra.isEmpty then bad := bad.push (n, extra)
  if !bad.isEmpty then
    throwError "non-standard axioms found: {bad.toList}"
  logInfo m!"{ids.size} statements checked: only propext, Classical.choice, Quot.sound are used."

''')
    for n in names:
        out.write(f'#print axioms {n}\n')
    out.write('\n#check_standard_axioms\n')
    for n in names:
        out.write(f'  {n}\n')
json.dump(dict(axioms=[dict(full=rename(a['full']), mod=rename(a['mod'])) for a in axioms],
               aliases={rename(k): dict(proof_module=rename(v[0]), proof=rename(v[1])) for k, v in alias_of.items()}),
          open(f'{DST}/scripts/ported_statements.json', 'w'), indent=1, ensure_ascii=False)
print('done', file=sys.stderr)
