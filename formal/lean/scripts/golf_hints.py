"""Hinted one-liners via the Lean REPL.

For each multi-line `theorem`/`lemma ... := by` proof, build candidate one-line proofs from the
lemmas and hint terms the proof already mentions (rewrite/simp lists, `[...]` hint lists of
linarith-family calls, `have ... := term` right-hand sides) and keep the shortest that elaborates
and is shorter than the original body.

Usage: python3 scripts/golf_hints.py <shard> <nshards> <outfile.jsonl>
"""
import json, os, re, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import golf

KEYWORDS = {'at', 'with', 'using', 'only', 'fun', 'by', 'this', 'at', 'in', 'if', 'then', 'else'}


def bracket_items(s):
    """Top-level comma-separated items of every `[...]` in s."""
    items = []
    for m in re.finditer(r'\[', s):
        depth, j = 0, m.start()
        while j < len(s):
            if s[j] in '([{':
                depth += 1
            elif s[j] in ')]}':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        inner = s[m.start() + 1:j]
        depth, cur = 0, ''
        for ch in inner:
            if ch in '([{':
                depth += 1
            elif ch in ')]}':
                depth -= 1
            if ch == ',' and depth == 0:
                items.append(cur.strip()); cur = ''
            else:
                cur += ch
        if cur.strip():
            items.append(cur.strip())
    return [x for x in items if x and not x.startswith('←') and '\n' not in x]


def candidates(body):
    items = bracket_items(body)
    locals_ = set(re.findall(r'\b(?:have|obtain|intro|rintro|set)\s+⟨?([\w\']+)', body))
    lemmas = [x for x in dict.fromkeys(items) if re.fullmatch(r"[A-Za-z_][\w.'!?]*", x) and x not in locals_]
    terms = [x for x in dict.fromkeys(items) if not re.fullmatch(r"[\w.'!?]*", x)]
    terms += [t.strip() for t in re.findall(r'\bhave\s+\w*\s*:=\s*([^\n]+)', body) if 'by' not in t]
    terms = [t for t in dict.fromkeys(terms) if not any(l in t.split() for l in locals_)]
    L = ', '.join(lemmas)
    T = ', '.join(terms)
    out = ['positivity', 'bound', 'field_simp; ring']
    if L:
        out += [f'simp [{L}]', f'grind [{L}]', f'norm_num [{L}]', f'simp_all [{L}]',
                f'(simp [{L}]; ring)', f'(simp only [{L}]; ring)']
    if T:
        out += [f'nlinarith [{T}]', f'linarith [{T}]', f'positivity']
    if L and T:
        out += [f'(simp [{L}]; nlinarith [{T}])']
    return list(dict.fromkeys(out))


def main():
    shard, nshards, outpath = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    cs = golf.chunks(open(golf.SOL).read())
    r = golf.Repl()
    envs, env = [], None
    t = time.time()
    for i, c in enumerate(cs):
        envs.append(env)
        resp = r.send({'cmd': c} if env is None else {'cmd': c, 'env': env})
        if golf.errors(resp):
            print(f'REPLAY ERROR at chunk {i}', flush=True)
            sys.exit(1)
        env = resp['env']
    print(f'replayed {len(cs)} commands in {time.time() - t:.0f}s', flush=True)
    targets = [(i, sp) for i, c in enumerate(cs) if (sp := golf.split_proof(c))]
    targets.sort(key=lambda x: -len(x[1][1].split()))
    done = set()
    if os.path.exists(outpath):
        done = {json.loads(l)['chunk'] for l in open(outpath)}
    with open(outpath, 'a') as out:
        for i, (header, body) in targets[shard::nshards]:
            if i in done:
                continue
            old = len(body.split())
            won = None
            for tac in sorted(candidates(body), key=lambda x: len(x.split())):
                if len(tac.split()) + 1 >= old:
                    continue
                resp = r.send({'cmd': golf.CAP + f'{header}:= by {tac}', 'env': envs[i]})
                if not golf.errors(resp):
                    won = tac
                    break
            out.write(json.dumps({'chunk': i, 'header': header, 'old': body, 'tactic': won,
                                  'saved': (old - len(won.split()) - 1) if won else 0}) + '\n')
            out.flush()
            if won:
                name = re.search(r'(?:theorem|lemma)\s+(\S+)', header).group(1)
                print(f'WIN {name}: {old} words -> by {won[:120]}', flush=True)


if __name__ == '__main__':
    main()
