"""Proof golf via the Lean REPL.

Replays Solution.lean command by command (recording the environment before each command),
then for every multi-line `theorem`/`lemma ... := by` proof tries one-line replacements,
shortest first, in the environment just before that declaration. A proof's body never
affects later declarations, so every candidate is tested independently.

Usage: python3 scripts/golf.py <shard> <nshards> <outfile.jsonl>
Needs the REPL built at ~/src/repl (leanprover-community/repl, toolchain v4.34.1).
"""
import json, os, re, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOL = os.path.join(ROOT, 'ThomsonN7/Solution.lean')
REPL = os.path.expanduser('~/src/repl/.lake/build/bin/repl')

# heartbeat cap for candidates: well under the default 200000 so a winner also builds without set_option
CAP = 'set_option maxHeartbeats 100000 in\n'
TACTICS = ['simp', 'ring', 'omega', 'grind', 'decide', 'norm_num', 'linarith', 'simp_all',
           'nlinarith', 'positivity', 'field_simp', 'norm_num [*]']

START = re.compile(r'^(/--|/-!|@\[|(private |protected |noncomputable |nonrec )*'
                   r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|example|opaque)\b|'
                   r'namespace\b|end\b|section\b|noncomputable section\b|open\b|variable\b|'
                   r'universe\b|attribute\b|set_option\b|#|mutual\b|include\b|omit\b)')


def chunks(text):
    """Split into top-level commands; a doc comment or attribute line stays with its declaration."""
    lines = text.split('\n')
    out, cur, pending_prefix = [], [], False
    in_block_comment = 0
    for l in lines:
        opens_prefix = l.startswith('/--') or l.startswith('@[') or bool(re.match(r'^open .* in$', l))
        if in_block_comment == 0 and START.match(l) and not pending_prefix and cur:
            out.append('\n'.join(cur))
            cur = []
        cur.append(l)
        in_block_comment += l.count('/-') - l.count('-/')
        in_block_comment = max(in_block_comment, 0)
        if opens_prefix:
            pending_prefix = True
        if pending_prefix and re.match(r'^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure)\b', l):
            pending_prefix = False
        if pending_prefix and l.startswith('@[') and not l.startswith('/--'):
            # `@[simp] lemma foo ...` on one line
            if re.search(r'\]\s*(private |noncomputable )*(theorem|lemma|def|instance)\b', l):
                pending_prefix = False
    if cur:
        out.append('\n'.join(cur))
    return out


class Repl:
    def __init__(self):
        self.p = subprocess.Popen(['lake', 'env', REPL], cwd=ROOT, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)

    def send(self, obj):
        self.p.stdin.write(json.dumps(obj) + '\n\n')
        self.p.stdin.flush()
        buf = []
        while True:
            line = self.p.stdout.readline()
            if line == '':
                raise RuntimeError('repl died')
            if line.strip() == '' and buf:
                break
            buf.append(line)
        return json.loads(''.join(buf))


def errors(resp):
    return [m for m in resp.get('messages', []) if m['severity'] == 'error'] or (
        [{'data': resp['message']}] if 'message' in resp and 'env' not in resp else [])


def split_proof(chunk):
    """(header, body) for `theorem/lemma ... := by\\n  body` with a multi-line tactic body."""
    m = re.match(r'(?s)^(.*?^(?:private |protected )*(?:theorem|lemma)\s.*?):= by\s*\n(.+)$', chunk, re.M)
    if not m or '\n' not in m.group(2).strip():
        return None
    return m.group(1), m.group(2)


def main():
    shard, nshards, outpath = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    text = open(SOL).read()
    cs = chunks(text)
    r = Repl()
    t = time.time()
    envs = []  # env id in effect *before* chunk i
    env = None
    for i, c in enumerate(cs):
        envs.append(env)
        req = {'cmd': c} if env is None else {'cmd': c, 'env': env}
        resp = r.send(req)
        if errors(resp):
            print(f'REPLAY ERROR at chunk {i}: {errors(resp)[0]["data"][:300]}\n{c[:300]}', flush=True)
            sys.exit(1)
        env = resp['env']
    print(f'replayed {len(cs)} commands in {time.time() - t:.0f}s', flush=True)

    targets = [(i, sp) for i, c in enumerate(cs) if (sp := split_proof(c))]
    targets.sort(key=lambda x: -len(x[1][1].split()))
    mine = targets[shard::nshards]
    print(f'{len(targets)} multi-line proofs; shard {shard} has {len(mine)}', flush=True)
    done = set()
    if os.path.exists(outpath):
        done = {json.loads(l)['chunk'] for l in open(outpath)}
    with open(outpath, 'a') as out:
        for i, (header, body) in mine:
            if i in done:
                continue
            old_words = len(body.split())
            won = None
            for tac in sorted(TACTICS, key=len):
                if len(tac.split()) + 1 >= old_words:
                    continue
                cand = f'{header}:= by {tac}'
                resp = r.send({'cmd': CAP + cand, 'env': envs[i]})
                if not errors(resp):
                    won = tac
                    break
            rec = {'chunk': i, 'name': re.search(r'(?:theorem|lemma)\s+(\S+)', header).group(1),
                   'old_words': old_words, 'tactic': won}
            out.write(json.dumps(rec) + '\n')
            out.flush()
            if won:
                print(f'WIN {rec["name"]}: {old_words} words -> by {won}', flush=True)


if __name__ == '__main__':
    main()
