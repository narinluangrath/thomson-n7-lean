"""REPL server holding the environment before every command of Solution.lean.

Usage: python3 scripts/verify_server.py <dir>
Clients (scripts/verify.py) write <dir>/req-<id>.json = {"name": <decl name>, "text": <replacement>}
and read <dir>/resp-<id>.json = {"ok": bool, "errors": [...], "seconds": float}. The replacement is
elaborated in the environment just before the named declaration, with the default heartbeat limit.
"""
import json, os, re, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import golf

d = sys.argv[1]
os.makedirs(d, exist_ok=True)
cs = golf.chunks(open(golf.SOL).read())
r = golf.Repl()
envs, env, where = [], None, {}
t = time.time()
for i, c in enumerate(cs):
    envs.append(env)
    m = re.search(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev)\s+(\S+)', c, re.M)
    if m:
        where.setdefault(m.group(1), i)
    resp = r.send({'cmd': c} if env is None else {'cmd': c, 'env': env})
    if golf.errors(resp):
        print('REPLAY ERROR', i, flush=True)
        sys.exit(1)
    env = resp['env']
json.dump({n: i for n, i in where.items()}, open(os.path.join(d, 'names.json'), 'w'))
print(f'READY: {len(cs)} commands in {time.time() - t:.0f}s', flush=True)
open(os.path.join(d, 'READY'), 'w').write('1')
while True:
    for f in sorted(os.listdir(d)):
        m = re.match(r'req-([\w-]+)\.json$', f)
        if not m or os.path.exists(os.path.join(d, f'resp-{m.group(1)}.json')):
            continue
        try:
            q = json.load(open(os.path.join(d, f)))
        except json.JSONDecodeError:
            continue  # still being written
        t = time.time()
        if q['name'] not in where:
            out = {'ok': False, 'errors': [f'unknown declaration {q["name"]}']}
        else:
            resp = r.send({'cmd': q['text'], 'env': envs[where[q['name']]]})
            errs = [f"L{m['pos']['line']}: {m['data'][:1500]}" for m in golf.errors(resp) if 'pos' in m] or \
                   [e['data'][:1500] for e in golf.errors(resp)]
            sorry = [m for m in resp.get('messages', []) if 'sorry' in m['data']]
            out = {'ok': not errs and not sorry, 'errors': errs + [s['data'] for s in sorry]}
        out['seconds'] = round(time.time() - t, 1)
        tmp = os.path.join(d, f'.resp-{m.group(1)}.json')
        json.dump(out, open(tmp, 'w'), indent=1)
        os.rename(tmp, os.path.join(d, f'resp-{m.group(1)}.json'))
    time.sleep(0.2)
