"""Long-lived Lean REPL positioned just before a given declaration of Solution.lean.

Usage: python3 scripts/repl_server.py '<regex matching the target chunk start>' <dir> [max-GB]
Replays every command before the target, then serves requests: write Lean text to
<dir>/req-<n>.lean and read the REPL's JSON reply from <dir>/resp-<n>.json. Each request runs in
the environment just before the target (requests do not see each other).
"""
import json, os, re, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import golf

target, d = sys.argv[1], sys.argv[2]
os.makedirs(d, exist_ok=True)
cs = golf.chunks(open(golf.SOL).read())
stop = next(i for i, c in enumerate(cs) if re.match(target, c))
cap = float(sys.argv[3]) * 2 ** 20 if len(sys.argv) > 3 else float('inf')  # kB


def replay():
    r = golf.Repl()
    env = None
    t = time.time()
    for c in cs[:stop]:
        resp = r.send({'cmd': c} if env is None else {'cmd': c, 'env': env})
        if golf.errors(resp):
            print('REPLAY ERROR', golf.errors(resp)[0]['data'][:300], flush=True)
            sys.exit(1)
        env = resp['env']
    print(f'READY: replayed {stop} commands in {time.time() - t:.0f}s, env {env}', flush=True)
    return r, env


def rss(r):
    # the REPL runs under `lake env`; sum the RSS of its process tree
    pids, tot = [r.p.pid], 0
    while pids:
        p = pids.pop()
        try:
            tot += int(next(l for l in open(f'/proc/{p}/status') if l.startswith('VmRSS')).split()[1])
            pids += [int(x) for x in open(f'/proc/{p}/task/{p}/children').read().split()]
        except (OSError, StopIteration):
            pass
    return tot


r, env = replay()
open(os.path.join(d, 'READY'), 'w').write(str(env))
while True:
    for f in sorted(os.listdir(d)):
        m = re.match(r'req-(\d+)\.lean$', f)
        if m and not os.path.exists(os.path.join(d, f'resp-{m.group(1)}.json')):
            t = time.time()
            resp = r.send({'cmd': open(os.path.join(d, f)).read(), 'env': env})
            resp['seconds'] = round(time.time() - t, 1)
            json.dump(resp, open(os.path.join(d, f'resp-{m.group(1)}.json'), 'w'), indent=1)
            if rss(r) > cap:  # each request's environment stays in memory; start afresh
                print(f'RESTART at {rss(r) // 2 ** 20} GB', flush=True)
                r.p.kill()
                r.p.wait()
                r, env = replay()
    time.sleep(0.3)
