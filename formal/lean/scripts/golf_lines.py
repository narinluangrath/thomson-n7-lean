"""Greedy tactic-line deletion via the Lean REPL.

For each multi-line `theorem`/`lemma ... := by` proof (largest first), try deleting each tactic
line in turn, keeping a deletion when the declaration still elaborates without errors in the
environment just before it. Proof bodies never affect later declarations, so declarations are
independent. Writes one JSON line per declaration with the shortened proof (if any).

Usage: python3 scripts/golf_lines.py <shard> <nshards> <outfile.jsonl>
"""
import json, os, re, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import golf


def ok(r, env, text):
    return not golf.errors(r.send({'cmd': text, 'env': env}))


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
            lines = body.rstrip('\n').split('\n')
            k = 0
            while k < len(lines):
                trial = lines[:k] + lines[k + 1:]
                if trial and ok(r, envs[i], header + ':= by\n' + '\n'.join(trial)):
                    lines = trial
                else:
                    k += 1
            new = '\n'.join(lines)
            saved = len(body.split()) - len(new.split())
            out.write(json.dumps({'chunk': i, 'header': header, 'old': body, 'new': new, 'saved': saved}) + '\n')
            out.flush()
            if saved:
                name = re.search(r'(?:theorem|lemma)\s+(\S+)', header).group(1)
                print(f'SAVED {saved} words in {name}', flush=True)


if __name__ == '__main__':
    main()
