"""Check a replacement declaration against the running verify_server.

Usage: python3 scripts/verify.py <decl-name> <file-with-replacement.lean>
Prints OK or the Lean errors. The replacement must be the whole declaration (doc comment optional),
keep the exact statement, and is checked in the environment just before the original declaration.
"""
import json, os, re, sys, time, uuid

D = os.environ.get('VERIFY_DIR', '/tmp/claude-1000/-home-narin/9df4a59e-5e80-4ae0-8dfb-3d40370f24f2/scratchpad/verify')
name, path = sys.argv[1], sys.argv[2]
text = open(path).read()
if not re.search(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:theorem|lemma|def)\s+'
                 + re.escape(name) + r"(?![\w'])", text, re.M):
    sys.exit(f'FAILED: {path} does not contain a declaration named {name} (an empty file would pass the server)')
rid = uuid.uuid4().hex[:12]
tmp = os.path.join(D, f'.req-{rid}.json')
json.dump({'name': name, 'text': text}, open(tmp, 'w'))
os.rename(tmp, os.path.join(D, f'req-{rid}.json'))
resp = os.path.join(D, f'resp-{rid}.json')
while not os.path.exists(resp):
    time.sleep(0.3)
r = json.load(open(resp))
print('OK' if r['ok'] else 'FAILED', f"({r['seconds']} s)")
for e in r['errors']:
    print(e)
