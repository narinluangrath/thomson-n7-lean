"""Inline the per-slab `H*_le_phi` wrappers into the slab specifications.

Each slab had three wrappers `HX_le_phi` around `Cert.sound parHX certHX certHX_ok …` used once, in
`slab_<x>`. They go; `slab_<x>` calls `Cert.sound` directly (the `certHX_ok` kernel checks stay separate
declarations, so each keeps its own elaboration budget).
Usage: python3 scripts/gen_slab.py <in.lean> <out.lean>
"""
import re, sys

src = open(sys.argv[1]).read()
slabs = re.findall(r'^namespace (Slab_\w+)$', src, re.M)
for x in slabs:
    s = src.index(f'namespace {x}\n')
    e = src.index(f'end {x}\n', s)
    body = re.sub(r'\ntheorem H[ABC]_le_phi .*?(?=\n\n|\nend )', '', src[s:e], flags=re.S)
    src = src[:s] + body + src[e:]
    q = f'SlabOneD.{x}.'
    old = (f'    (fun _ => {q}HA_le_phi) (fun _ => {q}HB_le_phi)\n'
           f'    (fun _ => {q}HC_le_phi)')
    new = (f'    (fun _ _ h => SlabOneD.Cert.sound _ _ {q}certHA_ok (by norm_num [{q}parHA]; linarith)\n'
           f'      (by norm_num [{q}parHA]; linarith) (by linarith))\n'
           f'    (fun _ _ h => SlabOneD.Cert.sound _ _ {q}certHB_ok (by norm_num [{q}parHB]; linarith)\n'
           f'      (by norm_num [{q}parHB]) h)\n'
           f'    (fun _ _ h => SlabOneD.Cert.sound _ _ {q}certHC_ok (by norm_num [{q}parHC]; linarith)\n'
           f'      (by norm_num [{q}parHC]) h)')
    assert src.count(old) == 1, x
    src = src.replace(old, new)
src = src.replace('`SlabOneD.Slab_x.HA_le_phi` therefore gives', '`SlabOneD.Cert.sound` on the certificate `certHA` of the slab gives')
open(sys.argv[2], 'w').write(src)
print('slabs:', slabs, ' remaining H*_le_phi refs:', len(re.findall(r'H[ABC]_le_phi', src)))
