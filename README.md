# This fork: trying to make the proof smaller

> **Disclaimer:** I (Narin) don't really know what I'm doing here. I barely understand Lean. The work on this branch
> was done by Claude (Anthropic's model) and a team of Claude subagents, with me steering. Everything below has been
> machine-checked by Lean, but please don't take my word on any of the mathematics.

## What we're trying to do

The original proof in this repository is enormous: 17,895 lines and about 389,000 words, most of it machine-generated
certificate data and machine-written proofs. The experiment on the `compress` branch is simple: **make the proof as
short as possible while it still fully verifies**, and see what happens to it.

The hope is that a shorter proof is a more comprehensible one. We don't know if that will work. There are roughly
three ways this could go:

- **Minified JavaScript.** The proof gets shorter by becoming denser and more opaque: fewer words, but no easier to
  read, and maybe harder.
- **The essence.** Stripping away scaffolding exposes the irreducible core of the argument, a proof that actually
  illuminates why the pentagonal bipyramid is optimal.
- **Somewhere in between,** which is the most likely outcome.

The measure is **word count** (whitespace-separated tokens), not characters or lines, and we don't game it: no
joining lines, no squeezing whitespace, no packing numbers into hex. A shorter proof only counts if it passes the full
build and the checks described in `COMPRESSION.md`.

## Where we are (2026-10-02, updated as work continues)

| | Original | Now | Change |
|---|---:|---:|---:|
| Words | 389,377 | 53,722 | -86.2% |
| Data words (certificate numbers) | 227,658 | 17,178 | -92.5% |
| Proof words | 154,705 | 36,011 | -76.7% |
| Lines | 17,895 | 5,388 | -69.9% |

The same two theorems (`thomson_seven` and `thomson_seven_unique`) still verify, with only Lean's standard axioms, and
the statement still matches the fixed challenge file exactly.

**What got us here, roughly:**

- **Deleting dead code:** about 330 declarations the theorems never used.
- **Turning long proofs into data plus one kernel check, and back.** Unrolled certificate proofs became data plus a
  single computed check. Some stored data became computation (a Hessian built from a formula instead of being stored).
- **Re-solving one of the certificates** (an SDP) with smaller blocks once it turned out some blocks were dead weight.
- **Rounds of AI "golf"** on the largest proofs.
- **Rewriting whole sections from scratch,** keeping only what the rest of the proof needs. Twenty-three sections were cut,
  most by 40 to 73%. This is now the most productive approach.

The full account, with every phase, what didn't work and the caveats, is in [`COMPRESSION.md`](COMPRESSION.md).

**So far, the honest answer to "is it more comprehensible?" is: mixed.**

- **Clearer:** the section rewrites often replaced hand-built machinery with standard Mathlib facts (Gram-matrix
  positivity, reflections) and removed layers of intermediate lemmas. That reads closer to the actual mathematics.
- **Less readable:** most doc comments are gone, and some proofs are now single dense blocks close to Lean's time
  limits. That is the minified-JavaScript direction.
- **Unchanged:** about 17,000 words are still raw certificate numbers that no human reads, most of them one SDP
  certificate that is already at its minimum size for this formulation.

## Is shorter more comprehensible? Two framings

**Wolfram's "alien proofs".** In [*What's the future for pure math research in the age of AI?*](https://writings.stephenwolfram.com/2026/09/whats-the-future-for-pure-math-research-in-the-age-of-ai/)
(September 2026), Stephen Wolfram points to his own machine proof of the simplest axiom for Boolean algebra. It is
very long and "alien", and in 26 years nobody has found a human-level version. His explanation is computational
irreducibility: some facts have no shortcut, so the only proof is the computation itself. That predicts this project
lands in between: the structure of the argument can become clearer, but the certificate computations won't, however
small we make them. It also matches what we see. The rewrites that both shortened a section and made it read better
did it by using concepts Mathlib already has (Gram-matrix positivity, reflections), which is close to his point that
mathematics only becomes useful once it is "knitted into" shared mathematical culture. The rewrites that only folded
lemmas into one big proof went the minified direction.

**The skeleton test.** To check this directly, we stripped the compressed proof to its statements: no proofs, no
data. That leaves 430 declarations and about 12,000 words. A spine of about 1,700 words still tells the paper's
argument in the paper's order, and most of it reads like the paper. But about 20 intermediate steps the paper cites
by name have been inlined away, because the word count charges for every named lemma. Full results are in
[`SKELETON.md`](SKELETON.md), and the skeleton itself is in [`SKELETON.lean.txt`](SKELETON.lean.txt).

**Our current answer: in between.** The top-level structure is close to an essence. The certificates are irreducibly
alien. And optimising for words has started to delete the named steps a reader needs, so going further may need a
different metric, not more compression.

**Next:** more section rewrites (only small regions, about 2k proof words, are left un-rewritten), and eventually deciding
whether the remaining structure is the "essence" or just a smaller pile.

---

*Everything below this line is the original README of the upstream snapshot. Its hashes, line numbers and verification
records describe the original `Solution.lean`, not the compressed one on this branch.*

---

# Thomson problem, N = 7: Lean proof package

Snapshot of 2026-09-27. Among seven distinct points on the unit sphere, the regular pentagonal bipyramid uniquely
minimises the Coulomb energy. This repository contains the Lean 4 proof, the paper that explains it, the scripts that
check it and the records of those checks.

## Start here

- **paper/thomson-n7-paper.pdf**: readable copy of the informal proof and its map to the Lean file.
- **paper/PAPER.md**: the paper source.
- **formal/lean/ThomsonN7/Solution.lean**: the Lean proof. The two final theorems are at the end of the file (lines 17884–17893).
- **formal/lean/ComparatorChallenges/ThomsonN7.lean**: the fixed statement, with the theorems left as `sorry`.
- **info/CLAIM.md**: the theorems in full and the shape of the proof.
- **info/THEOREM_MAP.md**: where the paper's arguments appear in Lean.
- **REPRODUCE.md**: build and verification instructions.

## What is established in this snapshot

`formal/lean/ThomsonN7/Solution.lean` proves `ThomsonN7.thomson_seven` and `ThomsonN7.thomson_seven_unique`. Together
they say that for every configuration `x` of seven distinct points on the unit sphere of ℝ³,

    E(x) = Σ_{i<j} ‖x_i − x_j‖⁻¹  ≥  E(P) = 14.4529774142…,

where P is the regular pentagonal bipyramid, and that equality holds only when `x` is P moved by a linear isometry and
relabelled.

The proof splits on the smallest inner product between two of the points. Configurations with no nearly antipodal
pair (smallest inner product at least −9/10) are handled by one three-point semidefinite bound. The rest are covered by
five slabs and a cap, each with its own typed three-point certificate; on the cap, which contains P, a rigidity argument
and an exact second-order local minimality theorem finish the proof. Every certificate is exact integer or rational data
checked in the Lean kernel.

The file is 17,895 lines and imports only Mathlib. From a clean copy of this repository, the complete build passed
(8,928 jobs); the theorems depend exactly on Lean's standard `propext`, `Classical.choice` and `Quot.sound`; the Lean
Comparator accepted the solution against the fixed statement ("Your solution is okay!"); and a second kernel
implementation, nanoda, checked the 47,854 declarations of the exported proof with no errors and rejected an export
with one certificate integer changed. See `verification/`.

The proof was produced by ten Claude Sonnet 5.5 agents over about 15 hours in September 2026. Its method follows the
N = 8 work of Kryvonos, Liehr and Taylor (arXiv:2609.22077) and the Lean development of Tooby-Smith and Zughaid
(https://github.com/jstoobysmith/Thomson-N-8-Warrant).

## Source integrity and portability

- `formal/lean/` is a self-contained Lake package. Its only dependency is Mathlib at commit
  `d13f23b723b8a846827a245b89c10fc7d3f11612`, on Lean `v4.34.1`.
- `ThomsonN7/Solution.lean` has sha256 `6545e982abaeb4cae0a906c74ca51cc502621aa2a05783bb8da35d96493cc9ce` and
  `ComparatorChallenges/ThomsonN7.lean` has sha256 `2cf12e8ca6bd6ebfb31ae7343ca87ed75a3ba37cbe3d6eb5abbfae483dafbaae`.
  Lines 1–310 of the two files are byte-identical; `formal/check.sh` checks both hashes and that identity.
- Both files declare the same names inside `namespace ThomsonN7`, so they are separate Lake libraries and are never
  imported into one file.
- `formal/lean/claims.tsv` indexes every Lean line the paper cites; the check fails if a cited line no longer declares
  its name.
- `formal/lean/SHA256SUMS.txt` covers the Lake package. `PACKAGE_SHA256SUMS.txt` covers the whole repository.
- The PDF is a typeset copy of `paper/PAPER.md`.
