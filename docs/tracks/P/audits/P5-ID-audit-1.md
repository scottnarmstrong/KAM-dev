# Independent package audit 1: P5-ID

Overall verdict: **PASS WITH NOTES**. The P5-ID helper package passes statement,
proof, axiom and kernel checks. The only expected hygiene exception is the stale
generated root (lint receipt below). No frozen anchor is proved or sealed by this
package; this verdict does not establish P-G or discharge the remaining extension
and jet constructions.

Audited HEAD `687bf80264ad43ff3491e8bf2c8a9d9f7bc40456`, compared with
`inp` at `aa359d8fcbe90f6489dc2c4a3ccaf7b5a8e7f8ec`, on 2026-10-28.
`git diff inp...HEAD --stat` contains exactly one added file:
`KAM/Planetary/PGAssembly/RealSlice.lean`, 159 insertions. The pre-existing
untracked handoff is not part of the branch diff.

Scope follows the handoff's AUDIT FOCUS: only `RealSlice*.lean`, with dependencies
inspected for applicability and quarantine. Read repository AGENTS, PLAN and
DECISIONS; `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`; the handoff;
P45 design revision 3 (package row at line 485, obligations at 415 and 418,
signatures at 1498–1508); all three design audits under `docs/tracks/P/design/`
(their P5-ID rows agree); the current shared P45 signatures; P5 blueprint gluing
and jet steps; track P statement and the frozen P-G telescope for context.
The user's exact report destination overrides the generic brief's main-worktree
destination. No production file was edited.

## Declaration-by-declaration decisions

All names below are in namespace `KAM.Planetary` and all four declarations are public.

| Node / role | Declaration (RealSlice line) | Verdict | Reason |
|---|---|---|---|
| Max-norm helper for ext-glue | `mem_ball_realInclusion_iff` (30) | PASS | Exact positive-radius Pi-ball characterization; no changed norm or carrier. Positivity also handles the empty coordinate type correctly. |
| Coordinate identity helper for ext-glue | `polydisc_zero_of_real_zero` (38) | PASS | Holomorphy and zero real restriction on the same polydisc imply zero on the full complex polydisc. The explicit real-zero premise is appropriate to this separately named helper and is supplied by the main theorem. |
| `stepP:p5:ext-glue`; identity component of `stepP:p5:be-jet` | `real_slice_identity` (105) | PASS | Exact design telescope and conclusion, including open/preconnected U, holomorphy, nonempty open real V, inclusion and equality there. No added premise, lost conclusion, or changed quantifier. |
| Connectedness component of `stepP:p5:be-jet` | `connected_complex_tube` (136) | PASS | Exact design signature: connected real X and positive radius imply connected frozen actionNbhd. No openness, boundedness or convexity assumption on X. |

No provider export or new frozen declaration exists in this diff. Provider=frozen
type and frozen seal-body probes are therefore **not applicable**. In their place,
the independent scratch probe copied both exact design telescopes under fresh
names and supplied bodies applying the actual exported proofs to every explicit
argument in order. Both elaborated. Whitespace-normalized telescope comparisons
against both design Appendix A and the live shared signatures returned True for
both main declarations. The shared signature SHA256 was
`f4c7752bf23b8b149e4e5c0f1fac5288b4c32c10d19c4a17d3afe79af1c13ca2`.

## Proof and consumer audit

The induction at lines 44–102 complexifies precisely a finite set of coordinates.
At the empty set, all imaginary parts vanish, giving an actual real vector. At an
inserted coordinate j, replacing z[j] by any w in its radius-r disc stays inside
the original max-norm ball (59–65). Composition with the differentiable update map
proves one-variable holomorphy (66–72). The induction hypothesis supplies zero for
real replacements (73–79). For every punctured neighborhood of the real center,
the proof constructs a distinct real point at displacement min(epsilon,r)/2
(81–94). This verifies genuine accumulation, rather than misapplying a
one-variable theorem to a several-variable real slice. One-variable analyticity
and the identity theorem then give zero at the original coordinate (95–100).
Taking the full finite set proves the result, including N=0.

For `real_slice_identity`, the minimum of a complex neighborhood radius in U and
a real neighborhood radius in V gives a positive polydisc whose real points lie
in V (111–126). The previous helper supplies zero for f-g on an entire complex
neighborhood. `KAM.analyticOnNhd_of_differentiableOn` is applicable to the open
finite-dimensional complex domain and complete scalar target (127–128); it is
the proved several-variable result in `KAM/Strip/AnalyticTaylor.lean:198`.
The subsequent Mathlib analytic identity principle requires neighborhood equality,
which is now supplied, and preconnectedness, which is an original premise.
It does not assume the desired global identity.

For `connected_complex_tube`, X times the nonempty convex complex ball is
connected. The continuous addition map `(J,w) ↦ realInclusion J + w` has exactly
the frozen witness-defined tube as image (139–155). Both set inclusions are proved
explicitly. This avoids any inference that an arbitrary union of connected balls
is connected.

Blueprint `p5-pg-assembly.tex:34` says the overlap is “convex hence connected” and
that its extensions agree on real points. A nonempty overlap of equal-radius
balls with real centers contains the real midpoint and an open real neighborhood,
so it supplies this theorem's nonempty V. The caller must still construct that
overlap and its real agreement. At line 60 the blueprint says the tube is
connected because closure V is connected. Applying this package to closure V
gives precisely that fact, and V is an open nonempty real uniqueness set inside
the positive tube. Holomorphy of the jet functions and their real vanishing remain
P5-JET obligations. This audit does not claim the enclosing extension or Birkhoff
lemma has been completed.

## Definitions and imports

There are **no new def, abbrev, structure, instance, or global norm definitions**.
Local `set` expressions B, delta and r denote literal balls or radius formulas;
there is no fallback or junk-value construction.

Direct imports are Mathlib, `KAM.Strip.Analytic`, and
`KAM.Frozen.Defs.ActionNbhd`. Recursive traversal of the eight KAM modules in this
import closure found only frozen `ActionNbhd` and `ComplexStrip`; both definition
anchors have manifest state SEALED. There is no provider or DRAFT_SORRY frozen
theorem in that closure. The original `realInclusion` is the continuous real-linear
coordinate inclusion, and `actionNbhd` is the original strict witness-radius set.

## Independent verification receipts

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, recursion or synthesis budget override was used. The build waited
for the prescribed compile gate. No clean, update, cache retrieval, dependency
edit, root regeneration or state-changing git operation was issued.

1. Targeted gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5id KAM.Planetary.PGAssembly.RealSlice
   [inp-gate] slot 2 acquired 08:55:40 for KAM.Planetary.PGAssembly.RealSlice
   Build completed successfully (9054 jobs).
   exit 0
   ```

   This is the targeted Lake dependency-graph job count, not a claim that 9054
   modules were freshly compiled. There were no warnings or errors.

2. Design telescope applications and all public theorem axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5IDAudit.lean
   'KAM.Planetary.mem_ball_realInclusion_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.polydisc_zero_of_real_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.real_slice_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.connected_complex_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   No sorryAx or other axiom; no warnings or errors. Scratch probe removed after use.

3. Kernel replay, one invocation covering the sole new lemma module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.RealSlice
   replaying KAM.Planetary.PGAssembly.RealSlice
   exit 0
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (499 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The exit status is solely the explicitly permitted generated-root exception.
   No forbidden-token, line-length, size, module, errata, frozen-guard or ABI
   failure was reported. The ABI subprocess inherited niceness and the single
   Lean-thread setting, and ran after all other Lean checks had finished.

5. Static hygiene: 159 total lines; maximum Unicode line length 100; zero lines
   over 100; no forbidden proof escapes or resource options. Copyright, `module`,
   public imports, module docstring and exposed public section are present.
   No ambient EuclideanSpace or custom Pi norm instance. New public declarations
   are exactly the four rows above.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no
   output, exit 0. `git diff --check inp...HEAD` produced no output, exit 0.
   Final report check: `git diff --no-index --check /dev/null
   docs/tracks/P/audits/P5-ID-audit-1.md` produced no whitespace diagnostics,
   exit 1 (the new-file difference status). An independent text check found no
   trailing whitespace and confirmed the terminal newline and balanced fences.
   Final `git status --short` lists only this new report and the pre-existing
   untracked `P5-ID-handoff.md`; no tracked file changed. Scratch probe absent.

## Findings, limitations and handoff

No material defect, new suspected pinned-source erratum, blueprint contradiction
or introduced mathematical deviation was found in this scope. The helpers prove
their whole-carrier statements without hidden dimensional restrictions. This is
an infrastructure PASS; the generated-root exception is the only package note.
No paper-level claims outside the designated identity/connectedness scope were
re-adjudicated. Existing P45 findings on other packages remain outside this audit.

Only persistent audit edit:
`/root/code/KAM-inp-p5id/docs/tracks/P/audits/P5-ID-audit-1.md`.
The pre-existing handoff, audited Lean source, frozen files, manifest, design,
shared signatures, generated root and README remain untouched.
