# Independent S7-6 package audit 1

Overall verdict: **PASS WITH NOTES** for S7-6, `KAM.Nekhoroshev.Stability.Resonant`.
All four public theorem implementations pass the design/blueprint contract and proof checks.
There is no frozen anchor or provider export in this package: frozen-provider type matching and
seal-body checks are inapplicable. This is approval of the infrastructure package, not a seal of
N-HEAD-C or any track I/N/P headline.

## Scope and authority

Audited only `KAM/Nekhoroshev/Stability/Resonant.lean`, as expressly required by AUDIT FOCUS.
Read the package brief, AGENTS.md, PLAN, DECISIONS, S7-6 handoff, design v2 (including Appendix B
signatures and S7-6 proof plan), both design audits, Track N statement and blueprint Part 7.
Checked the definitions of the dependencies actually used, including frozen `frequencyMap`,
`realPart` and the Hamiltonian field, and the actual orbit/norm/domain predicates. Dependencies
S7-1/2/3/5 were inspected for applicability, not independently re-audited as packages.

Snapshot:

- HEAD: `d45c8414a40176f11193fd24f75faae31e17212c`.
- Observed `inp`: `4f65a1f8055d14808ab27ed9bff2e18d69eac46c`.
- `git diff inp...HEAD` warns of multiple merge bases and selects
  `88983f74ff9952994d1de31d0ed671307437b563`. Its six-file diff includes the predecessor
  packages and `.drafts/handoff-S7-5.md`; only Resonant is in this audit's authorized scope.
- Resonant SHA-256: `37a5e621288d3e96bdecebd050e83dc7ed918d51d3947ed71f7d2b6f863f579e`.
- Design SHA-256: `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2`.
- Blueprint p7 SHA-256: `f3d6e993abd74759469db1c9ae3c2c6d7cc65555a6d13167e8bfc7c38493e4bd`.

The user's exact report path overrides the brief's generic instruction to write in the main
worktree. No source, frozen file, manifest, generated file, or git state was edited. The handoff
was already untracked at intake. No agents were delegated.

## Declaration ledger

All names below have namespace `KAM.Stability`.

| Node / source | Declaration (Resonant line) | Verdict | Reason |
|---|---|---|---|
| `s-energy#rs` | `ResSetting` (32), including its fields and generated structure API | PASS | Byte-identical to design L1201–1230. Bundles source regularity, reality, weighted bounds, resonance and smallness premises, not a proof conclusion. |
| `s-energy#rs` | `resRho` (57) | PASS | Literal radius `δ/(4M)`; byte-identical design body. |
| `s-energy#rs` | `IsAdmissible` (60) | PASS | Strict Euclidean distance witness in D; byte-identical design body. |
| `admissible` | `admissible` (261) | PASS | Exact design signature; closed Euclidean ball lies in the open max-norm tube, projection bound varies by `M‖I−I₀‖₂`, initial bound `5δ/4`. |
| `no-exit` | `no_exit` (388) | PASS | Exact design signature; all three exit, segment-curvature and time hypotheses retained. Contradiction proved from the core. |
| Lemma 1 | `resonant_lemma1` (430) | PASS | Exact design signature; stopped convex confinement for either time direction, including zero time-product cases. |
| Lemma 2 | `resonant_lemma2` (447) | PASS | Exact design signature; both radius conditions retained, arbitrary valid Ω bound, quasi-convexity used only after proving the cone inequality. |

There are no other source-written public declarations in this module. All auxiliary lemmas
are private. A mechanical comparison found the four complete theorem headers identical to
Appendix B modulo whitespace, and all three definition blocks byte-identical. An independent
probe copied each design theorem under a fresh name and supplied exactly the implementation
applied to its explicit binders. All four elaborated at default resource limits, including
implicit carriers and binder order.

Relative to the blueprint, the carried `Mg,η,ζ` bounds implement the approved bound-predicate
formulation, with summability explicitly present in `WBound`. Any upper bound Ω generalizes
the blueprint maximum; specializing to that maximum recovers the statement. Multiplicative
time inequalities retain the documented infinite-time cases without division by zero.
No extra hypothesis or weaker conclusion was introduced against the approved design.

## Definitions and proof examination

`ResSetting` is an honest Prop structure on the full declared carrier. Its analytic, reality,
Hessian, Fourier support and numerical fields are standing/source premises. It does not bundle
confinement, the energy estimate, or a conclusion-shaped witness.
`resRho` uses ordinary total real division; at `M=0` Lean gives its standard value, but every
use requiring a radius proves `M>0` from `0<m≤M`. No proof uses a fallback.
`IsAdmissible` is the intended existential strict-distance predicate for all parameter values.
There are no additional new defs, abbrevs, structures or instances.

The proof chain was checked as follows:

- L125–179: scalar mean value applied to `a ↦ Dh(J+aΔ)[v]`, with v the gradient
  difference, gives the Euclidean gradient Lipschitz estimate by bilinear duality. Holomorphy
  on the open tube supplies real C² regularity; HessBound is used on the whole chord.
- L94–120 and L261–308: self-adjointness/idempotence make P contractive in the Euclidean
  norm and annihilate `resSpace Λ`. The closeness witness and `Mρ=δ/4` supply the initial
  projection bound. Strict initial distance keeps the entire closed ball inside the open tube.
- L310–385: `rs_energy` applies S7-5 `energy_core` on `realNbhd D r` to the actual real
  Hamiltonian. S7-2 `real_system`, `resonant_gradient`, and `theta_derivative` supply the
  smoothness, vanishing perpendicular resonant gradient, size and derivative bounds.
  The private real-gradient bridge identifies actual derivatives, not an assumed bound.
- L388–411: no-exit uses `Δ≥15r/16`, `Δ≤r`, `A≤mr²/16`, `B≤5mr²/16`,
  `C≤mr²/24` (only `exp 1≥2`). Thus the core would give
  `225mr²/512 ≤ 5mr²/12`, impossible since m,r are positive.
  This replaces the blueprint's Young-inequality arithmetic without changing its result.
- L413–444: S7-1 `exit_ball`, available through the S7-3 Transfer import, gives an actual
  first boundary time on either side of zero; continuity comes from the genuine orbit.
  Convexity on the chord and monotonicity of the nonnegative time product close Lemma 1.
- L447–514: Ω bounds every chord frequency. The perpendicular estimate and time bound
  give the error `≤mr²/24`. The projection term is `≤(7/8)ℓΔ`; using
  `mr≤2ℓ` and `r≤(16/15)Δ`, the total is at most
  `(7/8+4/45)ℓΔ=(347/360)ℓΔ≤ℓΔ`. This contradicts the strict first
  quasi-convex alternative, leaving the required Hessian bound for no-exit.

The weaker numerical estimates in these two proof steps remain sufficient. No source premise
is replaced by a hard step assumed as a hypothesis. The imports are precisely Energy,
Gradient and Transfer; their transitive KAM import closure contains no provider and no frozen
theorem. All 19 imported frozen modules are definition anchors in manifest state SEALED.

## Independent checks

All auditor-started Lean commands were sequential with `LEAN_NUM_THREADS=1` and nice level 5.
The build used the required compile gate. No cache fetch, clean, library-wide build, package
modification, heartbeat, recursion-depth or synthesis-heartbeat override was used.

1. Target build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s76 KAM.Nekhoroshev.Stability.Resonant
   [inp-gate] slot 2 acquired 06:56:01 for KAM.Nekhoroshev.Stability.Resonant
   Build completed successfully (3239 jobs).
   exit 0
   ```

   This was an incremental replay against the worktree snapshot. Resonant warnings are unused
   `hPid` (263:5) and `ht₁0` (391:29), both design-fixed binders. Replayed dependencies also
   warn about unused `hgr`, `NormedSpace` and `hϱ`; no elaboration failure occurred.

2. Design probes and axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S76Audit.lean
   'KAM.Stability.admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Stability.audit_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Stability.no_exit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Stability.audit_no_exit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Stability.resonant_lemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Stability.audit_resonant_lemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Stability.resonant_lemma2' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Stability.audit_resonant_lemma2' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

3. Kernel replay (one invocation; no separate provider/lemma modules exist in S7-6):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Stability.Resonant
   replaying KAM.Nekhoroshev.Stability.Resonant
   exit 0
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   Lean lines over 100 characters:
   /root/code/KAM-inp-s76/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (436 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

5. Static checks: Resonant has **520 lines**, with **zero lines over 100 Unicode characters**.
   Copyright, `module`, public imports, module docstring and exposed public noncomputable
   section are present. No forbidden proof escape, resource override or EuclideanSpace occurs.
   `git diff --check inp...HEAD` exits 0. The protected-path command
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has empty diff output
   (only the multiple-merge-base warning).

## Notes, defects and limits

1. Repository-wide lint is not a clean pass: see its exact output above. The overlong
   `Liouville.lean` line is outside S7-6 and absent from this branch diff. The generated-root
   complaint is the brief's allowed exception. Neither is an S7-6 source defect; no unauthorized
   repair was made. The full lint issue still needs repository-owner cleanup.
2. Resonant L429 says Lemma 1 is “consumed by track I only.” Design §8 L383 and design audit-1
   N3 explicitly classify that reuse as prospective, with no current blueprint-I consumer.
   Suggested documentation replacement: “Lemma 1; off the published graph, available for
   prospective track I reuse.” This is an inherited documentation overstatement, not a theorem
   or applicability failure.
3. The handoff reports 518 lines; the audited file has 520. This does not approach the hard cap.

No new suspected defect in a pinned mathematical source was found. The already documented
Pos93 Lemma 2 proof gap and its added `Mr≤ℓ/4` repair are explicitly retained in the blueprint
(p7 L222–227) and design; no silent source correction was introduced. This audit checks the
local package against that approved contract, without claiming a new independent PDF audit.
The arithmetic route variations above are valid implementation deviations from the written
proof plan. There is no remaining mathematical uncertainty identified within S7-6's scope.

Only this report is the auditor's retained artifact. Auditor-created signature probe and kernel
log were removed from `.lake/abi-scratch/` after recording the results. Final report checks:
no trailing whitespace, balanced code fences, no pending-result placeholder.
