# T14 independent package audit 1

**Overall verdict: FAIL — missing required inverse-rotation-lift attachment.**
The signed frame theorem and all three signed definitions pass fidelity and proof checks.
The failure is slice completeness under the design's U9 reconciliation requirement, not a
counterexample to the frame theorem or the lift formula. No frozen anchor is implemented by
T14; provider/frozen-type equality and frozen seal-body checks are N/A. T14 does not seal
P-PLANAR, P-FIXED, or any other campaign theorem.

## Scope and authority

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-t14`.
HEAD: `df340cc0d070b41153ebd3a8e113bb8e0672e628`.
Observed `inp`: `eff45716c45678ce9fbb21a346ab5821d70a823b`.
Only `KAM/Planetary/PlanarTorsion/Frame*.lean` is assigned; the matching production file is
`Frame.lean`, 183 lines. The exact user-specified report destination overrides the generic
brief's main-worktree destination. No production file, frozen file, manifest, generated root,
or git state was changed. The pre-existing untracked `T14-handoff.md` was left unchanged.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external package-audit brief, T14 handoff,
P11C-LEAN-DESIGN.md, DESIGN-P11C-design-audit-1.md, the external P11CSignatures.lean, track P
statement, Part 11b and its graph packet, relevant Part 9 lift definitions/theorem, inherited
T12 spectral adapter, and frozen coordinate definitions. The physical frozen headlines were
inspected for context; they are not imported or proved by this package.

`git diff inp...HEAD` reports multiple merge bases and selects
`48e9326d764f4bb7e1704209fddf71863ec4eb9e`. Its five added files are Frame.lean,
SpectralAdapter.lean, T12-audit-1.md, T12-audit-2.md, and T12-handoff.md (1190 lines total).
The latter four are inherited through merge `5db7fe31`; `git diff 5db7fe31..HEAD --stat`
contains only Frame.lean, 183 insertions. The protected-path three-dot diff is empty.
Inherited T12 reports are historical evidence, not substitutes for checking this checkout.
In particular, the current inherited adapter already proves sigma identification, the spectral
gap, negativity, and projector identities; the first T12 audit's old omissions are not charged
to T14.

| Audited input | SHA-256 |
|---|---|
| Frame.lean | `2ca445afb8dde23e70e3e9316591e4de4744856836b43a395cfbab5be8d3b01d` |
| /root/code/KAM-inp/.drafts/design/P11CSignatures.lean | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| P11C-LEAN-DESIGN.md | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |

## F1 — required U9 lift identification is absent

Design `docs/tracks/P/design/P11C-LEAN-DESIGN.md:54` says:
“Identify `p11c_Q`, `p11c_sigma`, projector and inverse rotation lift with upstream spectral
objects; prove equalities, never assume them.” Row T14 at line 215 assigns the global frame
and concrete rotationLift, with U9. Line 245 explicitly assigns this part's
`p11c_rotationLift` to Frame and says Lift takes the existing Part-9 inverse rotation lift
for composition. The design audit at line 3 expressly does not permit skipping these gates.

Implementation `Frame.lean:171–179` supplies the exact signed formula and then ends.
There is no equality to `SecularSpectrum.liftInv`, no invocation of `SecularSpectrum.lift`,
and no theorem establishing the chart properties of this concrete lift. The inherited
SpectralAdapter explicitly reserves the rotation lift to T14 (line 284) and supplies no
such equality either.

The upstream object is `KAM/Planetary/SecularSpectrum/Lift/Basic.lean:39`. It uses the
matrix-valued derivative of R in `R.transpose * fderiv R`. The signed T14 formula uses
scalar derivatives of individual entries in an expanded triple sum. These are the intended
same expression on the physical analytic domain, with the correct positive angle shift,
but identifying them requires a derivative/projection argument and finite-sum algebra.
An equality of the signed body with its signature copy does not establish this attachment.
The upstream helper `Lift/Analytic.lean:70`, `SecularSpectrum.fderiv_entry`, specifically
requires differentiability of the matrix family; that premise must be derived from the
frame theorem and the analytic axis map.

The retained consumer is the signed `PlanarBirkhoffResult` (signature lines 594–630):
the same T must equal `p11c_rotationLift p` composed with the chi-flow lift and be a chart
and injective, with action preservation and translation covariance. T11's signed
`lift_map` (lines 502–508) covers only `p11c_liftFlow`, not this rotation. Thus there is a
literal unproved attachment at the boundary through which the existing Part-9 rotation-lift
theorem is supposed to supply those properties. No invalid chart conclusion is assumed in
T14's theorem; the problem is an undelivered design obligation.

Closeout: prove the identification with `SecularSpectrum.liftInv
(fun I => p11c_frame p (p.axes I))` on valid physical data and actions whose axes lie in
`p11c_axes`, deriving differentiability from the existing frame theorem. Then expose the
needed domain/regularity interface for applying Part 9. Alternatively, obtain an explicit
ownership revision naming the producer of this retained attachment before consumers and
audit that composition. Handoff line 35, “a definition only (no theorem about it is signed
for T14),” does not waive the design's explicit equality gate.

## Declaration and node inventory

Names are in `KAM.Planetary`. Every public declaration in the audited file appears below.
Unsigned helpers have distinct names and do not purport to export an entire graph node.

| Node / role | Declaration (Frame.lean line) | Verdict | Reason |
|---|---|---|---|
| Concrete common slow rotation | `p11c_rotateSlow` (29) | PASS WITH NOTE | Exact signed type and body; definition ownership moved from the T13 signature block. |
| bt-rot frame | `p11c_frame` (33) | PASS | Exact signed normalized eigenvector and positive quarter-turn. |
| U9 positivity | `p11c_Q_off_pos` (42) | PASS | Part-8 identification and Part-9 pair/action positivity; only valid data and ordered positive axes. |
| Normalization denominator | `p11c_frame_norm_pos` (53) | PASS | Positive off-diagonal entry forces squared vector length positive. |
| Ordered first eigenvector | `p11c_frame_eigen` (60) | PASS | Symmetry and proved trace/determinant identities; no spectral hypothesis added. |
| Domain topology | `p11c_axes_isOpen` (74) | PASS | Intersection of strict coordinate inequalities. |
| Physical matrix regularity | `p11c_Q_analyticAt` (79) | PASS | Local equality with analytic physical coefficients on the open cone. |
| First eigenvalue regularity | `p11c_sigma0_analyticAt` (87) | PASS | Positive discriminant, analytic square root, exact smaller-root formula. |
| Frame regularity | `p11c_frame_analyticAt` (101) | PASS | Positive normalization denominator and analytic entry formulas. |
| bt-rot / bt-rot#lift replacement | `global_planar_frame` (125) | PASS | Exact signed statement: analytic entries, UᵀU=1, det U=1, ordered diagonalization on the whole cone. |
| Concrete inverse rotation lift | `p11c_rotationLift` (171) | PASS formula / FAIL attachment | Exact signed body; F1: no required identification with Part 9's lift. |
| T14 slice | global frame plus U9 lift interface | FAIL | F1; no failure of the signed frame theorem. |

Design node-table lines 131–136 jointly assign bt-rot, bt-rot#lift, bt-K, bt-nf, bt-avg,
and bt-frozen to T14–T16. T14 delivers the matrix-frame input to those later arguments.
The physical Taylor/normal-form/average/frozen conclusions belong to T15/T16 and are not
claimed complete here. The full lift-map node remains assigned to T11, with the concrete
rotation adapter supplied by T14; F1 concerns that adapter boundary, not a demand that T14
prove the chi-flow theorem.

The literal analytic-angle conclusion is also not proved. This is the design's expressly
authorized replacement at lines 12 and 174: a global analytic SO(2) matrix suffices for the
displayed consumers. Frame has no unsigned export named `bt-rot#lift` claiming its literal
angle conclusion. Keep the graph's SOURCE_GAP and NOT_STARTED records at
`docs/graph/P/packets/P-p11b.nodes.md:1359` and `:1390`; a later BYPASSED status requires
the separate consumer review specified by the design. Do not record an analytic angle as
proved from this audit.

## Definitions, premises, and proof review

There are three new definitions and no new structures, abbreviations, instances, or bundled
assumptions.

| Definition | Whole-carrier classification |
|---|---|
| `p11c_rotateSlow` | Genuine linear application of any real 2×2 matrix to both slow blocks. Orthogonality is not baked into the definition or assumed for arbitrary U. |
| `p11c_frame` | Exact total normalized-vector formula. For arbitrary invalid data or degenerate axes it can be degenerate because Lean inverse and square root are total. Every frame theorem is guarded by p.Valid and membership in the axis cone, where the denominator is proved positive. No proof uses a degenerate extension as an SO(2) frame. |
| `p11c_rotationLift` | Exact total extension in frozen (phi,q;I,p) coordinates. Fast actions stay fixed; slow blocks are both multiplied by U; the positive angle correction is yᵀ(Uᵀ∂U)x. Outside the physical analytic locus, scalar fderiv retains its total Lean meaning; no chart or analyticity claim is made there. F1 is the missing attachment on the intended locus. |

Premise classification: p, a, indices, matrices, and phase points are TYPING; hp expands to
0<G, 0<m0, and positive planet masses (STANDING); ha expands to 0<a0<a1 (SOURCE).
The main theorem has precisely p and hp and quantifies over the whole source cone internally.
The unsigned pointwise helpers use only these same premises, plus typing indices. There
are no EXCESS, conclusion-shaped, or owner-ruling hypotheses, and no conclusion hidden in
a typeclass or structure field. No new constant with enlarged dependence is introduced.

The eigenvector proof obtains the two component equations from symmetry and the already
proved eigenvalue sum/product. The main proof normalizes using the strictly positive square
root, obtains e0²+e1²=1, and verifies orthogonality, orientation, and all four diagonalization
entries by finite polynomial identities. Analyticity uses equality on a neighbourhood in the
open cone, not equality at a single point. The proof never needs a branch of an angle or
simply-connectedness. The result is stronger in domain than the local good-patch frame
required by the consumers.

## Independent checks

All Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The compile-gate script itself applies nice to its lake build. Lint's ABI subprocess inherits
the parent's niceness and thread setting. No clean, update, cache download, resource-budget
override, root regeneration, or additional agent was used.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t14 KAM.Planetary.PlanarTorsion.Frame
   [inp-gate] slot 1 acquired 20:48:16 for KAM.Planetary.PlanarTorsion.Frame
   Build completed successfully (9188 jobs).
   exit 0
   ```

   This was a targeted cached build. Replayed dependencies emitted unused-variable and
   deprecated-name/style warnings in Kepler/Poincare/SecularSpectrum/Coefficients modules;
   no warning or error was attributed to Frame.lean.

2. Signed-declaration and axiom probe, `.lake/abi-scratch/T14Audit.lean`:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T14Audit.lean
   exit 0
   ROOT_SHADOW_CHECK PASS
   ```

   The three signed definitions were copied from the authority signature under fresh names
   and compared to the production definitions by `rfl`. Whitespace-normalized source bodies
   also matched exactly. The copied signed theorem statement elaborated under a fresh name
   with body `by exact global_planar_frame p hp`; its normalized header matched exactly.
   No additional premise or altered quantifier was introduced.

   Exact `#print axioms` output for every audited declaration:

   ```text
   'KAM.Planetary.p11c_rotateSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_Q_off_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame_norm_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_axes_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_Q_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_sigma0_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_frame_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.global_planar_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11c_rotationLift' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (one invocation; no provider module exists in this package):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Frame
   replaying KAM.Planetary.PlanarTorsion.Frame
   exit 0
   ```

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (940 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failure is the generated-root staleness explicitly excepted by the audit brief.
   Hygiene therefore passes with that permitted note; the generated root was not changed.

5. Static/import/protected-path checks:

   - Direct imports are Mathlib, SpectralAdapter, and SecularForm.Coefficients. Recursive
     local import scan reaches 55 frozen anchors, all definition-kind and SEALED; no frozen
     theorem, provider, or DRAFT_SORRY anchor is imported.
   - Comment/string-masked source scan found no forbidden escape, EuclideanSpace, or
     set_option. The file has 183 lines and maximum width 96 characters. Copyright, module,
     public imports, module docstring, and exposed public noncomputable section are present.
   - A declaration-site scan of KAM found no duplicate short name for any of the eleven new
     public declarations; the fresh Lean environment probe found no corresponding root names.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produces no diff, only
     the multiple-merge-base diagnostic described above.
   - `git diff --check` exits 0. The untracked report was also checked separately with
     `git diff --no-index --check /dev/null docs/tracks/P/audits/T14-audit-1.md`.
     Audit probe and log files were removed from `.lake/abi-scratch/` after recording results.

## Errata, deviations, and limits

No new pinned-source defect or frozen-statement defect was found. The existing Part 11b
line 217 analytic-angle SOURCE_GAP is preserved, with the design's explicit matrix-frame
replacement; this audit does not claim to prove that literal angle statement.

The extra T13-block definition `p11c_rotateSlow` in Frame is byte-for-byte the signed body
up to whitespace. It has no current duplicate. On integration T13 must import its owner
instead of defining the same public name; this is an ownership/dependency deviation, not
a mathematical weakening. No audit-introduced production deviation occurred.

The handoff's claim of no uncertainties is too broad because of F1. The signed frame
theorem is proved and independently checked; the whole T14 design slice is not ready to
be marked complete until the retained lift identification is paid or explicitly reassigned.
