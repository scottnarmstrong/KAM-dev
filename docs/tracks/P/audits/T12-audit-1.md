# T12 independent package audit 1

Overall verdict: **FAIL — assigned spectral-data slice incomplete.** The signed definitions and
`quadratic_physical_bridge` pass fidelity and proof checks. This is a completeness failure, not a
counterexample to the bridge. No frozen theorem anchor is implemented or sealed by this package;
provider/frozen-type and seal-body checks are therefore N/A. The exact signed bridge is proved.

Audit date: 2026-10-28. Worktree `/root/code/KAM-inp-p11c-t12`, HEAD
`70ff97817a3fdc2f9059395c42e2e5681c8c8226`; comparison `inp` at inspection
`be6fc7b01267bd5d16506ff11a84c1f7b93cc791`. `git diff inp...HEAD` adds only
`KAM/Planetary/PlanarTorsion/SpectralAdapter.lean` (281 lines). The pre-existing untracked
`T12-handoff.md` was read and left unchanged. Only this report is a lasting audit edit.
The user's explicit worktree report path overrides the generic brief's main-worktree destination.

Authority read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, T12 handoff,
P11C-LEAN-DESIGN.md and DESIGN-P11C-design-audit-1.md, P11CSignatures.lean, track P statement,
Part 11b source and graph packet, and the relevant Part-8 definitions and quadratic theorem.
The lean-statement-audit skill supplied the binder/body checks; this is an infrastructure audit,
not promotion of a DRAFT_SORRY anchor. No subagents or production edits were used.

## Finding F1: incomplete spectral attachment (major)

Design `docs/tracks/P/design/P11C-LEAN-DESIGN.md:125` assigns
`bpP:p11b:sec-beta#data` to T12, and line 213 explicitly lists
“actual quadratic_physical_bridge, Q/sigma/projector; T4/T1, U8b/U9”. Line 54 requires:
“Identify `p11c_Q`, `p11c_sigma`, projector and inverse rotation lift with upstream spectral
objects; prove equalities, never assume them.”

The assigned source, `blueprint-P/parts/p11b-planar-torsion.tex:180–182`, says
“the orthogonal projection onto the $\sigma_1$-eigenspace” and gives rank-one identities
`pi11 + pi22 = 1`, `pi11*pi22 = pi12^2`, and `Pi1 = e1*e1ᵀ` for the diagonalizing frame.
The graph packet `docs/graph/P/packets/P-p11b.nodes.md:1166–1185` retains all these properties
in SOURCE_CONCLUSION. They are needed by `bf-gram` (packet line 1274), `bf-avg` (1307),
`bt-rot` (1379), and `as-ent` (1725). The signature's T13 `beta_formula` assumes a rotation
and its rank-one projector parametrization; it does not connect that parametrization to
`p11c_projector p a`. Thus exact signed declarations alone do not discharge these consumers.

Implementation lines 36–50 define the three formulas. Lines 83–109 identify Q with Part-8
`SecularForm.coeffs`, on valid data and admissible axes. There is no theorem identifying
`p11c_sigma` with `SecularSpectrum.sigma`, proving the spectral gap/negativity, or proving
projector characterization, rank-one relations, or its relation to a diagonalizing frame.
No upstream spectral module is imported. The existing upstream sigma is defined using
`sorted` in `SecularForm/Coefficients.lean:121`; equality with the explicit square-root
formula is not definitional and is not supplied by Q equality.

Handoff lines 27–28 expressly defer this to T14 because it is absent from the signature list.
T14 does own `global_planar_frame` and the rotation lift (design line 215), so the lift itself
is not demanded here. However, the design assigns the spectral-data node to T12 and makes
T14 depend on T12; neither the node table nor the design audit authorizes omitting that node's
spectral attachment. Design audit opening paragraph explicitly says its approval is not
“permission to skip its explicit upstream reconciliation gates”. No implemented consumer
composition closes the missing attachment in this audited file.

Required closeout: establish the spectral identification and source projector properties with
source premises only, or obtain an explicit scope/ownership revision that places every retained
obligation at a named producer before consumers and independently audit those compositions.
Do not mark `sec-beta#data` complete from this module's current exports.

## Declaration and node inventory

All names below are in `KAM.Planetary`. Unsigned helpers have distinct names and are not
substituted for graph conclusions. No public helper short-name duplicate was found anywhere
in KAM; a Lean environment probe also found no root declaration with any new public short name.

| Node / role | Declaration (implementation line) | Verdict | Evidence |
|---|---|---|---|
| sec-beta#data, physical matrix | `p11c_Q` (36) | PASS | Exact signed body; equals physical Part-8 coefficients on source domain. |
| sec-beta#data, sorted spectrum | `p11c_sigma` (43) | PASS formula / FAIL attachment | Exact signed formula; upstream equality and spectral characterization absent. |
| sec-beta#data, projection | `p11c_projector` (48) | PASS formula / FAIL attachment | Exact signed formula; source projector identities absent. |
| U8a adapter | `p11c_laplace_eq_laplace_def` (54) | PASS | Equality for all real s,a and integer k; no positivity premise added. |
| U8b typing | `p11cSecularData` (66) | PASS | Physical fields copied; positivity from p.Valid; dimension 2 proved. |
| Axis adapter | `p11c_axes_mem` (75) | PASS | Increasing positive two-axis cone implies Part-8 positive strictly monotone axes. |
| U8b physical matrix | `p11c_Q_eq_coeffs` (83) | PASS | Source positivity proves action/root identities; finite matrix equality. |
| Calculus helper | `p11c_iteratedFDeriv_two_of_isBigO` (179) | PASS | Analytic O(norm⁴) remainder has zero second diagonal derivative. |
| Calculus helper | `p11c_iteratedFDeriv_two_quad` (188) | PASS | Arbitrary real matrix and constant; exact factor 2, no symmetry premise. |
| U8b / sec-beta#data bridge | `quadratic_physical_bridge` (223) | PASS | Signed type exactly; physical fixed-Sun average, homogeneous jet divided by 2!. |
| Private power-series cut | `p11c_eq_zero_of_isBigO` (113) | PASS | Divides only at nonzero t, then tends to zero. |
| Private analytic cut | `p11c_diag_eq_zero` (131) | PASS | Strong induction removes lower terms; O(t^(j+1)) for j≤3 forces coefficient zero. |
| Entire assigned node | `bpP:p11b:sec-beta#data` | FAIL | F1: formulas and quadratic attachment do not establish spectral characterization. |

The bridge uses `SecularForm.quadratic_form` at actual physical data. It restricts the analytic
remainder to fixed actions through `ι w = (w.1,I,w.2)`, proves the max-norm ball lies in the
source realDisc, and uses `axis_action` to fix its coefficients. The scalar-line power-series
argument removes the quadratic jet of that remainder. The polynomial second derivative is
computed separately; the factorial cancels its factor 2. No secular matrix, derivative identity,
or spectral result is assumed as a premise. The average normalization is the frozen radian
mean `(2*pi)^(-2)` with the same `(q,p)` slow order throughout.

## Expanded binder audit

SOURCE means the literal signed source domain, STANDING its physical positivity, and TYPING
ambient data. The generic calculus helpers are standalone mathematical lemmas; their analytic
and remainder assumptions are discharged inside the physical bridge, not added to its type.
Each listed binder is counted once. No EXCESS or RULED input occurs.

| Declaration | Binder | Bin | Authority / meaning |
|---|---|---|---|
| bridge | p | TYPING | PlanarData: G, m0, m : Fin 2 → ℝ. |
| bridge | hp | STANDING | Expanded: 0<G, 0<m0, ∀i, 0<m i; Part 11b line 14. |
| bridge | a | TYPING | Fin 2 → ℝ axes. |
| bridge | ha | SOURCE | Expanded: 0<a 0 and a 0<a 1, Part 11b A2. |
| bridge | z | TYPING | Phase 2 = (Fin 2 → ℝ) × (Fin 2 → ℝ). |
| laplace equality | s | TYPING | Real exponent, exact integral definitions. |
| laplace equality | k | TYPING | Integer Fourier mode. |
| laplace equality | a | TYPING | Real integral parameter. |
| axes_mem | a | TYPING | Implicit two-axis vector. |
| axes_mem | ha | SOURCE | Positive ordered cone. |
| Q_eq_coeffs | p | TYPING | Same physical data. |
| Q_eq_coeffs | hp | STANDING | Same three positivity clauses. |
| Q_eq_coeffs | a | TYPING | Implicit axis vector. |
| Q_eq_coeffs | ha | SOURCE | Same ordered cone. |
| two_of_isBigO | E | TYPING | Arbitrary ambient real normed space. |
| two_of_isBigO | NormedAddCommGroup E | TYPING | Ambient norm/additive structure. |
| two_of_isBigO | NormedSpace ℝ E | TYPING | Ambient real scalar structure. |
| two_of_isBigO | h | TYPING | E → ℝ function. |
| two_of_isBigO | hh | SOURCE | AnalyticAt ℝ h 0; locally proved as hR in bridge. |
| two_of_isBigO | C | TYPING | Real bound coefficient. |
| two_of_isBigO | hl | SOURCE | Eventually |h z|≤C*norm(z)^4; hRb from quadratic_form. |
| two_of_isBigO | z | TYPING | Diagonal derivative direction. |
| two_quad | Q | TYPING | Any real 2×2 matrix. |
| two_quad | c | TYPING | Any constant term. |
| two_quad | z | TYPING | Any slow direction. |

Theorem binder totals: SOURCE 5, STANDING 2, TYPING 18, RULED 0, EXCESS 0 (25 binders).
The adapter definition `p11cSecularData` has p:TYPING and hp:STANDING; its bundled target
contains only physical fields, the same positivity proofs, and the proved fact 0<2.

## Definition classification

Four new definitions; no abbrev, structure, nonunique choice or conclusion bundle.

| Definition | Classification | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | Verdict |
|---|---|---|---|---|---|---|---|
| p11c_Q | Literal signed matrix | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| p11c_sigma | Literal signed square-root formula | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS formula |
| p11c_projector | Literal signed quotient formula | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS formula |
| p11cSecularData | Physical record adapter | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

The signed formulas are total Lean real expressions on arbitrary p,a; they do not assert
spectral properties outside the physical domain. No invented conditional fallback or arbitrary
chosen object is used. These formula verdicts certify literal definitions, not the missing
on-domain spectral characterization in F1. Q's on-domain identification is proved, while sigma
and projector currently lack that semantic attachment.

## Independent mechanical checks

All completed audit Lean commands were serialized. The build, exact-signature probe, and kernel
replay used `LEAN_NUM_THREADS=1 nice -n 5`; the final full lint invocation uses the same prefix
because lint eventually launches its own Lean ABI probe. An initial unprefixed lint was stopped
while still in its Python frozen-anchor guard, before its Lean ABI step, and restarted correctly.
No audit Lean invocations overlapped. Other workers' processes were not controlled or stopped.

1. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0.
2. `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t12 KAM.Planetary.PlanarTorsion.SpectralAdapter`:
   exit 0, final output `Build completed successfully (9173 jobs).` Replayed warnings concerned
   existing Kepler, Hamiltonian, Poincare and SecularForm/Coefficients modules; none in the target.
3. Signature comparison: whitespace-normalized complete defining commands for `p11c_Q`,
   `p11c_sigma`, `p11c_projector`, and full theorem header for `quadratic_physical_bridge`
   match `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` exactly.
4. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T12Audit.lean`: exit 0.
   The disposable probe imported the target, copied all three signed definitions under fresh names,
   proved each equal by `rfl`, copied the signed bridge type and filled it with
   `exact quadratic_physical_bridge p hp a ha z`, and checked
   `example : type_of% @quadratic_physical_bridge := @t12audit_signature`.
   It also checked every public short name against the root environment. No root shadows found.
   The probe's entire axiom output was:

```text
'KAM.Planetary.p11c_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_eq_laplace_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cSecularData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_axes_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_Q_eq_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedFDeriv_two_of_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedFDeriv_two_quad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.quadratic_physical_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

5. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.SpectralAdapter`:
   exit 0, exact output `replaying KAM.Planetary.PlanarTorsion.SpectralAdapter`.
   This single invocation covers the only new module, including its private proof cuts.
6. Static hygiene: 281 lines, maximum line width 99; copyright, `module`, public imports,
   docstring, exposed public noncomputable section present. No forbidden proof escape, resource
   override, or EuclideanSpace. Every new public short name is unique among KAM declarations.
   Recursive project-import inventory: 127 KAM modules, zero providers, 55 frozen definition
   modules, all manifest state SEALED; no frozen theorem imports or DRAFT_SORRY imports.
   Frozen physical carrier, assemble and secular-average definitions retain their source meaning.

Snapshot SHA-256:

```text
dd1416e29f564165ec9040ac0ab780730c78276edbf22f4af70d208e624aebaa  SpectralAdapter.lean
51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36  P11C-LEAN-DESIGN.md
34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079  P11CSignatures.lean
```

## Errata, deviations, and limits

No suspected mathematical defect in a pinned paper or the frozen definitions was identified.
No fresh external PDF verification was needed for this exact signed/blueprint slice. F1 concerns
missing implementation of the retained blueprint contract, not an assertion that its mathematics
is false. The handoff's unilateral T14 deferral is a scope deviation requiring explicit reconciliation.
The design audit's existing generic-jet placement note is respected: the imported Setting module
already owns `p11c_homogeneousPart`, so T12 does not import later quartic work.

The module's proof of the signed fixed-Sun quadratic bridge is accepted. This report does not
certify moving-Sun higher jets, T14's future frame, any physical headline, or any frozen seal.

## Final lint and closeout receipt

`LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` completed, **exit 1**, with exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p11c-t12/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (885 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale generated root is the brief's explicit exception. The frozen 101-character line is
an additional pre-existing global lint failure, not covered by that exception; full lint therefore
is not recorded as passing. It is absent from the package diff and was not repaired. There is
no target-file lint finding. Frozen guard and all 144 elaborated ABI hashes pass independently
within this full lint run.

The exact-signature/axiom/root-name probe was deleted from `.lake/abi-scratch/` after use.
`git diff --check` passes. Final status contains only this new report and the pre-existing
untracked handoff; no tracked file was edited. Overall **FAIL** remains F1, with a proved exact
signed bridge and the baseline lint failure separately recorded. No requested validation remains
pending.
