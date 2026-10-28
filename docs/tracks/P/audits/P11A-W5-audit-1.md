# Independent P11A-W5 package audit 1

Overall verdict: **PASS WITH NOTES** for P11A-W5, including `KAM.Planetary.ball_sublevel`. No proof or statement-fidelity defect found in the two assigned modules. This is infrastructure approval; **no frozen anchor is proved or seal-ready on the strength of this package alone**. Frozen-provider type/seal checks are not applicable here.

## Scope and authority

Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff and its AUDIT FOCUS, Revision-3 P11A design (especially row P11A-W5, mapping rows and proof plan), design audits 1–3, designated `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, track-P statement and `blueprint-P/parts/p11a1-weak-measure.tex` (conventions, external facts, ball-sublevel and proof steps). Inspected the downstream frozen `ProperlyDegenerateKAM` context; the audited declarations themselves use no frozen definitions or theorem anchors. The explicit user report destination overrides the generic brief's main-worktree destination.

Only these implementation files were audited:

- `KAM/Planetary/WeakMeasure/MeasureTools.lean` (119 lines), SHA-256 `c422c2f59ce1aeb9f909a62e7d846c1dc723f3928cbf54c7e25bcfe0a82c5023`.
- `KAM/Planetary/WeakMeasure/BallSublevel.lean` (287 lines), SHA-256 `9ad5b90047a9abf9aa95a8596828c1eb142859ee788ccf0dcdd5bf45592001cd`.

HEAD: `3c7ff422ccbb245c95fdae70c1fe7db40e64fcbb`. Initial `inp`: `5991245cabc06e69ec900cb6006b45f72cc85eb0` (also its merge base with HEAD). Initial `inp-p11aw4`: `f0f0c51aa212de72afb45448f27149b61e44d4e2`; its merge base with HEAD is `980e204384bfbfebdc210d7ccbb40cc5f56f25ad`.

Ran both required comparisons: `git diff inp...HEAD` and the focus's `git diff inp-p11aw4...HEAD`. Both contain the two new audited files. The full inp comparison additionally contains predecessor Basic, DividedDifference, ScalarSublevel and W0 reports; the current W4 comparison contains substantial unrelated inherited work. Neither is represented as a two-file package diff. `git diff --name-status 06b9af4..HEAD` isolates the actual three W5 commits and lists exactly the two audited files. No unrelated predecessor declaration is certified by this report.

Signature pin: `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`. The signature file is absent from this checkout's `.drafts/design`; the designated inp copy was read without modification. `ball_sublevel`'s entire declaration header is equal to that signature after whitespace normalization. An independent fresh-name declaration copied from the signature, applied to the implementation using every explicit binder in order, elaborated successfully.

## Declaration and node ledger

All names below are in namespace `KAM.Planetary`. Every new public declaration is listed; private/local proof facts are discussed below.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| f-meas / determinant | `p11_det_abs_eq_one` (MeasureTools:34) | PASS | From Q Qᵀ = I, det² = 1; proves nonzero determinant and absolute inverse determinant 1. |
| f-meas / linear volume | `p11_measurePreserving_mulVec` (MeasureTools:46) | PASS | Mathlib determinant pushforward formula; Euclidean orthogonality on the Pi carrier, ordinary coordinate Lebesgue volume. |
| f-meas / affine volume | `p11_measurePreserving_orthogonal` (MeasureTools:55) | PASS | Composes the linear map with translation; no extra regularity or measure hypothesis. |
| f-meas / Tonelli | `p11_volume_le_of_sections` (MeasureTools:67) | PASS | Measurable S, first-coordinate box bounds and a uniform section bound give exactly ofReal((2R)^m c). |
| f-mvt / line chain rule | `p11_iteratedDeriv_line` (BallSublevel:39) | PASS WITH NOTES | All k ≤ q on the open domain, arbitrary base point and direction; correct iterated Fréchet derivative evaluation. Module placement differs from the design's Basic assignment. |
| conv#data / Euclidean identity | `p11euclid_sq` (BallSublevel:73) | PASS | Explicit Euclidean square equals dot product; all n, including n=0. |
| f-orth / unit identity | `p11euclid_eq_one` (BallSublevel:78) | PASS | Unit Euclidean length implies self dot product 1. |
| bs-rot / ball preservation | `p11euclid_mulVec` (BallSublevel:81) | PASS | QᵀQ = I follows from QQᵀ = I; preserves explicit Euclidean length, without changing the Pi norm. |
| bs-tonelli / projection | `abs_apply_le_p11euclid` (BallSublevel:93) | PASS | Coordinate absolute value ≤ Pi norm ≤ explicit Euclidean length. |
| f-orth | `p11_householder` (BallSublevel:105) | PASS | In dimension m+1, every Euclidean unit vector is the last column of an orthogonal matrix; includes m=0. |
| bs-sections / splitting | `p11euclid_snoc` (BallSublevel:174) | PASS | Exact squared Euclidean splitting into m coordinates and the last coordinate. |
| bs-sections / affine line | `p11_snoc_eq` (BallSublevel:179) | PASS | Exact decomposition into snoc(x′,0) + t e_last. |
| ball-sublevel | `ball_sublevel` (BallSublevel:190) | PASS | Literal signature, same q, n, positivity, local smoothness, closed ball, unit direction, lower bound and constant 2q(2r)^(n−1)(eps/beta)^(1/q). |
| bs-rot | locals `Φ`, `hΦ`, `hnorm`, `h1` (BallSublevel:200–217) | PASS | Affine measure preservation and Euclidean ball pullback; correct measure-preimage direction. |
| bs-sections | locals `hsec`, `hΦt`, `hsect`, `hlow′` (BallSublevel:225–277) | PASS | Scalar estimate on each nondegenerate interval; null singleton treatment for zero sqrt, including exterior sections. |
| bs-tonelli | local `key` (BallSublevel:278–283) | PASS | Uniform section bound integrated over [−r,r]^m; rearranges precisely to the target constant. |

The f-meas external-fact node also lists distribution-function continuity, monotonicity and countable subadditivity. W5 supplies the determinant and Tonelli components used here; distribution-function helpers belong to the inherited scalar-sublevel layer. This report does not claim W5 alone reimplements every item in that shared external-fact node.

## Definitions and proof inspection

There are **no new top-level def, abbrev, structure, instance or opaque declarations** in either file. The 13 public declarations are theorems. Existing `P11Vec n` is `Fin n → ℝ`; `p11euclid` unfolds to sqrt of the sum of squared real coordinate norms. The proof uses these literal objects, not a max-norm ball disguised as a Euclidean ball, and never uses index/amount infima or selector defaults from Basic.

Local constructions are ordinary intended objects on their whole carriers:

- MeasureTools: the measurable coordinate equivalence `e`, its preimage `T`, and the box `B` are literal coordinate splitting, transported set and Cartesian interval product. The section estimate works also at m=0 and R=0. No missing c≥0 premise is needed: `ENNReal.ofReal` clips a negative bound to zero, forcing null sections and the corresponding zero conclusion.
- Householder: e is the last coordinate unit vector, v=e−a, c=2/(v·v), and Q=I−c vvᵀ. The a=e branch uses I; otherwise v≠0 and v·v>0 are proved before division is used. No division-by-zero fallback supplies orthogonality or the last-column identity.
- Ball proof: Φ, the closed ball K, its sublevel S, pullback S′, c, y1, ρ and s=sqrt(r²−ρ²) have their literal geometric/arithmetic meanings. For nonpositive radicand s=0, the section inclusion forces a subset of {0}, hence zero volume; positive s invokes the scalar theorem. Thus sqrt's zero branch is handled mathematically, not exploited as a fake interval.

The chain-rule induction obtains equality in a neighborhood inside the open preimage of V, differentiates the continuous multilinear derivative evaluation, and uses the successor iterated derivative identity. It requires no global regularity outside V. Closedness of the target sublevel follows from continuity on the closed ball, rather than unjustified global continuity of g. The n=1 case is included by m=0; the empty coordinate product has its usual unit volume. The derivative lower bound is used only where the line is inside the original closed ball.

No conclusion-shaped hypothesis, hard-step field, hidden constant dependence, fallback-dependent proof, ambient-type change or weakened conclusion was found. The scalar estimate is an actual imported proved theorem, not an assumed input field. A recursive project-import inspection found seven KAM modules and **zero KAM.Frozen or KAM.Provider modules**. Hence no DRAFT_SORRY import or provider-quarantine violation occurs, and no manifest-state exception is needed.

## Independent checks

All audit-owned Lean/Lake/checker calls were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`. The build used the prescribed compile gate. No clean, update, cache fetch, library-from-scratch build, generated-root regeneration, source repair, git mutation or frozen edit occurred.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw5 KAM.Planetary.WeakMeasure.MeasureTools KAM.Planetary.WeakMeasure.BallSublevel
[inp-gate] slot 2 acquired 09:54:10 for KAM.Planetary.WeakMeasure.MeasureTools KAM.Planetary.WeakMeasure.BallSublevel
⚠ [9051/9053] Replayed KAM.Planetary.WeakMeasure.DividedDifference
warning: KAM/Planetary/WeakMeasure/DividedDifference.lean:96:59: Variable name `hab` is not explicitly referenced.
Build completed successfully (9053 jobs).
exit 0
```

The warning is in an inherited dependency, not either audited file. The gate invokes `nice -n 5 lake build` internally.

2. Fresh signature/application probe and exhaustive axiom prints:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW5Audit.lean
exit 0
```

The copied signature was given fresh name `audit_ball_sublevel` and body:

```lean
by
  exact ball_sublevel hn hq hV hr ha hb he hsub hg hlow
```

Every one of the following `#print axioms KAM.Planetary.<name>` commands returned exactly `[propext, Classical.choice, Quot.sound]`:

```text
p11_det_abs_eq_one
p11_measurePreserving_mulVec
p11_measurePreserving_orthogonal
p11_volume_le_of_sections
p11_iteratedDeriv_line
p11euclid_sq
p11euclid_eq_one
p11euclid_mulVec
abs_apply_le_p11euclid
p11_householder
p11euclid_snoc
p11_snoc_eq
ball_sublevel
```

No `sorryAx` or extra axiom occurs. Frozen export equality and literal frozen seal probes: **N/A**, because W5 has no provider export or frozen anchor. The fresh signature probe above is the applicable implementation-type check.

3. Kernel replay, one invocation covering both implementation modules:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.MeasureTools KAM.Planetary.WeakMeasure.BallSublevel
replaying KAM.Planetary.WeakMeasure.BallSublevel
replaying KAM.Planetary.WeakMeasure.MeasureTools
LEANCHECKER_EXIT=0
```

The stdout/stderr above is the complete checker output, apart from the shell exit marker.

4. Full source lint, after kernel replay exited:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (528 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
LINT_EXIT=1
```

The raw exit status is 1 solely for the explicitly permitted stale generated `KAM.lean` exception. All other lint checks pass. The generated file was not regenerated or edited.

5. Source/integrity checks: each file has copyright, `module`, public interface imports, module docstring and public noncomputable section. No forbidden proof escape, resource override or EuclideanSpace code; file sizes 119 and 287, both below 1500. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff --check` exits 0. The stale protected-root delta in the broader W4 comparison is inherited and is absent from both the required inp protected-path comparison and the isolated W5 commits.

## Notes, uncertainties and suspected defects

- **Placement deviation (nonblocking):** design mapping at P11A-LEAN-DESIGN.md:205 and :444 places the line chain rule in WeakMeasure/Basic; implementation BallSublevel:39 provides it publicly here. The actual consumer imports it successfully. The planned local names bs_rot/bs_sections/bs_tonelli are represented by hΦ/hnorm, hsec and key; their obligations are proved, not omitted.
- **Existing declared source deviation:** blueprint p11a1:111 replaces Rus01's Gamma/Stirling ball constant with the circumscribed-cube constant (D2). The implementation follows the accepted blueprint and exact signature. It introduces no further constant change.
- **Errata:** no new suspected blueprint or pinned-source defect arose in this scope. No external PDF claim is newly certified: this audit checks the pinned blueprint/design contract and its Lean implementation. Earlier design findings outside the two W5 modules are outside this package audit.
- **Release boundary:** package PASS does not prove P-FIXED, P-G, the remaining weak-measure layer, or any other frozen headline. The generated-root staleness exception and dependency warning are recorded separately from kernel correctness.

Final integrity: HEAD, inp and inp-p11aw4 refs remained unchanged during the audit. Both implementation SHA-256 values remained unchanged. The pre-existing untracked handoff was preserved; the only new persistent repository artifact is this report. All audit-owned probe/log files were removed from `.lake/abi-scratch/`. `git diff --check` and the report whitespace/fence/pending-marker checks passed. No production file was edited.
