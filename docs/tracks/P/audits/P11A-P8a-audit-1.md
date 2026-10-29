# P11A-P8a independent audit 1

Overall verdict: **FAIL for literal graph-slice completeness (F1)**. The exported basic-spec theorem is sound and passes the proof/hygiene checks below; `pr-a` passes. The full `pr-basic` graph conclusion is not established at its stated domain/radius. This is a scope-completeness finding, not a counterexample to any proved Lean theorem.

Audited HEAD: `3879a7bacc20e4b3a294bffa2f0819327d96f123`.
Comparison ref `inp`: `911694d963d1b8682f9984a2a5120bdb037ec5b2`.
Git reports multiple merge bases and chooses `a2464f937a8b578ae414ec08331359284ec94a78` for `inp...HEAD`; this exact requested comparison was used.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, the P8a handoff and its AUDIT FOCUS, the Track P statement, the design node table and prepared sections, the two graph records, blueprint-P/parts/p11-cp09-preparation.tex:187-207, and the relevant signature text. Signature file: `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA256 `fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.

Only `KAM/Planetary/Preparation/PreparedBasic.lean` is audited. Per the orchestrator's correction during this audit, imported signed definitions from PreparedData are **given** and are being audited separately in the P11A-P8 data audit. Comparisons/probes using those definitions below test PreparedBasic's fidelity to that interface, and do not certify PreparedData. The handoff's claim that PreparedData had already been audited is superseded.

The full `git diff inp...HEAD` inventory has 14 files, 3242 insertions and one deletion: PreparedBasic (548 lines), PreparedData (112), Slow facade, nine Slow proof modules, and the P7c audit/handoff. These inherited/dependency files are not additional audit targets. No production file was edited. The brief's generic output-location instruction is overridden by the user's exact absolute report path in this worktree.

There is no provider or frozen anchor in this slice, hence no per-anchor seal assertion or provider/frozen seal-body probe applies. `prepared`, `amount`, frequency/jet/scalar clauses and P8e assembly remain assigned elsewhere under the explicit split ruling and are not findings here.

| Contract | Verdict | Result |
|---|---|---|
| stepP:p11:pr-basic | FAIL | F1: missing literal complex polar-domain conclusion, notably rz/4 rather than rz/2. |
| stepP:p11:pr-a | PASS | Correct bound, exponent, log factor, norm bridge and c2-to-c comparison. |
| Basic selected signed clauses | PASS | Exact clauses and no extra premise in the final existence theorem. |
| Frozen anchors | N/A | None supplied or claimed in P8a. |

## F1: pr-basic's full domain chain is not established

Authority: `docs/graph/P/DEPGRAPH.md:20562`, also `docs/tracks/P/design/P11A-LEAN-DESIGN.md:388`, and blueprint `p11-cp09-preparation.tex:206`.

The graph explicitly requires:

> Theta hat into T_{sigma_F/6} x D(J_0, s_2) x B_{r_z/4} in D_1 prime

The implementation instead proves, at `PreparedBasic.lean:378-398`, the local fact

```lean
have hmem : p11PolarC (A.Psi y) ∈
    p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2) := ...
```

This is inside `p11PreparedCoreOf_chain_eq`, where `y` is the rescaling of a **real** point (`:362`); its exported conclusion (`:353-356`) is the real fixed-Hamiltonian identity. The subsequent `hWdom` (`:408-410`) proves membership after Fast.map in the secular working domain, also locally. Neither is a standalone complex-carrier chain conclusion. In particular, `C.rz/2` membership does not imply `C.rz/4` membership. The imported bound used at `:380`, `p11_polarC_mem`, itself concludes rz/2, not rz/4. Thus even allowing a node to be proved inside another proof does not pay the literal rz/4 obligation.

`p11Rescale_mem_dom` exports the first arrow correctly, and the slow spec supplies the Psi arrow. However, `P11PreparedBasicSpec` (`:427-447`) contains no polar-image/domain-chain clause; `p11_prepared_basic` consequently does not export this missing conclusion. The module docstring at `:24` mentions `p11PreparedCore_chain_mem`, but no such declaration exists in KAM. The source-form complex Hamiltonian identity can be composed from source clauses, but this module exports the signed real identity rather than the entire graph contract. The explicit AUDIT FOCUS requires pr-basic literally by an export, so the current signed-clause success alone cannot close that node.

This finding does **not** reject the signed unit action neighbourhood in favour of the larger blueprint E: the missing rz/4 image fact remains absent even on the signed carrier. It also does not request any P8b/P8c/P8e clause.

Required disposition: prove/export the full complex domain chain with the graph's action and oscillator radii, deriving its smallness from a sufficiently small eps3. For example, the existing bound `||p11PolPt|| <= 4*sqrt eps` can support rz/4 after further shrinking eps3; a new external smallness hypothesis on the final existence theorem would not satisfy the existing contract. Alternatively, an explicit controlling graph/design ruling must record the weaker sufficient route and its consumer applicability. No such ruling was supplied. No repair was made by this auditor.

## Declaration-by-declaration review

All names below have namespace `KAM.Planetary`. Locations are in PreparedBasic.lean.

| Node / purpose | Declaration | Line | Verdict | Reason |
|---|---|---:|---|---|
| pr-basic / construction | `p11PreparedCoreOf` | 38 | PASS | Explicit N, P, real chart chain and free checkW; no fallback. |
| pr-basic / construction | `p11PreparedCore` | 49 | PASS | Specializes the preceding construction to the imported selected data. |
| geometry | `p11RescaleReal` | 54 | PASS | Explicit real affine rescaling. |
| geometry | `p11Rescale_real` | 58 | PASS | Exact compatibility with real inclusion. |
| geometry | `p11Box_isOpen` | 72 | PASS | Open polydisc, arbitrary real radii including empty cases. |
| geometry | `p11Box_mono` | 79 | PASS | Coordinate radius monotonicity. |
| geometry | `p11_actionNbhd_norm_lt` | 84 | PASS | Coordinate norm < 3/2 on the signed unit action neighbourhood. |
| pr-basic / first domain arrow | `p11Rescale_mem_box` | 97 | PASS | Image in half slow box; pi*eps <= s2 suffices on this carrier. |
| geometry | `p11Rescale_differentiable` | 124 | PASS | Globally complex differentiable affine map. |
| pr-basic / first domain arrow | `p11Rescale_mem_dom` | 132 | PASS | Exact first arrow on the signed carrier; sigma/12/6 = sigma/72. |
| pr-basic / N holomorphy | `p11PreparedCoreOf_N_differentiableOn` | 142 | PASS | Uses source h0/g2 holomorphy and the proved domain inclusion. |
| pr-basic / P holomorphy | `p11PreparedCoreOf_P_differentiableOn` | 165 | PASS | Source f3 holomorphy composed with rescaling. |
| pr-basic / periodicity | `p11PreparedCoreOf_P_periodic` | 177 | PASS | Single-coordinate period one, exactly the selected signed clause. |
| complex arithmetic | `p11_im_div_ofReal` | 190 | PASS | Standard identity, valid even at zero denominator under Lean conventions. |
| pr-basic / reality | `p11PreparedCoreOf_rescale_real_mem` | 194 | PASS | Real input maps into the required slow domain. |
| pr-basic / N reality | `p11PreparedCoreOf_N_real` | 204 | PASS | Real h0/g2 divided by positive real eps. |
| pr-basic / P reality | `p11PreparedCoreOf_P_real` | 224 | PASS | Source RealOn transferred through real affine rescaling. |
| pr-basic / total reality | `p11PreparedCoreOf_NP_real` | 236 | PASS | Sum of the preceding two real quantities. |
| pr-a / norm bridge | `p11_norm_le_of_wbound_open` | 254 | PASS | Local action ball in the open set permits the weighted-to-pointwise theorem. |
| stepP:p11:pr-a | `p11PreparedCoreOf_P_bound` | 277 | PASS | Literal endpoint bound with c; intermediate source bound is proved pointwise at lines 290-303. |
| pr-basic / polar reality | `p11_slowBox_re_pos` | 309 | PASS | Oscillator action real part > pi*eps on V2. |
| pr-basic / real identity | `p11PreparedCoreOf_chain_eq` | 325 | PASS WITH NOTES | Sound real identity with source clauses as premises; does not export the full complex domain chain (F1). |
| selected signed clauses | `P11PreparedBasicSpec` | 427 | PASS | Exactly the selected clauses of the given signed spec, modulo whitespace and unused lets. |
| source clause projection | `p11_secular_ham_chart` | 456 | PASS | Extracts the chart identity from the given secular spec. |
| conditional assembly | `p11_prepared_basic_of_spec` | 467 | PASS | Discharges every basic clause from three source specs and explicit smallness conditions. |
| small-eps assembly | `p11_prepared_basic` | 501 | PASS WITH NOTES | No extra external premise; eps3 before eps, c and W. Proves the basic spec but not full graph pr-basic (F1). |

## Definitions and hypothesis audit

- `p11PreparedCoreOf`: literal formulas on the entire function carrier; N takes only actions, P uses rescaled f3, chain uses Fast.map after the polar/Psi maps and then the real secular chart, and checkW is exactly the caller's W. No conditional branch or fabricated witness. Taking real parts in the total definition is justified by the reality proof on the theorem's real domain.
- `p11PreparedCore`: the same construction with the imported signed selected objects. Those imported selections are given here; the final proof obtains their source specifications on its small-eps interval.
- `p11RescaleReal`: the intended total real affine map, with no fallback.
- `P11PreparedBasicSpec`: a conjunction of precisely the selected signed properties; no hidden assumption or bundled proof field. Omitting unused lets does not change these clauses. Its missing graph domain conclusion is F1, not a false definition.

The generic clause lemmas assume only the relevant source differentiability, periodicity, reality, bounds or map identities. The conditional assembly clearly carries three source specs and smallness assumptions. The final theorem derives all of these from D and `1 <= nu`; it assumes no conclusion-shaped hypothesis.

`p11_prepared_basic` chooses eps3 using D and nu before quantifying eps, c and W. Its c threshold is exactly `p11SlowConstant D nu <= c`. The chosen bound is the minimum of u/2, eps1, the selected slow eps2, exp(-1)/MF and rz^2/65 (`:513-516`). All are proved positive; the proof derives log nonnegativity and compares c2 with c using nonnegative rpow factors. No dependence of eps3 on c or W is introduced. The unrestricted `forall W` is stronger uniformity than a chosen frequency datum and is compatible with later assembly.

The pr-a proof turns the parameterwise weighted bound into a pointwise complex norm bound using an open action ball, divides by positive eps, and uses
`eps^(nu+3/2)*eps = eps^nu*eps^(5/2)`.
The resulting c2 bound is enlarged to c in `:489-494`. No alternate norm or radius is used in this argument.

## Interface probes

Temporary file: `.lake/abi-scratch/P11AP8aAudit.lean`. It imported only the audited module and used default elaboration limits. It contained:

1. A renamed copy of the signature file's `P11PreparedSpec` definition and an `rfl` proof that it equals the given imported spec. This checks the interface used for the next probe, not PreparedData as a separate audit target.
2. This exact projection (all selected clauses, including the final Hamiltonian identity):

```lean
example {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (Q : P11PreparedData n)
    (h : P11PreparedSpec D nu eps c Q) : P11PreparedBasicSpec D nu eps c Q := by
  rcases h with ⟨a,b,d,e,f,g,i,j,k,l,m,o,p,q⟩
  exact ⟨a,b,d,e,f,g,i,j,q⟩
```

3. An explicit expected-type example for `p11_prepared_basic D hnu`:

```lean
example {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ eps3 : ℝ, 0 < eps3 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps3 → ∀ c : ℝ,
      p11SlowConstant D nu ≤ c → ∀ W : P11Vec (n+n) → P11Vec (n+n),
        P11PreparedBasicSpec D nu eps c (p11PreparedCore D nu eps W) :=
  p11_prepared_basic D hnu
```

4. `#print axioms` for all 26 declarations listed above.

A separate whitespace-normalized text comparison removed only the five excluded frequency/jet/scalar conjuncts from the signed spec and compared all retained conjuncts with BasicSpec: `True`. Thus retained clauses are verbatim modulo formatting, not merely logically equivalent. This is not a proof of the deferred full spec.

## Checks and exact results

All Lean/Lake commands ran sequentially with `LEAN_NUM_THREADS=1`, under `nice -n 5`. Lint was also serialized because its ABI check launches Lean.

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8a KAM.Planetary.Preparation.PreparedBasic
[inp-gate] slot 2 acquired 01:19:17 for KAM.Planetary.Preparation.PreparedBasic
Build completed successfully (9419 jobs).
exit 0
```

The target's only warnings are `dif_pos` deprecations at 510:32, 534:8 and 540:8, each recommending `dite_eq_left`. Dependency replay also emits existing unused-variable/simp/deprecation warnings; these are not proof failures.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP8aAudit.lean
exit 0
```

The examples emitted no errors. Axiom output, verbatim:

```text
'KAM.Planetary.p11PreparedCoreOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Box_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Box_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_actionNbhd_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_mem_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_mem_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_N_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_im_div_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_rescale_real_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_N_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_NP_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_le_of_wbound_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slowBox_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_chain_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11PreparedBasicSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_secular_ham_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prepared_basic_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prepared_basic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedBasic
replaying KAM.Planetary.Preparation.PreparedBasic
exit 0
```

No provider/other new in-scope lemma module exists to add to this single replay invocation.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1192 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the generated-root staleness explicitly allowed by the audit brief.
No generated file was regenerated. All substantive lint, module, frozen guard and ABI checks pass.

Additional read-only checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty stdout, exit 0 (only the multiple-merge-base warning on stderr).
- `git diff --check inp...HEAD`: empty stdout, exit 0 (same warning).
- Source-mask scan: no sorry/admit/axiom/unsafe/opaque/EuclideanSpace or set_option in the audited file.
- All 26 declaration short names checked against every other KAM source declaration: no clash. All exports remain inside KAM.Planetary; no harmful root shadow.
- File length 548 lines; maximum Unicode line width 100. Copyright, module command, public imports, module docstring and exposed public noncomputable section are present.
- Recursive project import scan: 373 KAM modules in the closure, no KAM.Provider module and no frozen theorem module. Thus no DRAFT_SORRY theorem is imported; only frozen definition interfaces are involved.

## Errata, deviations and limits

No pinned-source mathematical defect was established. F1 is an implementation/graph mismatch, with exact blueprint/design/graph and code locations above; it must not be silently reclassified as graph closure. The non-existent chain_mem reference in the docstring should also be corrected when the missing export is supplied. PreparedData's audit status is corrected in Scope above.

The signed selected clauses, final quantifier order, absence of added external premises, axiom restriction and kernel validity pass. This report does not certify the separately audited data interface, deferred prepared/amount results, any frozen anchor or campaign theorem.
