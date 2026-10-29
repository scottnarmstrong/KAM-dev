# P5-BU prover handoff (branch inp-p5bu, 3b850def; contains P5-FAM; offloaded package run by the main orchestrator)


## Files (new; all committed, nothing else touched)
- `KAM/Planetary/PGAssembly/ActionBudgetDefs.lean` (51 lines): `kamMeasureConstant`, `pgMeasureUpper1`,
  `pgMeasureUpper2`, `pgBudget`, copied VERBATIM from P45Signatures.lean.
- `ActionBudgetReal.lean` (136): real N1/N2/N3 (`real_N1`, `real_N2`, `real_N3`) read off `PGAnalyticSpec`
  through the real slice (`jpGrad_realSlice`, `jetOmega_real`, `jetBeta_real`, isometric `realInclusion`),
  using `hsymm` for the transpose in N3.
- `ActionBudgetData.lean` (158): `pgMu1`, `pgMeasureData` (the P4 `MeasureData` on a compact core),
  `budget_facts` (parameter facts from `rstar`, `kh_dyn`), `measure_c1_nonneg`, `measure_c1_le`
  (`measure_c1 ≤ pgMeasureUpper1` using core volume ≥ ½ vol V).
- `ActionBudgetDio.lean` (216): `twoScale_smul_inv`, `dio_real`, `volume_pgActionDomain`, `budget_dio`
  (`stepP:p5:bu-dio`).
- `ActionBudgetCollar.lean` (179): `one_add_pow_sub_one_le`, `checkedCore_isClosed`, `budget_collar_fast`,
  `budget_collar` (`stepP:p5:bu-collar`).
- `ActionBudget.lean` (108): `pgMeasureUpper1_nonneg`, `budget` (`bpP:p5:budget`, `stepP:p5:bu-read`
  inside its proof). Facade importing the above.

## Nodes
- `bpP:p5:budget` -> `budget` (statement verbatim, first conjunct `0 < pgBudget d`, second the bound).
- `stepP:p5:bu-read` -> proof of `budget` (clause 6 of `PGFamilySpec` + containment of the missed set).
- `stepP:p5:bu-dio` -> `budget_dio`; `stepP:p5:bu-collar` -> `budget_collar` (+ `budget_collar_fast`).
- `bpP:p5:budget#constant` -> `pgBudget`, `pgMeasureUpper1/2`, `budget`. Positive denominators:
  `volume_V_pos` (P5-TH), `pgMu1_pos`, core volume positivity inside `budget_dio`; `pgBudget > 0` proved.
- `kamMeasureConstant` was not defined anywhere in KAM; it is defined here (signature file, verbatim).

## Approach
`budget`: missed set ⊆ the set of clause (3.1) of the family spec (D ⊆ N_rK D, rK > 0), so it is at most
c_n (vol(D\D0) + vol(N_rK D \ D)). `D\D0` ⊆ resonanceBad on innerCore×shell with α_i = 2πγ_i
(`resonanceBad_eq`, `twoScale_smul_inv`), bounded by `two_scale_diophantine_measure` with λ = l2top,
μ ≤ r^6, λ ≥ r²/4, 2λ ≤ 4·ell, vol innerCore ≤ vol V ≤ 4 vol checkedCore: gives 4^(b+1)·2π k0 (5U1+4U2)√r·vol D.
Collar: `domain_collar_helper` with E=(A+Cdio·Cγ)√r (from `collar` and `pgAnalytic_dio`), `r_k` for the relative
enlargement ((1+x)^b<2, x ≤ k1√r/(64(a+b))) and an inductive Bernoulli bound; gives
(8(A+Cdio Cγ)/vol V + b k1/16)√r·vol D. Sum = pgBudget·√r.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-p5bu KAM.Planetary.PGAssembly.ActionBudget`: "Build completed
  successfully (9391 jobs)", no warnings or sorry in the six new files.
- `scripts/lint_sources.sh`: PASS for all my files (module check PASS, frozen anchor guard OK, ABI OK,
  no line > 100). It reports only `KAM.lean is out of date; run scripts/gen_root_imports.py` — expected,
  six new modules, KAM.lean not edited per rules (orchestrator regenerates).
- `#print axioms KAM.Planetary.budget` : [propext, Classical.choice, Quot.sound]; same for `pgBudget`.
- No set_option of any kind; no EuclideanSpace; no new axiom/sorry; every file < 220 lines.

## Uncertainties / deviations / errata
- None needed: no signature changed, no hypothesis added. Only structural deviation: the signed declarations
  live in `ActionBudgetDefs`/`ActionBudget` and helpers in four extra modules (all names `budget_*`, `dio_real`,
  `real_N*`, `pgMu1*`, `pgMeasureData`, etc.; grepped for clashes before use). `kamMeasureConstant` is defined
  in ActionBudgetDefs (P5-LO should import ActionBudget).
- Suspected source imprecision (not an error): blueprint step bu-dio says λ = λ2' ∈ [λ2/2, 1] and uses
  (2λ)^b ≤ (4ℓ)^b; the Lean design uses the trimmed shell λ = l2top = ell + l1 (ell ≥ r²/4, l1 ≤ ell), same
  constants 4^(b+1), 5, 4. No design signals (no heartbeat issues).

AUDIT FOCUS: design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-BU (action budget) and its node table; P45 design audits; signatures /root/code/KAM-inp/.drafts/design/P45Signatures.lean. P5-FAM (Family*.lean) is in its own audit: audit ONLY KAM/Planetary/PGAssembly/ActionBudget*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
