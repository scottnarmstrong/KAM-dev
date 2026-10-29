# Q6 prover handoff (branch inp-p11c-q6, 0093556d; contains B20 (passed) and the P11B chain; offloaded package run by the main orchestrator)


Branch `inp-p11c-q6`; all edits committed (last commit "Q6: weak_kam_quantitative").

## Files (new)
- `KAM/Planetary/Quantitative/AssemblyData.lean` (106 lines): `p11c_selData_exists` builds the upstream
  `SelectionData` from `QuantitativeData` + `h` (with `selectionM₀ ≤ m0`, `qbcOfSelection ds m0 = d`);
  norm identifications (`euclid` = `selectionLength`), boundedness of the diagonal derivative sSup.
- `KAM/Planetary/Quantitative/AssemblyTori.lean` (68): openness of `p11c_realDomain`, differentiability of
  `realHamiltonian` on it, transfer of `IsLatticeTorus` between Hamiltonians agreeing on the open domain.
- `KAM/Planetary/Quantitative/Assembly.lean` (229): `p11c_cDelta` (= `selectionCDelta` as a function of
  `(N,mu,tau,s,C1)`), `p11c_asm_*` helpers, `p11c_asm_family` (positive branch at selection level),
  `p11c_asm_zero_family`, and the signed `weak_kam_quantitative` (statement copied verbatim).

## Approach (design Q6 plan: cDelta first, eps = 0 split, then positive branch)
1. `cDelta := p11c_cDelta N mu tau s C1` (explicit formula, outside all varying data; junk value 1 when
   `¬(1 ≤ N ∧ 0 < s ∧ 1 ≤ C1)`, where the statement is vacuous since `Valid` forces them).
2. `eps = 0`: `zero_case` (Q5) for `realHamiltonian h 0`; `f` vanishes on strip x nbhd, so the Hamiltonians agree
   on the open real domain and the lattice-torus clause transfers.
3. `eps > 0`: selection data from `d`,`h`; `eps ≤ thresholds d ≤ selectionAdmissible` by `polyBudget_threshold_le`
   (B20 file, from Q2 comparison); `evaluation_bilipschitz` (which extends `SelectionLipschitz` /
   `SelectionDisplacement` / `SelectionTori`, i.e. `free_radius`, `limit_torus`, `displacement`) gives the
   family; `good := Hinf`, `torus := selectionEvaluation defect`, `freq := ωstar`. Displacement uses
   `delta_absolute` and `delta_power` with `gamma d = selectionGamma` (`qbc_gamma_sel`).
   Tori lie in the real domain via `action_displacement` (s₀ ≤ ϑ, Q₀ ≤ 2⁻¹¹).
Not used: `parameter_selection` / `parameter_selection_adapted` directly (they are consumed inside
`evaluation_bilipschitz`), `adm_budget`, `displacement_power` (the uniform constant is the explicit
`selectionCDelta`, so B20 is only used for `polyBudget_threshold_le`).

## Checks
- `LEAN_NUM_THREADS=1 inp_lake_build.sh . KAM.Planetary.Quantitative.Assembly`: success, no warnings in my files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK. It prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: I did not touch KAM.lean; the three new
  modules need to be added by the orchestrator's regeneration).
- `#print axioms KAM.Planetary.weak_kam_quantitative`: `[propext, Classical.choice, Quot.sound]`.
- No lines over 100 columns; no `set_option`, no sorry/axiom; no EuclideanSpace; no provider/DRAFT_SORRY import.

## Uncertainties / errata / deviations
- None for the statement; it was provable as signed. The signed `QuantitativeInput` has no `M0`-positivity or
  `d.M0 ≥ selectionM₀` premise beyond its last clause; this is exactly what `p11c_selData_exists` uses.
- No suspected source errata. No design signals (all elaboration at default heartbeats).
- Public helper short names introduced: `p11c_cDelta`, `p11c_cDelta_eq`, `p11c_cDelta_pos`, `p11c_euclid_eq`,
  `p11c_selectionReal_eq`, `p11c_thick_eq`, `p11c_scalar_eq`, `p11c_dg_bdd`, `p11c_mem_thick`,
  `p11c_selData_exists`, `p11c_asm_*`; grep showed no pre-existing use.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row Q6 (weak_kam_quantitative; Q4/Q5, U11a3 parameter_selection, U11a4 free_radius/limit/displacement/evaluation) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean (weak_kam_quantitative; note Q4's signed budget is p11c_budget by ruling). Check the identification of QuantitativeData with the upstream SelectionData (p11c_selData_exists, selectionM0 <= m0) adds no premise, and that the positive branch uses parameter_selection_adapted / free_radius / limit_torus / displacement / evaluation_bilipschitz as the design says. Audit ONLY KAM/Planetary/Quantitative/{AssemblyData,AssemblyTori,Assembly}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
