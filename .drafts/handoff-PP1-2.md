# Handoff PP1-2 (P Part 1, Diophantine)

**Files:** new `KAM/Planetary/Hamiltonian/Diophantine.lean` (~150 lines). KAM.lean not touched (lint reports it out of date; expected, orchestrator regenerates).

**Nodes proved** (signatures verbatim from PPart1Signatures.lean section E):
- two-scale: `KAM.Planetary.twoScaleDiophantine` (def)
- dio-basic: `IsDiophantine.mono`, `isDiophantine_of_le_l1`, `isDiophantine_smul_iff`, `isDiophantine_min_of_mem_twoScale`
- dio-sources: `smul_mem_twoScale`, `cp10_isDiophantine`, `cp09_isDiophantine`

**Extra helpers** (new names, not in signature file): `one_le_l1_of_ne_zero` (|k|₁ ≥ 1 for k ≠ 0), `dio_smul_bound` (termwise scaling equivalence).

**Approach:** as in design plan: sign split on gamma, rpow monotonicity in exponent/base, scaling by `s⁻¹ * ·`; cp09 via `isDiophantine_of_le_l1` with ν = Euclidean norm (√∑k² ≤ ∑|k| by `sum_sq_le_sq_sum_of_nonneg`), then smul_iff with s = 2π; `d-1 < d ≤ dμ < τ`.

**Checks:** gate build `KAM.Planetary.Hamiltonian.Diophantine`: success, no sorry. Only warning: unused `hγ` in `cp09_isDiophantine` (signature hypothesis retained verbatim, as design Section 4.2 intends). `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; only complaint is KAM.lean out of date (not mine to edit).
`#print axioms` for all 7 theorems: [propext, Classical.choice, Quot.sound].

**Uncertainties / design signals:** none; no heartbeat issues. **Errata:** none. **Deviations:** none.
