# S7-5 prover handoff (branch inp-s75, 7ff4bf5; contains inp-s71 (S7-1, delivered); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- NEW `KAM/Nekhoroshev/Stability/Energy.lean` (≈330 lines). No other file touched. KAM.lean not edited.

## Nodes proved (namespace `KAM.Stability`)
- `bpN:p7:ext-linalg`: `IsOrthProj`, `exists_orthProj` (dot-product `Matrix.toBilin' 1`, `B.orthogonal V`,
  `isCompl_orthogonal_of_restrict_nondegenerate`, `Submodule.projection`; symmetry from decomposition).
- `bpN:p7:resonance-data`: `resSpace`, `IsCloseToRes`, `IsMConvex`, `IsQuasiConvex`, `HessBound` (signature-verbatim; one
  def signature re-wrapped over two lines for the 100-char lint).
- `bpN:p7:energy-core`: `energy_core` (signature verbatim, all four conclusions).
- Extra public helpers (not graph nodes): `clm_eq_dot`, `euclid_sq_eq_dot`, `abs_dot_le_euclid` (Cauchy-Schwarz).
  Private: `taylor_segment`, `HR_diffAt`, `theta_split`, `hasDerivAt_dot_snd`.

## Approach
(a) `ham_energy` + `hHR`. (b) scalar mean value for `τ ↦ c ⬝ᵥ (z τ).2` with `c = Δ - PΔ`: derivative is
`-c ⬝ θf` because `c ⬝ θg = Pc ⬝ θg = 0`; then `c⬝Δ = c⬝c` gives `|c|² ≤ |c| B |t₁|` (avoids a Euclidean-norm mean
value theorem). (c) `taylor_mean_remainder_lagrange` (n = 1) on `φ(a)=hR(x+aΔ)` over `uIcc 0 1`. (d) combine with
Cauchy-Schwarz and symmetry of `P`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-s75 KAM.Nekhoroshev.Stability.Energy`: "Build completed successfully (3202 jobs)", no warnings
  for the file.
- `sh scripts/lint_sources.sh`: only message is "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: new
  module; root is generated and I may not edit it). check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- `#print axioms`: `exists_orthProj` and `energy_core`: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
None. No statement needed an extra hypothesis. No heartbeat issues (no overrides; build 5 s). Orchestrator must regenerate KAM.lean.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row S7-5 and proof plan; audits DESIGN-N67-design-audit-{1,2}.md; blueprint-N p7 resonance-data, energy-core): (1) statements = design v2 signatures and blueprint; exists_orthProj correct; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the S7-5 module(s) (KAM/Nekhoroshev/Stability/Energy*).
