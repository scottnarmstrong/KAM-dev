# N12-10b prover handoff (branch inp-n1210b, a82e346; contains inp-n1203c and inp-n1210a (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (all committed; none under KAM/Frozen or manifest; KAM.lean not edited)
- `KAM/Nekhoroshev/Averaging/FlowChain.lean` (≈395 lines, new helper, generic): `RegOn` (regularity of a family of
  maximal solutions on `J × U`), `regOn_comp`, `shift_sol`, `hasDerivAt_fderiv_volterra` (FTC on the Volterra
  equation), `LocalFlow`/`exists_localFlow` (wraps `ext_dep`), `regOn_extend`, `reg_forward` (sup argument over
  `[0,T]` chaining local flows), time reversal (`RegOn.of_neg`, via `IsMaximalSolution.neg`), `reg_all`.
- `KAM/Nekhoroshev/Averaging/FlowRegular.lean` (82): `isOpen_avgDomain'`, `data_smul'`, `avgH_contDiffOn`,
  `avgField_contDiffOn`, `avgFlow_regOn`, and **`flow_variational`** (signature byte-identical to N12Signatures.lean).
- `KAM/Nekhoroshev/Averaging/FlowSymplectic.lean` (≈187, new helper): real symplectic form `sympl`, Hessian skewness
  (`sympl_fderiv_field_skew`, symmetry of D²H), `sympl_const_of_skew`, `det_eq_one_or_neg_one`.
- `KAM/Nekhoroshev/Averaging/Flow.lean` (≈250): `isOpen_avgFlowDomain`, `continuousOn_avgFlow`,
  `continuousOn_fderiv_avgFlow`, `isOpen_avgOmega`, `contDiffOn_avgFlow`, `avgFlow_inverse`, `det_fderiv_avgFlow`,
  `avgFlow_translate(_fwd)`, and **`flow`** (signature byte-identical to N12Signatures.lean).
Import edges: FlowChain → LocalDependence, ODE.Maximal; FlowRegular → FlowChain, FlowDefs; Flow → FlowRegular,
FlowSymplectic; FlowSymplectic → Averaging.Setting. No provider / DRAFT_SORRY import.

## Approach
Generic over a finite-dim real space `E`, `C¹` field `F` on open `W`, family `z x` of maximal solutions.
`RegOn F W Tm Tp z J U` = {U⊆W, J ⊆ eIoo(x) ∀x∈U, joint continuity of `z` and of `x ↦ fderiv (z · s) x` on `J×U`,
`HasFDerivAt` and `HasDerivAt` in time of the initial derivative with derivative `DF(z x s) ∘ D z`}. `ext_dep` gives it near
time 0; a local flow slab at `T₁` is glued by `shift_sol` (maximality + uniqueness) and composition (`regOn_comp`);
`reg_forward` takes `s* = sup{T ≥ 0 reachable}` and extends past it; negative times by reversal to `-F`.
Inverse: `shift_sol` at the flow-point gives `-t ∈ eIoo(φ_t x)` and `φ_{-t}φ_t x = x` (uses a shifted solution of F, not -F's).
Determinant: `Φ' = DX_H Φ`, `DX_H` ω-skew ⇒ ω preserved ⇒ det² = 1 (nondegenerate form), continuity of det on the connected
maximal interval and `det Φ(0)=1` fix the sign. Translation: `gen_symmetry_translate` + maximality, both directions via `-k`.

## Checks
- Gate builds: `inp_lake_build.sh /root/code/KAM-inp-n1210b KAM.Nekhoroshev.Averaging.Flow` → "Build completed successfully (2967 jobs)", no warnings
  in my files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; it reports "KAM.lean is out of date" (generated; the
  orchestrator regenerates; the new modules FlowChain, FlowRegular, FlowSymplectic, Flow need to be in the regenerated root).
- `#print axioms KAM.Nekhoroshev.flow` and `flow_variational`: `[propext, Classical.choice, Quot.sound]`.
- Signature heads of `flow` and `flow_variational` compared textually (whitespace-normalised) with N12Signatures.lean: identical.
- No `set_option` overrides, no sorry/axiom; all files < 1500 lines.

## Uncertainties / notes
- None of the signatures changed; no statement was false or under-hypothesised. No suspected errata in pinned sources.
- Deviations: added helper modules FlowChain and FlowSymplectic (not in the module table) to keep FlowRegular/Flow near their line budgets;
  `FlowRegular`/`Flow` are at the table paths. `data_smul'` (copy of the private `data_smul` in FlowDefs) is public in FlowRegular; FlowDefs untouched.
- No design signals (all elaboration at default heartbeats).

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-10b and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (flow_variational, local-to-global chaining, inverse, translation, symplectic determinant); (2) proofs sound (N12-03c ext_dep and KAM.ODE.{Hamiltonian,Uniqueness,Maximal} consumed as designed); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the FlowRegular and Flow modules.
