# R3 prover handoff (branch inp-p11c-r3, 6e298e3e; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/PlanarTorsion/RealFlow/Variational.lean` (~290 lines). No other file touched.

**Declarations:** `real_analytic_hamiltonian_local_flow` (verbatim signature; node `bpP:p11b:e-ode`).
Helpers (prefix `p11cVar`): `p11cVar_clm_eq_sum`, `p11cVarLin`, `p11cVar_form_lin_left/right`,
`p11cVar_form_add_form_eq_zero` (Hessian symmetry => Ω(Mw,v)+Ω(w,Mv)=0), `p11cVar_hasDerivAt_form`,
`p11cVar_hasFDerivAt_field`, `p11cVar_fderiv_field`, `p11cVar_hessian_symm`, `p11cVar_field_form`,
`p11cVar_fderiv_slice`, `p11cVar_variational` (variational equation), `p11cVar_form_hasDerivAt`,
`p11cVar_form_const` (frozen-form conservation), `p11cVar_isSymplecticOn`.

**Approach:** R2's `p11c_analytic_hamiltonian_flow` gives analytic Φ. Differentiating ∂ₜΦ = X_H∘Φ in the
data direction and using symmetry of D²Φ (analytic => `isSymmSndFDerivAt_of_omega`) gives
d/dt DΦₜ u = DX_H(Φₜ) DΦₜ u. DX_H = J·Hess H with symmetric Hessian, so d/dt Ω(DΦu,DΦv)=0; the
form is constant on Ioo(-T,T) (`IsOpen.is_const_of_deriv_eq_zero`), equal to Ω(u,v) at t=0.
Only the local-at-a-point R2 result is used; the compact common-neighbourhood version is NOT needed
(no merge of READY-R2b required).

**Checks:** `inp_lake_build.sh ... KAM.Planetary.PlanarTorsion.RealFlow.Variational`: Build completed
successfully, no warnings in my file at the end. `#print axioms` of real_analytic_hamiltonian_local_flow and
p11cVar_variational: [propext, Classical.choice, Quot.sound]. `scripts/lint_sources.sh`: module check PASS, frozen
anchor guard OK, ABI hashes OK; only message: "KAM.lean is out of date; run scripts/gen_root_imports.py"
(I must not edit KAM.lean: orchestrator to regenerate). No lines > 100 columns. No heartbeat options.

**Uncertainties:** none known. **Errata / deviations:** none. Signature copied verbatim (the theorem keeps
its own `{d : ℕ}` binder; shadows the file-level `variable {d}`, harmless).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row R3 (variational equation, Hessian symmetry, frozen form conservation, real_analytic_hamiltonian_local_flow) and its node table incl. bpP:p11b:e-ode (R1-R3 jointly); P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. R2's compact common-neighbourhood version is being added in a fix round on inp-p11c-r2: note whether R3 used or needed it. Audit ONLY KAM/Planetary/PlanarTorsion/RealFlow/Variational*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
