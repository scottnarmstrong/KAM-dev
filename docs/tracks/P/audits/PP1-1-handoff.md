# PP1-1 prover handoff (branch inp-pp11, 6123a91; off inp with inp-design-p1; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Hamiltonian/Algebra.lean` (~200 lines). Nothing else touched (KAM.lean not regenerated; lint notes it is out of date, expected).

**Nodes:** `bpP:p1:conv#data` -> `linearField`, `hamiltonianVectorField_eq_linearField` (rfl).
`bpP:p1:omega-algebra` (a): `symplecticForm_antisymm`, `eq_zero_of_symplecticForm_right`, `symplecticForm_linearField`,
`eq_linearField_iff`, `symplecticForm_hamiltonianVectorField`; (b): `bijective_of_symplectic`, `abs_det_of_symplectic`,
`apply_linearField_comp_of_symplectic`; (c): `symplectic_neg_iff`. All 10 theorems + 1 def are verbatim from the signature file.

**Approach:** coordinate expansion of linear forms (private `apply_eq_sum`) gives `Ω(w,X_ℓ)=ℓ w`; nondegeneracy by testing on
basis vectors; uniqueness via a private `symplecticForm_sub_right`. Bijectivity: injective by nondegeneracy, then
`LinearMap.injective_iff_surjective`. Determinant: private `omegaForm` (Ω as `BilinForm`, nondegenerate), Gram matrix in
`(Pi.basisFun).prod (Pi.basisFun)`, `BilinForm.toMatrix_comp`, `nondegenerate_iff_det_ne_zero`, so `det(A)^2 = (c^d)^2`.
`A X_{ℓ∘A} = c X_ℓ`: surjectivity of A plus `eq_linearField_iff` for `c • ℓ` (private `linearField_smul`).
Imports: Mathlib + frozen Defs (SymplecticForm, HamiltonianVectorField, Phase) only; no provider, no theorem anchor.

**Checks:**
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-pp11 KAM.Planetary.Hamiltonian.Algebra`: Build completed
  successfully; only warning: unused `hc` in `abs_det_of_symplectic` (signature kept verbatim; the statement is true without `hc`).
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; note "KAM.lean is out of date"
  (generated; not edited per rules). One line >100 chars remains at the verbatim docstring of
  `symplecticForm_hamiltonianVectorField` (signature text, 101 bytes incl. multibyte; lint passes).
- `#print axioms` of all 10 theorems: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties:** none. No heartbeat issues (file builds in ~16 s); no `set_option`.
**Suspected errata / deviations:** none. Design note: `abs_det_of_symplectic` does not need `hc` (harmless over-hypothesis from the signature).
**Audit notes applied:** N2 `Basis.prod` -> `Module.Basis.prod` (used `Module.Basis` and the bilinear-form/toMatrix route; no Euclidean inner product).

AUDIT FOCUS (design docs/tracks/P/design/PART1-LEAN-DESIGN.md row P1-1 (Algebra) and proof plan; its audit DESIGN-P1-design-audit-1.md; blueprint-P p1 conv#data (X_ℓ), omega-algebra): (1) statements = design signatures and blueprint (coordinate-free linear-field algebra, the conformally symplectic identities, totality); (2) proofs sound; (3) hygiene. Audit ONLY the PP1-1 module(s) (KAM/Planetary/Hamiltonian/Algebra*).
