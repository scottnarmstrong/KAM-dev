# B5 design: the exact-torus adapter (plan §3.4, §7 row B5)

Status: design (kam-b1, 2026-11-03, overnight D71; scope set by root-b8). Pure Lean, no data. Nothing is frozen.
Owner decisions are OD-B13 to OD-B15 in `OWNER-DECISIONS.md`.

## Goal

Turn the v2/hybrid output `KAM.Certificate.CertifiedTorus c ω*` (`KAM/Certificate/Defs.lean:356`) into a B1-T
instance (`torus_confinement`) near the certified torus, with every chart premise derived from the certificate.
`CertifiedTorus` provides an exact embedding `Kinf` with these properties:
- holomorphic on the strip `T_{ρ∞}`, primary, and real on reals;
- invariant, `invarianceError H Kinf (s∞ ω*) = 0`, for some `s∞ ∈ (1, σω)`;
- energy `H ∘ Kinf = E0`;
- `B(Kinf θ, μ/2) ⊆ D` and `‖DKinf‖ ≤ σK − μ/2`;
- `‖Kinf − K_c‖ ≤ disp`.

## Mathematics

1. **Lagrangian (derived, not assumed).** With zero invariance error, the Lagrangian matrix
   `Ω_K = DKᵀ Ω₀ DK` (`KAM.lagrangeMat`, `KAM/Torus/Objects.lean`) vanishes on a smaller strip. Two routes:
   - the repo's a-posteriori bound `KAM.Sharp.geometry_sep` at `ε = 0`;
   - directly: `∂_ω Ω_K = 0`, periodicity, density of a Diophantine orbit, and zero average (exactness of
     `Σ dIᵢ ∧ dθᵢ` on a primary torus).
2. **Chart (plan (Chart)).** Real `K(φ) = (x(φ), v(φ))` with `x = φ + u`, where `u` and `v` are periodic and
   `‖Du‖ ≤ κ < 1`. Define `Ψ(φ, J) = (x(φ), v(φ) + Dx(φ)^{-T} J)` and
   `Ψinv(y, p) = (x⁻¹ y, Dx(x⁻¹ y)ᵀ (p − v(x⁻¹ y)))`.
   - `x` is a global diffeomorphism commuting with lattice shifts; its inverse comes from a contraction,
     `φ = y − u(φ)`.
   - `Ψ` is C², lattice-equivariant and symplectic **iff** `Dxᵀ Dv` is symmetric (the real Lagrangian condition).
   - `Ψinv ∘ Ψ = id` everywhere, and `Ψ(φ, 0) = K(φ)`.
3. **Normal form.** With `ω' := s∞ ω*`:
   - `H(Ψ(φ, 0)) = E0`, by the energy identity;
   - `∂_J (H∘Ψ)(φ, 0) = ω'`, by invariance: `∂_p H(K) = Dx ω'`, so `∂_p H(K) · Dx^{-T} e_j = ω'_j`.

   Hence `H ∘ Ψ = N(J) + R` with `N(J) = E0 + ω'·J`. The remainder satisfies `R(φ, 0) = 0` and `∂_J R(φ, 0) = 0`.
   So `∂_φ R(φ, 0) = 0` and `∂_φ∂_J R(φ, 0) = 0`, which gives `|∂_{φ_j} R(φ, J)| ≤ C₃ |J|²/2`, where `C₃` bounds the
   third derivatives. `C₃` comes from Cauchy estimates for the holomorphic `H ∘ Ψ` on a complex neighbourhood.
   B1-T then applies with `η_j = C₃ b²/2`: drift `≤ C₃ b² |t|/2`, the classical quadratic-in-radius bound.
   Higher-order normalization around the torus composes later with B4 (FT checker in the Ψ chart).
4. **Projection bound from certificate data.**
   `‖Du_∞‖ ≤ ‖Du_c‖_{strip} + disp/δ` (Cauchy on the strip loss `δ`) `< 1` is a finite check.

## Package split (≤ ~1.5k lines each; two provers)

| Package | Content | Depends on |
|---|---|---|
| **B5-CHART** | Generic real chart theorem (item 2): contraction inverse of `x`, C² regularity, lattice equivariance, the symplecticity ⇔ symmetric `Dxᵀ Dv` computation, explicit `Ψinv`. Real analysis only. | B1 |
| **B5-LAG** | From `CertifiedTorus`: `lagrangeMat Kinf = 0` on a smaller strip (item 1). The real slice `x, v` with the symmetric `Dxᵀ Dv`. The frequency identity `DK·ω' = X_H∘K` on reals. Real primary/periodic structure and the `κ` bound (item 4). | Certificate, Torus, Sharp/Apost |
| **B5-NF** | Item 3: `H∘Ψ = E0 + ω'·J + R`, `∂_J` at `J = 0`, the third-derivative Cauchy bound, and B1-T's drift premise `|∂_φ R| ≤ C₃ b²/2` on `|J| ≤ b`. | B5-CHART, B5-LAG |
| **B5-ROUTE** | `certifiedTorus_confinement`: `CertifiedTorus c ω*` + finite checks (κ, radii, `C₃`, margin) ⇒ `torus_confinement`'s conclusion for the certificate's real Hamiltonian, chart `Ψ_{Kinf}`. | all |
