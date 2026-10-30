# Errata and deviations

*Working record, generated from the findings ledger [`ledger.json`](ledger.json) by
`scripts/render_errata.py`; do not edit by hand. The reader-facing record is [`ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md); every
erratum is verified against the pinned PDF by its writer and then by an independent refute-first verifier. Until
then an erratum marked CANDIDATE is a report to check, not a claim.*

**Policy.** Erratum: a defect in a pinned source (typo, wrong constant/sign, missing hypothesis, false as stated, gap). A gap counts as an erratum only when a printed assertion is false; a supplied argument for a true step is a deviation. Deviation: a deliberate difference of the formalization from the source (scope, conventions, reformulation, explicit parameter windows, proof supplements, different proof routes). Our own statement repairs are neither.

Locations refer to the pinned versions in [`sources.json`](../sources.json); counts are of entries, not occurrences.

## Count

| Source | Errata | Deviations |
|---|---|---|
| Pos01 (arXiv:0908.2234v1) | 5 | 2 |
| GJLV05 (doi:10.1088/0951-7715/18/2/020) | 6 | 1 |
| FdlLS09 (arXiv:0903.0311v1) | 1 (1 candidate) | 0 |
| CCdlL13 (doi:10.1016/j.jde.2013.05.001) | 1 | 1 |
| HL19 (arXiv:1711.05515v1) | 16 (1 candidate) | 8 |
| Nek77 (doi:10.1070/RM1977v032n06ABEH003859) | 3 | 6 |
| LP17 (arXiv:1703.07125v2) | 1 | 2 |
| Chi05 (pinned PDF) | 1 | 3 |
| CC03 (doi:10.1090/memo/0878) | 1 (1 candidate) | 1 |
| BM11 (arXiv:1004.1014v2) | 4 | 7 |
| GCB16 (arXiv:1403.6776v1) | 3 (1 candidate) | 0 |
| Pos93scan (doi:10.1007/BF03025718) | 5 (2 candidate) | 6 |
| Nei76 (pinned PDF) | 1 | 3 |
| CP10pin (doi:10.3934/dcdss.2010.3.545) | 16 (3 candidate) | 10 |
| Fej04r (doi:10.1017/S0143385704000410) | 15 | 8 |
| Fej07e (pinned PDF) | 1 | 0 |
| Arn63b (doi:10.1070/RM1963v018n06ABEH001143) | 1 (1 candidate) | 0 |
| CP11 (doi:10.1007/s00222-011-0313-z) | 2 | 1 |
| CP09 (arXiv:1206.3475v1) | 11 (3 candidate) | 3 |
| Rus01 (doi:10.1070/RD2001v006n02ABEH000169) | 2 | 0 |
| Rus05 (doi:10.1070/RD2005v010n01ABEH000297) | 3 | 1 |
| AKN06 (doi:10.1007/978-3-540-48926-9) | 0 | 1 |
| FH24 (arXiv:2304.10205) | 3 | 0 |
| FHL17 (arXiv:1601.00084v1) | 3 | 0 |
| CCdlL20d (arXiv:2002.10647) | 3 | 0 |
| CCGdlL22 (arXiv:2107.02853) | 2 | 0 |
| CCdlL20s (arXiv:2007.08394) | 1 (1 candidate) | 0 |
| CC07 (doi:10.1090/memo/0878) | 1 | 0 |
| CC87 (doi:10.1063/1.527418) | 1 | 0 |
| CC97 (doi:10.1007/s002200050115) | 1 | 0 |
| CC88 (doi:10.1007/BF01218480) | 0 | 0 |
| CC95 (pinned PDF) | 1 | 0 |
| VL22 (arXiv:2101.07785) | 1 | 0 |
| FH25 (arXiv:2403.10152) | 2 (2 candidate) | 0 |
| Pos96W (doi:10.1007/BF02566420) | 3 | 2 |
| Pos96K (pinned PDF) | 1 | 1 |

## Pos01 (arXiv:0908.2234v1)

### Errata

1. **p. 29 (arXiv v1.3), footnote to Lemma A.2.** *missing hypothesis; CONFIRMED* (E-Pos01-1). Printed: (print version, PSPUM 69) condition Kσ ≥ 1 absent. missing hypothesis: the condition Kσ ≥ 1 is missing in the printed version; the author's own footnote in arXiv v1.3 says so and the pinned arXiv version contains it. Evidence: author's footnote, arXiv v1.3 p. 29. Effect: none on the pinned version; relevant only if the measure layer uses Pöschel's Appendix A.
2. **p. 23 (arXiv v1.3), choice of h₀ and K₀ in the proof of Theorem A.** *gap; CONFIRMED* (E-Pos01-2). Printed: (to be quoted from the pinned PDF). the choices of h₀ and K₀ violate h₀ ≤ α(2K₀^ν)⁻¹ (Bou20, footnote 1); Kou19 Rem. 2.1.5(4), p. 28: 'Theorem A and B are not valid for ν = τ+1' with that proof; Bou20 restores Theorem A as stated by Rüssmann approximation and a linear scheme. Evidence: Bou20 (arXiv:2006.04453v1) footnote 1; Kou19 (arXiv:1904.13062v1) Rem. 2.1.5(4). Effect: relevant only if the measure layer follows Pöschel's proof.
3. **p. 13 (arXiv v1.3), measure statement after Theorem A.** *typo; CONFIRMED* (E-Pos01-3). Printed: "measure of Ωα × Tn". should be the measure of (Ω ∖ Ωα) × Tⁿ. Evidence: context of the measure estimate. Effect: none.
4. **p. 6, after the definition of Ω_α.** *false as stated; CONFIRMED* (E-Pos01-4). Printed: "or at least of dimension n − 1 so that the measure of a boundary layer of size α is O(α)". Hausdorff dimension n − 1 of the boundary does not give O(α) boundary layers. Counterexample: n = 1, Ω = (0,1) ∖ {1/k : k ≥ 1}: the boundary has dimension 0 but the inner α-layer has measure ≳ √α. The right condition is finite upper Minkowski content, or a layer bound as in our HEAD. Evidence: the counterexample. Effect: none; HEAD assumes the layer bound directly.
5. **p. 11, proof of Prop. 2.** *wrong constant; CONFIRMED* (E-Pos01-5). Printed: ≤ |ϕ̄|_{L,Ω} m(Ω − Ω_α). the Lipschitz constant must be raised to the power n (Lipschitz maps scale n-dimensional measure by L^n; compare BC17 footnote 32). Evidence: scaling of Lebesgue measure under Lipschitz maps. Effect: none; our measure lemma uses Λ^d.

### Deviations

1. **whole proof.** *different proof route; PLANNED* (D-ROUTE-1). Proof route: the tori are obtained from an a-posteriori fixed-frequency KAM theorem (parameterization method, no canonical changes of variables) applied at each Diophantine frequency, not by Pöschel's iteration of symplectic transformations. Effect: no effect on the statement; recorded for readers comparing the proofs.
2. **Theorem (p. 6), Prop. 1–2 (p. 11).** *scope (weaker rate); PLANNED* (D-MEAS-1). Rate: our route proves meas(complement) ≤ C·ε^{1/4} (γ ~ ε^{1/4}), not Pöschel's O(√ε); the measure step applies the McShane extension of App. B to F̂ − id in frequency coordinates; in the proof the tori are parameterized by actions (not frequencies), so ∇h(B) needs no regular boundary (blueprint Part 4, V1–V2). Effect: the headline's exponent is 1/4 (owner question Q1).


## GJLV05 (doi:10.1088/0951-7715/18/2/020)

### Errata

1. **p. 862, Theorem 3 (closeness bound).** *typo; CONFIRMED* (E-GJLV05-1). Printed: cγ²δ^{−2σ}. presumably cγ^{−2}δ^{−2σ}, as in Theorems 1 and 5. Evidence: comparison with Theorems 1, 5 and the proof. Effect: none if confirmed as a typo.
2. **p. 865, Theorem 5.** *typo; CONFIRMED* (E-GJLV05-2). Printed: ‖e₀‖_{ρ₀}. ρ₀ is not defined in the statement (presumably ρ). Evidence: statement of Theorem 5. Effect: none.
3. **pp. 884–885, Lemma 14 (choice of the phase).** *gap; CONFIRMED* (E-GJLV05-3). Printed: contraction Ψ on Θ = {|τ| < ‖K₁ − K₂‖_ρ}. the proof never shows that Ψ maps Θ into itself, and Θ is open; Ψ(0) can be as large as ‖T‖_ρ‖K₁ − K₂‖_ρ. Correction: use the closed ball of radius 2‖T‖_ρ‖K₁ − K₂‖_ρ. Evidence: Ψ(0) estimate in the proof. Effect: none on our statements; G2's proof uses the closed ball.
4. **p. 885, proof of Theorem 2.** *typo; CONFIRMED* (E-GJLV05-4). Printed: 0 < δ, ρ/2. should read 0 < δ < ρ/2. Evidence: context. Effect: none.
5. **p. 889, Prop. 18.** *typo; CONFIRMED* (E-GJLV05-5). Printed: Σ_(j=1)^n ω_j ∂v/∂θ_i = h; ‖v‖_(ρ−δ) ≤ c δ^(−σ) γ^(−1) ‖v‖_ρ. the derivative index should be θ_j, and the right-hand side norm should be ‖h‖_ρ. Evidence: the statement's own variables. Effect: none.
6. **p. 866, Theorem 6.** *typo (sign of an exponent); CONFIRMED* (E-GJLV05-6). Printed: |λ∞| < cγ²δ₀^{−2σ}‖e₀‖_{ρ₀}. wrong exponent: γ appears to the power +2; compare Theorem 1 (cγ^{−2}δ₀^{−2σ}) and Theorem 6’s own K-estimate with γ^{−2}; almost certainly γ^{−2} (the same issue as Theorem 3, E-GJLV05-1). Evidence: checked on the PDF page images by the helper. Effect: none on our use (GJLV05 is a cross-check).

### Deviations

1. **Theorem 2 (maps), §6, §8.** *proof supplement; PLANNED* (D-UNIQ-1). Proof supplement: local uniqueness modulo phase for flows. No published statement exists in this framework (GJLV05 Rem. 7: 'We do not formulate such a theorem'; HL19 Rem. 3.5 asserts it without proof). We prove it by adapting the map proof of GJLV05 §6 with the flow reducibility of §8 and Prop. 18, directly for flows (not through the time-one map, which needs map-Diophantine frequencies).. Proof written in blueprint Part 3: linearization at K₁ (not K₂), the phase fixed once by ⟨BLᵀ(K₂(·+ψ) − K₁)⟩ = 0, a uniqueness constant independent of γ (|ω| ≤ Γ from invariance, so γ ≤ Γ), the small-divisor exponent τ + n, and the conclusion on T_{ρ/2}. Effect: a gate theorem of our own; no source statement changes.


## FdlLS09 (arXiv:0903.0311v1)

### Errata

1. **p. 13, Theorem 3.14.** *typo; DROPPED* (E-FdlLS09-1). Printed: ρ^{−2ν} with δ = ρ/4. δ is introduced but unused; the bound presumably involves δ. Evidence: statement of Theorem 3.14. Effect: none.
2. **§7.1, pp. 42–43.** *gap; CANDIDATE* (E-FdlLS09-2). Printed: (measure conclusion of §7.1). a bi-Lipschitz map ω ↦ K_ω into a function space does not by itself give a Lipschitz inverse of (θ, ω) ↦ K_ω(θ); the measure conclusion needs the argument we supply (D-LIP-1, D-MEAS-1). Evidence: the Lipschitz constant ~γ⁻² of ω ↦ K_ω is not small relative to the unperturbed map. Effect: none on our statements; we do not use §7.1's conclusion.

### Deviations

None.


## CCdlL13 (doi:10.1016/j.jde.2013.05.001)

### Errata

1. **pp. 31–32 (preprint mp_arc 11-188).** *typo; CONFIRMED* (E-CCdlL13-1). Printed: (meaning of ℓ = 2). the two pages describe ℓ = 2 inconsistently. Evidence: pp. 31 vs 32. Effect: none.
2. **arXiv v1, Def. 4, p. 10.** *wrong hypothesis; DROPPED* (E-CCdlL13-2). Printed: "τ ≥ 1, ν ≥ 1" with |ωk − q| ≥ ν|k|^{−τ}. incompatible hypotheses: at k = 1 one needs ν ≤ 1/2, and the paper later uses ν ≈ 0.382. Evidence: competitors report §3.6 (conformal helper). Effect: none.
3. **arXiv v1, Lemma 3, p. 9.** *inconsistent constant; DROPPED* (E-CCdlL13-3). Printed: "C_{c,ℓ} = ℓ!(2π)^{−1}". inconsistent with C_c = 1 stated just above (it gives 1/(2π) at ℓ = 1); a disc-automorphism example gives a ratio near 1/2 as δ → 0; apparently unused in App. B. Evidence: competitors report §3.6 (conformal helper). Effect: none.
4. **(3.14).** *wrong strip in the conclusion; DROPPED* (E-CCdlL13-4). Printed: closeness stated on the strip ρ₀ − δ₀. gap: the proof schedule gives closeness on ρ∞ = ρ₀/2 = ρ₀ − 2δ₀; H5 allows any 0 < δ₀ < ρ₀ while the schedule fixes δ₀ = ρ₀/4. Evidence: competitors report §3.6 (conformal helper). Effect: none.

### Deviations

1. **Cor. 29–30.** *proof supplement; PLANNED* (D-LIP-1). Lipschitz dependence on the frequency by re-applying the a-posteriori theorem at a nearby frequency (CCdlL13 template), with the error estimate ‖E′‖ ≲ (ε + ‖K_ω − K⁰_ω‖_{C¹})·|ω − ω′| and Lipschitz defect O(ε/γ⁴); refinements: stability always relative to the unperturbed torus, phase controlled by the average normalization, far pairs above λ_*γ² (blueprint Part 4, V3). Effect: explicit constants of our own.


## HL19 (arXiv:1711.05515v1)

### Errata

1. **p. 18, (3.11).** *typo; CONFIRMED* (E-HL19-1). Printed: ‖K∞ − K‖_{ρ∞} < C₂‖E‖_ρ/(γ²ρ^{2τ}). the strict inequality is false when E = 0, where it would require ‖K∞ − K‖ < 0; it should read ≤. Evidence: with E = 0 the bound reads ‖K∞ − K‖ < 0, which no K∞ satisfies. Effect: none; G1 uses ≤.
2. **p. 42, (5.66).** *typo; CONFIRMED* (E-HL19-2). Printed: denominator σ_B − ‖B‖. in the estimate for the twist term the denominator should be σ_T − |⟨T⟩⁻¹|. Evidence: the left side of the same display (5.66) has σ_T − |⟨T⟩⁻¹|. Effect: none on the statements.
3. **p. 55, Lemma A.1.** *typo; CONFIRMED* (E-HL19-3). Printed: |M̄⁻¹ − M⁻¹| < 2σ²|M̄ − M|. false for M̄ = M (it would give 0 < 0); should be ≤. Also (A.3)'s '< ½' only follows with ≤. Evidence: take M̄ = M. Effect: none; our Neumann lemma uses ≤.
4. **p. 33, (5.15)–(5.18); p. 43, (5.68).** *typo; CONFIRMED* (E-HL19-4). Printed: strict inequalities in the step estimates. false when E = 0; should be ≤ (the origin of E-HL19-1). Evidence: E = 0. Effect: none.
5. **p. 42, after (5.67).** *typo; CONFIRMED* (E-HL19-5). Printed: "(5.12) and (5.16)". should refer to (5.13) and (5.17). Evidence: context. Effect: none.
6. **p. 44.** *typo; CONFIRMED* (E-HL19-6). Printed: "→ 0 when s → 0". should read s → ∞. Evidence: the iteration index grows. Effect: none.
7. **p. 44 vs Theorem 3.1 (p. 17).** *typo; DROPPED* (E-HL19-7). Printed: proof concludes dist(K∞(Tᵈ), ∂B) > 0; the theorem claims dist(K∞(Tᵈ_{ρ∞}), ∂B) > 0. the proof's concluding sentence states the margin on the real torus only, but (5.73) does control dist(K_s(T_{ρ_s}), ∂B) on the complex strips, so the theorem's strip margin is proved; the sentence on p. 44 misstates what (5.73) gives. Evidence: HL19 (5.73), p. 44 (blueprint Part 2 review, finding 3). Effect: none.
8. **p. 19, Theorem 3.6 (3.16).** *strict zero-error bound; CONFIRMED* (E-HL19-8). Printed: ‖K∞−K‖ρ∞ < C₂‖E_c‖ρ/(γ²ρ^(2τ)), |ω∞−ω| < C₃‖E_c‖ρ/(γ²ρ^(2τ)). Both strict estimates fail for exact input E_c=0; replace < by ≤. Extension of existing E-HL19-1 to the isoenergetic theorem. Evidence: An exact admissible torus makes both right sides zero; a norm cannot be strictly negative.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
9. **p. 18, (3.12), compared with p. 20 (4.1).** *sign; CONFIRMED* (E-HL19-9). Printed: X_h(K(θ)) = L_ω K(θ). The sign conflicts with L_ω=−Σω_i∂_i and with (3.14). Read X_h(K)=−L_ωK. Evidence: Substitution of an exact torus with nonzero frequency distinguishes the signs.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
10. **p. 19, Remark 3.7.** *sign; CONFIRMED* (E-HL19-10). Printed: Dh(K(θ))N(θ) = X_h(K(θ))ᵀ Ω(K(θ))N(θ). Insert a minus before X_hᵀΩN in the first equality; the subsequent sign and final ωᵀ row have the intended value. Evidence: ΩX_h=Dhᵀ and Ωᵀ=−Ω imply Dh=−X_hᵀΩ.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
11. **p. 59, Table 5 caption.** *cross-reference; CONFIRMED* (E-HL19-11). Printed: Constants introduced in Section 5.3. The table collects (6.45)–(6.51), hence Section 6.3. Evidence: Caption and formula labels read directly.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
12. **p. 53, (6.51), compared with p. 19 (3.16).** *constant normalization; CONFIRMED* (E-HL19-12). Printed: |ω∞−ω| < C₃‖E_c‖ρ/(γρ^τ), thus obtaining the estimates in (3.16). The same C₃ is attached to different powers of γρ^τ in (6.51) and (3.16); a uniform rescaling is necessary. This does not refute an existentially rescaled theorem. Evidence: Table 5 defines the (6.51) constant. No γρ^τ≤1 guard makes the displayed implication automatic.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
13. **pp. 49–51, (6.33), (6.36), (6.44).** *wrong error quantity; CONFIRMED* (E-HL19-13). Printed: ‖E‖ρ on the right sides of (6.33), (6.36), (6.44). Use the combined error ‖E_c‖ρ, including the prescribed-energy error; E alone cannot bound these corrections. Evidence: With E=0 and energy discrepancy e≠0, the bordered solve gives ξ₀ᴺ=−eω/|ω|², ξ^ω=e/|ω|²; a variable torsion gives nonzero L_ωξᴸ. For H=|I|²/2 the bordered inverse changes despite E=0. See audit §9.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
14. **p. 52, iteration convergence.** *limit-index typo; CONFIRMED* (E-HL19-14). Printed: when s → 0. The iteration number s tends to infinity. Separate occurrence from existing E-HL19-6 on p. 44. Evidence: The preceding bound is a₁^(−4τs)‖E_c‖, a₁>1.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
15. **p. 52, frequency-margin paragraph.** *cross-reference; CONFIRMED* (E-HL19-15). Printed: the eight term in (6.15). The eighth term is in the maximum (6.16), not the pair of inequalities (6.15). Evidence: Compare p. 49 explicit eighth-term reference to (6.16).. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
16. **p. 46, (6.9), constant term under the cohomological inverse.** *alleged omitted term; DROPPED* (E-HL19-16). Printed: ξᴸ = R_ω(ηᴸ − Tξᴺ). DROPPED as an erratum: omitting the constant ω̂ξ^ω inside R_ω is harmless because R_ω annihilates constants. The full zero-average compatibility condition is still required. Evidence: Part 1 borderline solve and the zero-mode definition of R_ω.. Effect: Keep explanatory compatibility calculation; no source correction required..
17. **p. 19, H5′.** *boundary convention / missing qualification; CANDIDATE* (E-HL19-17). Printed: Notice that, by definition, we have dist(ω, ∂Θ) > 0.. For ambient boundary in R^d, d≥2, a ray has empty interior and every point lies on its boundary. Specify relative boundary in its line, equivalently endpoint distances. Evidence: Direct topology check; frozen ν is explicitly the distance to the two endpoints.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
18. **§5.3, p. 43, with Lemma 4.1.** *gap; CONFIRMED* (E-HL19-19). Printed: "taken to be the same for all steps by considering the worst value of δ_s, that is, δ₀". conditional uniformity gap: freezing c_R at δ₀ is justified for a uniform c_R, but Lemma 4.1 also permits a δ-dependent c_R(δ), which need not be bounded by its value at δ₀; a uniform-in-later-bites bound or stage-specific constants are needed. Evidence: blueprint remark bp:p2s2sd:errata (branch sharp-v2). Effect: none for a uniform c_R (as HL19 state for Rüssmann’s constant); the v2 engine uses each stage's own constant.

### Deviations

1. **§3.1 (analytic functions and norms).** *convention / reformulation; PLANNED* (D-NORM-1). Estimates are carried out in weighted ℓ¹ Fourier(–Taylor) coefficient norms instead of sup norms on complex strips; hypotheses are stated for real-analytic functions and converted once at the interface. Effect: constants differ from the printed ones; the frozen statements carry their own explicit constants or are qualitative.
2. **§2 (Hamiltonian systems and invariant tori).** *specialization; PLANNED* (D-COORD-1). Phase space Tⁿ × B is represented in coordinates: angles in ℝⁿ with ℤⁿ-periodicity, actions in an open set of ℝⁿ (no manifold structure, no general symplectic form). Effect: the general exact-symplectic setting of the source is specialized to the standard form on Tⁿ × ℝⁿ.
3. **Theorem 3.1, pp. 16–18; App. B (5.74)–(5.77).** *reformulation (uniform constants); PLANNED* (D-G1-1). Uniform constants: C₁, C₂ depend only on n, τ, ρ, ρ∞, a bound M for the Hamiltonian's derivatives, σK, σB, σT, a margin μ (gaps σ − ‖·‖ and distance to the boundary) and an upper bound γbar ≥ γ (App. B's constants increase with γ; without γbar the statement is false: machine-checked counterexample). Dropped hypotheses implied up to 2n factors: σ_{Kᵀ}, c_{X_hᵀ,1}; first integrals and the estimate on ⟨c∘K∞⟩ not transcribed. Pointwise operator norms on the open strip instead of sums of sups on the closed strip. Conclusion strengthened to explicit margins (μ/2) and ≤ in the closeness bound (cf. E-HL19-1). Same uniformization in our G2, where no γbar is needed: invariance with H2–H3 bounds |ω|, hence γ; note: the hypotheses bound the frequency, γ ≤ |ω| ≤ 2nσ_Kσ_B(M + e), so γ̄ is needed only because the smallness condition alone does not bound e (Part 2 uses γ̄ once, to force e ≤ 1). Effect: G1 as drafted v0.2; G2.
4. **§2.2, p. 7, eq. (2.3).** *proof supplement; PLANNED* (D-LAG-1). Proof supplement: the isotropy (Lagrangian property) of invariant tori with nonresonant frequency, asserted as well known, is proved in blueprint Part 4 (lemma lagrangian), citing GJLV05 Lemma 19. Effect: none on statements.
5. **Theorem 3.6; frozen I-G1.** *scope / quantified uniformity; ADOPTED* (D-I-G1-UNIFORM). Uniformize constants over fixed strip/ray/margin bounds, including γ̄, ν and ω*, rather than silently reusing source pointwise constants. Evidence: docs/tracks/I/AUDIT-statements-v0.1.md §9; blueprint-I/reviews/p1-review-1.md and p2-review-1.md. Effect: Constants C₁,C₂,C₃ precede the variable Hamiltonian, torus and error; no theorem premise is added..
6. **Theorem 3.6; frozen I energy class.** *scope / convention; ADOPTED* (D-I-ENERGY). Use the physical energy h, pointwise strip bounds and a bordered extended torsion in the frozen convention. Evidence: docs/tracks/I/AUDIT-statements-v0.1.md §9; blueprint-I/reviews/p1-review-1.md and p2-review-1.md. Effect: Specialized isoenergetic theorem and corrected combined error..
7. **blueprint-I Part 1 geometry-noA5 / perturbation-noA5.** *proof supplement / reformulation; PLANNED* (D-I-NOA5). Restate and prove geometry/perturbation helpers without track K admissibility A5, using only their actual analytic/matrix premises. Evidence: blueprint-I/reviews/p1-review-1.md and round2-closure.md; blueprint-I/parts/p1-iso-linear.tex. Effect: Avoid importing a stronger unrelated theorem hypothesis into I-G1..
8. **p. 46 Lemma 6.1 and source Lemma 5.1; I Part 1.** *proof supplement / reformulation; PLANNED* (D-I-LINEAR-SOLVE). Supply the full bordered zero-mode and cohomological solve, including the energy identity and signs, rather than invoke analogy and an external Lemma 5.1 proof. Evidence: blueprint-I/parts/p1-iso-linear.tex; blueprint-I/reviews/p1-review-1.md. Effect: A proof supplement to true linear algebra; the constant omitted under the cohomological inverse is not itself an erratum..


## Nek77 (doi:10.1070/RM1977v032n06ABEH003859)

### Errata

1. **pp. 56 and 58 (§12).** *typo; CONFIRMED* (E-P-A-N77-1). Printed: compactness lemma printed as 12.3.A, cited as 12.4.A. the same compactness lemma is printed with one label and cited with another; numbering only. Evidence: p. 56 label vs p. 58 citation. Effect: none; cite by page and title.
2. **p. 56, (12.6).** *typo; CONFIRMED* (E-P-A-N77-2). Printed: T = (1/2) Σ mᵢ (ẋᵢ²/2). duplicate factor 1/2 in the kinetic energy; the momentum formula (12.8) Pᵢ = mᵢẋᵢ + mᵢΣmⱼẋⱼ on the same page follows from T = (1/2) Σ mᵢ ẋᵢ². Evidence: differentiate both candidate kinetic energies and compare with (12.8). Effect: none; the frozen moving Hamiltonian matches LP17 (5)–(6) independently.
3. **p. 15, §1.18.** *typo; CONFIRMED* (E-N-ADD-1). Printed: "the perturbation H−H₀ becomes small". when two bodies approach one another the reciprocal-distance interaction grows; the sentence should read 'ceases to be small'. Evidence: context of §1.18 (angular-momentum discussion). Effect: none; not used as an analytic assumption.

### Deviations

1. **§12, Theorem 12.3, pp. 55–56.** *specialization; ADOPTED* (D-P-A-1). P-EXP-SAFE specializes Theorem 12.3 to the planar problem with G = m₀ = 1, fixed positive planetary weights, planar prograde data in an explicit separated-annulus low-AMD region (AMDBox), with a symmetric exponential window and explicit uniqueness, Newton-equation and relative-distance conclusions; canonical element transfer is proof work. Evidence: docs/tracks/P/REVIEW-additions.md. Effect: owner-approved D25 (Q-P-A1, Q-P-A2).
2. **Theorem 4.4 p. 30, Remarks 4.5.A–B.** *proof supplement / reformulation; ADOPTED* (D-N-ADD-1). N-PARTIAL-CONVEX states the stopped theorem for Hamiltonians convex in the fast actions, with hypotheses on an enlarged fast domain G′ ⊇ G + (real ρ-ball) and conclusions for initial fast actions in G; the steepness of the source is obtained by an explicit convex specialization of its proof, not by a verbatim import (the naive import fails at ∂G: audit F-NADD-1). Evidence: docs/tracks/N/REVIEW-additions.md; AUDIT-additions-v0.3.md §3. Effect: owner-approved D25 (N questions 1–2).
3. **§§4,10 versus D25 partial convexity.** *scope restriction; ADOPTED* (D-N-ADD-3). Specialize to a definite fast Hessian with global sign on an enlarged convex fast domain, fixed h and explicit complex Hessian bound. Evidence: docs/tracks/N/notes.md D-N-ADD-3; D25. Effect: Do not claim the full steep/quasi-convex source generality..
4. **D25 stopped partial theorem.** *representation; ADOPTED* (D-N-ADD-4). Use max norms, closed erosion and queried histories, normalized perturbation and positive μ bound, with explicit conversion of non-strict inequalities. Evidence: docs/tracks/N/notes.md D-N-ADD-4; D25. Effect: Source Euclidean domains and stopping conventions require proof-level conversion..
5. **§10 Lemma 10.6 endpoint specialization.** *convex proof specialization; ADOPTED* (D-N-ADD-6). Use the direct definite-Hessian endpoint argument and explicit G′ collar instead of asserting source-global steepness on arbitrary bounded G. Evidence: docs/tracks/N/AUDIT-additions-v0.4-delta.md; D25. Effect: Refines the proof specialization already covered in existing D-N-ADD-1; not an extra source erratum..
6. **§10 and blueprint-N Part 11.** *proof supplement / reformulation; PLANNED* (D-N-PARTIAL-ROUTE). Attempt an independent extended normal form and frequency-free convex energy argument, advertising 1/(2n) only after proof. Evidence: blueprint-N/reviews/p11-review-1.md; Nek77 first-page announcement and §10; D25 unchanged. Effect: UNVERIFIED strengthening: p11-review-1 N11-01 identifies use of a Cauchy estimate outside its valid tube. Our blueprint error is not a source erratum. Acquisition of Nek79II is an alternative, not mathematical necessity..


## LP17 (arXiv:1703.07125v2)

### Errata

1. **p. 17, between (B.9) and (B.10).** *typo; CONFIRMED* (E-P-A-LP17-1). Printed: {F, H₀} = 0. F is not introduced in that argument; the surrounding brackets use the integral K, so it should read {K, H₀} = 0. Evidence: rendered page. Effect: none; the frozen statements use only (B.5), (B.8) and rotational invariance.

### Deviations

1. **(B.5), (B.8), App. B.** *specialization / new result; ADOPTED* (D-P-A-2). P-SECULAR-BOX uses the raw untruncated full average over both mean longitudes in the fixed zero-coupling chart, implemented through the eccentric-longitude integral with its Jacobian, and a new elementary rational box at cited decimal masses; it is a statement about the averaged model, not the full Newtonian problem. Evidence: docs/tracks/P/REVIEW-additions.md. Effect: owner-approved D25 (Q-P-A4, Q-P-A5).
2. **P Parts 7/8, D25 secular definitions.** *proof supplement / reformulation; PLANNED* (D-P-SECULAR). Identify moving/fixed secular functions exactly to all orders up to the action-only term, rather than infer equality of full germs from a quadratic match. Evidence: blueprint-P/reviews/p8-review-1.md; LP17 Hamiltonian (5)–(6). Effect: Transport frozen secular definitions and jets in the exact canonical chart..


## Chi05 (pinned PDF)

### Errata

1. **pp. 13–14, (3.38)–(3.39); compare p. 17 phase-space description.** *missing domain exclusion; CONFIRMED* (E-Chi05-1). Printed: (x^(2), X^(2)) ∈ R² minus {0} × R². The printed domain also includes the secondary collision x^(2)=x_circ^(1)(t), where the displayed potential is singular if m₁>0. Exclude it. Evidence: x_circ^(1)(t) has unit length, is nonzero and belongs to the printed domain; the secondary denominator vanishes.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **pp. 13–16, (3.38)–(3.43).** *alleged truncation; DROPPED* (E-Chi05-2). Printed: H̃₂ := H̃₁ ◦ φ̂_D. DROPPED: the allegation that these formulas are only a first-order truncated Hamiltonian is false. The coordinate changes are exact; CC03 separately labels its approximation. Evidence: Fresh comparison of (3.38)–(3.43); blueprint-I/reviews/p67-review-1.md.. Effect: Use exact restricted Hamiltonian; do not attribute a truncation erratum to Chi05..

### Deviations

1. **§2 versus frozen I-KEPLER.** *scope / parameterization; ADOPTED* (D-I-KEPLER). Allow general positive Kepler parameter and rotation rate, and prove the action mean identities explicitly. Evidence: docs/tracks/I/statement.md; blueprint-I/parts/p6-kepler.tex. Effect: Frozen κ,Ω parameter order retained..
2. **§3 versus frozen I-R3BP.** *physical reformulation; ADOPTED* (D-I-PHYSICAL). Use the exact barycentric restricted Hamiltonian, collision-free annuli, μ=0 endpoint, uniform μ₀≤1/2 and physical uniqueness/solution transfer. Evidence: docs/tracks/I/statement.md; blueprint-I/parts/p7-delaunay.tex and p8-r3bp.tex. Effect: No first-order truncation stands in for the physical Newtonian system..
3. **p. 11 analytic Kepler equation; blueprint-I Part 7.** *proof supplement / reformulation; PLANNED* (D-I-KEPLER-TUBE). Supply an explicit complex tube with an eccentricity-dependent displacement guard and verify every chart consumer; the source qualitative small-|e| assertion is not false. Evidence: blueprint-I/reviews/round2-closure.md; blueprint-I/parts/p7-delaunay.tex. Effect: Uniform analytic chart through e=0 without claiming a global inverse on an unrestricted complex strip..


## CC03 (doi:10.1090/memo/0878)

### Errata

1. **p. 7, Theorem 1.1 closing sentence.** *scope clarification; CANDIDATE* (E-CC03-1). Printed: A similar statement holds if ε_SJ is replaced by any complex perturbative parameter ε with |ε| ≤ 10⁻³.. Scope ambiguity: nonreal ε generally does not define a real Hamiltonian flow. Clarify whether the similar statement complexifies phase space and invariance, or restrict a physical-flow version to real ε. Evidence: Rendered p. 7 checked. The phrase “similar statement” may intend complexified objects, so no unconditional refutation is asserted.. Effect: Unused comparator; no blocker for frozen track I..

### Deviations

1. **Theorem 1.1 versus frozen I-HEAD.** *different theorem / proof route; ADOPTED* (D-I-CONFINEMENT). Prove a general all-initial-point two-degree-of-freedom confinement theorem through energy charts, Diophantine barriers and continuation, rather than reuse one computer-assisted fixed-energy region. Evidence: docs/tracks/I/statement.md; blueprint-I/parts/p3-iso-local-charts.tex and p5-confinement.tex. Effect: New qualitative uniform confinement proof; no CC03 numerical bounds imported..


## BM11 (arXiv:1004.1014v2)

### Errata

1. **p. 5, Theorem 2.1.** *zero-endpoint convention; DROPPED* (E-N-BM-1). Printed: |f|_s < ε; 0 ≤ ε ≤ ε₀. DROPPED as a false-theorem allegation: at ε=0 the strict size premise is empty. An explicit integrable supplement is a useful reformulation, not a counterexample to this implication. Evidence: Strict |f|_s<0 cannot hold; distinguish this from a non-strict theorem genuinely admitting ε=0.. Effect: D-N-3 records the separate zero case..
2. **p. 9, Lemma 3.3.** *missing parameter margin / notation; CONFIRMED* (E-N-BM-2). Printed: there exist stable constants ρ₀ and C; B(Ψ_h(I₀), Cρ). A uniform image-ball radius cannot be independent of an unrestricted λ₀>0 in Ψ_h(I,λ)=(h(I),λω(I)); the centre also suppresses λ₀. Retain the pointwise inverse theorem or restrict λ₀ quantitatively. Evidence: For h(I)=|I|²/2+v·I, transverse frequency directions contract proportionally to λ₀, so no fixed C>0 works as λ₀→0.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
3. **p. 13, restart argument.** *missing boundary margin in inference; CONFIRMED* (E-N-BM-3). Printed: taking ε₀ small enough, we can ensure that I(t*) ∈ B(0,R/2). A displacement bound independent of the distance of I₀ to the boundary does not imply restart in the same inner ball for all I₀∈B(0,R/2). Evidence: Choose I₀ within less than the allowed outward displacement of ∂B(0,R/2). A larger-domain resonant contract supplies the repair; this refutes the printed implication, not Theorem 2.1.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
4. **p. 8, Pos93 import; compare p. 4 B(M).** *missing import hypothesis; CONFIRMED* (E-N-BM-4). Printed: exactly the content of Theorem 3. Real-slice derivative bounds B(M) do not supply the uniform complex Hessian bound required by that literal Pos93 import. Additional analytic control or a different proof is needed. Evidence: h_N=3I₀+|I|²/2+sin(NI₁)/(4N³) has uniformly bounded real derivatives through order 3 but no uniform complex Hessian on a fixed strip. No counterexample to the headline BM theorem is claimed.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
5. **p. 12, resonant integer vector.** *missing guard / type typo; CONFIRMED* (E-N-BM-5). Printed: k′ = q e_i − p e_j ∈ Z; maximal since p and q are coprime. Require k′≠0 before deducing primitivity: i=j and p=q=1 give zero despite coprimality. The ambient integer set is Z^n. Evidence: Choose a strictly interior approximating rational excluding the degenerate coincidence and recheck numerical constants.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..

### Deviations

1. **docs/tracks/N/statement.md, deviation D-N-1.** *scope; ADOPTED* (D-N-1). Restrict the selected quasi-convex theorem to n≥3, while supporting local lemmas explicitly quantify their own dimensions. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
2. **docs/tracks/N/statement.md, deviation D-N-2.** *size convention; ADOPTED* (D-N-2). Replace strict perturbation size by a non-strict pointwise upper bound and absorb a fixed factor in thresholds. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
3. **docs/tracks/N/statement.md, deviation D-N-3.** *endpoint reformulation; ADOPTED* (D-N-3). Separate ε=0 and prove the integrable orbit for all times; do not evaluate positive-time formulas at a zero denominator. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
4. **docs/tracks/N/statement.md, deviation D-N-4.** *ODE strengthening; ADOPTED* (D-N-4). Conclude genuine closed-interval solution existence and uniqueness as well as drift; impose the explicit constant margin C ε₀^(1/(2n))≤R/4. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
5. **docs/tracks/N/statement.md, deviation D-N-5.** *representation; ADOPTED* (D-N-5). Spell out all typing, real analytic regularity, guarded domains and Lean-totality cases. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
6. **docs/tracks/N/statement.md, deviation D-N-6.** *local reformulation; ADOPTED* (D-N-6). Use the pointwise inverse-function conclusion on a general open set instead of the unrestricted λ-uniform ball assertion. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
7. **docs/tracks/N/statement.md, deviation D-N-7.** *endpoint / solution convention; ADOPTED* (D-N-7). Select only the classical stability endpoint; no improved tradeoff, fixed-radius second clause, Gevrey extension or optimality claim is frozen. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..


## GCB16 (arXiv:1403.6776v1)

### Errata

1. **p. 4, main stability theorem.** *endpoint convention; CANDIDATE* (E-N-GCB-1). Printed: 0 ≤ ε < ε₀; T/√ε exp(c/ε^a). The ε=0 time expression needs an explicit integrable all-time convention or separate zero branch. This is an undefined endpoint in the literal real formula, not a refutation for positive ε. Evidence: The printed parameter interval includes zero and the time uses negative powers.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **p. 3, quasi-convex steepness sentence.** *index typo; CONFIRMED* (E-N-GCB-2). Printed: α₁ = ··· = α_n = 1. The steepness indices run through n−1; the last subscript should be n−1. Evidence: Compare the steepness definition on the same page.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
3. **p. 3, footnote 5.** *index typo; CONFIRMED* (E-N-GCB-3). Printed: |u| = Σ_i |u₁|. The summand of the intended ℓ¹ norm must be |u_i|. Evidence: As printed, a vector with u₁=0 and another nonzero coordinate has zero size.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..

### Deviations

None.


## Pos93scan (doi:10.1007/BF03025718)

### Errata

1. **printed p. 190 (PDF p. 5), explanatory norm sentence.** *false complex norm identification; CONFIRMED* (E-N-POS-1). Printed: For the symmetric operator Q this norm amounts to the spectral radius norm.. Restrict this equality to real symmetric Q. It is false for arbitrary complex symmetric Hessians on V_(r₀)P; retain the operator norm in the preceding hypothesis. Evidence: Q=[[i,1],[1,−i]] is symmetric, nonzero, and Q²=0. Its spectral radius is zero but its operator norm is positive.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **printed p. 194 (PDF p. 9), end of Case B.** *exponent-sign misprint; CONFIRMED* (E-Pos93-1). Printed: ≤ e^(Ks/6) ε. The concluding target has lost its minus sign; the preceding calculation gives e^(−Ks/6)ε. The printed plus-sign upper bound is weaker and true, but does not express the intended remainder estimate. Evidence: Rendered scan read; compare the first line of the display and Normal Form Lemma target.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
3. **printed p. 195 (PDF p. 10), final telescoping display.** *unverified estimate allegation; CANDIDATE* (E-Pos93-2). Printed: |W₀(DΨ−I)W₀⁻¹| ≤ 2qε₀/(αρ₀σ₀). The stated derivative bound is questioned: later iteration scales introduce ρσ/(ρ₀σ₀)=3/(2N²). The blueprint supplies componentwise bounds instead. No violating map has been established, so the mathematical defect remains unverified. Evidence: Printed display and scale arithmetic checked. Failure of the coarse telescoping estimate alone does not disprove the sharper bound.. Effect: Do not use the questioned derivative constant; use proved componentwise displacement and separate preimage arguments..
4. **printed p. 197 (PDF p. 12), Proposition 1 small-Ks branch.** *misattributed remainder claim; DROPPED* (E-Pos93-3). Printed: For Ks < 6. DROPPED: the source does not assert the Normal Form Lemma exponential remainder bound for the identity map in this branch. It proves Proposition 1 directly by the original vector field. Evidence: The direct speed estimate and |t|≤sr e^(Ks/6)/(5ε) give the claimed bound when Ks<6.. Effect: Use iterative-direct / direct-speed branch; no factor-e degradation or source correction needed..
5. **printed p. 199 (PDF p. 14), Lemma 2 proof.** *unverified printed inference / missing proof guard; CANDIDATE* (E-Pos93-4). Printed: |⟨ω(I(s)), PΔI⟩| ≤ (5/4)δ‖ΔI‖. The cited projected-frequency closeness was established only on U_ρD, while this segment may run to r−ρ. The printed inference is unsupported without further control; a sufficient repair is Mr≤ℓ/4 in the energy lemma and Mr≤ℓ/2 in Proposition 2. Evidence: Fresh scan pp. 198–200: mean value gives ‖Pω(I(s))‖≤5δ/4+M‖I(s)−I₀‖, not the quoted bound on the entire segment. The headline lemma might admit another proof.. Effect: Use repaired helper. Full-rank block r=r₀ additionally needs r₀≤ℓ/(2M); non-full blocks satisfy the bound using A=11M/m and K≥1..
6. **printed p. 200 (PDF p. 15), Proposition 2 small-Ks branch.** *proof-margin allegation; DROPPED* (E-Pos93-5). Printed: Ks < 6. DROPPED as a demonstrated false source statement: the half-radius issue is a proof-margin/transfer obligation, not a refutation of the proposition. Record the explicit smaller-radius argument as a supplement. Evidence: Part 7 review distinguishes an unpaid imported radius from a false source conclusion.. Effect: D-N-POS-TRANSFER supplies the smaller-radius and preimage arguments..
7. **printed p. 204 (PDF p. 19), choice A=11M/m.** *alleged constant failure; DROPPED* (E-Pos93-6). Printed: A = 11M/m. DROPPED: the alleged failed numerical domination ignores m≤M at a nonempty real point in dimension at least two. With that comparison the inequality used in the proof holds. Evidence: For q=9,p=9/8,b=1/8, p/b=9 and 11(M/m)≥9(M/m)+√2 if M/m≥1.. Effect: Supply the elementary Hessian comparison; separate empty-domain cases in our theorem..
8. **printed p. 214 (PDF p. 29), Lemma B.3 proof, action Cauchy formula.** *Cauchy denominator typo; CONFIRMED* (E-Pos93-7). Printed: u_(I_i) = (1/(2πi)) ∫_γ u(I+ζ,θ)/ζ dζ. The derivative formula needs ζ² in the denominator; the printed integral with ζ returns u itself. The next integral estimate needs the corresponding derivative kernel. Evidence: For u≡1 the printed derivative identity reads 0=1. Scan rendered and checked independently.. Effect: The blueprint uses the correct ζ⁻² kernel; no frozen change..

### Deviations

1. **docs/tracks/N/statement.md, deviation D-N-8.** *approved stronger analytic input; ADOPTED* (D-N-8). Introduce separately named N-HEAD-C with a uniform complex Hessian bound and positive frequency lower bound; do not alter original N-HEAD. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
2. **docs/tracks/N/statement.md, deviation D-N-9.** *quantified guards; ADOPTED* (D-N-9). Allow N-QC and N-ZERO in all dimensions by removing unused hypotheses, including the n=2 instances needed by track I; headline dimension restrictions remain separate. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
3. **docs/tracks/N/statement.md, deviation D-N-10.** *norm / period conversion; ADOPTED* (D-N-10). Convert source Euclidean/2π/Fourier norms to frozen max/period-one pointwise norms, paying coth and √n factors and time prefactors. Evidence: docs/tracks/N/notes.md and AUDIT-statements-v0.1.md §9. Effect: Frozen contracts stay literal; source conversions are provider obligations..
4. **pp. 196, 199–200; N Parts 3/7.** *proof supplement / reformulation; PLANNED* (D-N-POS-TRANSFER). Supply near-identity preimage surjectivity by contraction, stopped transfer, periodic continuation, first exit and the explicit half-radius small-Ks argument. Evidence: blueprint-N/parts/p3-hamiltonian-ode.tex and p7-stability.tex; reviews/p7-review-1.md. Effect: These missing explanations of true steps are proof supplements, not errata..
5. **pp. 200–204; N Parts 8/9.** *proof supplement / reformulation; PLANNED* (D-N-POS-GEOMETRY). Use explicitly saturated Euclidean resonance lattices, distinguish K_a and K_g=√n K_a, and prove lattice volume, primitive-line and covering inequalities. Evidence: blueprint-N/reviews/p8-review-1.md and p9-review-1.md; blueprint-N/parts/p8-resonance-geometry.tex. Effect: Pay the √n analytic cutoff/time loss instead of silently interchanging ℓ¹ and Euclidean balls..
6. **pp. 211–215 Appendices B–C; shared N Parts 4/5.** *proof supplement / reformulation; PLANNED* (D-N-LIE-SERIES). Prove weighted Fourier/domain/norm conversions, the flow and composition identity explicitly with η≤1/2, and propagate the stronger smallness into normal-form iterations. Evidence: blueprint-N/reviews/p45-review-1.md; blueprint-N/parts/p4-weighted-norms.tex and p5-canonical-maps.tex. Effect: Equality of the convergent Lie series and composition is a true step needing a proof, not an erratum; choose the bracket sign consistently with the homological equation..


## Nei76 (pinned PDF)

### Errata

1. **p. 1298, (17), with z(t) on p. 1297 and h in (4) p. 1295.** *false sup/integral identity in proof; CONFIRMED* (E-NAVG-NEI-17). Printed: sup_(0≤t≤ε⁻¹) z(t) = ∫_(U′) h dI⁰ dφ⁰ < K₁√ε. The equality interchanges supremum and initial-data integration. Only sup_t∫error≤∫sup_t error is automatic; the fixed-time Gronwall bound does not establish the required mean maximum. Evidence: All four pinned pages read; (17) rendered. On two equal-measure data groups with errors peaking at different times, the two sides differ. This is not a counterexample to the averaging theorems.. Effect: D-NAVG-3 records the explicit maximum-envelope/cohort repair; it remains a proof obligation..

### Deviations

1. **pp. 1295–1298; averaging v0.5.** *proof supplement / reformulation; ADOPTED* (D-NAVG-1). Analytic Hamiltonian specialization, equal action/angle dimensions n≥2, fixed h,f,K before constants, period one, max norms and actual ODE solutions. Evidence: docs/tracks/N/notes.md v0.5 D-NAVG-1. Effect: Conservative specialized averaging statements; no proof receipt. Adopted with the owner-approved statements (D28)..
2. **p. 1296, condition 3°; AKN06 p. 243.** *proof supplement / reformulation; ADOPTED* (D-NAVG-2). Replace a single nonzero first-frequency-component ratio chart by intrinsic projective-rank geometry and a quantitative finite chart cover. Evidence: docs/tracks/N/notes.md v0.5 D-NAVG-2. Effect: Prove compact transversality estimates; AKN already states the intrinsic alternative. Adopted with the owner-approved statements (D28)..
3. **(17) and averaging v0.5 repair.** *proof supplement / reformulation; ADOPTED* (D-NAVG-3). Apply Gronwall to the integral of the running maximum using a Fourier envelope; construct actual-exit cohorts explicitly. Evidence: docs/tracks/N/notes.md v0.5 D-NAVG-3. Effect: Repairs the invalid sup/integral exchange. Not independently certified as a complete averaging proof in this task. Adopted with the owner-approved statements (D28)..


## CP10pin (doi:10.3934/dcdss.2010.3.545)

### Errata

1. **pp. 547, 551, 561, ball conventions.** *domain convention; DROPPED* (E-P-CP10-DOMAIN). Printed: ball. DROPPED as a mathematical erratum: conventions need a precise product-domain dictionary, but the word ball alone does not establish a false theorem. Frozen product discs are a disclosed choice. Evidence: The source uses several block norms; the chosen cylinder/disc conventions are recorded in D-PG-3.. Effect: Use explicit product discs, no silent norm conversion..
2. **p. 556, Step 1, extension of the frequency diffeomorphism.** *missing boundary hypothesis; CONFIRMED* (E-P-CP10-INV). Printed: Without loss of generality. Invertibility on an open V need not extend uniformly to V_ρ₀ at its boundary. A neighborhood of cl V with a quantitative inverse bound is an extra assumption or localization. Evidence: h(I)=I^16/16 on (0,1) has invertible real Hessian there but degeneracy at the boundary. The frequency sublevel near zero scales as γ^(1/15), not γ.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
3. **p. 561, after (56).** *missing boundary regularity; CONFIRMED* (E-P-CP10-BOUNDARY). Printed: meas (V_ρ₀ minus V) ≤ C γ̄₂. An arbitrary bounded open set need not have a linear boundary-collar volume estimate. Add a boundary regularity/collar hypothesis or localize to interior boxes. Evidence: A bounded open comb with many increasingly narrow gaps gives collar volume decaying more slowly than its thickness. Frozen hboundary is a disclosed repair.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
4. **p. 561, (56); compare p. 559 (47).** *wrong dimension exponent; CONFIRMED* (E-P-CP10-ANNULUS). Printed: ε^(n₂/2). For the positive rectangular action shell the excluded fraction is 1−(1−c√ε)^n₂, asymptotic to n₂c√ε, rather than O(ε^(n₂/2)) when n₂≥2. Evidence: Elementary product-volume calculation with c=check c₁/check c₂. The final O(√ε) rate is unaffected; a signed ambient action ball additionally changes normalization.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
5. **p. 564, conclusion for Theorem 1.5.** *unverified saturation inference; CANDIDATE* (E-P-CP10-WHOLE). Printed: K = K* ∩ P_(c₂ε). The operation of intersecting a torus family with a cylinder alone does not prove saturation by whole invariant tori. The stronger containment/subfamily selection used by P needs a proof supplement. No actual violating CP10 family has been established. Evidence: An intersection of an invariant set with an arbitrary cylinder need not be invariant; this logical observation is not itself a counterexample to this particular constructed family.. Effect: D-P-CELL records whole-torus selection; do not count bare intersection as a proof of frozen saturation..
6. **p. 554, Proposition 3 definition of Û.** *dimension typo; CONFIRMED* (E-CP10-1). Printed: n × n₁ submatrix; Û_ij=U_ij for n₁+1≤i≤n, 1≤j≤n. The index ranges define the last n₂ rows, an n₂×n matrix, not n×n₁. Evidence: Read definition against the block Hessian estimates.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
7. **p. 565, Lemma B.1 initialization.** *initialization typo; CONFIRMED* (E-CP10-2). Printed: M̂₀ := M. Initialize the slow Hessian bound by M̂, not M, consistently with Proposition 3. Evidence: The slow-scale radius in (73) depends on M̂_j.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
8. **p. 566, B.1(i), frequency-map composition.** *map-index typo; CONFIRMED* (E-CP10-3). Printed: ω_(j−1)⁻¹ ◦ ω_(j−1). This is the identity and has the wrong target domain. Read ω_j⁻¹ ◦ ω_(j−1), as the one-step construction on p. 568 does. Evidence: Typed domains D_(j−1)→D_j and the conjugacy of frequencies identify the corrected order.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
9. **p. 555 (35), slow displacement; p. 572 (107).** *unverified estimate mismatch; CANDIDATE* (E-CP10-4). Printed: |v₂(·;ω)−I₂⁰(ω)| ≤ 10n(M̄₂/M̄ + M̂/M) Êρ̂. The printed slow M̂/M refinement is not obtained by the displayed one-step estimate (107). Replacing that ratio by 1 gives the bound actually reconstructed. This is an unverified sharper-estimate allegation, not a supplied counterexample. Evidence: The separate normalization M̄_i≤M̄ in (74) can be ensured by compatible choices of bounds and is not an intrinsic obstruction.. Effect: Use the independently proved two-scale bounds with stated compatible constants..
10. **p. 551, norm conventions and Appendix B estimates.** *unverified blanket norm allegation; CANDIDATE* (E-CP10-5). Printed: |I|₁, |φ|∞, |p|∞, |q|∞. Mixed norms are explicit, but the blanket allegation that the printed constants cannot all hold has no supplied failing inequality in those norms. The same-constant Kirszbraun step also needs its Euclidean conversion checked, not merely a change of norms asserted. Evidence: P3 review E5/E10 qualifies the accusation. Our max-norm McShane replacement and larger constants are deviations.. Effect: Do not represent incompatible-looking norms as a proved counterexample; use D-P-NORM..
11. **p. 555, Proposition 3.** *missing normalization; CONFIRMED* (E-CP10-6). Printed: a unique real–analytic embedding. Without phase normalization the embedding is not unique: φ_ω(θ+a) has the same torus, frequency, analyticity and equations. Evidence: Translation of the parameter torus preserves every listed invariant-torus condition.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
12. **p. 555, Proposition 3 global parameter Lipschitz claim; Appendix B.** *missing global-domain control; CONFIRMED* (E-CP10-7). Printed: the map (ϑ;ω) → φ_ω(ϑ) is Lipschitz and one–to–one. An arbitrary unbounded disconnected D does not give a global inverse-Lipschitz frequency map from a bounded inverse differential. At f=0 this can obstruct the claimed global parameter Lipschitz map. Evidence: Take separated action islands near j² with local h′(I)=I−j²+j, h″=1. The frequencies lie near j but action distances grow quadratically; nonresonant centers can be chosen with uniformly separated fractional part. Local bounds are uniform but the inverse is not globally Lipschitz.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
13. **p. 565, (70) and its two following sums.** *wrong mode set; CONFIRMED* (E-CP10-8). Printed: Σ_(|k|≤K̄, k∈Λ) f_k(u)/(i k·ω(I)) e^(ik·φ). The sums must run over k∉Λ, including (0,k₂)∉Λ in the slow part. Retained resonant modes are not divided by their divisors. Evidence: For Λ={0} the printed sum includes division of the zero mode by zero and removes no nonresonant mode; compare (64) and g₊−g=Π_ΛT_K f.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
14. **p. 564, Lemma A.1 (66).** *wrong target strip; CONFIRMED* (E-CP10-9). Printed: φ: W_(v−2ν,s−2σ) → W_(v,σ). The target angular width should be s, not σ. Evidence: Set f=g=0. The map is the identity and cannot send all of width s−2σ to width σ when s>3σ.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
15. **p. 563, Theorem 1.5 proof Step 1; compare p. 564 A.1.** *inconsistent loss substitution; CONFIRMED* (E-CP10-10). Printed: ρ=ρ̄; r=ρ̄. This substitution violates A.1 requirement ρ<r/2. To obtain the stated output action radius ρ̄/2, the natural inferred loss is ρ=ρ̄/4. Evidence: Rendered source and A.1 assumptions checked; the proposed value is a repair, not a quotation.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
16. **p. 563, same Step 1.** *misquotation; DROPPED* (E-CP10-11). Printed: r_p = r_q = ε₀. DROPPED: the alleged printed r_p=r_q=0 is a misreading. The page prints ε₀, consistently with p. 556. Evidence: Page image confirms epsilon subscript zero.. Effect: No zero-radius erratum..
17. **pp. 562–563, Lemma 3.1 and (59).** *missing radius dependence; CONFIRMED* (E-CP10-12). Printed: for a suitable integer p depending on D̄ and ω₁; with c_i independent of ε and μ. The asserted restricted dependence is too strong for the abstract lemma when the slow radius r̂ shrinks. The covering number, hence its constants, can grow as 1/r̂. Evidence: For D̄=[0,1], ω=(I₁,I₁+I₂), β=1, all stated fixed data stay fixed, but p≥(1+2r̂)/(2ar̂). The divisor at (1,−1) is |I₂|. Let γ₂/r̂→0 to force c₁≳1/r̂. This refutes abstract uniformity, not properly degenerate KAM.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
18. **p. 562, use of Lemma 3.1 (59).** *invalid resonance-set substitution; CONFIRMED* (E-CP10-13). Printed: ω = ω_resc := (∂_(J₁)(H₀+μN̆), ∂_(J₂)N̆). Rescaling only the slow block changes mixed resonances. A measure bound for ω_resc does not directly bound the originally defined ω_μ=(fast, μ slow) mixed-resonant set. Evidence: H₀(I)=I²/2, N(ξ)=ξ+ξ²/2, μ=√2/10, (I,ξ)=(μ,0): ω_μ=(μ,μ) is resonant at (1,−1); ω_resc=(μ,1) is Diophantine for small thresholds. Both maps are diffeomorphisms.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
19. **p. 569, (91).** *valid weaker estimate; DROPPED* (E-CP10-14). Printed: (8/9)(4s)^(τ+1) Ê². DROPPED: the calculation gives the sharper exponent 2(τ+1), but since 4s<1 the printed weaker upper bound remains true. Evidence: A sharper arithmetic estimate is not an erratum. P3 E6.. Effect: Use a sharper bound if helpful without alleging a false printed inequality..
20. **p. 573, Step 3.** *misattributed missing step; DROPPED* (E-CP10-15). Printed: Using (108). DROPPED: the claim that Appendix B never uses (108) overlooks this explicit sentence. Limit analyticity/domain details may still need supplementation. Evidence: Source explicitly uses the scaled Lipschitz estimate; P3 E8.. Effect: Record fixed-strip analytic-limit argument as a proof supplement..
21. **p. 567, Remark 3, and pp. 567–570 proof.** *misclassified citation; DROPPED* (E-CP10-16). Printed: generalizes the inductive theorem. DROPPED: the historical Arnold comparison is not an additional unproved Arnold dependency of B.1; Appendix B supplies an inductive proof. The genuine [4] finite-averaging dependency is separate. Evidence: Read B.1 proof and explicit [4] invocations on pp. 564–565; P3 E11.. Effect: Prove the finite averaging package; do not invent an extra Arnold black box..

### Deviations

1. **docs/tracks/P/statement.md, D-PG-1.** *approved uniform analytic input; ADOPTED* (D-PG-1). Joint analyticity on a closed μ interval and a data-dependent complex oscillator neighborhood, with constants uniform in μ. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
2. **docs/tracks/P/statement.md, D-PG-2.** *period / coordinate convention; ADOPTED* (D-PG-2). Fast physical angles use 2π periodicity; abstract torus parametrizations have period one with explicit lattice/frequency conversion. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
3. **docs/tracks/P/statement.md, D-PG-3.** *domain convention; ADOPTED* (D-PG-3). Use product oscillator discs and explicit max/Fourier norms rather than an ambiguous unqualified ball. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
4. **docs/tracks/P/statement.md, D-PG-4.** *boundary input; ADOPTED* (D-PG-4). Assume the fast frequency diffeomorphism on a fixed neighborhood of cl V with quantitative inverse control. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
5. **docs/tracks/P/statement.md, D-PG-5.** *boundary geometry; ADOPTED* (D-PG-5). State an explicit boundary-collar measure hypothesis, or use interior boxes with its proved loss. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
6. **Appendix A / source [4], P Parts 2/3.** *proof supplement / reformulation; PLANNED* (D-P-AVERAGING). Prove finite two-scale averaging with direct complex nonresonance, oscillator extensions and η≤1/2 Lie-series losses. Evidence: blueprint-P/reviews/p2-review-1.md, p3-review-1.md and p3-review-2.md. Effect: Shared N scalar estimates do not automatically give P two-scale displacement bounds; all constants need proof..
7. **pp. 551, 573, P Parts 1–4.** *proof supplement / reformulation; PLANNED* (D-P-NORM). Use frozen max norms, period transport, explicit Fourier/sup conversion and componentwise McShane plus cube-measure estimates. Evidence: blueprint-P/reviews/p3-review-1.md E5/E10. Effect: Changed constants replace implicit Euclidean same-constant Kirszbraun usage; no blanket source numerical refutation..
8. **Appendix B, P Part 3.** *proof supplement / reformulation; PLANNED* (D-P-KAM-SUPPLEMENTS). Prove inverse ball lifting, near/far parameter Lipschitz bounds and fixed-strip holomorphic convergence on explicit domains. Evidence: blueprint-P/reviews/p3-review-1.md E7/E8; arbitrary D need not be convex. Effect: These supply true steps rather than declare every omitted inverse/limit argument erroneous..
9. **pp. 559–564, P Parts 4/5.** *proof supplement / reformulation; PLANNED* (D-P-CELL). Use Liouville representatives and whole-torus inner containment, then a measurable subfamily deletion to obtain both strict measure inequalities. Evidence: blueprint-P/reviews/p4-review-1.md; p5-review-1.md and p5-review-2.md. Effect: A bare intersection with the physical cylinder is insufficient; deletion proves strict upper bound without attributing its omission to a false source theorem..
10. **Theorem 1.5, P Part 5.** *proof supplement / reformulation; PLANNED* (D-P-REMAINDER). Prove the uniform fifth-order remainder from the analytic jet after choosing the data-dependent oscillator radius after the circular-torus collar. Evidence: blueprint-P/reviews/p5-review-1.md and p5-review-2.md. Effect: An analytic O(5) assertion is not false merely because its Cauchy estimate needs to be supplied..


## Fej04r (doi:10.1017/S0143385704000410)

### Errata

1. **p. 55, proof of Proposition 73, q_jk display.** *mass indices / relative coefficient; CONFIRMED* (E-P-Fej04r-1). Printed: m_k m_k in the second q_jj sum and in q_jk for j<k. Replace these mass products by m_jm_k. The second diagonal sum also lacks the denominator factor 2 present in the first and required by (36). Evidence: Unequal masses refute symmetry as printed. Compare pairwise quadratic form (36) and the j>k expression. The additional global normalization issue is E-P-Fej04r-3.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **p. 56, Lemma 76.** *false analytic continuation; CONFIRMED* (E-P-Fej04r-2). Printed: fonctions méromorphes sur la sphère de Riemann ayant pour points singuliers les quatre pôles 0, ±1, ∞. The universal single-valued meromorphic/pole assertion is false. b_(1/2)^(0)(α) has logarithmic divergence at α=1 and is regular at zero. Evidence: Near θ=0 its defining mean contains ∫dθ/√((1−α)²+θ²), logarithmic as α→1. Local holomorphy for |α|<1 suffices.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
3. **pp. 50–51, (35)–(37), compared with corrected (31) p. 47.** *normalization factor; CONFIRMED* (E-P-Fej04r-3). Printed: C₁=−α b_(3/2)^(1)(α)/(2a_j), C₂=α b_(3/2)^(2)(α)/(2a_j). Under the pinned corrected sqrt(2Λ) chart normalization, the coefficients of the quadratic matrix in (35)–(37) are twice the canonical ones. Halve both C₁ and C₂ in the displayed matrix convention. Evidence: Independent circular-chart average: diagonal −m_jm_k α b₁/(4a_outer Λ_j), mixed Hessian m_jm_k α b₂/(2a_outer√(Λ_jΛ_k)). Fresh scratch rerun agrees at 96 and 192 nodes. Historical missing sqrt(2) belongs to the original printing, not pinned (31).. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
4. **p. 53, Lemma 71 statement and proof.** *alleged incompatible constant; DROPPED* (E-P-Fej04r-4). Printed: 3 in the statement; 2(1+O(ε)) in the proof. DROPPED: for sufficiently small ε, 2(1+O(ε)) is bounded by 3. These constants are compatible; an explicit threshold is an enhancement. Evidence: Operator norm is expressly defined by (23), and is referenced by Lemma 70. P9 review rejects the inconsistent-constant allegation.. Effect: Use an explicit uniform version if desired; no source refutation from 2 versus 3..
5. **pp. 54–55, Lemma 74 proof.** *alleged incomplete induction; DROPPED* (E-P-Fej04r-5). Printed: l’inégalité voulue s’en déduit pour tout s ∈ R⁺ minus N par récurrence. DROPPED: the proof continues on p. 55, where both recurrences and a positive difference formula complete the induction. Evidence: The displayed difference is [j b_s^j+(j+1)b_s^(j+1)]/[s(1+α)²]+[b_s^j−b_s^(j+1)]/(1+α)². Starting at 0<s<1 proves the claim.. Effect: A narrower j=1 proof is a deliberate dependency reduction..
6. **pp. 53–54, Corollary 72.** *missing boundedness hypothesis; CONFIRMED* (E-P-Fej04r-6). Printed: A_ε ∈ M_n(R) symmetric; (A_ε)_nn=c₁+c₂ ε^β; σ_n(ε)=ε(c₁+c₂ε^β)+O(ε²). A uniform boundedness assumption on the family A_ε is missing. Evidence: D=diag(1,0), A_ε=[[0,1/ε],[1/ε,0]], c₁=c₂=0: D+εA_ε has fixed eigenvalues (1±√5)/2, none O(ε²).. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
7. **p. 58, induction block matrix.** *wrong block exponent; CONFIRMED* (E-P-Fej04r-7). Printed: Q̂_h + O(a_n^(5/2)). The old diagonal block generically has a nonzero O(a_n²) correction, so the stronger printed O(a_n^(5/2)) assertion is false. The off-diagonal O(a_n^(5/2)) is a valid weaker bound than O(a_n^(11/4)). Evidence: b_(3/2)^(1)(α)=3α/2+O(α³); the added inner-planet contribution to a fixed outer diagonal is a nonzero constant times a_n². The normalization factor does not change this exponent.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
8. **p. 58, end of Proposition 77 induction.** *proof supplement misclassified; DROPPED* (E-P-Fej04r-8). Printed: Par un raisonnement analogue à ci-dessus. DROPPED as a demonstrated false source assertion: omitted quantitative detail in a true induction is a proof supplement, not an erratum. Evidence: Part 10 supplies spectral branches, resonance products and nonvanishing witnesses. No false printed conclusion is identified by the phrase alone.. Effect: D-P-INDUCTION records explicit reconstruction..
9. **p. 56, domain A^C after Lemma 76.** *false topology; CONFIRMED* (E-P-Fej04r-9). Printed: l’ouvert simplement connexe. A^C as defined is not simply connected: simultaneously rotate all nonzero axes through one full turn. Ratios stay fixed while each axis winds around zero. Evidence: Projection to a₁∈C* sends the loop to winding number one, so it cannot contract inside A^C. This was called E-P-Fej04r-3 in the early statement audit; that ID now denotes the quadratic factor error.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
10. **p. 53, Lemma 71 proof.** *missing normalization; CONFIRMED* (E-P-Fej04r-10). Printed: il existe une unique matrice U ∈ M_n(R) telle que e^(−εU)(D+εA)e^(εU)=D+O(ε²). Uniqueness needs a diagonal/skew normalization. If U solves [D,U]=−A, so does U+C for every diagonal C. A unique zero-diagonal skew solution is the intended choice. Evidence: First-order commutator expansion; taking A=0 already leaves every diagonal U as a solution. This is separate from the refuted coefficient allegation E-P-Fej04r-4.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
11. **p. 48, small-eccentricity/inclination expansion before Theorem 62.** *normalization factor; CONFIRMED* (E-P7-Fej48). Printed: |r_j|=√(Λ_j/2) ε_j(1+O(ε_j²)); |z_j|=√(Λ_j/2) ι_j(1+O(ε_j²)+O(ι_j²)). The leading factors should be √Λ_j after the corrected sqrt(2) in (31). These are stale asymptotics in the revised text. Evidence: 2(Λ−G)=Λe²+O(e⁴), so |r|=√Λ e(1+O(e²)); similarly for inclination.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
12. **p. 50, Lemma 64.** *missing mass factor; CONFIRMED* (E-P8-Fej50). Printed: Y_j = μ_j Ẋ_j = (μ_j³ M_j²/Λ_j³) ∂_(λ_j) X_j. The derivative expression for momentum misses an extra μ_j: mean motion is μ_j³M_j²/Λ_j³, whereas Y_j=μ_j Ẋ_j. Evidence: Use (33) p. 48 and the kinetic convention |Y|²/(2μ). The correct last coefficient is μ_j⁴M_j²/Λ_j³.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
13. **p. 45, proof of Theorem 60, flat remainder.** *overstated flatness inference; CONFIRMED* (E-P-Fej04r-11). Printed: Comme le jet d’ordre infini de R₃ est nul ... la restriction de R₃ à un petit voisinage de ce tore est exponentiellement petite en fonction de la taille du voisinage.. Smooth flatness alone does not imply an exponential-in-inverse-radius estimate. It implies every fixed polynomial order; this weaker consequence can suffice after a finite threshold is chosen. Evidence: For x>0 take f(x)=exp(−(log(1/x))²), extended by zero at x=0. It is C∞ and flat, but for every a,c>0 it is larger than exp(−c/x^a) for sufficiently small x. This challenges the stated inference, not the existence of KAM tori.. Effect: Use explicit finite polynomial flatness bounds with domains/constants; no analytic identity theorem for a merely smooth flat remainder..
14. **p. 42, Theorem 60(1°–3°), versus Definition 32 p. 17 and proof p. 45.** *fixed arithmetic constant / missing rescaling; CONFIRMED* (E-P-Fej04r-12). Printed: il existe des réels ε₀, γ, τ > 0; β de 0; (α,β) ∈ DH_(γ,τ)(p,q). A fixed γ is incompatible with normal frequencies β=O(ε) and positive volume for every arbitrarily small ε when q>0. The proof instead chooses a shrinking γ̂. Evidence: Definition 32 includes k=0 and l=e_j, requiring |β_j|≥γ. The stated ε-closeness to zero excludes it for ε<γ (or γ/C under an O(ε) interpretation). Step 6 p. 45 explicitly sets γ̂=(εδ^(p+q−1))^(p+q+1).. Effect: Specify coupling-dependent full-frequency arithmetic constants; frozen P headlines permit them. This does not show absence of invariant tori with smaller γ..
15. **p. 34, Example 47, with (23)–(24) p. 33.** *wrong example constants; CONFIRMED* (E-P-Fej04r-13). Printed: est (1/√p, (p−1)!)-gauche. These constants fail for the printed Euclidean operator norm. Choose appropriate dimension-dependent constants. Evidence: At p=2,t=1 the derivative matrix is [[1,1],[0,1]], whose operator norm and inverse norm are (1+√5)/2>1. Claimed b=1 and inverse bound 1/(a√p)=1 both fail.. Effect: No core theorem depends on this numerical example..
16. **pp. 38–39, proof of Theorem 58 slicing displays.** *wrong set complement / reciprocal ratio; CONFIRMED* (E-P-Fej04r-14). Printed: (a/b+1)(γ/a)^(1/p); ν̂(t′) ∈ DH_(γ,τ)(p); ν̂(t̂) ∈ DH_(γ,τ)(p). The linewise estimate concerns the bad set, but the p. 39 displays switch to the good set. They need ∉. The p. 38 reciprocal ratio also differs from the b/a factor in the theorem and preceding one-dimensional bound. Evidence: For p=1, ν≡1 and 0<γ<1, the good set is the whole nonzero-length interval, while any stated bound tending to zero with γ fails. Thus it is the bad set that can have the small measure. Reconstruct Fubini with cover/Jacobian constants.. Effect: Keep the intended bad-set theorem and supply its quantitative slicing proof; no refutation of qualitative almost-everywhere Diophantinity..
17. **p. 44, Step 5 polar localization, compare CP09 p. 15.** *missing component margin; CONFIRMED* (E-P-Fej04r-15). Printed: boule centrée en ρᵒ et de rayon δ=‖ρᵒ‖/2. For an arbitrary positive vector ρᵒ this radius need not stay inside the positive action orthant. Choose comparable components or a radius controlled by min_j ρᵒ_j. Evidence: ρᵒ=(1,.01) and increment (0,−.02) has norm less than ‖ρᵒ‖/2 but makes its second action negative. This is the same domain issue as E-CP09-2.. Effect: Harmless dimension-dependent localization repair, not a global obstruction to the KAM route..
18. **p. 58, after the induction block matrix.** *index typo; CONFIRMED* (E-P-Fej04r-16). Printed: σ̂₁,...,σ̂_n sont les valeurs propres de Q̂_h. The (n−1)-planet old block has n−1 eigenvalues; end the hatted list at n−1. Evidence: The immediately preceding text lists σ_j=σ̂_j+O(a_n^(5/2)) for j=1,...,n−1. See p10-review-1 source handoff.. Effect: Correct the list independently of the remainder-exponent repair E-P-Fej04r-7..

### Deviations

1. **docs/tracks/P/statement.md, D-PLANAR-1.** *scope; ADOPTED* (D-PLANAR-1). State analytic planar four-dimensional tori without the source factor-four restriction; keep actual physical closure obligations. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
2. **docs/tracks/P/statement.md, D-PHYS-1.** *physical reformulation; ADOPTED* (D-PHYS-1). Restore arbitrary G>0 and prove physical Newtonian reconstruction, collision exclusion, confinement and uniqueness. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
3. **docs/tracks/P/statement.md, spatial sketch.** *proof supplement / reformulation; PLANNED* (D-SPATIAL-1). Defer an exact spatial Lean theorem; distinguish reduced and reconstructed frequencies/resonances. Evidence: docs/tracks/P/statement.md. Effect: No spatial theorem is approved by the planar proof..
4. **pp. 50–55, P Parts 8/9.** *proof supplement / reformulation; PLANNED* (D-PROOF-1). Derive the corrected planar secular matrix in frozen increasing-axis order directly from pair averages. Evidence: docs/tracks/P/statement.md; blueprint-P/parts/p8-secular-form.tex. Effect: Do not copy mass/index/normalization misprints..
5. **p. 56, P Parts 9/10.** *proof supplement / reformulation; PLANNED* (D-PROOF-2). Use local holomorphy, symmetric spectral products and connected-domain continuation instead of false global meromorphy/simple connectivity. Evidence: docs/tracks/P/statement.md; blueprint-P/parts/p10-nondegeneracy.tex. Effect: Nonvanishing/resonance arguments use exact sufficient topology..
6. **pp. 46–48 Theorem 62, P Part 7.** *proof supplement / reformulation; PLANNED* (D-P-KEPLER). Prove the analytic symplectic Poincaré chart through e=0 using regular Kepler coordinates and the guarded I-track tube, then extend symplecticity by density. Evidence: blueprint-P/reviews/p7-review-1.md. Effect: Explicit proof replaces an external Poincaré/Che88 citation; chart normalization remains sqrt(2Λ)..
7. **p. 51, spectral oscillator change; CP09 p. 14.** *proof supplement / reformulation; PLANNED* (D-P-CANONICAL-LIFT). Lift action-dependent slow rotations to the fast angles using the exact canonical one-form correction. Evidence: blueprint-P/reviews/p9-review-1.md; p11-route-study.md. Effect: A symplectic fiber map with fixed actions is not alone a full symplectic chart. Source statements with actions fixed on a fiber are not automatically false..
8. **pp. 57–58, P Part 10.** *proof supplement / reformulation; PLANNED* (D-P-INDUCTION). Supply quantitative symmetric spectral perturbation, resonance-product and axis-degeneration induction details. Evidence: blueprint-P/reviews/p10-review-1.md. Effect: True omitted induction details are a proof supplement, not E-P-Fej04r-8..


## Fej07e (pinned PDF)

### Errata

1. **pp. 1–4, author corrections to original 2004 article.** *author-reported original errata; CONFIRMED* (E-P-Fej07e). Printed: Les arguments donnés sont insuffisants. / les constantes des estimations des inverses des opérateurs linéaires sont fausses. / Remplacer m_i m_j par m_j m_k. / sans le facteur √2, elles ne sont que conformément symplectiques.. Historical author-reported corrections: Corollary 22 inverse parameter argument; inverse-operator constants A_j→A_j A′_(j+p+τ+1)/(2π); pair masses (28); sqrt(2) in (31). Pp. 3–4 also distinguish smooth construction and analytic planar addendum. The pinned revision already includes the (28)/(31) corrections. Evidence: Pinned 5-page erratum inspected; original unrevised printing is not pinned, so verification is of the author report, not original text.. Effect: Use revised formulas and corrected smooth argument where relevant; do not claim historical missing sqrt(2) persists in revised (31)..

### Deviations

None.


## Arn63b (doi:10.1070/RM1963v018n06ABEH001143)

### Errata

1. **reported in CP11 p. 34, footnote 53, concerning Arnold p. 138 (3.4.31).** *reported exponent typo; CANDIDATE* (E-P-Arn63b). Printed: in [2], a₂⁴ should be corrected into a₂⁷. CP11 reports this original exponent typo and a factor-two invariant normalization. Original English (3.4.31) has not been independently verified. Evidence: CP11 footnote read. An available Russian scan is not a substitute for verifying the cited English printing.. Effect: Derive quartic coefficients directly; do not promote the reported correction to original-text verification..

### Deviations

None.


## CP11 (doi:10.1007/s00222-011-0313-z)

### Errata

1. **p. 62, Appendix B (B.2).** *missing factor 1/2; CONFIRMED* (E-P-CP11-1). Printed: C₂(a,b) = α β₂^(3)(α)/b. Insert 1/2 for this off-diagonal matrix coefficient under the frozen sqrt(2Λ) normalization. Evidence: Direct pair-average derivation and differentiation: the cross coefficient differs by two, while the diagonal/overall convention agrees with (6.9). P8 scratch mixed Hessian agrees numerically.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **p. 63, Appendix B (B.6), r₁.** *wrong exponent in exact quartic coefficient; CONFIRMED* (E-P-CP11-2). Printed: 37 α⁴ β₄^(9)(α)  [CP11 p. 61: β_k^(r) := b_(r/2),k]. The r₁ expression is only asymptotically correct as printed; its final 37α⁴ must be 37α³ to match the exact quartic coefficient. At axes (1,2) the printed and exact coefficients have opposite signs. Evidence: Fresh independent scratch: masses .7,1.9, inner-axis coefficient exact −0.03097386529961853 versus printed +0.05742931465995163. Exact symbolic integration-by-parts residual for the replacement is zero; printed-minus-exact starts 238095 α⁸(1−α)/(32768β).. Effect: No frozen statement changed; provider/blueprint must use the documented correction..

### Deviations

1. **Appendix B, P Part 11b interface.** *proof supplement / reformulation; PLANNED* (D-P-QUARTIC). Derive finite-axis exact quartic coefficients from the averaged interaction and correct B.6 rather than use only hierarchical leading asymptotics. Evidence: blueprint-P/reviews/p8-review-1.md; independent scratch integration-by-parts certificate. Effect: No claimed independent verification of every other r₂,r₃,r₄ coefficient..


## CP09 (arXiv:1206.3475v1)

### Errata

1. **p. 21, perturbation threshold calculation.** *wrong inequality direction in proof; CANDIDATE* (E-CP09-1). Printed: ε₀ ≤ c̄ ε^ν₀. An upper bound on an admissible threshold does not show a prepared remainder is below that threshold. The application needs an explicit admissible lower bound of polynomial size, or a threshold chosen by equality after all estimates. Evidence: The needed implication is remainder≤c ε^ν≤ε₀, not ε₀≤c ε^ν. Does not refute the KAM theorem.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **p. 15, polar action domain.** *missing component margin; CONFIRMED* (E-CP09-2). Printed: ρ ∈ B^p_(|ρ₀|/2). A Euclidean radius controlled by |ρ₀| does not protect every oscillator component from zero. Use a radius smaller than a fixed fraction of min_j ρ₀j. Evidence: ρ₀=(1,.01), ρ=(0,−.02) lies in the printed ball but ρ₀₂+ρ₂<0, so the real polar square root is undefined.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
3. **p. 14, action-dependent Birkhoff change.** *missing symplectic lift; CONFIRMED* (E-CP09-3). Printed: (θ,r)=(θ̃,r̃). An action-dependent slow canonical change generally requires a fast-angle lift; it cannot leave both fast blocks unchanged while remaining symplectic. Evidence: The mixed terms dI∧(slow one-form) from an I-dependent oscillator rotation are nonzero. Fixing θ as well cannot cancel them; add its exact angle correction.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
4. **pp. 14–15, Birkhoff normal form Q_*.** *degree / decomposition typo; CONFIRMED* (E-CP09-4). Printed: Q_* starts with degree one in the slow actions. The quadratic oscillator term is already written separately; including it again in Q_* double counts it. Q_* must start at degree two in the slow actions in that decomposition. Evidence: Compare the explicit linear Ω·r term to the displayed polynomial indexing.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
5. **p. 15, torsion matrix dimension.** *dimension typo; CONFIRMED* (E-CP09-5). Printed: T ∈ R^(2p×2p). There are p slow actions, so their torsion Hessian is p×p, not 2p×2p. Evidence: The oscillator phase space has dimension 2p; its action Hessian does not.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
6. **p. 15, polar coordinate display.** *repeated subscript; CONFIRMED* (E-CP09-6). Printed: ρ₀j + ρ₀j. The second term should be the variable ρ_j. Evidence: The change must parametrize variable radial actions, consistently with the next normal form.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
7. **p. 11, frequency-selected action set.** *missing preimage; CONFIRMED* (E-CP09-7). Printed: K ∩ D_(γ,τ). D_(γ,τ) is a frequency set; the action set is K∩ω⁻¹(D_(γ,τ)). Evidence: Action and frequency spaces have distinct meanings despite equal dimensions.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
8. **p. 11, internal reference; p. 6, footnote 8.** *cross-reference; CONFIRMED* (E-CP09-8). Printed: Theorem 2; Theorem 1.7, page 127. The local result is Lemma 2, and the statement of Rüssmann Theorem 1.7 starts on printed p. 126 in the pinned Rus01, with continuation/proof remarks on p. 127. Evidence: Internal numbering and Rus01 pinned pagination checked.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
9. **p. 6, Theorem 3 threshold dependencies versus p. 17 Lemma 8.** *missing dependency; CANDIDATE* (E-CP09-9). Printed: ε₀ = ε₀(ε*,n,μ,β,τ,ω,K). The analytic neighborhood A also enters quantitative thresholds through its margin ϑ. Omitting it is not a uniform statement over arbitrarily thin domains. Evidence: Rus01 Theorem 1.7 explicitly quantifies A and CP09 Lemma 8 has ϑ-dependent C*. Treat A as fixed or include it.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
10. **p. 17, transformed perturbation display.** *repeated symbol; CONFIRMED* (E-CP09-10). Printed: f(r,ρ,c̄₁,c̄₁). The repeated constant in the two shifted oscillator blocks should use the two distinct shifts c̄₁,c̄₂ defined in preparation. Evidence: Compare definitions of the translation immediately preceding this displayed composition.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
11. **p. 22, planetary application of Theorem 4.** *source-interface qualification; CANDIDATE* (E-CP09-11). Printed: Theorem 4. The Kepler splitting used in the application depends on ε, whereas the preceding abstract theorem is stated with ε-independent input. A uniform parameter-family wrapper or exact zero-coupling splitting is required for this import. Evidence: The prepared masses/actions and frequency data vary with the perturbation parameter. The existence of an appropriate uniform wrapper is plausible, not proved by merely identifying the formulas.. Effect: Use joint analytic parameter control and a proved uniform wrapper; do not alter frozen P-FIXED..

### Deviations

1. **docs/tracks/P/statement.md, D-FIXED-1.** *new physical specialization; ADOPTED* (D-FIXED-1). Treat the fixed-center theorem as a new Newtonian deduction from the analytic maximal-torus route with exact physical transfer. Evidence: docs/tracks/P/statement.md and owner D20/D25. Effect: Frozen D20/D25 statement preserved; analytic/chart/measure obligations remain proof work..
2. **pp. 17–21 Remark 5 / Lemma 8; Rus01 §§13–20.** *proof supplement / reformulation; PLANNED* (D-P-WEAK-KAM). Reconstruct the maximal case with strict power-law divisors, polynomial admissible thresholds and parameter inverse-Lipschitz/displacement control. Evidence: blueprint-P/reviews/p11-route-study.md and p11a-russmann-check.md. Effect: UNVERIFIED route: power Φ is not an instance of Rus01 all-power decay. The all-power condition is also used in analytic convergence, not only measure. Do not certify a full KAM proof from CP09’s remark..
3. **Theorems 3–4 and Proposition 2; P Part 11a.** *proof supplement / reformulation; PLANNED* (D-P-LOCAL-WRAPPER). Prove a local compact-action maximal-KAM wrapper with exact analytic domains, derivative nondegeneracy stability, parameter-family control and ambient whole-torus measure. Evidence: blueprint-P/reviews/p11-route-study.md A2/A7 and p11a-russmann-check.md. Effect: C⁰ O(ε) alone on shrinking domains does not preserve a specified ε^μ derivative amount; use analytic margins and derivative estimates. Qualitative “close to” alone is not false..


## Rus01 (doi:10.1070/RD2001v006n02ABEH000169)

### Errata

1. **p. 123, (1.2).** *dimension typo; CONFIRMED* (E-Rus01-1). Printed: A:Y → R^(p×p). The elliptic z-block has 2p coordinates, so its symmetric quadratic matrix A must be 2p×2p. Evidence: Compare z∈R^(2p), A J_p and the 2p eigenvalues in §1.3.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **p. 171, item 5, compared with (14.7) p. 165.** *inconsistent norm definition; CONFIRMED* (E-Rus01-2). Printed: C• = |ω| + |Ω| + |Q|. The defining bound (14.7) uses |A|, not just its elliptic frequencies |Ω|. General symmetric quadratic matrices with nonuniform conditioning are not controlled by their Hamiltonian eigenfrequencies alone. Evidence: For A=diag(L,L⁻¹), A J has fixed frequencies while ‖A‖→∞; (14.7) requires the full matrix norm.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..

### Deviations

None.


## Rus05 (doi:10.1070/RD2005v010n01ABEH000297)

### Errata

1. **p. 26, Lemma 8, strip integral representation.** *missing growth hypothesis; CONFIRMED* (E-Rus05-1). Printed: Every holomorphic function. A boundedness or suitable growth hypothesis is needed to discard vertical contour sides and ensure the improper integral converges. Evidence: The entire function exp(z²) grows quadratically exponentially on horizontal lines; the displayed strip kernel cannot make the improper integrals converge. Actual periodic bounded applications on narrower strips are safe.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
2. **pp. 30–31, §11 (46) and final estimate.** *dimension rescaling / constant; CONFIRMED* (E-Rus05-2). Printed: |F−F_(nTq)|₀ ≤ [(1+E(Tρ))^n−1] ‖F‖ρ. For the multipliers constructed there, dimension rescaling changes E(Tρ) to E(Tρ/n). The printed estimate fails for that construction; this is not a counterexample to existence of different approximation multipliers. Evidence: n=4,T=4,q=e^(−10),ρ=5,r=6,F=e^(3ix₁−18). Cube cutoff T/√n=2 removes the mode 3. Error on radius 1 is e^(−15)=3.0590e−7, above claimed [(1+8e^(−20)/π)^4−1]=2.0995e−8.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..
3. **p. 21, abstract footnote referencing Rus01.** *cross-reference; CONFIRMED* (E-Rus05-3). Printed: p. 136. The pinned Rus01 footnote explaining the approximation source is on p. 135. Evidence: Rus01 pp. 134–136 and Rus05 abstract compared.. Effect: No frozen statement changed; provider/blueprint must use the documented correction..

### Deviations

1. **§§8–11; Rus01 §7.3–7.5.** *proof supplement / reformulation; PLANNED* (D-P-APPROX). Either repair dimension/growth estimates and redo the schedules or prove elementary Fourier/Taylor approximation with changed constants. Evidence: blueprint-P/reviews/p11a-russmann-check.md. Effect: PLANNED reconstruction, not a literal proof receipt for Rus01 sharp constants; external scalar sublevel/approximation leaves remain..


## AKN06 (doi:10.1007/978-3-540-48926-9)

### Errata

None.

### Deviations

1. **§6.1.9 versus averaging drafts.** *proof supplement / reformulation; PLANNED* (D-N-ADD-5). Specialize to analytic Hamiltonians, fixed h,f,K, period-one angles, absolute volume and separate local existence. Evidence: docs/tracks/N/notes.md D-N-ADD-5 and v0.5. Effect: This averaging draft is not an approved or proved frozen addition..


## FH24 (arXiv:2304.10205)

### Errata

1. **Lemma 2.14, p. 14 (arXiv v1).** *wrong constant (loose, still valid); CONFIRMED* (E-FH24-1). Printed: ĉ_R = (2^{d+1−2τ} ζ(2,2^τ) π^{−2τ−2} Γ(2τ+1))^{1/2}; middle expression (γ²δ^{2τ}2^d Σ e^{−4π|k|₁δ}|k·ω|^{−2})^{1/2}. derivation defect: the displayed c_R(δ) omits the factor (2π)^{-1} of the solution operator (2.21); the printed ĉ_R is twice the δ→0 leading coefficient that the corrected route gives. The printed ĉ_R remains a valid (conservative) uniform bound; halving it uniformly needs a separate proof. Evidence: independent re-derivation in blueprint/parts/p2s2-smalldiv.tex, remark bp:p2s2sd:errata (branch sharp-v2). Effect: none on validity: the printed value is an upper bound; the derivation as displayed is inconsistent.
2. **Table 3, (3.72), p. 38 (arXiv v1).** *wrong constant (underestimate); CONFIRMED* (E-FH24-2). Printed: C_ΔN̄̄ᵀ = δσ_Bσ_L c_DJᵀ C_ΔK̄̄ + σ_B C_ΔL̄̄ c_Jᵀ + C_ΔB̄̄ σ_L c_Jᵀ. false as stated: since Nᵀ = BLᵀJᵀ the bound needs σ_Lᵀ and C_ΔL̄̄ᵀ where σ_L and C_ΔL̄̄ are printed; with σ_Lᵀ = 2nσ_K the printed bound underestimates by a factor up to 2n (in the canonical case it coincides with (3.71)). Evidence: scripts/apost_sharp/benchmark_fh24.py (erratum switch) and dominance.py, APOST-SHARP-V2.md §5 and §8 (branch sharp-v2). Effect: the printed constants are not valid general bounds. Corrected FH24 with c_R = c♮(1) never beats the v2 design on the 108-point grid (printed: leads at 48). With the legally available uniform constant c♮(ρ/3) it leads v2 by up to 0.63 orders at (n,τ) = (4,3) (audit finding F7); a fair rerun is pending.
3. **(3.10) and p. 19 (arXiv v1).** *typo; CONFIRMED* (E-FH24-3). Printed: "C_E =" and "Corollary 2.14". typos: "C_E" stands for C_{Eᵀ}, and the cross-reference "Corollary 2.14" should be Corollary 2.16. Evidence: APOST-SHARP-V2.md §8. Effect: none.
4. **(2.24) with (3.99) and Table 1.** *imprecise statement (benign: positive powers of γ); DROPPED* (E-FH24-4). Printed: the smallness constant C presented as a constant. the "constant" C is not γ-free: (3.99) contains γδ^τ·max{1,C_sym}/ν and Table 1 contains terms like C_E = C_E^L + γδ^τ C_E^N. Evidence: competitors report §7. Effect: none.
5. **hypothesis H3.** *typo; DROPPED* (E-FH24-5). Printed: "ν < 1, κ and κ < 1". typesetting: the second κ is presumably κ̂ ((3.91) needs a^{τ+1}Qε₀/(γδ₀^{τ+1}) < κ < 1 and (3.95) needs ε₀/(γδ₀^{τ+1}) < κ̂). Evidence: competitors report §7. Effect: none.

### Deviations

None.


## FHL17 (arXiv:1601.00084v1)

### Errata

1. **proof of Theorem 2.5, p. 16.** *gap; CONFIRMED* (E-FHL17-1). Printed: constants evaluated at "the worst value of δ_s, that is δ₀" while (90) allows c_R(δ). conditional uniformity gap, as in HL19 §5.3: correct for a uniform c_R, but (90) allows c_R(δ), which need not be bounded by its value at δ₀. Evidence: blueprint remark bp:p2s2sd:errata (branch sharp-v2). Effect: none for a uniform c_R.
2. **p. 37.** *numerical inconsistency; CONFIRMED* (E-FHL17-2). Printed: "6 orders" at ε = 0.96 with τ = 1. At the printed τ = 1 and Table 5 inputs, the stated six-order gain cannot come solely from replacing (90) by (96). A calculation at τ = 1.26 has the six-order scale, but the exact cause of the reported number remains unverified. Evidence: SHARP-PLUS FHL17 helper report; APOST-SHARP-V2.md §8. Effect: none on our use.
3. **introduction.** *misattribution; CONFIRMED* (E-FHL17-3). Printed: attributes "ε < 0.68" for the standard map to Celletti–Chierchia, CMP 118 (1988). misattribution: CC88 gives |ε| ≤ 0.65 (and Celletti–Chierchia JSP 1991 gives 0.838). Evidence: competitors report §7 (KNF helper). Effect: none.

### Deviations

None.


## CCdlL20d (arXiv:2002.10647)

### Errata

1. **p. 10, Definition 4.** *wrong hypothesis; CONFIRMED* (E-CCdlL20d-1). Printed: "τ ≥ 1, ν ≥ 1" with |ωk − q| ≥ ν|k|^{−τ}. In arXiv:2002.10647v1, p. 10, Definition 4, replace ν ≥ 1 by ν > 0 (or a suitable positive small-constant range): at k = 1 the hypothesis forces ν ≤ 1/2, and the paper later uses ν ≈ 0.382. Evidence: competitors report §3.6 (conformal helper). Effect: none on our use (CCdlL13 serves the Lipschitz re-application only); location in the pinned preprint to be mapped.
2. **p. 9, Lemma 3.** *inconsistent constant; CONFIRMED* (E-CCdlL20d-2). Printed: "C_{c,ℓ} = ℓ!(2π)^{−1}". The general derivative constant C_{c,ℓ} = ℓ!(2π)^{−1} in Lemma 3 is invalid for the stated sup norm and geometric strip; the ordinary Cauchy choice C_{c,ℓ} = ℓ! is valid. Whether the faulty constant is used computationally was not established. Evidence: competitors report §3.6 (conformal helper). Effect: none on our use.
3. **(3.14).** *wrong strip in the conclusion; CONFIRMED* (E-CCdlL20d-3). Printed: closeness stated on the strip ρ₀ − δ₀. (3.14) is not justified on ρ₀ − δ₀ by the §5.5 schedule; that schedule reaches ρ₀/2 and fixes δ₀ = ρ₀/4. Use that final strip or reprove a schedule matching the stated free δ₀. Evidence: competitors report §3.6 (conformal helper). Effect: none on our use.

### Deviations

None.


## CCGdlL22 (arXiv:2107.02853)

### Errata

1. **arXiv v1, p. 15.** *wrong constant; CONFIRMED* (E-CCGdlL22-1). Printed: "ν = ((3−√5)/2)^{−1}". impossible value (≈ 2.618 violates the Diophantine bound at k = 1); presumably ν = (3−√5)/2; unknown whether the code used the wrong value. Evidence: competitors report §3.6 (conformal helper). Effect: none on our use.
2. **(37).** *wrong strip in the conclusion; CONFIRMED* (E-CCGdlL22-2). Printed: closeness stated on ρ₀ − δ₀. The exhibited schedule reaches ρ₀/2 and does not prove the (37) closeness estimate on ρ₀ − δ₀. This is an analytic-strip proof mismatch, not an established counterexample to the underlying existence result. Evidence: competitors report §3.6 (conformal helper). Effect: none on our use.

### Deviations

None.


## CCdlL20s (arXiv:2007.08394)

### Errata

1. **p. 20.** *unsupported claim; CANDIDATE* (E-CCdlL20s-1). Printed: claims JDE 2013 contains a "direct proof of the results for flows". The pinned mp_arc 11-188 version of CCdlL13 does not contain the direct flow convergence proof described in CCdlL20s p. 20: its Appendix A explicitly limits itself to formal calculations. Whether the published JDE 2013 version supplies it remains unverified. Evidence: competitors report §3.6 (conformal helper). Effect: none on our use.

### Deviations

None.


## CC07 (doi:10.1090/memo/0878)

### Errata

1. **preprint (Dec 2003) p. 109 with (2.130) p. 49 and p. 96.** *possibly false as stated (computer-assisted closing inequality); CONFIRMED* (E-CC07-1). Printed: β₁ = Ω*/γ in (2.130), while the printed β₁± equal Ω*±/ρ with ρ = 0.2. In the pinned December 2003 preprint, the tabulated β₁ uses Ω*/ρ instead of (2.130)'s Ω*/γ. Applying that fourth-power correction to the reported first closing evaluations gives approximately 849 and 7.26, so the displayed numerical justification fails on that reading. The published 2007 text and a full interval replay remain unchecked. Evidence: competitors report §7 (KNF helper; the ratio match was verified by the helper). Effect: none on our use; it affects the competitor comparison only.

### Deviations

None.


## CC87 (doi:10.1063/1.527418)

### Errata

1. **p. 2079.** *numerical inconsistency; CONFIRMED* (E-CC87-1). Printed: "ε_c ∼ 1/29.41". inconsistent with the paper’s own ratios (ε_c ≈ 0.31). Evidence: competitors report §7 (KNF helper). Effect: none.

### Deviations

None.


## CC97 (doi:10.1007/s002200050115)

### Errata

1. **p. 447.** *numerical error (conclusion unaffected); CONFIRMED* (E-CC97-1). Printed: a displayed expression printed as 3.585·10⁻⁸. numerical error: the expression evaluates to about 2.36; the underlying (4.31) gives about 3.8·10⁻³ < 1, so the conclusion stands. Evidence: competitors report §7 (KNF helper). Effect: none.

### Deviations

None.


## CC88 (doi:10.1007/BF01218480)

### Errata

1. **Lemma 11.** *imprecise statement; DROPPED* (E-CC88-1). Printed: error bound stated at the final strip. imprecise statement: presumably the bound holds at ξ₀ = 1/10. Evidence: competitors report §7 (KNF helper). Effect: none.

### Deviations

None.


## CC95 (pinned PDF)

### Errata

1. **p. 103 versus Planet. Space Sci. 46 (1998).** *inconsistency between sources; DROPPED* (E-CC95-1). Printed: Moon trapping index "k = 2, 3, …, 35". inconsistency between sources: Dyn. Rep. p. 103 says k ≤ 35 (verified on the page image); PSS 1998 says k ≤ 40. Evidence: competitors report §7 (KNF helper). Effect: none.
2. **p. 99.** *misattribution; CONFIRMED* (E-CC95-2). Printed: attributes 6.75·10⁻⁴ to the (√5−1)/2 torus. CC95 p. 99 discusses the (√5−1)/2 forced-pendulum torus, while its cited CFP87 computation explicitly treats (1+√5)/2. The historical summary needs a torus-specific qualification; it must not attribute CFP87's calculation to the same flow torus merely because the frequencies differ by one. The precise provenance of 6.75·10⁻⁴ remains to be mapped among the grouped references. Evidence: competitors report §7 (KNF helper). Effect: none.

### Deviations

None.


## VL22 (arXiv:2101.07785)

### Errata

1. **eqs. (46), (47), (50)–(52), (65).** *typos and an unreproducible constant; CONFIRMED* (E-VL22-1). Printed: strip "|Im| ≤ ρ"; norm sum over k; λ* = 10⁻⁸⁵·⁷. In VL22 (46), use σ for the angular strip widths. In (47), include the zero Fourier mode when defining the stated functional norm. The numerical λ* report is reproducible at τ = 1 using the printed base 20 and is conservative; the alleged 34-order discrepancy is withdrawn. Evidence: competitors report (KNF helper). Effect: none on our use; affects the applications comparison only.

### Deviations

None.


## FH25 (arXiv:2403.10152)

### Errata

1. **§5.** *reproducibility note; CANDIDATE* (E-FH25-1). Printed: the pair (‖η^{DK}‖, ‖ηᴺ‖) = (10⁻³⁸, 10⁻⁴⁴) reported as a numerically checked closure of FH24’s Iterative Lemma. FH25 §5 does not report enough intermediate validation data to independently replay its numerical closure from the trial pair (10⁻³⁸, 10⁻⁴⁴). A direct coarse global FH24-majorant calculation with derived torsion bounds fails by several orders, but this neither reproduces nor refutes the paper's stated finite-prefix-then-theorem computation. Retained as a reproducibility request, not a confirmed erratum. Evidence: dominance.py --fh25 and APOST-SHARP-V2.md §10.4 (branch sharp-v2). Effect: none on our theorems; it bounds what the SJS feasibility study can assume.
2. **§5 (choice of δ) against Theorem A.1 (arXiv v1).** *hypothesis boundary (harmless numerically); CANDIDATE* (E-FH25-2). Printed: "we choose the radius of analiticity to be ρ = 0.1 and δ = ρ/6"; Theorem A.1: "for each δ ∈ ]0, ρ/6[". the application's choice δ = ρ/6 lies on the excluded endpoint of the open interval that Theorem A.1 (FH24 Theorem 2.18) requires; any δ slightly below ρ/6 would do. Evidence: docs/campaign/handoffs/SJS-FEAS.md, suspected errata E3 (branch sjs-feas); pinned text lines 553 and 723 of the local extraction. Effect: none on our theorems.

### Deviations

None.


## Pos96W (doi:10.1007/BF02566420)

### Errata

1. **p. 285, proof of Lemma 4, Case 1.** *wrong constant; CONFIRMED* (E-W-Pos96W-1). Printed: δ′(m) = ½(1/λ_i + 1/λ_j + 1/λ_k − 1/λ_l) ≥ 1/λ_i. The displayed lower bound is false; the valid bound is δ′(m) ≥ 1/(2λ_i). Lemma 4 survives with a smaller absolute constant. Evidence: (i,j,k,l)=(1,10,10,19), m=1: δ′ = 0.426778 while 1/λ₁ = 0.707107. Effect: Constant only; blueprint-W proves |δ| ≥ m/(27(n²+m)^{3/2}).
2. **p. 286, proof of Lemma 4, Case 2.** *missing case; CONFIRMED* (E-W-Pos96W-2). Printed: it suffices to study δ_{+−−+}. The reduction misses the subcase i = j < k = l: there δ_{+−−+} ≡ 0 (paired), while δ_{−−++} = 2(λ_k − λ_i) is nonpaired and still needs a positive lower bound. Lemma 4 is true; the case needs a separate outer-pair bound. Evidence: (1,1,2,2), m=1: δ_{−−++} = 1.643709 while the comparison divisor δ_{+−−+} = 0. Effect: Proof supplement only (blueprint-W bpW:w3:divisor); statement of Lemma 4 unaffected.
3. **p. 286, proof of Lemma 4.** *typo; CONFIRMED* (E-W-Pos96W-3). Printed: λ_{j+2i} − λ_j ≥ 2(λ_{j+1} − λ_j) ≥ 2i f′(j). The first factor 2 should be 2i: λ_{j+2i} − λ_j ≥ 2i(λ_{j+1} − λ_j) ≥ 2i f′(j) (sum of 2i increasing unit gaps). Evidence: i=2, j=3, m=1: 2(λ₄−λ₃) = 1.921656 < 2i f′(3) = 3.794733, so the printed chain fails at its second inequality. Effect: None on the final bound.

### Deviations

1. **frozen docstrings of KAM.Wave.linearTorus, reconU, reconV (approved text docs/tracks/W/W-STATEMENTS.md rev 1, ffcbdb93).** *whitespace-only rewrap of approved text; ADOPTED* (D-W-FREEZE-1). One space replaced by a newline in each of three approved declaration docstrings, to meet the 100-column lint (D-WF1, main orchestrator ruling 2026-10-30; AmdConfinement precedent). Evidence: docs/tracks/W/FREEZE.md; ABI hashes (pp.all #print/#check) identical before and after; identity audit docs/tracks/W/audits/W-FREEZE-identity-audit.md. Effect: none: docstring whitespace only, ABI unchanged.
2. **frozen docstrings of KAM.Wave.reconV and KAM.Wave.nlw2 (approved text docs/tracks/W/W-STATEMENTS.md rev 1, ffcbdb93).** *docstring-only correction of approved text; ADOPTED* (D-W-FREEZE-2). Docstring corrections (D-WF2, main orchestrator ruling 2026-10-30): reconV 'where `q = coeff y`' -> 'where `p = coeff y`' (the formula is in the momentum coordinate p); nlw2 '**W-NLW2 (proposed).**' -> '**W-NLW2.**' (now owner-approved and frozen). Evidence: docs/tracks/W/FREEZE.md; ABI hashes (pp.all #print/#check) identical before and after; identity audit docs/tracks/W/audits/W-FREEZE-identity-audit.md. Effect: none: docstring only, ABI unchanged.


## Pos96K (pinned PDF)

### Errata

1. **p. 127 (PDF p. 10), proof of Lemma 1 (operator part F^{11} of the homological equation).** *false as stated (Hilbert-space estimate applied to operator norms); CONFIRMED* (E-W-Pos96K-1). Printed: Expanding R̃ into its Fourier series with operator valued coefficient R̃_k we have, as before, Σ_k |||R̃_k|||² e^{2|k|s} ≤ 2ⁿ|||R̃|||_{D(s)}. The weighted square-sum (Parseval-type) bound is false for operator-valued coefficients: 'as before' transfers the Hilbert-valued bound of p. 126 to the operator space on ℓ², which is not a Hilbert space. Use instead the Banach-valued coefficient bound |||R̃_k||| ≤ M e^{−|k|s} with lattice sums after a strip loss (blueprint-W bpW:w1:fourier-banach, bpW:w1:lattice, bpW:w1:schur). Evidence: Fix s>0, n≥1, N. R̃(x)e_j = e^{−js}e^{ijx₁}e_j for j≤N, 0 otherwise: entire, 2π-periodic, finite-rank, diagonal, sup over the strip = 1, and Σ_k |||R̃_k|||² e^{2|k|s} = N > 2ⁿ for N > 2ⁿ (n=2: N=8), under either reading of the RHS (squared or not). Realized as the weight-conjugated R^{11} Hessian of R = Σ_{j≤N} j^{p−p̄}e^{−js}e^{ijx₁}z_j z̄_j; a real cosine variant has square sum N/2 (fails for N>2^{n+1}). blueprint-W remark bpW:w1:operator-fourier. Effect: Theorem A is not refuted; the F^{11} estimate is redone with Banach-valued coefficient bounds and lattice sums, changing only internal constants/exponents of track W's W4. No frozen W declaration (KAM/Frozen/Wave, incl. nlw2) depends on it.

### Deviations

1. **p. 147, Lemma A.4 (flows of parameter-dependent vector fields), second displayed estimate.** *proof supplement (mean-value segment step); ADOPTED* (D-W-Pos96K-A4). The proof bounds the field difference at two trajectory points by ‖DX‖_V‖Δφ^s‖_U, which needs the segment between them to lie in the derivative-controlled domain (V is only open, not convex); blueprint-W supplies this: both trajectories and all Picard iterates stay in a convex ball B(w,δ) with margin 2δ, where Cauchy gives ‖DX‖ ≤ M/δ. Evidence: blueprint-W/parts/w1-sequences.tex bpW:w1:flow; reviews w1-review-1.md (gap confirmed, repair valid) and w1-review-2.md. Effect: Lemma used with the explicit ball-margin hypotheses of blueprint-W bpW:w1:flow; W5 must instantiate the margins.
