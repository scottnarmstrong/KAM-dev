# Errata and deviations

This record lists where the Lean statements and proofs of this formalization differ from the printed sources, and
the defects in those sources that were found along the way. An **erratum** is a defect in a pinned source itself: a
typo, a wrong constant or sign, a missing hypothesis, a statement false as printed, or a gap. **Gap policy:** a gap
counts as an erratum only when a printed assertion is false; where a missing argument for a true step is supplied,
the entry is a deviation (a proof supplement). A **deviation** is a deliberate difference of a formal statement or
proof from its source: scope, conventions, the reading of an ambiguous phrase, strengthened, specialized or
reformulated statements, explicit parameter windows in place of "small enough", proof supplements, and different
proof routes.

The record is a reader-facing rendering of the findings ledger [`errata/ledger.json`](errata/ledger.json); each
entry ends with its ledger identifier. It makes no claim about the formal proofs beyond the entries themselves. The
list of frozen theorems, their status and their axioms is in [`STATEMENTS.md`](STATEMENTS.md).

**Status of the errata.** Every erratum was checked against the pinned PDF by an independent verifier.

- *Verified* means that the verifier confirmed the local defect described in the entry, within the scope the entry
  states. It does not mean that the source's main theorem is false, that every proposed repair is certified, or
  that any formal proof was checked.
- *Historical report, verified* means that the verifier confirmed an author's published report of a defect in an
  earlier printing; the pinned version already contains the correction. These are counted separately.
- *Unverified* means that the verifier could neither confirm nor refute the allegation from the pinned text (for
  example because no source-admissible counterexample is known, or because the original is not pinned). Such entries
  are reports, not claims that the authors made an error. Where the verifier judged that an entry is better read as
  a convention or a proof supplement, the entry says so.
- Two earlier allegations were found to be wrong and are withdrawn; they are listed at the end.

**Quotations and locations.** Locations refer to the pinned version of each source recorded in
[`sources.json`](sources.json) (arXiv version or DOI, with the SHA-256 of the pinned PDF). "PDF p." is the page of the
pinned file; "p." alone is the printed page number where the two coincide or where the entry says so. Text in
quotation marks is verbatim prose of the pinned PDF. Displayed formulas, marked "Printed (transcribed)", are linearized
Unicode transcriptions of the printed mathematics, not verbatim typesetting. Counts are of entries, not occurrences;
editorial misprints are counted.

## Count

| Source | Pinned version | Errata verified | Historical reports | Unverified | Deviations |
|---|---|---|---|---|---|
| [Pos01](#pos01) | arXiv:0908.2234v1 | 4 | 1 | 0 | 2 |
| [GJLV05](#gjlv05) | doi:10.1088/0951-7715/18/2/020 | 5 | 0 | 0 | 1 |
| [FdlLS09](#fdlls09) | arXiv:0903.0311v1 | 0 | 0 | 1 | 0 |
| [CCdlL13](#ccdll13) | doi:10.1016/j.jde.2013.05.001 | 1 | 0 | 0 | 1 |
| [HL19](#hl19) | arXiv:1711.05515v1 | 14 | 0 | 1 | 8 |
| [Nek77](#nek77) | doi:10.1070/RM1977v032n06ABEH003859 | 3 | 0 | 0 | 6 |
| [LP17](#lp17) | arXiv:1703.07125v2 | 1 | 0 | 0 | 2 |
| [Chi05](#chi05) | pinned PDF | 1 | 0 | 0 | 3 |
| [CC03](#cc03) | doi:10.1090/memo/0878 | 0 | 0 | 1 | 1 |
| [BM11](#bm11) | arXiv:1004.1014v2 | 4 | 0 | 0 | 7 |
| [GCB16](#gcb16) | arXiv:1403.6776v1 | 2 | 0 | 1 | 0 |
| [Pos93scan](#pos93scan) | doi:10.1007/BF03025718 | 3 | 0 | 2 | 6 |
| [Nei76](#nei76) | pinned PDF | 1 | 0 | 0 | 3 |
| [CP10pin](#cp10pin) | doi:10.3934/dcdss.2010.3.545 | 13 | 0 | 3 | 10 |
| [Fej04r](#fej04r) | doi:10.1017/S0143385704000410 | 15 | 0 | 0 | 8 |
| [Fej07e](#fej07e) | pinned PDF | 0 | 1 | 0 | 0 |
| [Arn63b](#arn63b) | original not pinned | 0 | 0 | 1 (historical) | 0 |
| [CP11](#cp11) | doi:10.1007/s00222-011-0313-z | 2 | 0 | 0 | 1 |
| [CP09](#cp09) | arXiv:1206.3475v1 | 8 | 0 | 3 | 3 |
| [Rus01](#rus01) | doi:10.1070/RD2001v006n02ABEH000169 | 2 | 0 | 0 | 0 |
| [Rus05](#rus05) | doi:10.1070/RD2005v010n01ABEH000297 | 3 | 0 | 0 | 1 |
| [AKN06](#akn06) | doi:10.1007/978-3-540-48926-9 | 0 | 0 | 0 | 1 |
| **Total** | | **82** | **2** | **13** | **64** |

Withdrawn allegations (not counted above): 2.

## Pos01

J. Pöschel, *A lecture on the classical KAM theorem*, Proc. Symp. Pure Math. 69 (2001) 707–732. Pinned: arXiv:0908.2234v1.

### Errata

1. **PDF p. 24–25, choice of h₀ and K₀ in the proof of Theorem A.** *gap; verified.* Printed: "after fixing σ0 , K0 and E0 , we may set" h₀ = αc₀E₀σ₀^ν (formula transcribed; prose as in the PDF text layer) (p. 24) and "K0 is chosen so large that the left hand side of (f) is smaller than its right hand side, and small enough so that E0 can be fixed to meet (a) and (d)" (p. 25). These initial choices violate h₀ ≤ α(2K₀^ν)⁻¹, as Bou20 (arXiv:2006.04453v1, footnote 1, which locates the passage on p. 23) points out; Kou19 (arXiv:1904.13062v1, Remark 2.1.5(4), printed p. 28) shows that Theorems A and B are not obtained for ν = τ + 1 by that proof. This is a local proof defect, not a false KAM theorem: Bou20 restores Theorem A as stated by a different argument. Effect: none; the formal measure layer does not follow this proof. [E-Pos01-2]
2. **p. 13, measure statement after Theorem A.** *typo; verified.* Printed: "measure of Ωα × Tn". The O(α) estimate concerns the complement: it should read the measure of (Ω ∖ Ωα) × Tⁿ, since Ωα × Tⁿ itself has large measure as α → 0. Effect: none. [E-Pos01-3]
3. **p. 6, after the definition of Ω_α.** *false as stated; verified.* Printed: "or at least of dimension n − 1 so that the measure of a boundary layer of size α is O(α)". Hausdorff dimension n − 1 of the boundary does not give O(α) boundary layers. Counterexample: n = 1, Ω = (0,1) ∖ {1/k : k ≥ 1}; the boundary has dimension 0, but about α^(−1/2) separated boundary points already give an inner α-layer of measure of order √α. Effect: none; `KAM.kam_positive_measure` assumes a boundary-layer bound directly. [E-Pos01-4]
4. **p. 11, proof of Prop. 2.** *wrong constant; verified.* Printed (transcribed): ≤ |ϕ̄|_{L,Ω} m(Ω − Ω_α). The Lipschitz constant must be raised to the power n: the map x ↦ Lx scales n-dimensional measure by Lⁿ, so a map with L > 1 refutes the displayed general estimate. Effect: none; the formal measure lemma uses Λ^d. [E-Pos01-5]

### Historical report

1. **p. 29, footnote to Lemma A.2.** *missing hypothesis in the original printing; historical report, verified.* The author's footnote in the pinned arXiv version reports that the condition Kσ ≥ 1 is missing in the printed version (PSPUM 69); the pinned lemma contains it. This is a defect of the earlier printing, not of the pinned version. Effect: none. [E-Pos01-1]

### Deviations

1. **Whole proof.** *different proof route.* The tori are obtained from an a-posteriori fixed-frequency KAM theorem (parameterization method, no canonical changes of variables) applied at each Diophantine frequency, not by Pöschel's iteration of symplectic transformations. The setting is the same general Hamiltonian one. Effect: none on the statement `KAM.kam_positive_measure`. [D-ROUTE-1]
2. **Theorem (p. 6), Prop. 1–2 (p. 11).** *scope (weaker rate).* `KAM.kam_positive_measure` bounds the measure of the complement by C·ε^{1/4} (γ ~ ε^{1/4}), not Pöschel's O(√ε), and assumes a boundary-layer bound for the action domain. In the proof the tori are parameterized by their actions, and the measure step applies a McShane extension in action coordinates, so no regularity of the boundary of the frequency image is needed. Effect: the exponent of the headline is 1/4. [D-MEAS-1]

## GJLV05

R. de la Llave, A. González, À. Jorba, J. Villanueva, *KAM theory without action-angle variables*, Nonlinearity 18 (2005) 855–895. Pinned: doi:10.1088/0951-7715/18/2/020.

### Errata

1. **p. 864 (PDF p. 10), conclusion of Theorem 3.** *typo; verified.* Printed (transcribed): cγ²δ^{−2σ}, in both the embedding and the parameter bound. The exponent of γ should be −2, as in the proof step and in Theorems 1 and 5. Effect: none. [E-GJLV05-1]
2. **p. 865, Theorem 5.** *typo; verified.* Printed (transcribed): ‖e₀‖_{ρ₀} in the second smallness condition. The statement fixes ρ; ρ₀ is a stray subscript. Effect: none. [E-GJLV05-2]
3. **pp. 884–885, Lemma 14 (choice of the phase).** *gap; verified.* Printed (transcribed): a contraction Ψ on the open ball {|τ| < ‖K₁ − K₂‖_ρ}. For K₁ = K₂ this ball is empty, which already refutes the literal existence assertion; for K₁ ≠ K₂ the contraction estimate alone does not show that Ψ maps the ball into itself. Correction: use the closed ball of radius 2‖T‖_ρ‖K₁ − K₂‖_ρ. Effect: none on the formal statements; the proof of `KAM.local_uniqueness_flow` uses a closed ball. [E-GJLV05-3]
4. **p. 885, proof of Theorem 2.** *typo; verified.* Printed (transcribed): 0 < δ, ρ/2. It should read 0 < δ < ρ/2, as the preceding lemma and the loss calculations require. Effect: none. [E-GJLV05-4]
5. **p. 889, Prop. 18.** *typo; verified.* Printed (transcribed): a sum over j differentiated in θ_i, and the solution bounded by its own norm ‖v‖_ρ. The derivative index should be θ_j and the right-hand side should be ‖h‖_ρ. Effect: none. [E-GJLV05-5]

### Deviations

1. **Theorem 2 (maps), §6, §8.** *proof supplement.* `KAM.local_uniqueness_flow` states local uniqueness modulo phase for flows. GJLV05 (p. 865, Remark 7) declines to formulate such a theorem, and HL19 (Remark 3.5) asserts it without proof; the cited sources do not state or prove this exact flow theorem. It is proved directly for flows by adapting the map argument of GJLV05 §6 with the flow reducibility of §8 and Prop. 18 (not through the time-one map, which would need map-Diophantine frequencies): linearization at K₁, the phase fixed once by an average normalization, a uniqueness constant independent of γ, and the conclusion on the strip of half width. Effect: a statement of this formalization; no source statement changes. [D-UNIQ-1]

## FdlLS09

E. Fontich, R. de la Llave, Y. Sire, *Construction of invariant whiskered tori by a parameterization method. Part I: Maps and flows in finite dimensions*, J. Differential Equations 246 (2009) 3136–3213. Pinned: arXiv:0903.0311v1.

### Unverified

1. **§7.1, pp. 42–43.** *missing argument; unverified, classified as a proof supplement.* Printed: "Hence, we conclude that the map ω 7→ Kω is bi-Lipschitz from the set of Diophantine vectors with fixed Diophantine constants. Since the set D(κ, ν) has positive l-dimensional measure, we conclude that the set of tori also has 2l-dimensional measure" (the "7→" is ↦ in the PDF text layer). A bi-Lipschitz map ω ↦ K_ω into a function space does not by itself give positive measure of the union of the tori in phase space; an additional phase-space argument is needed. No counterexample to the conclusion under the paper's hypotheses is known, so this is a missing argument rather than an established false assertion. Effect: none; the formalization does not use §7.1 and supplies its own argument (D-LIP-1, D-MEAS-1). [E-FdlLS09-2]

### Deviations

None.

## CCdlL13

R. Calleja, A. Celletti, R. de la Llave, *A KAM theory for conformally symplectic systems: efficient algorithms and their validation*, J. Differential Equations 255 (2013) 978–1049. Pinned: doi:10.1016/j.jde.2013.05.001 (page numbers of the preprint mp_arc 11-188).

### Errata

1. **pp. 31–32.** *inconsistent statement; verified.* Printed: p. 31, "ℓ = 2 if we allow the constants to be independent on λ."; p. 32, "ℓ = 2 if we allow the constants to depend on λ.", followed on the same page by "where ℓ = 2 in the uniform case". The second sentence contradicts the other two. Effect: none. [E-CCdlL13-1]

### Deviations

1. **Cor. 29–30.** *proof supplement.* Lipschitz dependence of the tori on the frequency is obtained by re-applying the a-posteriori theorem at a nearby frequency (the CCdlL13 template), with an explicit error estimate, the phase controlled by the average normalization, and far pairs of frequencies treated separately. This is a proof deviation, not a hypothesis of a frozen theorem. Effect: explicit constants of the formalization. [D-LIP-1]

## HL19

A. Haro, A. Luque, *A-posteriori KAM theory with optimal estimates for partially integrable systems*, J. Differential Equations (2019). Pinned: arXiv:1711.05515v1.

### Errata

1. **p. 18, (3.11).** *strict inequality; verified.* Printed (transcribed): ‖K∞ − K‖_{ρ∞} < C₂‖E‖_ρ/(γ²ρ^{2τ}), and the other bounds of (3.11), including the bound on the average of the first integrals, strict. For an exact admissible torus, E = 0, each would require a nonnegative quantity to be < 0; they should read ≤. Effect: none; `KAM.aposteriori_kam` uses ≤. [E-HL19-1]
2. **p. 42, (5.66).** *typo; verified.* Printed (transcribed): denominator σ_B − ‖B‖. In the estimate of the twist term the denominator is σ_T − |⟨T⟩⁻¹|, as in the left part of the same display. Effect: none. [E-HL19-2]
3. **p. 55, Lemma A.1.** *strict inequality; verified.* Printed (transcribed): |M̄⁻¹ − M⁻¹| < 2σ²|M̄ − M|. This fails for M̄ = M; it should be ≤. In the proof, (A.3) reads |M⁻¹||M̄ − M| < σ²|M̄ − M|/(σ − |M⁻¹|) < 1/2: its first strict comparison fails when M̄ = M, and under (A.1), which is a non-strict hypothesis, the last comparison holds only with ≤ 1/2. The conclusion that M̄ is invertible is unaffected. Effect: none; the formal Neumann-series lemma uses ≤. [E-HL19-3]
4. **p. 33, (5.15)–(5.18); p. 43, (5.68).** *strict inequality; verified.* Printed (transcribed): ‖K̄ − K‖_{ρ−2δ} < C_ΔK‖E‖_ρ/(γ²δ^{2τ}) (5.15), and likewise strict bounds in (5.16), (5.17), ‖Ē‖_{ρ−2δ} < C_E‖E‖²_ρ/(γ⁴δ^{4τ}) (5.18) and (5.68). E = 0 is allowed by the smallness hypotheses and turns each into 0 < 0; they should be ≤. This is the origin of item 1. Effect: none. [E-HL19-4]
5. **p. 42, after (5.67).** *cross-reference; verified.* Printed: "(5.12) and (5.16)". The estimate of the inverse twist uses (5.13) and (5.17); (5.12) and (5.16) concern B. Effect: none. [E-HL19-5]
6. **p. 44.** *typo; verified.* Printed (transcribed): → 0 when s → 0. The iteration index s tends to infinity: s → ∞. Effect: none. [E-HL19-6]
7. **p. 19, Theorem 3.6 (3.16).** *strict inequality; verified.* Printed (transcribed): ‖K∞ − K‖_{ρ∞} < C₂‖E_c‖_ρ/(γ²ρ^{2τ}), |ω∞ − ω| < C₃‖E_c‖_ρ/(γ²ρ^{2τ}). For exact input with the correct energy, E_c = 0, both fail; replace < by ≤. This is the isoenergetic analogue of item 1. Effect: none; `KAM.Iso.isoenergetic_kam` uses non-strict bounds. [E-HL19-8]
8. **p. 18, (3.12), compared with p. 20, (4.1).** *sign; verified.* Printed (transcribed): X_h(K(θ)) = L_ω K(θ). With L_ω = −Σ ω_i ∂_i as defined in (4.1), and with (3.14), which uses X_h(K) − DK ω, the equation should read X_h(K) = −L_ω K. Effect: none. [E-HL19-9]
9. **p. 19, Remark 3.7.** *sign; verified.* Printed (transcribed): Dh(K(θ))N(θ) = X_h(K(θ))ᵀ Ω(K(θ))N(θ). From ΩX_h = Dhᵀ and Ωᵀ = −Ω one gets Dh = −X_hᵀΩ, so a minus sign is missing in the first equality; the next equality changes sign again, inconsistently. Effect: none. [E-HL19-10]
10. **p. 59, Table 5 caption.** *cross-reference; verified.* Printed: "Section 5.3". The constants of Table 5 are those of the isoenergetic Section 6.3, (6.45)–(6.51). Effect: none. [E-HL19-11]
11. **p. 53, (6.51), compared with p. 19, (3.16).** *constant normalization; verified.* Printed (transcribed): |ω∞ − ω| < C₃‖E_c‖_ρ/(γρ^τ), "thus obtaining the estimates in (3.16)". The same named constant C₃ is attached to γρ^τ in (6.51) and to γ²ρ^{2τ} in (3.16), and no displayed premise γρ^τ ≤ 1 makes the implication automatic. This is a normalization mismatch, not a failure of a theorem with suitably rescaled constants. Effect: none. [E-HL19-12]
12. **pp. 49–51, (6.33), (6.36), (6.44).** *wrong error quantity; verified.* Printed (transcribed): ‖E‖_ρ on the right-hand sides of (6.33), (6.36) and (6.44). The combined error ‖E_c‖_ρ, which includes the discrepancy from the prescribed energy, is needed: with E = 0 and an energy discrepancy e ≠ 0, the bordered zero-mode solve changes the frequency and the actions (for H = |I|²/2 the bordered inverse changes although E = 0), so E alone cannot bound these corrections. Effect: none. [E-HL19-13]
13. **p. 52, iteration convergence.** *typo; verified.* Printed (transcribed): when s → 0. As in item 6 (a separate occurrence), the decaying sequence a₁^(−4τs)‖E_c‖ with a₁ > 1 tends to zero as s → ∞. Effect: none. [E-HL19-14]
14. **p. 52, frequency-margin paragraph.** *cross-reference; verified.* Printed: "the eight term in (6.15)". The eighth term belongs to the maximum (6.16), as p. 49 states explicitly. Effect: none. [E-HL19-15]

### Unverified

1. **p. 19, H5′.** *boundary convention; unverified, classified as a convention.* Printed: "Notice that, by definition, we have dist(ω, ∂Θ) > 0". If ∂Θ is the boundary in ℝ^d with d ≥ 2, a segment has empty interior and the assertion fails; for the relative boundary of the segment it is correct, and that one-dimensional reading is probably intended. Effect: the frozen `KAM.Iso.isoenergetic_kam` measures the distance to the two endpoints explicitly. [E-HL19-17]

### Deviations

1. **§3.1 (analytic functions and norms).** *convention.* Following the source, hypotheses and conclusions of `KAM.aposteriori_kam` use pointwise (sup-type) bounds on complex strips; Fourier coefficient norms enter only in the proof of the cohomological estimates, through a conversion lemma. Effect: constants differ from the printed ones; the frozen statements carry their own constants or are qualitative. [D-NORM-1]
2. **§2 (Hamiltonian systems and invariant tori).** *specialization.* Phase space is represented in coordinates: angles in ℝⁿ with ℤⁿ-periodicity (period one), actions in an open subset of ℝⁿ, and the standard symplectic form, rather than the general exact-symplectic setting of the source. Effect: specialization of the setting. [D-COORD-1]
3. **Theorem 3.1, pp. 16–18; (5.74)–(5.77) in Section 5.3.** *reformulation (uniform constants).* In `KAM.aposteriori_kam` the constants depend only on n, τ, ρ, ρ∞, a bound on the derivatives of the Hamiltonian, σ_K, σ_B, σ_T, a margin μ and an upper bound γ̄ ≥ γ, whereas the source's constants depend on the input. The constants of the source increase with γ, which is why γ̄ is needed. Some hypotheses implied up to factors 2n are dropped, the first integrals are not transcribed, norms are pointwise operator norms on the open strip, and the conclusion has explicit μ/2 margins and ≤ in the closeness bound (cf. HL19 erratum 1). `KAM.local_uniqueness_flow` uses the same uniformization without γ̄. Effect: statements of `KAM.aposteriori_kam` and `KAM.local_uniqueness_flow`. [D-G1-1]
4. **§2.2, p. 7, (2.3).** *proof supplement.* The isotropy (Lagrangian property) of invariant tori with nonresonant frequency, which the source quotes as well known, is proved (modules `KAM/Head/Lagrangian.lean`, `KAM/Head/RealTorus.lean`), following GJLV05 Lemma 19. Effect: none on the statements. [D-LAG-1]
5. **Theorem 3.6; `KAM.Iso.isoenergetic_kam`.** *scope (uniform constants).* The constants C₁, C₂, C₃ are uniform over fixed strip, ray and margin bounds (including γ̄, ν and ω*) and precede the Hamiltonian, the torus and the error; the source's constants are tied to the input data. Effect: no theorem premise is added. [D-I-G1-UNIFORM]
6. **Theorem 3.6; energy convention of `KAM.Iso.isoenergetic_kam`.** *convention.* The theorem uses the physical energy h, pointwise strip bounds, a bordered extended torsion fixed in `KAM/Frozen/Iso/Defs/ExtendedTorsion.lean` and `EnergyAverage.lean`, and the combined error including the energy discrepancy. The sign corrections of HL19 errata 8–9 are separate. Effect: specialized isoenergetic theorem. [D-I-ENERGY]
7. **Theorem 3.6, geometric hypotheses.** *reformulation.* `KAM.Iso.isoenergetic_kam` assumes only its own analytic, frame, energy and ray premises. The geometric and perturbation lemmas it shares with the fixed-frequency development are stated without that development's admissibility condition A5, using only their own analytic and matrix premises. Effect: no unrelated hypothesis is imported into the isoenergetic theorem. [D-I-NOA5]
8. **p. 46, Lemma 6.1, and Lemma 5.1.** *proof supplement.* The bordered zero-mode and cohomological solve, including the energy identity and signs, is proved in full (`KAM/Iso/Linear/BorderUnique.lean` and neighbouring modules), where the source refers to the analogous computations of Section 5. The constant omitted under the cohomological inverse is not itself an erratum. Effect: none on the statements. [D-I-LINEAR-SOLVE]

## Nek77

N. N. Nekhoroshev, *An exponential estimate of the time of stability of nearly-integrable Hamiltonian systems*, Russian Math. Surveys 32(6) (1977) 1–65 (English translation). Pinned: doi:10.1070/RM1977v032n06ABEH003859.

### Errata

1. **pp. 56 and 58 (§12).** *numbering typo; verified.* Printed: the lemma is labelled "12.3.A" on p. 56 and cited as "12.4.A" on p. 58. Effect: none. [E-P-A-N77-1]
2. **p. 56, (12.6).** *typo; verified.* Printed (transcribed): T = (1/2) Σ mᵢ (ẋᵢ²/2). The inner factor 1/2 is duplicated: differentiating the printed kinetic energy gives half of the momentum formula (12.8) on the same page, whereas T = (1/2) Σ mᵢ ẋᵢ² agrees with it. Effect: none; the frozen moving Hamiltonian follows LP17 (5)–(6). [E-P-A-N77-2]
3. **p. 15, §1.18.** *typo; verified.* Printed: the perturbation "becomes small" when two bodies approach one another. The reciprocal-distance interaction grows instead; this is a local slip of wording, not a claim about close encounters. Effect: none. [E-N-ADD-1]

### Deviations

1. **§12, Theorem 12.3, printed pp. 55–56.** *specialization.* `planetaryExponentialSafety` specializes Theorem 12.3 to the planar problem with G = m₀ = 1, fixed positive planetary weights and planar prograde data in an explicit separated-annulus low-AMD region (`AMDBox`), with a symmetric exponential time window and explicit conclusions on uniqueness, Newton's equations and mutual distances. Effect: a narrower, explicit statement. [D-P-A-1]
2. **Theorem 4.4, p. 30, Remarks 4.5.A–B.** *specialization.* `KAM.Nekhoroshev.partialConvex_nekhoroshev` is a stopped theorem for Hamiltonians convex in the fast actions (G and G′ convex, a closed-ball collar G′ ⊇ G + real ρ-ball, complex Hessian control) with conclusions for initial fast actions in G. It specializes Theorem 4.4 rather than importing its steepness premise verbatim. Effect: a narrower input class. [D-N-ADD-1]
3. **§§4, 10, partial convexity.** *scope restriction.* The fast Hessian is definite with a global sign on the enlarged convex fast domain, h is fixed, and a complex Hessian bound is explicit; the more general steep setting of Theorem 4.4 is not claimed. Effect: narrower input class. [D-N-ADD-3]
4. **Theorem 4.4, stopped formulation.** *representation.* Max norms, a closed inner core, a normalized perturbation with a positive bound μ, and solution histories only on [0, t] for the queried time t. The solution on the stated interval is supplied as a hypothesis; unconditional long-time existence is not asserted by this stopped theorem. Effect: source Euclidean domains and stopping conventions are converted in the proof. [D-N-ADD-4]
5. **§10, Lemma 10.6 at the endpoint.** *proof specialization.* The endpoint argument uses the definite Hessian and the explicit collar G′ (energy argument in `KAM/Nekhoroshev/Partial/Energy.lean` and `EnergyIdentity.lean`) instead of steepness on an arbitrary bounded G. This refines item 2 and is not a separate erratum. Effect: none beyond item 2. [D-N-ADD-6]
6. **§10, normal form and time scale.** *different proof route.* The proof of the partial theorem uses an independent extended normal form and a frequency-free convex energy argument, with exponent 1/(2n); the threshold and time constants are assembled in `KAM/Nekhoroshev/Partial/Threshold.lean` and `ThresholdExplicit.lean`. An earlier draft of this argument used a Cauchy estimate outside its valid domain and was abandoned. Nekhoroshev's second paper (1979) is not pinned and is not used. Effect: none on the statement. [D-N-PARTIAL-ROUTE]

## LP17

J. Laskar, A. C. Petit, *AMD-stability and the classification of planetary systems*, Astronomy & Astrophysics 605 (2017) A72. Pinned: arXiv:1703.07125v2.

### Errata

1. **p. 17, between (B.9) and (B.10).** *typo; verified.* Printed (transcribed): {F, H₀} = 0. F is not the integral used in that argument; the surrounding identities use K, so it should read {K, H₀} = 0. Effect: none; the frozen statements use only (B.5), (B.8) and rotational invariance. [E-P-A-LP17-1]

### Deviations

1. **(B.5), (B.8), Appendix B.** *specialization; new result.* `secularBoxSafety` uses the full untruncated average over both mean longitudes in the fixed zero-coupling chart (`KAM/Frozen/Planetary/Defs/ExactSecularHamiltonian.lean`), and `secularBoxAtCitedMasses` gives an elementary rational box at cited decimal masses. They are statements about the averaged model, not the full Newtonian problem; LP17 Appendix B preserves angular momentum under averaging. Effect: averaged-model scope. [D-P-A-2]
2. **Secular definitions.** *proof supplement.* The moving and fixed secular functions are identified exactly, including the action-only diagonal term (`KAM/Planetary/SecularForm/Basic.lean`, `ParameterIntegral.lean`), rather than inferring equality of full germs from a match of quadratic jets. Effect: none on the statements. [D-P-SECULAR]

## Chi05

L. Chierchia, *The restricted, circular, planar three-body problem*, lecture notes, March 2005. Pinned: pinned PDF.

### Errata

1. **pp. 13–14, (3.38)–(3.39); compare p. 17.** *missing domain exclusion; verified.* Printed (transcribed): (x^(2), X^(2)) ∈ (ℝ² ∖ {0}) × ℝ². The displayed potential keeps the denominator of the secondary collision, which is singular at x^(2) = x_circ^(1)(t); this nonzero moving position belongs to the printed domain, so the domain is too large and must exclude it. Effect: none. [E-Chi05-1]

### Deviations

1. **§2; `KAM.Iso.kepler_bordered_det`.** *parameterization.* The theorem allows an arbitrary positive Kepler parameter κ and rotation rate Ω and gives the determinant 3κΩ²/L⁴; the source uses normalized constants. The action mean identities used in its proof are supporting lemmas, not conclusions of this theorem. Effect: none. [D-I-KEPLER]
2. **§3; `KAM.Iso.restricted_near_circular`.** *physical reformulation.* The theorem uses the exact barycentric restricted Hamiltonian, allows μ = 0, has a uniform μ₀ ≤ 1/2, and concludes all-time uniqueness of physical solutions and separation from both primaries; the source presents the heliocentric rotating problem. Effect: no truncated model stands in for the restricted problem. [D-I-PHYSICAL]
3. **p. 11, analytic Kepler equation.** *proof supplement.* The source's qualitative statement for small |e| is not false; the proof supplies an explicit complex tube with an eccentricity-dependent displacement guard (`KAM/Iso/Kepler.lean`, `KAM/Planetary/Poincare/Tube.lean`). This is not a premise of any frozen theorem. Effect: a uniform analytic chart through e = 0. [D-I-KEPLER-TUBE]

## CC03

A. Celletti, L. Chierchia, *KAM stability and celestial mechanics*, author preprint, December 2003; published as Mem. Amer. Math. Soc. 187(878) (2007). Pinned: doi:10.1090/memo/0878.

### Unverified

1. **p. 7, closing sentence of Theorem 1.1.** *scope ambiguity; unverified.* Printed: "A similar statement holds if ε_SJ is replaced by any complex perturbative parameter ε with |ε| ≤ 10⁻³" (transcribed from the rendered page; the text layer is corrupt). A nonreal ε does not in general define a real Hamiltonian flow; the "similar statement" may refer to complexified trajectories, in which case nothing is wrong. Effect: none; the result is not used. [E-CC03-1]

### Deviations

1. **Theorem 1.1; `KAM.Iso.all_time_confinement`.** *different theorem.* The formal theorem is a general qualitative confinement result for all points of a region and global solutions, with uniqueness; CC03's Theorem 1.1 is a computer-assisted statement for a specified numerical energy region. No numerical bound of CC03 is used. Effect: a different theorem. [D-I-CONFINEMENT]

## BM11

A. Bounemoura, J.-P. Marco, *Improved exponential stability for near-integrable quasi-convex Hamiltonians*, Nonlinearity 24 (2011) 97–112. Pinned: arXiv:1004.1014v2.

### Errata

1. **p. 9, Lemma 3.3.** *missing parameter restriction; verified.* Printed (transcribed): there exist constants ρ₀ and C, for unrestricted λ₀ > 0, and the ball B(Ψ_h(I₀), Cρ). The derivative of Ψ_h(I, λ) = (h(I), λω(I)) on p. 10 multiplies the transverse Hessian directions by λ₀, so in the quadratic example h(I) = |I|²/2 + v·I its smallest singular value tends to zero as λ₀ → 0 and no fixed C works; the centre also omits λ₀. A pointwise inverse-function statement, or a quantitative restriction on λ₀, is correct. Effect: none. [E-N-BM-2]
2. **p. 13, restart argument.** *invalid inference; verified.* Printed: "taking ε₀ small enough, we can ensure that I(t*) ∈ B(0,R/2)". A displacement bound that is uniform in I₀ does not keep I(t*) in the same open ball for I₀ arbitrarily close to its boundary. This refutes the stated inference only; enlarging the restart domain repairs it and Theorem 2.1 is not affected. Effect: none. [E-N-BM-3]
3. **p. 8, import of Pos93; compare p. 4, B(M).** *missing import hypothesis; verified.* Printed: "exactly the content of Theorem 3". Theorem 3 of Pos93 (printed p. 190) assumes a uniform complex Hessian bound, which the real derivative bounds B(M) do not supply: h_N = 3I₀ + |I|²/2 + sin(NI₁)/(4N³) has uniformly bounded real derivatives up to order 3 but no uniform complex Hessian bound on a fixed strip. This is a defect of the import, not a counterexample to the main theorem of BM11. Effect: none. [E-N-BM-4]
4. **p. 12, resonant integer vector.** *type typo; verified.* Printed (transcribed): k′ = q e_i − p e_j ∈ ℤ. The vector lies in ℤⁿ. Separately, coprimality of p and q does not by itself give k′ ≠ 0 (take i = j, p = q = 1), so the selection needs a guard excluding this degenerate case; this is not a counterexample to the stability theorem. Effect: none. [E-N-BM-5]

### Deviations

1. **Dimension.** *scope.* `KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` requires n ≥ 3; the supporting statements `quasiConvex_isoenergetic_derivative` and `zero_perturbation` carry no such bound. BM11 is more general. Effect: narrower headline. [D-N-1]
2. **Size of the perturbation.** *convention.* The perturbation size is a non-strict pointwise upper bound (`IsAnalyticPerturbation`), where BM11 uses a strict one; a fixed factor in the threshold converts between them. The positive-size theorem keeps ε > 0 separately. Effect: none. [D-N-2]
3. **ε = 0.** *endpoint reformulation.* `KAM.Nekhoroshev.zero_perturbation` states the integrable orbit for all times for size zero, separately from the exponential statement for positive ε, so no positive-time formula is evaluated at a zero denominator. Effect: none. [D-N-3]
4. **Solutions.** *strengthened conclusion.* The headline gives a solution on the symmetric closed exponential interval, the drift bound, uniqueness against other solutions, and assumes the explicit margin C ε₀^(1/(2n)) ≤ R/4. Effect: genuine additions to the statement. [D-N-4]
5. **Typing and domains.** *representation.* Typing, real-analytic regularity and domains are stated explicitly in `KAM/Frozen/Nekhoroshev/Defs/IsAnalyticIntegrable.lean`, `IsAnalyticPerturbation.lean` and `IsSolutionOn.lean`. Effect: none. [D-N-5]
6. **Lemma 3.3.** *local reformulation.* `KAM.Nekhoroshev.quasiConvex_isoenergetic_derivative` proves that the derivative is bijective at each admissible (I, λ), which supports a pointwise inverse-function argument, instead of the λ-uniform image ball (cf. BM11 erratum 1). Effect: none. [D-N-6]
7. **Selected endpoint.** *scope.* Only the classical stability estimate with exponent 1/(2n) is formalized; BM11's improved trade-offs, the fixed-radius second clause and the Gevrey extension are not. Effect: narrower headline. [D-N-7]

## GCB16

M. Guzzo, L. Chierchia, G. Benettin, *The steep Nekhoroshev's theorem*, Comm. Math. Phys. 342 (2016) 569–601. Pinned: arXiv:1403.6776v1.

### Errata

1. **p. 3, quasi-convex steepness sentence.** *index typo; verified.* Printed (transcribed): α₁ = ··· = α_n = 1. The definition that follows has n − 1 steepness indices; the last subscript should be n − 1. Effect: none. [E-N-GCB-2]
2. **p. 3, footnote 5.** *index typo; verified.* Printed (transcribed): |u| = Σ_i |u₁|. The summand should be |u_i|; as printed, a nonzero vector with first coordinate zero has size zero. Effect: none. [E-N-GCB-3]

### Unverified

1. **p. 4, main stability theorem.** *endpoint convention; unverified, classified as a convention.* Printed (transcribed): 0 ≤ ε < ε₀ and the time T/√ε exp(c/ε^a). At ε = 0 the time needs a limiting (integrable, all-time) convention; such conventions are common, and nothing false is asserted for positive ε. Effect: the formalization treats ε = 0 separately (D-N-3). [E-N-GCB-1]

### Deviations

None.

## Pos93scan

J. Pöschel, *Nekhoroshev estimates for quasi-convex Hamiltonian systems*, Math. Z. 213 (1993) 187–216. Pinned: doi:10.1007/BF03025718 (scan; printed page numbers, with PDF pages).

### Errata

1. **Printed p. 190 (PDF p. 5), explanatory sentence on the norm.** *false for complex matrices; verified.* Printed: "For the symmetric operator Q this norm amounts to the spectral radius norm". This holds for real symmetric Q but not for the complex symmetric Hessians in the preceding bound: Q = [[i, 1], [1, −i]] is symmetric and nonzero with Q² = 0. Effect: none; the operator norm is used. [E-N-POS-1]
2. **Printed p. 194 (PDF p. 9), end of Case B.** *sign misprint; verified.* Printed (transcribed): ≤ e^(Ks/6) ε. The preceding line and the target of the normal-form lemma have e^(−Ks/6) ε. The printed bound is weaker but true; this is an editorial misprint of the target. Effect: none. [E-Pos93-1]
3. **Printed p. 214 (PDF p. 29), proof of Lemma B.3, Cauchy formula.** *typo; verified.* Printed (transcribed): u_(I_i) = (1/(2πi)) ∫_γ u(I+ζ, θ)/ζ dζ. The derivative kernel needs ζ²: for u ≡ 1 the printed right-hand side is 1 while the derivative is 0. The subsequent integral estimate must change accordingly. Effect: none. [E-Pos93-7]

### Unverified

1. **Printed p. 195 (PDF p. 10), final telescoping display.** *questioned estimate; unverified.* Printed (transcribed): |W₀(Ψ − id)|_𝒫, ½|W₀(DΨ − I)W⁻¹|_𝒫 ≤ 2qε₀/(αρ₀σ₀) ≤ 2⁵qK ε/(αr). The derivative bound was questioned on the basis of the scales of the later iteration steps, but scale arithmetic does not refute a sharper estimate and no violating map is known. The formal proof uses componentwise displacement bounds and a separate preimage argument instead. Effect: none. [E-Pos93-2]
2. **Printed p. 199 (PDF p. 14), proof of Lemma 2.** *possible missing control; unverified.* Printed (transcribed): |⟨ω(I(s)), PΔI⟩| ≤ (5/4)δ‖ΔI‖. The projected-frequency estimate is established on a smaller domain than the segment on which it is used, and the mean-value theorem alone gives ‖Pω(I(s))‖ ≤ 5δ/4 + M‖I(s) − I₀‖. No Hamiltonian satisfying all the hypotheses and violating the estimate is known. The guards Mr ≤ ℓ/4 and Mr ≤ ℓ/2 used in the formal proof are sufficient, not evidence that the source is false. Effect: none. [E-Pos93-4]

### Deviations

1. **Hessian bound.** *stronger analytic input.* `KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` assumes a uniform complex Hessian bound and a positive lower frequency bound, given separately before the constants, as in Pos93 (printed p. 190). The real-bound version is not one of the frozen theorems. Effect: statement of the headline. [D-N-8]
2. **Dimension of supporting statements.** *scope.* `quasiConvex_isoenergetic_derivative` and `zero_perturbation` hold for arbitrary n with their actual geometric and analytic hypotheses; this does not enlarge the dimension range n ≥ 3 of the headline. Effect: none. [D-N-9]
3. **Norms and periods.** *convention.* The frozen statements use max norms and period-one angles; Pos93 uses Euclidean Hessian and Fourier norms and period 2π. The conversion factors (coth, √n, time prefactors) are paid in the proof. Effect: different constants. [D-N-10]
4. **Printed pp. 196, 199–200.** *proof supplement.* Surjectivity of near-identity maps onto preimages, stopped transfer to the original coordinates, continuation and first exit, which the source compresses, are proved explicitly (`KAM/Nekhoroshev/Partial/Preimage.lean`, `Transfer.lean`). No source assertion is shown false. Effect: none. [D-N-POS-TRANSFER]
5. **Printed pp. 200–204.** *proof convention.* The resonance geometry uses Euclidean lattices while the statement uses max coordinates; the cutoffs K_a and K_g = √n K_a are distinguished and the lattice volume and covering inequalities are proved. This is not a new premise. Effect: a √n loss in the cutoff and time constants. [D-N-POS-GEOMETRY]
6. **Printed pp. 211–215, Appendices B–C.** *proof supplement.* Equality of the convergent Lie series with the composition of flows, and the weighted Fourier and domain conversions, are proved explicitly in the analytic Hamiltonian composition and flow modules. The source's compressed calculation is a true step, not an erratum. Effect: none. [D-N-LIE-SERIES]

## Nei76

A. I. Neishtadt, *Averaging in multifrequency systems. II* (Russian: Об осреднении в многочастотных системах. II), Dokl. Akad. Nauk SSSR 226(6) (1976) 1295–1298. Pinned: pinned PDF.

### Errata

1. **p. 1298, (17); z(t) on p. 1297; h in (4), p. 1295.** *false identity in a proof; verified.* Printed (transcribed): sup_(0≤t≤ε⁻¹) z(t) = ∫_(U′) h dI⁰ dφ⁰ < K₁√ε. Here z(t) is the integral over initial data of the error at a fixed time, and h is the supremum in time of the error, pointwise in the initial data; the equality interchanges supremum and integral. Two groups of initial data whose errors peak at different times give different sides. Only sup_t ∫ ≤ ∫ sup_t holds in general. This is a false printed identity, not a counterexample to the averaging theorems. Effect: none; see D-NAVG-3. [E-NAVG-NEI-17]

### Deviations

1. **pp. 1295–1298.** *specialization.* `averaging_mean` and `averaging_most` treat analytic Hamiltonian systems with n ≥ 2 equal action and angle dimensions, fixed h, f and K before the constants, period-one angles, absolute volume and genuine solutions; Nei76 treats general multifrequency systems. Effect: narrower statements. [D-NAVG-1]
2. **p. 1296, condition 3°; AKN06, printed p. 243.** *reformulation.* `HasAveragingFrequencyRank` (in `KAM/Frozen/Nekhoroshev/Defs/`) requires either global surjectivity, or a nonzero frequency together with surjectivity of the augmented derivative. Nei76 uses a chart with a nonzero first frequency component; AKN06 uses the intrinsic projective rank. The frozen alternative is not a pointwise mixture of the two. Effect: none. [D-NAVG-2]
3. **(17).** *different proof.* The proof (`KAM/Nekhoroshev/Averaging/Mean.lean` and its envelope and exit modules) identifies supplied solutions with the maximal flow, integrates the error, and bounds the stopped error on a good set with a Markov-inequality exceptional set; it does not use the sup/integral equality of (17). Effect: none on the statements. [D-NAVG-3]

## CP10pin

L. Chierchia, G. Pinzari, *Properly-degenerate KAM theory (following V. I. Arnold)*, Discrete Contin. Dyn. Syst. Ser. S 3 (2010) 545–578. Pinned: doi:10.3934/dcdss.2010.3.545 (printed pages).

### Errata

1. **p. 556, Step 1, extension of the frequency diffeomorphism.** *missing hypothesis; verified.* Printed: "Without loss of generality" the frequency diffeomorphism is extended to V_ρ₀. Invertibility on the open set V alone allows a degenerate Hessian at the boundary (h = I¹⁶/16 on (0,1)), and then no fixed collar works. Effect: `properlyDegenerateKAM` assumes the diffeomorphism on a neighbourhood W ⊃ cl V (D-PG-4). [E-P-CP10-INV]
2. **p. 561, after (56).** *missing boundary regularity; verified.* Printed (transcribed): meas(V_ρ₀ ∖ V) ≤ C γ̄₂. A bounded open set need not satisfy a linear collar-volume bound (bounded open combs do not). Effect: `properlyDegenerateKAM` has an explicit boundary-collar hypothesis (D-PG-5). [E-P-CP10-BOUNDARY]
3. **p. 561, (56); compare p. 559, (47).** *wrong exponent; verified.* Printed (transcribed): ε^(n₂/2). Removing a √ε-fraction at each face of the rectangular action domain removes 1 − (1 − c√ε)^(n₂) ~ n₂c√ε, of order √ε. In addition, (56) compares this positive rectangular shell with a signed action ball, whose leading volume normalization needs separate correction; correcting the exponent alone does not repair the display. Neither issue changes the intended final O(√ε) rate. Effect: none. [E-P-CP10-ANNULUS]
4. **p. 554, Proposition 3, definition of Û.** *dimension typo; verified.* Printed (transcribed): "n × n₁ submatrix", Û_ij = U_ij for n₁+1 ≤ i ≤ n, 1 ≤ j ≤ n. The index ranges define an n₂ × n matrix. Effect: none. [E-CP10-1]
5. **p. 565, Lemma B.1, initialization.** *typo; verified.* Printed (transcribed): M̂₀ := M. The slow Hessian bound must be initialized by the separately given M̂, as the slow-scale radius and the displacement bookkeeping require. Effect: none. [E-CP10-2]
6. **p. 566, B.1(i), composition of frequency maps.** *index typo; verified.* Printed (transcribed): ω_(j−1)⁻¹ ∘ ω_(j−1). This is the identity; the stated codomain D_j and ω_j(D_j) = ω_(j−1)(D_(j−1)) require ω_j⁻¹ ∘ ω_(j−1). Effect: none. [E-CP10-3]
7. **p. 555, Proposition 3.** *missing normalization; verified.* Printed: "a unique real–analytic embedding". Without a phase normalization the embedding is not unique: for an exact torus and a positive error budget, small phase translations satisfy the same bounds and equation. Uniqueness of the torus as a set does not give uniqueness of the embedding. Effect: none. [E-CP10-6]
8. **p. 555, Proposition 3, global Lipschitz claim; Appendix B.** *missing global control; verified.* Printed: "the map (ϑ;ω) → φ_ω(ϑ) is Lipschitz and one–to–one". For an arbitrary, possibly disconnected and unbounded, parameter domain, a locally bounded inverse differential does not give a global Lipschitz bound: separated action islands near j² with local frequency map I ↦ I − j² + j have frequencies near j but action distances growing quadratically, and nonresonant centres preserve the obstruction at f = 0. This refutes the global formulation, not its local or compact version. Effect: none. [E-CP10-7]
9. **p. 565, (70) and the two sums that follow.** *wrong mode set; verified.* Printed (transcribed): Σ_(|k|≤K̄, k∈Λ) f_k(u)/(i k·ω(I)) e^(ik·φ). The hypothesis controls divisors only off Λ and the conclusion keeps the Λ-modes, so all three sums must run over k ∉ Λ; for Λ = {0} the printed sum divides the zero mode by zero. Effect: none. [E-CP10-8]
10. **p. 564, Lemma A.1, (66).** *wrong target strip; verified.* Printed (transcribed): φ : W_(v−2ν, s−2σ) → W_(v,σ). The target width should be s: for f = g = 0 the map is the identity and cannot send width s − 2σ into width σ when s > 3σ. Effect: none. [E-CP10-9]
11. **p. 563, proof of Theorem 1.5, Step 1; compare p. 564, A.1.** *inconsistent substitution; verified.* Printed (transcribed): ρ = ρ̄, r = ρ̄. Lemma A.1 requires ρ < r/2. A value such as ρ = ρ̄/4 would be consistent with the stated output radius; this is a suggested repair, not source text. Effect: none. [E-CP10-10]
12. **pp. 562–563, Lemma 3.1 and (59).** *overstated dependence; verified.* Printed: the covering integer p is "depending on D̄ and ω₁", with constants independent of ε and μ. For ω = (I₁, I₁ + I₂) the mixed resonance (1, −1) has divisor |I₂|, and as the slow radius r̂ → 0 its bad fraction is of order γ₁/r̂, not uniformly O(γ₁), even with γ₂ much smaller. The abstract lemma's restricted dependence is false; uniformity of the final KAM theorem is a different claim and is not refuted. Effect: none. [E-CP10-12]
13. **p. 562, use of Lemma 3.1, (59).** *invalid substitution; verified.* Printed (transcribed): ω = ω_resc := (∂_(J₁)(H₀ + μN̆), ∂_(J₂)N̆). Rescaling only the slow block changes the mixed divisors, so a bound for ω_resc does not bound the resonant set of ω_μ: with H₀(I) = I²/2, N(ξ) = ξ + ξ²/2, μ = √2/10, at (I, ξ) = (μ, 0) the map ω_μ = (μ, μ) is resonant at (1, −1) while ω_resc = (μ, 1) satisfies a Diophantine bound for small thresholds. This refutes the asserted inclusion, not properly degenerate KAM theory. Effect: none. [E-CP10-13]

### Unverified

1. **p. 564, conclusion for Theorem 1.5.** *missing argument; unverified, classified as a proof supplement.* Printed (transcribed): K = K* ∩ P_(c₂ε). The intersection of an invariant set with an arbitrary cylinder need not be invariant, but no torus of the constructed family that is actually cut by this cylinder has been exhibited. Effect: the formal proof selects whole tori (D-P-CELL). [E-P-CP10-WHOLE]
2. **p. 555, (35); p. 572, (107).** *questioned sharper estimate; unverified.* Printed (transcribed): |v₂(·;ω) − I₂⁰(ω)| ≤ 10n(M̄₂/M̄ + M̂/M) Êρ̂. The one-step estimate (107) gives the displacement without the M̂/M refinement, which does not exclude a stronger proof; no counterexample to (35) is known. Effect: the formal proof uses its own two-scale bounds. [E-CP10-4]
3. **p. 551, norm conventions and Appendix B.** *unverified.* Printed (transcribed): |I|₁, |φ|∞, |p|∞, |q|∞. The mixed norms are stated explicitly, which is not itself inconsistent, and no specific bound that fails in those norms has been identified. Effect: the formal proof uses max norms with its own constants (D-P-NORM). [E-CP10-5]

### Deviations

1. **Analyticity in the parameter.** *uniform analytic input.* `properlyDegenerateKAM` requires joint analyticity (`AnalyticOnNhd`) on [0, μ₀] times the closed cylinder, with all data fixed before r and μ; CP10 is less explicit about uniform parameter neighbourhoods. Effect: statement of the theorem. [D-PG-1]
2. **Angles.** *convention.* Physical fast angles have period 2π (`KAM/Frozen/Planetary/Defs/FastShift.lean`, `SecularAverage.lean`), while torus parametrizations and Diophantine conditions use period one; CP10 fixes its own 2π conventions. The conversion is part of the proof. Effect: none. [D-PG-2]
3. **Oscillator domain.** *convention.* The oscillator domain is a product of discs (`KAM/Frozen/Planetary/Defs/Cylinder.lean`), not a Euclidean ball in all oscillator variables, and the fast coordinate norm is the max norm; CP10's unqualified balls and mixed norms are made explicit this way. Effect: none. [D-PG-3]
4. **Frequency diffeomorphism.** *boundary input.* `properlyDegenerateKAM` assumes `HasFastDiffeomorphism H₀ W` on a neighbourhood W ⊃ cl V, which provides a C¹ inverse there (cf. CP10 erratum 1). Numerical bounds on the inverse are derived in the proof on compact collars; they are not a separate numerical hypothesis of the theorem. Effect: statement of the theorem. [D-PG-4]
5. **Boundary of V.** *boundary geometry.* `properlyDegenerateKAM` assumes an explicit linear measure bound for neighbourhoods of the frontier of V (the boundary-collar hypothesis; cf. CP10 erratum 2). Localizing to interior boxes is an alternative formulation that was not selected. Effect: statement of the theorem. [D-PG-5]
6. **Appendix A.** *proof supplement.* The two-scale averaging estimates are proved directly on complex domains in the planetary averaging and two-scale modules (`KAM/Planetary/Averaging/`, `KAM/Planetary/TwoScale/`); no numerical constant of CP10 is a premise of the theorem. Effect: none. [D-P-AVERAGING]
7. **pp. 551, 573, norms.** *proof convention.* The measure estimates use max norms and a componentwise McShane extension (`KAM/Measure/McShane.lean`) with changed constants, where CP10 uses mixed norms and Kirszbraun's theorem. This is a different route, not a refutation of the source constants. Effect: none. [D-P-NORM]
8. **Appendix B.** *proof supplement.* Inverse ball lifting, near/far parameter Lipschitz bounds and holomorphic convergence on a fixed strip are proved on explicit domains (`KAM/Planetary/TwoScale/LimitMapLip.lean`, `Lipschitz.lean`); CP10 suppresses these arguments. The global-domain issue is CP10 erratum 8. Effect: none. [D-P-KAM-SUPPLEMENTS]
9. **pp. 559–564, whole tori and measure.** *stronger conclusion.* `IsCylinderKolmogorovSet` requires each torus to lie entirely in the set, and `properlyDegenerateKAM` has both strict measure inequalities; the proof selects whole tori and deletes a measurable subfamily (`KAM/Planetary/PGMeasure/`). A bare intersection with the cylinder, as in the source, does not give this. Effect: statement of the theorem. [D-P-CELL]
10. **Theorem 1.5, fifth-order remainder.** *proof supplement.* The uniform fifth-order remainder is derived from the analytic jet on a smaller compact domain, after choosing the oscillator radius; the source's O(5) notation is not false. Effect: none. [D-P-REMAINDER]

## Fej04r

J. Féjoz, *Démonstration du 'théorème d'Arnold' sur la stabilité du système planétaire (d'après Michael Herman)*, Ergodic Theory Dynam. Systems 24(5) (2004) 1521–1582; pinned revision of January 2007, 65 pp. Pinned: doi:10.1017/S0143385704000410.

### Errata

1. **p. 55, proof of Proposition 73, q_jk display.** *mass indices; verified.* Printed (transcribed): m_k m_k in the second q_jj sum and in q_jk for j < k. These should be m_j m_k; the second diagonal sum also lacks the factor 2 in the denominator present in the first and required by (36). Unequal masses expose the asymmetry. The global normalization is item 3. Effect: none. [E-P-Fej04r-1]
2. **p. 56, Lemma 76.** *false analytic continuation; verified.* Printed: "fonctions méromorphes sur la sphère de Riemann ayant pour points singuliers les quatre pôles 0, ±1, ∞". b_(1/2)^(0) diverges logarithmically at α = 1 and is regular at 0, so it is not a single-valued meromorphic function with these poles. Effect: none. [E-P-Fej04r-2]
3. **pp. 50–51, (35)–(37), compared with the corrected (31), p. 47.** *normalization factor; verified.* Printed (transcribed): C₁ = −α b_(3/2)^(1)(α)/(2a_j), C₂ = α b_(3/2)^(2)(α)/(2a_j). The corrected chart (31) has √(2Λ), while (35)–(37) keep the coefficients of the older scale: the canonical pair average gives the diagonal −m_j m_k α b₁/(4 a_outer Λ_j), half the printed coefficient, so both C₁ and C₂ should be halved. Effect: none. [E-P-Fej04r-3]
4. **pp. 53–54, Corollary 72.** *missing hypothesis; verified.* Printed (transcribed): A_ε ∈ M_n(ℝ) symmetric; (A_ε)_nn = c₁ + c₂ε^β; σ_n(ε) = ε(c₁ + c₂ε^β) + O(ε²). A bound on A_ε is missing: D = diag(1, 0), A_ε = [[0, 1/ε], [1/ε, 0]], c₁ = c₂ = 0 gives two fixed nonzero eigenvalues, contradicting the O(ε²) conclusion. Effect: none. [E-P-Fej04r-6]
5. **p. 58, induction block matrix.** *wrong exponent; verified.* Printed (transcribed): Q̂_h + O(a_n^(5/2)) on the old diagonal block. Since b_(3/2)^(1)(a_n/a_j) = 3a_n/(2a_j) + O(a_n³), the block has a nonzero correction of order a_n² with the outer actions fixed. The off-diagonal coupling bound O(a_n^(5/2)) is true (it is in fact O(a_n^(11/4))). Effect: none. [E-P-Fej04r-7]
6. **p. 56, the domain A^C after Lemma 76.** *false topology; verified.* Printed: "l'ouvert simplement connexe". Rotating all a_j simultaneously through one turn preserves every ratio inequality, and its projection to a₁ ∈ ℂ* has winding number one, so the loop does not contract. (In an early version of the ledger this entry had the identifier now used by item 3.) Effect: none. [E-P-Fej04r-9]
7. **p. 53, proof of Lemma 71.** *missing normalization; verified.* Printed: "il existe une unique matrice U ∈ M_n(R) telle que e^(−εU)(D+εA)e^(εU)=D+O(ε²)" (formula transcribed). With A = 0 every diagonal U commutes with D and satisfies the identity; uniqueness holds for the zero-diagonal skew solution. Effect: none. [E-P-Fej04r-10]
8. **p. 48, small eccentricity and inclination expansion before Theorem 62.** *normalization factor; verified.* Printed (transcribed): |r_j| = √(Λ_j/2) ε_j(1 + O(ε_j²)); |z_j| = √(Λ_j/2) ι_j(1 + O(ε_j²) + O(ι_j²)). With the corrected (31), |r|² = Λe² + O(e⁴), so the factor is √Λ_j. Effect: none. [E-P7-Fej48]
9. **p. 50, Lemma 64.** *missing mass factor; verified.* Printed (transcribed): Y_j = μ_j Ẋ_j = (μ_j³ M_j²/Λ_j³) ∂_(λ_j) X_j. By (33) on p. 48 the coefficient μ_j³M_j²/Λ_j³ is the mean motion alone; the momentum needs one more μ_j. The zero-average argument of the lemma is unaffected. Effect: none. [E-P8-Fej50]
10. **p. 45, proof of Theorem 60, flat remainder.** *invalid inference; verified.* Printed: "Comme le jet d'ordre infini de R₃ est nul ... la restriction de R₃ à un petit voisinage de ce tore est exponentiellement petite en fonction de la taille du voisinage". The C^∞ flat function exp(−(log(1/x))²) is larger than exp(−c/x^a) near 0 for every a, c > 0. This refutes the general inference; finite-order flatness can suffice for the argument, and the existence of the tori is not in question. Effect: none. [E-P-Fej04r-11]
11. **p. 42, Theorem 60 (1°–3°), versus Definition 32, p. 17, and the proof, p. 45.** *fixed constant; verified.* Printed: "il existe des réels ε₀, γ, τ > 0", with β O(ε)-close to 0 and (α, β) ∈ DH_(γ,τ)(p, q) (transcribed). Definition 32 requires |β_j| ≥ γ, so for ε < γ/C no such frequencies exist; the proof on p. 45 instead chooses a shrinking γ̂. The statement with fixed γ and the proof's normalization differ. Effect: none; this does not concern the existence of tori with smaller γ. [E-P-Fej04r-12]
12. **p. 34, Example 47, with (23)–(24), p. 33.** *wrong example constants; verified.* Printed: "est (1/√p, (p−1)!)-gauche" (transcribed). With the Euclidean operator norm fixed on p. 33, at p = 2, t = 1 both [[1, 1], [0, 1]] and its inverse have norm (1 + √5)/2 > 1, so the stated pair of bounds fails. Effect: none. [E-P-Fej04r-13]
13. **pp. 38–39, proof of Theorem 58, slicing displays.** *wrong complement and ratio; verified.* Printed (transcribed): (a/b + 1)(γ/a)^(1/p) on p. 38; ν̂(t′) ∈ DH_(γ,τ)(p) and ν̂(t̂) ∈ DH_(γ,τ)(p) on p. 39. The p. 38 factor should be b/a as in the preceding bound, and the two p. 39 sets whose measure is declared small must use ∉: for p = 1 and a constant nonzero frequency the good set is the whole interval. Effect: none. [E-P-Fej04r-14]
14. **p. 44, Step 5, polar localization; compare CP09, p. 15.** *missing margin; verified.* Printed (transcribed): "boule centrée en ρ° et de rayon δ=‖ρ°‖/2". For a small multiple of ρ° = (1, 0.01) this ball contains points with negative second action, where the polar map is undefined; a radius controlled by min_j ρ°_j repairs it. Effect: none. [E-P-Fej04r-15]
15. **p. 58, after the induction block matrix.** *index typo; verified.* Printed: "σ̂₁,...,σ̂_n sont les valeurs propres de Q̂_h" (transcribed). The old block is (n−1) × (n−1), and the preceding line lists j = 1, …, n − 1; the list ends at n − 1. Effect: none. [E-P-Fej04r-16]

### Deviations

1. **Planar statement.** *scope.* `planarTwoPlanetKAM` assumes only a₀ < a₁, positive physical constants and η > 0, and gives a moving Kolmogorov set of four-dimensional tori. A factor-four restriction on the axes that appeared in an earlier proposal of this formalization was removed; it is not attributed to Fej04r. Effect: statement of the theorem. [D-PLANAR-1]
2. **Physical constants.** *physical reformulation.* `planarTwoPlanetKAM` and `fixedSunPlanetaryKAM` take arbitrary G, m₀ > 0, and their Kolmogorov-set and physical-torus predicates carry the reconstruction of Newtonian solutions, where Fej04r works in normalized coordinates. Effect: statement of the theorems. [D-PHYS-1]
3. **Spatial problem.** *scope limit.* No spatial planetary theorem is formalized; the planar results do not give one. Fej04r's spatial discussion is a comparator only. Effect: none. [D-SPATIAL-1]
4. **pp. 50–55, secular matrix.** *proof supplement.* The planar secular quadratic form is derived directly from pair averages in increasing-axis order (`KAM/Planetary/SecularForm/Quadratic.lean` and the diagonal-jet modules), where Fej04r uses the reverse order; the matrix corrections of errata 1, 3 are not copied. Effect: none. [D-PROOF-1]
5. **p. 56, analytic continuation.** *different proof.* The spectral and nondegeneracy arguments (`KAM/Planetary/SecularSpectrum/`, `KAM/Planetary/Nondegeneracy/`) use local analytic spectral data; no frozen theorem assumes global meromorphy of Laplace coefficients or simple connectivity of A^C (cf. errata 2, 6). Effect: none. [D-PROOF-2]
6. **pp. 46–48, Theorem 62, Poincaré chart.** *proof supplement.* The regular Poincaré chart through circular orbits is developed in `KAM/Planetary/Poincare/Holomorphic.lean`, `Symplectic.lean` and `Product.lean`, with the corrected √(2Λ) scale. Effect: none. [D-P-KEPLER]
7. **p. 51, spectral change of oscillator variables; CP09, p. 14.** *proof supplement.* A rotation of the oscillator variables that depends on the actions needs a correction of the fast angles to be symplectic on the full chart; this lift is constructed in the secular spectrum modules. A statement about a fixed-action fibre alone is not false. Effect: none. [D-P-CANONICAL-LIFT]
8. **pp. 57–58, induction.** *proof supplement.* Quantitative symmetric spectral perturbation, resonance products and the induction on the axes are supplied (secular spectrum and planar torsion modules); the frozen theorems need nondegeneracy on a suitable patch, not the omitted details as assumptions. This is separate from erratum 5. Effect: none. [D-P-INDUCTION]

## Fej07e

J. Féjoz, *Erratum de la Démonstration du 'théorème d'Arnold' et addendum*, 6 February 2007, 5 pp. Pinned: pinned PDF.

### Historical report

1. **pp. 1–3, author corrections to the original 2004 article.** *historical report, verified.* Printed: "Les arguments donnés sont insuffisants." / "les constantes des estimations des inverses des opérateurs linéaires sont fausses." / "Remplacer m_i m_j par m_j m_k." / "sans le facteur √2, elles ne sont que conformément symplectiques." The author reports, for the original printing, an insufficient argument for the inverse parameter map in Corollary 22, wrong constants in the inverse-operator estimates, wrong pair masses in (28), and a missing √2 in (31). The unrevised original is not pinned; the pinned revision (Fej04r) already contains the (28) and (31) corrections. These are not defects of the revision. Effect: none. [E-P-Fej07e]

### Deviations

None.

## Arn63b

V. I. Arnold, *Small denominators and problems of stability of motion in classical and celestial mechanics*, Russian Math. Surveys 18(6) (1963) 85–191 (doi:10.1070/RM1963v018n06ABEH001143). The original is **not pinned**: no PDF of the cited English printing is registered, so this entry rests on a secondary report.

### Unverified (historical report)

1. **p. 138, (3.4.31), as reported in CP11, p. 34, footnote 53.** *reported exponent typo; unverified.* CP11's footnote reports that in Arnold's (3.4.31) "a₂⁴ should be corrected into a₂⁷", and a factor-two normalization. The report in CP11 was confirmed; the original text was not inspected. Effect: none; the quartic coefficients are derived directly (D-P-QUARTIC). [E-P-Arn63b]

## CP11

L. Chierchia, G. Pinzari, *The planetary N-body problem: symplectic foliation, reductions and invariant tori*, Invent. Math. 186 (2011) 1–77. Pinned: doi:10.1007/s00222-011-0313-z.

### Errata

1. **p. 62, Appendix B, (B.2).** *missing factor 1/2; verified.* Printed (transcribed): C₂(a, b) = α β₂^(3)(α)/b. With the overall factor 1/2 already placed in the quadratic form in (6.9), p. 21, the canonical pair-average mixed Hessian requires halving C₂ alone; C₁ and the overall convention stand. Effect: none. [E-P-CP11-1]
2. **p. 63, Appendix B, (B.6), r₁.** *wrong exponent; verified.* Printed (transcribed): 37 α⁴ b_(9/2)^(4)(α). The exact quartic coefficient requires 37α³: replacing α⁴ by α³ makes the printed kernel differ from the exact one by an exact time derivative, so its average is exact for α > 0, α ≠ 1, and at α = 1/2 the printed and exact values of r₁ have opposite signs. Only the r₁ repair is checked; r₂, r₃, r₄ are not. Effect: none. [E-P-CP11-2]

### Deviations

1. **Appendix B, quartic coefficients.** *proof supplement.* The finite-axis quartic coefficients are derived from the averaged interaction (`KAM/Planetary/PlanarTorsion/Quartic/Diagonal.lean`), rather than taken from (B.6). Only the r₁ repair of erratum 2 has been independently checked; the other coefficients of (B.6) are not certified. Effect: none. [D-P-QUARTIC]

## CP09

L. Chierchia, F. Pusateri, *Analytic Lagrangian tori for the planetary many-body problem*, Ergodic Theory Dynam. Systems 29(3) (2009) 849–873. Pinned: arXiv:1206.3475v1.

### Errata

1. **p. 15, polar action domain.** *missing margin; verified.* Printed (transcribed): ρ ∈ D^p(0, |ρ₀|/2). The polar change has √(2(ρ₀j + ρ_j)); for positive unequal ρ₀, such as a small multiple of (1, 0.01), the ball contains ρ with ρ₀j + ρ_j < 0. Effect: none. [E-CP09-2]
2. **p. 14, Lemma 7, action-dependent Birkhoff change.** *missing symplectic correction; verified.* Printed: Φ⁴_ε : (θ, r, u, v) → (x̃, ỹ, p̃, q̃) "such that (θ, r) = (x̃, ỹ)" (transcribed). A Birkhoff change of the oscillator variables that depends on the actions produces mixed terms in the symplectic form, so it cannot leave both the angles and the actions unchanged and be symplectic in general; a correction of the angles is needed. Effect: none. [E-CP09-3]
3. **pp. 14–15, the polynomial Q⋆.** *duplicated term; verified.* Printed (transcribed): Q⋆ has the form ⟨Ω̂(r), I⟩ + ½⟨T(r)I, I⟩ + ···, with I_j := (u_j² + v_j²)/2. The quadratic part εΣ Ω̂_j(r)(u_j² + v_j²)/2 is already written separately on p. 14, so Q⋆ duplicates it, contradicting the preservation of the quadratic part. Effect: none. [E-CP09-4]
4. **p. 15, torsion matrix.** *dimension typo; verified.* Printed: "T (r) a 2p × 2p real–analytic matrix". With I ∈ ℝ^p in ⟨T(r)I, I⟩, T is p × p. Effect: none. [E-CP09-5]
5. **p. 15, transformed Hamiltonian H⁵_ε.** *repeated subscript; verified.* Printed (transcribed): Ω̂_j(I₀ + r)(ρ₀j + ρ₀j) in H⁵_ε. The second term should be ρ_j. The polar-coordinate display (27) just before it correctly has ρ₀j + ρ_j. Effect: none. [E-CP09-6]
6. **p. 11, (18), frequency-selected action set.** *missing preimage; verified.* Printed (transcribed): K ∩ D_(γ,τ), and K ∖ D_(γ,τ) in the following measure formula. K is a set of actions and D_(γ,τ) a set of frequencies; the right-hand side evaluates ω, confirming that K ∩ ω⁻¹(D_(γ,τ)) is meant. Effect: none. [E-CP09-7]
7. **p. 11, internal reference; p. 6, footnote 8.** *cross-references; verified.* Printed: "Theorem 2" (p. 11), where the result used is Lemma 2; and "Theorem 1.7, page 127" (footnote 8), whereas Theorem 1.7 of Rus01 begins on printed p. 126. Effect: none. [E-CP09-8]
8. **p. 17, transformed perturbation.** *repeated symbol; verified.* Printed (transcribed): f(r, ρ, c̄₁, c̄₁). The two shifts c̄₁, c̄₂ are defined just before; the second should be c̄₂. Effect: none. [E-CP09-10]

### Unverified

1. **p. 21, perturbation threshold.** *direction of an inequality; unverified.* Printed (transcribed): ε₀ ≤ c̄ ε^ν₀, after which the theorem is applied to a higher-order remainder. An upper bound on the threshold does not show that the remainder lies below it; this may be an editorial reversal of a chosen sufficient threshold. No counterexample to the existence statement is known; at most a missing lower bound or a misprinted inequality. Effect: none. [E-CP09-1]
2. **p. 6, Theorem 3, dependence of ε₀; compare p. 17, Lemma 8.** *dependence not listed; unverified.* Printed (transcribed): ε₀ = ε₀(ε*, n, μ, β, τ, ω, K). The analytic domain A is not listed although its margin enters the construction; but A is fixed as part of the problem, and the omission does not settle whether uniformity over varying A is intended. Effect: none. [E-CP09-9]
3. **p. 22, planetary application of Theorem 4.** *interface; unverified, classified as a proof supplement.* Printed: the functions H^i "depend also (in a regular and non influential way) on ǫ". The application to an ε-dependent family needs a uniform version of the abstract theorem; the source acknowledges the dependence and no failing family is known. Effect: the formal proof establishes the needed uniform parameter control (D-P-LOCAL-WRAPPER). [E-CP09-11]

### Deviations

1. **Fixed-centre problem.** *new physical specialization.* `fixedSunPlanetaryKAM` is a Newtonian theorem with a fixed centre, general n ≥ 2 and increasing positive axes, deduced from the analytic maximal-torus route with an exact physical transfer; CP09's analytic theorem is not a physical statement. Effect: statement of the theorem. [D-FIXED-1]
2. **pp. 17–21, Remark 5 and Lemma 8; Rus01 §§13–20.** *different proof.* CP09's maximal case relies on Rus01, whose approximation function decays faster than every power; the power-law case CP09 needs is not an instance of it. The formal proof uses its own scheme with power-law divisors and polynomial thresholds: the admissibility budget `adm_budget`, `adm_budget_beta` and the displacement power law `displacement_power` in `KAM/Planetary/WeakKAM/PolynomialBudget.lean`, with the iteration and limit in the other `KAM/Planetary/WeakKAM/` modules. Effect: none on the statements. [D-P-WEAK-KAM]
3. **Theorems 3–4 and Proposition 2.** *proof supplement.* The application needs uniform analytic domains, stability of the derivative nondegeneracy, parameter-family control and whole-torus measure transfer; C⁰ closeness alone does not provide them. These are established in the planetary preparation and assembly modules (`KAM/Planetary/Preparation/`, `KAM/Planetary/FixedAssembly/`). The qualitative "close to" of the source is not false. Effect: none. [D-P-LOCAL-WRAPPER]

## Rus01

H. Rüssmann, *Invariant tori in non-degenerate nearly integrable Hamiltonian systems*, Regul. Chaotic Dyn. 6(2) (2001) 119–204. Pinned: doi:10.1070/RD2001v006n02ABEH000169 (printed pages).

### Errata

1. **p. 123, (1.2).** *dimension typo; verified.* Printed (transcribed): A : Y → ℝ^(p×p). z has 2p coordinates and A J_p acts on them, so A is 2p × 2p. Effect: none. [E-Rus01-1]
2. **p. 171, item 5, compared with (14.7), p. 165.** *inconsistent definition; verified.* Printed (transcribed): C• = |ω| + |Ω| + |Q|, whereas (14.7) defines C• with |A|. A = diag(L, L⁻¹) has fixed Hamiltonian eigenfrequencies but unbounded norm, so the two are not interchangeable. Effect: none. [E-Rus01-2]

### Deviations

None.

## Rus05

H. Rüssmann, *Addendum to "Invariant tori in non-degenerate nearly integrable Hamiltonian systems"*, Regul. Chaotic Dyn. 10(1) (2005) 21–31. Pinned: doi:10.1070/RD2005v010n01ABEH000297 (printed pages).

### Errata

1. **p. 26, Lemma 8, integral representation on a strip.** *missing growth hypothesis; verified.* Printed: "Every holomorphic function" on the strip has the stated improper integral representation. For H(z) = exp(z²) the growth on horizontal lines beats the decay of the cosh kernel and the integral diverges. Bounded periodic applications are unaffected. Effect: none. [E-Rus05-1]
2. **pp. 30–31, §11, (46) and the final estimate.** *wrong constant for the constructed multipliers; verified.* Printed (transcribed): |F − F_(nTq)|₀ ≤ [(1 + E(Tρ))ⁿ − 1] ‖F‖_ρ. With the cutoff rescaled to T/√n and ρ = n log(1/q)/(2T) as printed on p. 30, the data n = 4, T = 4, q = e^(−10), ρ = 5, r = 6, F = e^(3ix₁−18) are admissible; the cube cutoff 2 removes the mode 3, so the error is e^(−15) ≈ 3.059·10⁻⁷, above the claimed bound ≈ 2.099·10⁻⁸. This refutes (46) for the multipliers constructed there, not the existence of suitable approximations or the KAM theorem. Effect: none. [E-Rus05-2]
3. **p. 21, footnote in the abstract.** *page reference; verified.* Printed: "p. 136". The Rus01 footnote referred to is on printed p. 135. Effect: none. [E-Rus05-3]

### Deviations

1. **§§8–11; Rus01 §7.3–7.5, approximation.** *different proof.* The formal proof does not use Rüssmann's approximation multipliers or their constants; the approximation step of the maximal-torus scheme uses a smooth cutoff obtained by convolution with a tensor kernel (`KAM/Planetary/WeakKAM/Cutoff.lean`, `CutoffBump.lean`, `CutoffTensor.lean`, `CutoffConv.lean`), with its own constants. Effect: none on the statements. [D-P-APPROX]

## AKN06

V. I. Arnold, V. V. Kozlov, A. I. Neishtadt, *Mathematical Aspects of Classical and Celestial Mechanics*, 3rd ed., Encyclopaedia Math. Sci. 3, Springer (2006). Pinned: doi:10.1007/978-3-540-48926-9.

### Errata

None.

### Deviations

1. **§6.1.9, printed p. 243 (PDF p. 254).** *specialization.* The mean and "most initial data" averaging estimates are formalized as `averaging_mean` and `averaging_most`, specialized to analytic Hamiltonian systems with fixed h, f, K, period-one angles, absolute volume and separately supplied solutions; see D-NAVG-1 to D-NAVG-3 for the comparison with Nei76. Effect: narrower statements. [D-N-ADD-5]

## Withdrawn allegations

Two allegations of earlier versions of this record were found not to be errata and are withdrawn.

1. **FdlLS09, p. 13, Theorem 3.14.** The bound uses ρ^(−2ν) while δ = ρ/4 is introduced. Since δ^(−2ν) = 4^(2ν) ρ^(−2ν) is absorbed in a constant allowed to depend on ν, nothing is wrong; at most δ is redundant notation. [E-FdlLS09-1]
2. **HL19, p. 44, versus Theorem 3.1, p. 17.** The proof's concluding sentence states the positive distance to the boundary for the real torus, while (5.73) proves the stronger margin on the complex strip asserted by the theorem. A true weaker sentence is not an erratum. [E-HL19-7]

## Outside scope

The general steep Nekhoroshev theorem (see D-N-ADD-3) and a spatial planetary theorem (D-SPATIAL-1) are not formalized. Sources consulted only as context or cross-checks are recorded in [`sources.json`](sources.json) and [`PAPERS.md`](PAPERS.md).
