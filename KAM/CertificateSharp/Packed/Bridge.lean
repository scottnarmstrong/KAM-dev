/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Product

/-!
# Bridge B1: the packed complex product proves the landed model-product proposition

`CertPoly.mulGmp` is the landed `CertPoly.mulPacked` assembly with its four real products taken by
the packed route `gmpRealProduct` (one multiplication and advice-free rounding each) instead of the
advice-checked `packedRealProduct`: the same boundary (`toMants`, `dyadicTerms`, `ofRatUp`), the
same placement of the parts (`re·re - im·im` real, `re·im + im·re` imaginary).

`CertPoly.mulGmp_sound` has **exactly** the conclusion of the landed `CertPoly.mulPacked_sound`,
the proposition that the landed `CertModel.polyProduct_sound`, and through it
`CertModel.Encloses.mul`, consume. A consumer proof written against the landed product contract
therefore applies verbatim to the packed route.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM.Certificate

open KAM KAM.Certificate.CertArith

/-- The packed complex product of two backend polynomials (mantissa scale `P`): the landed
`mulPacked` assembly over four packed real products. `none` on any failed decode, guard, boundary
or exactness check. -/
def CertPoly.mulGmp {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (W : CertWeight)
    (P : ℕ) (rr ii ri ir : GmpSpec) (a b : CertPoly α) : Option (CertPoly α × α) :=
  (a.toMants dec P).bind fun ma => (b.toMants dec P).bind fun mb =>
  (gmpRealProduct rr W (2 * P) ma.1 mb.1).bind fun pRR =>
  (gmpRealProduct ii W (2 * P) ma.2 mb.2).bind fun pII =>
  (gmpRealProduct ri W (2 * P) ma.1 mb.2).bind fun pRI =>
  (gmpRealProduct ir W (2 * P) ma.2 mb.1).bind fun pIR =>
  (dyadicTerms (2 * P) rr.s (fun v => ⟨v, ofInt 0⟩) pRR.1).bind fun tRR =>
  (dyadicTerms (2 * P) ii.s (fun v => ⟨v, ofInt 0⟩)
    (pII.1.map fun t => (t.1, -t.2))).bind fun tII =>
  (dyadicTerms (2 * P) ri.s (fun v => ⟨ofInt 0, v⟩) pRI.1).bind fun tRI =>
  (dyadicTerms (2 * P) ir.s (fun v => ⟨ofInt 0, v⟩) pIR.1).bind fun tIR =>
  some (⟨tRR ++ tII ++ tRI ++ tIR⟩, ofRatUp (pRR.2 + pII.2 + pRI.2 + pIR.2))

/-- **Bridge B1**: the packed complex product encloses the EXACT product on the strip, with the
conclusion of the landed `CertPoly.mulPacked_sound`. -/
theorem CertPoly.mulGmp_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {P : ℕ} {rr ii ri ir : GmpSpec} {a b : CertPoly α} {out : CertPoly α × α}
    (h : CertPoly.mulGmp dec W P rr ii ri ir a b = some out) :
    ∀ θ ∈ complexStrip n W.rho, ‖a.eval n θ * b.eval n θ - out.1.eval n θ‖ ≤ val out.2 := by
  intro θ hθ
  simp only [CertPoly.mulGmp, Option.bind_eq_some_iff] at h
  obtain ⟨ma, hma, mb, hmb, pRR, hRR, pII, hII, pRI, hRI, pIR, hIR, tRR, htRR, tII, htII,
    tRI, htRI, tIR, htIR, h⟩ := h
  simp only [Option.some.injEq] at h
  subst h
  have hre : ∀ v : α, (⟨v, ofInt 0⟩ : CC α).toC = 1 * val v := fun v => by
    apply Complex.ext <;> simp [CC.toC, LawfulCertArith.val_ofInt]
  have him : ∀ v : α, (⟨ofInt 0, v⟩ : CC α).toC = Complex.I * val v := fun v => by
    apply Complex.ext <;> simp [CC.toC, LawfulCertArith.val_ofInt]
  have eRR := dyadicTerms_sound hre θ htRR
  have eII := dyadicTerms_sound hre θ htII
  have eRI := dyadicTerms_sound him θ htRI
  have eIR := dyadicTerms_sound him θ htIR
  rw [intEval_map_neg] at eII
  have bRR := gmpRealProduct_sound hRR hW hθ
  have bII := gmpRealProduct_sound hII hW hθ
  have bRI := gmpRealProduct_sound hRI hW hθ
  have bIR := gmpRealProduct_sound hIR hW hθ
  have hout : CertPoly.eval n ⟨tRR ++ tII ++ tRI ++ tIR⟩ θ =
      (1 * (2 ^ rr.s / 2 ^ (2 * P)) * intEval n pRR.1 θ +
        1 * (2 ^ ii.s / 2 ^ (2 * P)) * -intEval n pII.1 θ) +
      Complex.I * (2 ^ ri.s / 2 ^ (2 * P)) * intEval n pRI.1 θ +
      Complex.I * (2 ^ ir.s / 2 ^ (2 * P)) * intEval n pIR.1 θ := by
    simp only [CertPoly.eval, List.map_append, List.sum_append, eRR, eII, eRI, eIR]
  rw [CertPoly.toMants_sound hma θ, CertPoly.toMants_sound hmb θ, hout]
  have hkey : (intEval n ma.1 θ + Complex.I * intEval n ma.2 θ) / 2 ^ P *
      ((intEval n mb.1 θ + Complex.I * intEval n mb.2 θ) / 2 ^ P) -
      ((1 * (2 ^ rr.s / 2 ^ (2 * P)) * intEval n pRR.1 θ +
        1 * (2 ^ ii.s / 2 ^ (2 * P)) * -intEval n pII.1 θ) +
      Complex.I * (2 ^ ri.s / 2 ^ (2 * P)) * intEval n pRI.1 θ +
      Complex.I * (2 ^ ir.s / 2 ^ (2 * P)) * intEval n pIR.1 θ) =
      ((intEval n ma.1 θ * intEval n mb.1 θ - 2 ^ rr.s * intEval n pRR.1 θ) -
        (intEval n ma.2 θ * intEval n mb.2 θ - 2 ^ ii.s * intEval n pII.1 θ) +
        Complex.I * (intEval n ma.1 θ * intEval n mb.2 θ - 2 ^ ri.s * intEval n pRI.1 θ) +
        Complex.I * (intEval n ma.2 θ * intEval n mb.1 θ - 2 ^ ir.s * intEval n pIR.1 θ)) /
        2 ^ (2 * P) := by
    have hP : (2 : ℂ) ^ (2 * P) = ((2 : ℂ) ^ P) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [hP]
    have hD : (2 : ℂ) ^ P ≠ 0 := pow_ne_zero _ two_ne_zero
    generalize (2 : ℂ) ^ P = D at hD ⊢
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hkey, norm_div, norm_pow, Complex.norm_ofNat]
  have hup := LawfulCertArith.ofRatUp_ge (α := α) (pRR.2 + pII.2 + pRI.2 + pIR.2)
  push_cast at hup
  rw [div_le_iff₀ (by positivity)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hup (by positivity))
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  calc _ ≤ ‖intEval n ma.1 θ * intEval n mb.1 θ - 2 ^ rr.s * intEval n pRR.1 θ‖ +
        ‖intEval n ma.2 θ * intEval n mb.2 θ - 2 ^ ii.s * intEval n pII.1 θ‖ +
        ‖intEval n ma.1 θ * intEval n mb.2 θ - 2 ^ ri.s * intEval n pRI.1 θ‖ +
        ‖intEval n ma.2 θ * intEval n mb.1 θ - 2 ^ ir.s * intEval n pIR.1 θ‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)) ?_
        · rw [norm_mul, hI, one_mul]
        · rw [norm_mul, hI, one_mul]
    _ ≤ _ := by
        rw [show (2 : ℝ) ^ (2 * P) = 2 ^ (2 * P) from rfl]
        nlinarith [bRR, bII, bRI, bIR]

end KAM.CertificateSharp.Packed
