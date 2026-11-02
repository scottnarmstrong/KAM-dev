/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.CompleteEquation
import Mathlib.Tactic.Linarith

/-!
# `L_N F` and `⟨⟨N,F⟩⟩` are continuous polynomials of degree `≤ 2` (`bpW:w4:lie` (i))

Blueprint label: `bpW:w4:lie` (i), step `stepW:w4:liebd` (continuity in
`(z, \bar z)`).

The clause of `bpW:w4:lie` (i) exported here: for `F ∈ 𝒯_{s'}` and `θ`, the functions
`(y, z, \bar z) ↦ L_N F(θ,y,z,\bar z)` and `(y, z, \bar z) ↦ ⟨⟨N,F⟩⟩(θ,y,z,\bar z)` on
`ℂ² × ℓ^N_{a,p} × ℓ^N_{a,p}` (the normal variables in the representative model `HomL2`) are
continuous polynomials of degree `≤ 2`, and in particular continuous in `(z, \bar z)`.

* `IsHomContQuadPoly f`: `f v = c + L v + B v v` with `c ∈ ℂ`, `L` continuous linear and `B`
  continuous bilinear (a continuous polynomial of degree `≤ 2`);
  `IsHomContQuadPoly.contQuad_continuous`;
* `HomPolyDom = ℂ² × HomL2 × HomL2`, the `(y, z, \bar z)` slots;
* `homLieN_contQuad_of_bound_gen`: CONDITIONAL helper, under `|W_j| ≤ K₀(j+2)` and `1 ≤ p + p_+`;
* `homLemma_lie_i_contPoly_gen` (general `p_+`) and `homLemma_lie_i_contPoly` (`p_+ = p + 1`):
  the source-premise exports (`HomFreqHyp`, `ξ ∈ Π`), with `ω = ω ξ`, `Ω = Ω ξ` and the carrier
  `homOmegaCarrier_of_bound … (homOmega_le h hξ)` of `homLemma1_equation_all_gen`.

Since `HomOmegaCarrier` is a `Prop`, `homLieN_gen` and `homWeakBracketN_gen` do not depend on the
carrier proof, so the statements hold for every carrier evidence.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- **A continuous polynomial of degree `≤ 2`** on a complex normed space:
`f v = c + L v + B v v` with `L` continuous linear and `B` continuous bilinear. -/
def IsHomContQuadPoly {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) : Prop :=
  ∃ (c : ℂ) (L : E →L[ℂ] ℂ) (B : E →L[ℂ] E →L[ℂ] ℂ), ∀ v, f v = c + L v + B v v

namespace IsHomContQuadPoly

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ}

theorem contQuad_continuous (hf : IsHomContQuadPoly f) : Continuous f := by
  obtain ⟨c, L, B, h⟩ := hf
  rw [show f = fun v => c + L v + B v v from funext h]
  exact (continuous_const.add L.continuous).add (B.continuous.clm_apply continuous_id)

/-- A continuous polynomial on `Y × X` is continuous in the second slot, the first one fixed. -/
theorem contQuad_continuous_slice {Y X : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup X] [NormedSpace ℂ X] {f : Y × X → ℂ} (hf : IsHomContQuadPoly f) (y : Y) :
    Continuous fun x : X => f (y, x) :=
  hf.contQuad_continuous.comp (continuous_const.prodMk continuous_id)

theorem contQuad_congr (hf : IsHomContQuadPoly f) (h : ∀ v, f v = g v) : IsHomContQuadPoly g := by
  rwa [← funext h]

theorem contQuad_const (c : ℂ) : IsHomContQuadPoly (fun _ : E => c) := ⟨c, 0, 0, fun v => by simp⟩

theorem contQuad_clm {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (L : F →L[ℂ] ℂ)
    (u : E →L[ℂ] F) :
    IsHomContQuadPoly (fun v => L (u v)) := ⟨0, L.comp u, 0, fun v => by simp⟩

theorem contQuad_bilin {F G : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (B : F →L[ℂ] G →L[ℂ] ℂ) (u : E →L[ℂ] F)
    (u' : E →L[ℂ] G) :
    IsHomContQuadPoly (fun v => B (u v) (u' v)) :=
  ⟨0, 0, B.bilinearComp u u', fun v => by simp⟩

theorem contQuad_add (hf : IsHomContQuadPoly f) (hg : IsHomContQuadPoly g) :
    IsHomContQuadPoly (fun v => f v + g v) := by
  obtain ⟨c, L, B, h⟩ := hf
  obtain ⟨c', L', B', h'⟩ := hg
  exact ⟨c + c', L + L', B + B', fun v => by simp [h, h']; ring⟩

theorem contQuad_const_mul (hf : IsHomContQuadPoly f) (d : ℂ) :
    IsHomContQuadPoly (fun v => d * f v) := by
  obtain ⟨c, L, B, h⟩ := hf
  exact ⟨d * c, d • L, d • B, fun v => by simp [h]; ring⟩

theorem contQuad_neg (hf : IsHomContQuadPoly f) : IsHomContQuadPoly (fun v => -f v) :=
  (hf.contQuad_const_mul (-1)).contQuad_congr fun v => by ring

theorem contQuad_sub (hf : IsHomContQuadPoly f) (hg : IsHomContQuadPoly g) :
    IsHomContQuadPoly (fun v => f v - g v) :=
  (hf.contQuad_add hg.contQuad_neg).contQuad_congr fun v => by ring

theorem contQuad_sum {ι : Type} (S : Finset ι) {f : ι → E → ℂ}
    (hf : ∀ i ∈ S, IsHomContQuadPoly (f i)) :
    IsHomContQuadPoly (fun v => ∑ i ∈ S, f i v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using contQuad_const (E := E) 0
  | insert i S hi ih =>
    refine ((hf i (Finset.mem_insert_self i S)).contQuad_add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))).contQuad_congr fun v => ?_
    rw [Finset.sum_insert hi]

end IsHomContQuadPoly

/-- The `(y, z, \bar z)` slots `ℂ² × ℓ^N_{a,p} × ℓ^N_{a,p}` (normal variables in `HomL2`). -/
abbrev HomPolyDom : Type := (Fin 2 → ℂ) × HomL2 × HomL2

/-- The `y`-slot of `HomPolyDom`. -/
def homPolyPrY : HomPolyDom →L[ℂ] (Fin 2 → ℂ) := ContinuousLinearMap.fst ℂ _ _

/-- The `z`-slot of `HomPolyDom`. -/
def homPolyPrZ : HomPolyDom →L[ℂ] HomL2 :=
  (ContinuousLinearMap.fst ℂ HomL2 HomL2).comp (ContinuousLinearMap.snd ℂ _ _)

/-- The `\bar z`-slot of `HomPolyDom`. -/
def homPolyPrZb : HomPolyDom →L[ℂ] HomL2 :=
  (ContinuousLinearMap.snd ℂ HomL2 HomL2).comp (ContinuousLinearMap.snd ℂ _ _)

@[simp] theorem homPolyPrY_apply (v : HomPolyDom) : homPolyPrY v = v.1 := rfl
@[simp] theorem homPolyPrZ_apply (v : HomPolyDom) : homPolyPrZ v = v.2.1 := rfl
@[simp] theorem homPolyPrZb_apply (v : HomPolyDom) : homPolyPrZb v = v.2.2 := rfl

variable {a p pb s : ℝ}

section pieces

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)

theorem homPairRep_contQuad_gen (c : HomL2) (u : HomPolyDom →L[ℂ] HomL2) :
    IsHomContQuadPoly (fun v => homPairRep_gen ha (homPP hp hpb) c (u v)) :=
  IsHomContQuadPoly.contQuad_clm (homPairL2 (homLamDiag_gen ha (homPP hp hpb) c)) u

theorem homPairRep_op_contQuad_gen (M : HomOp) (u u' : HomPolyDom →L[ℂ] HomL2) :
    IsHomContQuadPoly (fun v => homPairRep_gen ha (homPP hp hpb) (M (u v)) (u' v)) :=
  IsHomContQuadPoly.contQuad_bilin
    (homPairL2.comp ((homLamDiag_gen ha (homPP hp hpb)).comp M)) u u'

/-- `∂_{θ_l} F(θ, ·)` is a continuous polynomial of degree `≤ 2` in `(y, z, \bar z)`. -/
theorem homRtheta_contQuad_gen (T : HomTaylor_gen a p pb s) (l : Fin 2) (θ : Fin 2 → ℂ) :
    IsHomContQuadPoly (fun v : HomPolyDom => homRtheta_gen ha hp hpb T l θ v.1 v.2.1 v.2.2) := by
  have hb : IsHomContQuadPoly (fun v : HomPolyDom => ∑ k, homPartial l T.b θ k * v.1 k) :=
    IsHomContQuadPoly.contQuad_sum _ fun k _ =>
      (IsHomContQuadPoly.contQuad_clm (ContinuousLinearMap.proj k)
        homPolyPrY).contQuad_const_mul _
  open IsHomContQuadPoly in
  exact ((((((((contQuad_const (homPartial l T.a0 θ)).contQuad_add hb).contQuad_add
    (homPairRep_contQuad_gen ha hp hpb (homPartial l T.cp θ) homPolyPrZ)).contQuad_add
    (homPairRep_contQuad_gen ha hp hpb (homPartial l T.cm θ) homPolyPrZb)).contQuad_add
    (homPairRep_op_contQuad_gen ha hp hpb (homPartial l T.P θ) homPolyPrZ homPolyPrZ)).contQuad_add
    (homPairRep_op_contQuad_gen ha hp hpb (homPartial l T.Q θ) homPolyPrZ
      homPolyPrZb)).contQuad_add
    (homPairRep_op_contQuad_gen ha hp hpb (homPartial l T.P' θ) homPolyPrZb
      homPolyPrZb)).contQuad_congr fun v => rfl)

end pieces

/-- CONDITIONAL helper for `bpW:w4:lie` (i) (assumes `|W_j| ≤ K₀(j+2)` and `1 ≤ p + p_+`); the
source-premise exports are `homLemma_lie_i_contPoly_gen`, `homLemma_lie_i_contPoly`.
`(y, z, \bar z) ↦ L_N F(θ, y, z, \bar z)` is a continuous polynomial of degree `≤ 2`. -/
theorem homLieN_contQuad_of_bound_gen {K0 : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hp1 : 1 ≤ p + pb) (hK0 : 0 ≤ K0) {W : ℕ+ → ℝ} (hΩ : ∀ j : ℕ+, |W j| ≤ K0 * ((j : ℝ) + 2))
    (hC : HomOmegaCarrier ha hp hpb W) (w : Fin 2 → ℝ) (F : HomTaylor_gen a p pb s)
    (θ : Fin 2 → ℂ) :
    IsHomContQuadPoly (fun v : HomPolyDom => homLieN_gen ha hp hpb hC w F θ v.1 v.2.1 v.2.2) := by
  set D := homDiagW_gen ha hp1 hK0 hΩ
  -- `⟨x, Ω u⟩₀ = homPairL2 (D x) u` for an affine `x = c + A v`
  have hpair : ∀ (c : HomL2) (A u : HomPolyDom →L[ℂ] HomL2),
      IsHomContQuadPoly (fun v => homPairOmegaRaw_gen ha hp hpb W (c + A v) (u v)) := by
    intro c A u
    refine ((IsHomContQuadPoly.contQuad_clm (homPairL2 (D c)) u).contQuad_add
      (IsHomContQuadPoly.contQuad_bilin (homPairL2.comp D) A u)).contQuad_congr fun v => ?_
    rw [homPairOmega_eq_clm_gen ha hp hpb hp1 hK0 hΩ, map_add, map_add]
    rfl
  have hθ : IsHomContQuadPoly (fun v : HomPolyDom =>
      (2 * Real.pi : ℂ)⁻¹ * ∑ l, (w l : ℂ) * homRtheta_gen ha hp hpb F l θ v.1 v.2.1 v.2.2) :=
    (IsHomContQuadPoly.contQuad_sum _ fun l _ =>
      (homRtheta_contQuad_gen ha hp hpb F l θ).contQuad_const_mul _).contQuad_const_mul _
  have hz := hpair (F.cp θ) ((2 : ℂ) • (F.P θ).comp homPolyPrZ + (F.Qt θ).comp homPolyPrZb)
    homPolyPrZ
  have hzb := hpair (F.cm θ) ((F.Q θ).comp homPolyPrZ + (2 : ℂ) • (F.P' θ).comp homPolyPrZb)
    homPolyPrZb
  refine ((hθ.contQuad_sub (hz.contQuad_const_mul Complex.I)).contQuad_add
    (hzb.contQuad_const_mul Complex.I)).contQuad_congr fun v => ?_
  rw [homLieN_gen_eq]
  simp only [homPairOmega_gen, homRz_gen, homRzb_gen, FunLike.coe_add, Pi.add_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply, homPolyPrZ_apply,
    homPolyPrZb_apply, add_assoc]

section source

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ : ℝ}

/-- **Lemma `bpW:w4:lie` (i), `L_N F` and `⟨⟨N,F⟩⟩` are continuous polynomials of degree `≤ 2`**
(step `stepW:w4:liebd`; general `p_+`, `bpW:w5:w4-general`). Under the frequency hypotheses at
`ξ ∈ Π` (`ω = ω ξ`, `Ω = Ω ξ`), for `F ∈ 𝒯_{s'}`, `a, p ≥ 0`, `1 ≤ p + p_+` and every `θ`:
`(y, z, \bar z) ↦ L_N F(θ,y,z,\bar z)` and `(y, z, \bar z) ↦ ⟨⟨N,F⟩⟩(θ,y,z,\bar z)` are continuous
polynomials of degree `≤ 2` on `ℂ² × (ℓ^N_{a,p})²`, and for every `y` both are continuous in
`(z, \bar z)`. -/
theorem homLemma_lie_i_contPoly_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb)
    (F : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ) :
    IsHomContQuadPoly (fun v : HomPolyDom =>
        homLieN_gen ha hp hpb
          (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0)
            (homOmega_le h hξ)) (ω ξ) F θ v.1 v.2.1 v.2.2) ∧
      IsHomContQuadPoly (fun v : HomPolyDom =>
        homWeakBracketN_gen ha hp hpb
          (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0)
            (homOmega_le h hξ)) (ω ξ) F θ v.1 v.2.1 v.2.2) ∧
      ∀ y : Fin 2 → ℂ,
        Continuous (fun q : HomL2 × HomL2 =>
          homLieN_gen ha hp hpb
            (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0)
              (homOmega_le h hξ)) (ω ξ) F θ y q.1 q.2) ∧
        Continuous (fun q : HomL2 × HomL2 =>
          homWeakBracketN_gen ha hp hpb
            (homOmegaCarrier_of_bound ha hp hpb hp1 (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0)
              (homOmega_le h hξ)) (ω ξ) F θ y q.1 q.2) := by
  have hK0 : 0 ≤ 1 + M0 := by linarith [h.consts_nonneg.1]
  have hL := homLieN_contQuad_of_bound_gen ha hp hpb hp1 hK0 (homOmega_le h hξ)
    (homOmegaCarrier_of_bound ha hp hpb hp1 hK0 (homOmega_le h hξ)) (ω ξ) F θ
  have hB := hL.contQuad_neg.contQuad_congr fun v => (homWeakBracketN_eq_neg_lieN_gen ha hp hpb
    (homOmegaCarrier_of_bound ha hp hpb hp1 hK0 (homOmega_le h hξ)) _ F θ _ _ _).symm
  exact ⟨hL, hB, fun y => ⟨hL.contQuad_continuous_slice y, hB.contQuad_continuous_slice y⟩⟩

/-- **Lemma `bpW:w4:lie` (i), `L_N F` and `⟨⟨N,F⟩⟩` are continuous polynomials of degree `≤ 2`,
`p_+ = p + 1`** (step `stepW:w4:liebd`): the original W4 setting `F ∈ 𝒯_{s'}` (`HomTaylor a p s`),
`a, p ≥ 0`, frequency hypotheses at `ξ ∈ Π`, every `θ`. -/
theorem homLemma_lie_i_contPoly (h : HomFreqHyp Par ω Ω M0 Mω MΩ) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) (ha : 0 ≤ a) (hp : 0 ≤ p) (F : HomTaylor a p s) (θ : Fin 2 → ℂ) :
    IsHomContQuadPoly (fun v : HomPolyDom =>
        homLieN_gen ha hp (homPlusOne_le p)
          (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
            (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ))
          (ω ξ) F θ v.1 v.2.1 v.2.2) ∧
      IsHomContQuadPoly (fun v : HomPolyDom =>
        homWeakBracketN_gen ha hp (homPlusOne_le p)
          (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
            (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ))
          (ω ξ) F θ v.1 v.2.1 v.2.2) ∧
      ∀ y : Fin 2 → ℂ,
        Continuous (fun q : HomL2 × HomL2 =>
          homLieN_gen ha hp (homPlusOne_le p)
            (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
              (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ))
            (ω ξ) F θ y q.1 q.2) ∧
        Continuous (fun q : HomL2 × HomL2 =>
          homWeakBracketN_gen ha hp (homPlusOne_le p)
            (homOmegaCarrier_of_bound ha hp (homPlusOne_le p) (by linarith)
              (by linarith [h.consts_nonneg.1] : 0 ≤ 1 + M0) (homOmega_le h hξ))
            (ω ξ) F θ y q.1 q.2) :=
  homLemma_lie_i_contPoly_gen h hξ ha hp (homPlusOne_le p) (by linarith) F θ

end source

end KAM.Wave
