/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Stage
public import KAM.CertificateSharp.Packed.Box

/-!
# The reduce computed in the kernel (`V2-PACKED.md` §12.4 (Z))

`PEnc.stage` (B3b) validates a memoized candidate (`packRepOk`) and compares its residual against
the memo's radius. Here the candidate is computed by the kernel itself and no literal is needed:

* `zPart`: the candidate part on the box `Ld` of a part `Z` on the source `Ls` (same stride and
  width), rounded by `s` bits: offset digits, the rounded digit shift (`digitShift`, Round.lean),
  the box slots masked and moved by `off` slots, the offset removed. Its correctness is **not**
  needed: a wrong candidate fails `boxOk` or the residual, so the check fails closed;
* `PEnc.stageRep`: the residual stage for any candidate with a `PCRep`, with the radius
  `r + pnorm(residual)` and the norm bound `pnorm(candidate)` computed, not compared;
* `PEnc.reduceZ`: the same with the `PCRep` from `boxOk` on both parts.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-! ### The candidate (kernel computation, untrusted) -/

/-- The candidate part on the box (`D₀ × D₁`, row stride `S`, slot width `w`, `off` slots into
the source of `Ns` slots), rounded by `s ≥ 1` bits; `ls` is the offset exponent (digits of `Z` in
`[-2^ls, 2^ls)`, `s ≤ ls`). -/
def zPart (w Ns ls s S D0 D1 off : ℕ) (Z : ℤ) : ℤ :=
  ((((digitShift w Ns s
      (Z + (periodic w Ns (2 ^ ls) : ℤ) + (periodic w Ns (2 ^ (s - 1)) : ℤ)).toNat) &&&
        (boxPat w S D0 D1 (2 ^ w - 1) <<< (w * off))) >>> (w * off) : ℕ) : ℤ) -
    (boxPat w S D0 D1 (2 ^ (ls - s)) : ℤ)

/-- The candidate of a packed complex value. -/
def zPC (w Ns ls s S D0 D1 off : ℕ) (x : PC) : PC :=
  ⟨zPart w Ns ls s S D0 D1 off x.re, zPart w Ns ls s S D0 D1 off x.im⟩

/-- The residual `x - 2^s · x'` on the source (as `nodeRes`). -/
def zRes (n : ℕ) (Lu : PackLayout) (s : ℕ) (x x' : PC) : PC :=
  pcAdd x (pcNeg (pcMul x' (pcUnit Lu.width (zslot n Lu) (2 ^ s))))

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **The residual stage for any candidate** with a packed representation: a packed model on
`Ls` at scale `2^e` gives one of the candidate on `Ld` at scale `2^(e - s)`, with the radius
`r + pnorm(residual)` and the norm bound `pnorm(candidate)`. -/
theorem PEnc.stageRep {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {m : ℕ}
    {Ls Ld Lu : PackLayout} (hc : PackLayout.compat m Ld Lu = true) (hwd : layoutWf Ld = true)
    (hwu : layoutWf Lu = true) (heq : win Ld Lu = Ls)
    (hp : Lu.slot (List.replicate n 0) = some (zslot n Lu)) {A A' e s q lr ln : ℕ} (hse : s ≤ e)
    (hokr : normOk W q lr (A + mulLoad Ld Lu A' (2 ^ s)) Ls = true)
    (hokn : normOk W q ln A' Ld = true) {x : PC} {r nb : α} {f : (Fin n → ℂ) → ℂ}
    (hx : PEnc Ls A e x r nb n W.rho f) {x' : PC} {G : (Fin n → ℂ) → ℂ}
    (hG : PCRep Ld A' x' n G) :
    PEnc Ld A' (e - s) x' (upAdd r (pnorm W q lr Ls e (zRes n Lu s x x')))
      (pnorm W q ln Ld (e - s) x') n W.rho f := by
  obtain ⟨F, hF, hb⟩ := hx
  have hu := PCRep.unit (n := n) hwu hp ((2 : ℤ) ^ s)
  rw [Int.natAbs_pow] at hu
  have hGu := PCRep.mul hc hwd hwu hG hu
  rw [heq] at hGu
  have hR := hF.add hGu.neg
  refine ⟨G, hG, fun θ hθ => ⟨?_, ?_⟩⟩
  · have h1 := (hb θ hθ).1
    have h2 := norm_le_ofRatUp (α := α) hR hokr hW hθ e
      (g := (F θ - G θ * ((2 ^ s : ℤ) : ℂ)) / 2 ^ e)
      (by rw [div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]; ring)
    have hu' := LawfulCertArith.upAdd_ge r (pnorm W q lr Ls e (zRes n Lu s x x') : α)
    have hsplit : f θ - G θ / 2 ^ (e - s) =
        (f θ - F θ / 2 ^ e) + (F θ - G θ * ((2 ^ s : ℤ) : ℂ)) / 2 ^ e := by
      have h2s : (2 : ℂ) ^ e = 2 ^ (e - s) * 2 ^ s := by
        rw [← pow_add, Nat.sub_add_cancel hse]
      push_cast
      rw [h2s]
      field_simp
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h2' : ‖(F θ - G θ * ((2 ^ s : ℤ) : ℂ)) / 2 ^ e‖ ≤
        val (pnorm W q lr Ls e (zRes n Lu s x x') : α) := h2
    linarith
  · exact norm_le_ofRatUp (α := α) hG hokn hW hθ (e - s) (g := G θ / 2 ^ (e - s))
      (by field_simp)

/-- A packed complex value whose parts pass `boxOk` has a packed representation. -/
theorem PCRep.ofBoxOk {L : PackLayout} {l : ℕ} {x : PC} (hre : boxOk L l x.re = true)
    (him : boxOk L l x.im = true) : ∃ G : (Fin n → ℂ) → ℂ, PCRep L (2 ^ l) x n G := by
  obtain ⟨dr, hr⟩ := boxOk_sound hre
  obtain ⟨di, hi⟩ := boxOk_sound him
  exact ⟨fun θ => slotSum L n dr θ + Complex.I * slotSum L n di θ, dr, di, hr, hi, fun _ => rfl⟩

/-- **The reduce computed in the kernel**: any candidate whose parts pass `boxOk` on `Ld`. -/
theorem PEnc.reduceZ {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {m : ℕ}
    {Ls Ld Lu : PackLayout} (hc : PackLayout.compat m Ld Lu = true) (hwd : layoutWf Ld = true)
    (hwu : layoutWf Lu = true) (heq : win Ld Lu = Ls)
    (hp : Lu.slot (List.replicate n 0) = some (zslot n Lu)) {A e s q lr ln lb : ℕ} (hse : s ≤ e)
    (hokr : normOk W q lr (A + mulLoad Ld Lu (2 ^ lb) (2 ^ s)) Ls = true)
    (hokn : normOk W q ln (2 ^ lb) Ld = true) {x : PC} {r nb : α} {f : (Fin n → ℂ) → ℂ}
    (hx : PEnc Ls A e x r nb n W.rho f) {x' : PC} (hre : boxOk Ld lb x'.re = true)
    (him : boxOk Ld lb x'.im = true) :
    PEnc Ld (2 ^ lb) (e - s) x' (upAdd r (pnorm W q lr Ls e (zRes n Lu s x x')))
      (pnorm W q ln Ld (e - s) x') n W.rho f := by
  obtain ⟨G, hG⟩ := PCRep.ofBoxOk (n := n) hre him
  exact PEnc.stageRep hW hc hwd hwu heq hp hse hokr hokn hx hG

omit [LawfulCertArith α] in
/-- A packed model stays one with a larger radius and norm bound. -/
theorem PEnc.weaken {L : PackLayout} {A e : ℕ} {x : PC} {r nb r' nb' : α} {ρ : ℝ}
    {f : (Fin n → ℂ) → ℂ} (hx : PEnc L A e x r nb n ρ f) (hr : val r ≤ val r')
    (hnb : val nb ≤ val nb') : PEnc L A e x r' nb' n ρ f := by
  obtain ⟨F, hF, hb⟩ := hx
  exact ⟨F, hF, fun θ hθ => ⟨(hb θ hθ).1.trans hr, (hb θ hθ).2.trans hnb⟩⟩

end Sound

end KAM.CertificateSharp.Packed
