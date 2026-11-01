/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Tors

/-!
# Rounded and truncated packed nodes, verified by residual

A **node entry** `NodeEntry` is an untrusted memo of a packed model on a small layout `Ld` at
scale `2^(e - s)`: mantissas, a radius bound and a norm bound. Its check against an exact packed
value `x` on a larger layout `Ls` at scale `2^e` (`stageOk`):

* the memo packs on `Ld` within `A'` (`memoPackOk`);
* the **residual** `x - 2^s · memo` is formed exactly on `Ls` (the memo times a power of two at the
  zero key of a unit layout `Lu` with `win Ld Lu = Ls`), and the radius of `x` plus the residual's
  packed norm stays below the memo's radius;
* the memo's packed norm stays below its norm bound.

Then the memo is a packed model of the same function (`PEnc.stage`, `PMat.Encloses.stage`): the
rounding of the mantissas and the truncation of the modes outside `Ld` are both in the residual, so
their correctness is never assumed. The memo is computed by untrusted tooling.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- One memoized node entry: real and imaginary mantissas, a radius bound, a norm bound. -/
abbrev NodeEntry := List (CertKey × ℤ) × List (CertKey × ℤ) × ℚ × ℚ

section Defs

variable {α : Type} [CertArith α]

/-- The packed array of a node entry. -/
def nodePC (L : PackLayout) (t : NodeEntry) : PC := ⟨packOf L t.1, packOf L t.2.1⟩

/-- Both parts of a node entry pack on `L` within `B`. -/
def nodePackOk (L : PackLayout) (B : ℕ) (t : NodeEntry) : Bool :=
  packRepOk L t.1 B && packRepOk L t.2.1 B

/-- The residual `x - 2^s · memo` on the source layout. -/
def nodeRes (n : ℕ) (Ld Lu : PackLayout) (s : ℕ) (x : PC) (t : NodeEntry) : PC :=
  pcAdd x (pcNeg (pcMul (nodePC Ld t) (pcUnit Lu.width (zslot n Lu) (2 ^ s))))

/-- **The check of one node entry** against the exact value `x` (radius `r`) at scale `2^e`. -/
def stageOk (n : ℕ) (W : CertWeight) (q lr ln : ℕ) (Ls Ld Lu : PackLayout) (A' e s : ℕ) (x : PC)
    (r : α) (t : NodeEntry) : Bool :=
  nodePackOk Ld A' t &&
    ble (upAdd r (pnorm W q lr Ls e (nodeRes n Ld Lu s x t))) (ofRatUp t.2.2.1) &&
    ble (pnorm W q ln Ld (e - s) (nodePC Ld t) : α) (ofRatUp t.2.2.2)

/-- A memoized node matrix. -/
def nodeAt (tab : List (List NodeEntry)) (i j : ℕ) : NodeEntry :=
  (tab.getD i []).getD j ([], [], 0, 0)

/-- The packed model matrix of a memoized node. -/
def nodeMat (Ld : PackLayout) (tab : List (List NodeEntry)) : PMat α :=
  ⟨fun i j => nodePC Ld (nodeAt tab i j), fun i j => (ofRatUp (nodeAt tab i j).2.2.1 : α),
    fun i j => (ofRatUp (nodeAt tab i j).2.2.2 : α)⟩

/-- Every entry `(i, j)`, `i < R`, `j < C`, of a memoized node against the matrix `M`. -/
def stageAll (n : ℕ) (W : CertWeight) (q lr ln : ℕ) (Ls Ld Lu : PackLayout) (A' e s R C : ℕ)
    (M : PMat α) (tab : List (List NodeEntry)) : Bool :=
  (List.range R).all fun i => (List.range C).all fun j =>
    stageOk n W q lr ln Ls Ld Lu A' e s (M.x i j) (M.r i j) (nodeAt tab i j)

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **One node entry**: a passing `stageOk` turns a packed model on `Ls` at scale `2^e` into one
of the memo on `Ld` at scale `2^(e - s)`, with the memo's radius and norm bound. -/
theorem PEnc.stage {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true) {m : ℕ}
    {Ls Ld Lu : PackLayout} (hc : PackLayout.compat m Ld Lu = true) (hwd : layoutWf Ld = true)
    (hwu : layoutWf Lu = true) (heq : win Ld Lu = Ls)
    (hp : Lu.slot (List.replicate n 0) = some (zslot n Lu)) {A A' e s q lr ln : ℕ} (hse : s ≤ e)
    (hokr : normOk W q lr (A + mulLoad Ld Lu A' (2 ^ s)) Ls = true)
    (hokn : normOk W q ln A' Ld = true) {x : PC} {r nb : α} {f : (Fin n → ℂ) → ℂ}
    (hx : PEnc Ls A e x r nb n W.rho f) {t : NodeEntry}
    (h : stageOk n W q lr ln Ls Ld Lu A' e s x r t = true) :
    PEnc Ld A' (e - s) (nodePC Ld t) (ofRatUp t.2.2.1 : α) (ofRatUp t.2.2.2) n W.rho f := by
  simp only [stageOk, nodePackOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpr, hpi⟩, hrad⟩, hnb⟩ := h
  obtain ⟨F, hF, hb⟩ := hx
  obtain ⟨d1, s1, e1⟩ := srep_of_packRepOk hwd hpr
  obtain ⟨d2, s2, e2⟩ := srep_of_packRepOk hwd hpi
  set G : (Fin n → ℂ) → ℂ := fun θ => intEval n t.1 θ + Complex.I * intEval n t.2.1 θ
  have hG : PCRep Ld A' (nodePC Ld t) n G :=
    ⟨d1, d2, s1, s2, fun θ => by simp only [G]; rw [e1 n θ, e2 n θ]⟩
  have hu := PCRep.unit (n := n) hwu hp ((2 : ℤ) ^ s)
  rw [Int.natAbs_pow] at hu
  have hGu := PCRep.mul hc hwd hwu hG hu
  rw [heq] at hGu
  have hR := hF.add hGu.neg
  have hpos : (0 : ℝ) < 2 ^ (e - s) := by positivity
  refine ⟨G, hG, fun θ hθ => ⟨?_, ?_⟩⟩
  · have h1 := (hb θ hθ).1
    have h2 := norm_le_ofRatUp (α := α) hR hokr hW hθ e
      (g := (F θ - G θ * ((2 ^ s : ℤ) : ℂ)) / 2 ^ e)
      (by rw [div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]; ring)
    have hre := LawfulCertArith.ble_sound _ _ hrad
    have hu' := LawfulCertArith.upAdd_ge r (pnorm W q lr Ls e (nodeRes n Ld Lu s x t) : α)
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
        val (pnorm W q lr Ls e (nodeRes n Ld Lu s x t) : α) := h2
    linarith
  · have h3 := norm_le_ofRatUp (α := α) hG hokn hW hθ (e - s) (g := G θ / 2 ^ (e - s))
      (by field_simp)
    exact h3.trans (LawfulCertArith.ble_sound _ _ hnb)

/-- **A memoized node matrix** from the exact one: every entry checked by `stageOk`. -/
theorem PMat.Encloses.stage {W : CertWeight} {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    {m : ℕ} {Ls Ld Lu : PackLayout} (hc : PackLayout.compat m Ld Lu = true)
    (hwd : layoutWf Ld = true) (hwu : layoutWf Lu = true) (heq : win Ld Lu = Ls)
    (hp : Lu.slot (List.replicate n 0) = some (zslot n Lu)) {A A' e s q lr ln R C : ℕ}
    (hse : s ≤ e) (hokr : normOk W q lr (A + mulLoad Ld Lu A' (2 ^ s)) Ls = true)
    (hokn : normOk W q ln A' Ld = true) {ι κ : Type*} {ri : ι → ℕ} {ci : κ → ℕ}
    (hri : ∀ i, ri i < R) (hci : ∀ j, ci j < C) {M : PMat α}
    {F : (Fin n → ℂ) → Matrix ι κ ℂ} (hM : PMat.Encloses Ls A e n W.rho ri ci M F)
    {tab : List (List NodeEntry)} (h : stageAll n W q lr ln Ls Ld Lu A' e s R C M tab = true) :
    PMat.Encloses Ld A' (e - s) n W.rho ri ci (nodeMat (α := α) Ld tab) F := by
  intro i j
  simp only [stageAll, List.all_eq_true, List.mem_range] at h
  exact PEnc.stage hW hc hwd hwu heq hp hse hokr hokn (hM i j) (h _ (hri i) _ (hci j))

end Sound

end KAM.CertificateSharp.Packed
