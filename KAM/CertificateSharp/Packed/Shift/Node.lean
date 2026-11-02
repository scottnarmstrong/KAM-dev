/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Shift.Base
public import KAM.CertificateSharp.Packed.JetLeaf

/-!
# Window-sized powers as shifts: the jet nodes

The node operations of `JetNode.lean` and `JetLeaf.lean` with the shift leaves of `Shift/Base.lean`
(`jUnitS`, `jUpS`, `jAddS`, `jRedWS`, `jRedS`, `jMulS`, `jLeafS`), each equal to the landed one
(`…S_eq`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

/-- `jUnit` with a shift. -/
def jUnitS (L : PackLayout) (k : ℕ) : PC := pcUnitS L.width (zslot n L) (2 ^ k)

/-- `jUp` with shifts. -/
def jUpS (nd : JNode α) (u' : Bool) (e' : ℕ) : Option (JNode α) :=
  if nd.u = u' ∧ nd.e = e' then some nd
  else if nd.e ≤ e' then
    if nd.u = true ∧ u' = false then
      some ⟨false, mulLoad jb.LU0 jb.Lb nd.A (2 ^ (e' - nd.e)), e',
        pcMul nd.x (jUnitS n jb.Lb (e' - nd.e)), nd.r, nd.nb⟩
    else if nd.u = u' then
      some ⟨u', mulLoad (jLay jb u') jb.LU0 nd.A (2 ^ (e' - nd.e)), e',
        pcMul nd.x (jUnitS n jb.LU0 (e' - nd.e)), nd.r, nd.nb⟩
    else none
  else none

/-- `jAdd` with shifts. -/
def jAddS (a b : JNode α) : Option (JNode α) :=
  match jUpS n jb a (a.u && b.u) (max a.e b.e), jUpS n jb b (a.u && b.u) (max a.e b.e) with
  | some a', some b' =>
    some ⟨a.u && b.u, a'.A + b'.A, max a.e b.e, pcAdd a'.x b'.x, upAdd a'.r b'.r,
      upAdd a'.nb b'.nb⟩
  | _, _ => none

/-- `jRedW` with shifts. -/
def jRedWS (A e : ℕ) (x : PC) (r : α) (eT : ℕ) : Option (JNode α) :=
  if A ≤ jb.aW ∧ eT < e ∧ e - eT ≤ jb.smax then
    if boxOkS jb.Lb jb.lb (zPCS jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
          (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x).re &&
        boxOkS jb.Lb jb.lb (zPCS jb.Lw.width jb.Lw.denseLen jb.ls (e - eT)
          (jb.Lb.stride.getD 0 0) (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x).im then
      some ⟨false, 2 ^ jb.lb, eT,
        zPCS jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
          (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x,
        upAdd r (pnormS W jb.q jb.lr jb.Lw e (zResS n jb.Lb (e - eT) x
          (zPCS jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
            (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x))),
        pnormS W jb.q jb.ln jb.Lb eT
          (zPCS jb.Lw.width jb.Lw.denseLen jb.ls (e - eT) (jb.Lb.stride.getD 0 0)
            (jb.Lb.dims.getD 0 0) (jb.Lb.dims.getD 1 0) jb.off x)⟩
    else none
  else none

/-- `jRed` with shifts. -/
def jRedS (nd : JNode α) (eT : ℕ) : Option (JNode α) :=
  if nd.A ≤ jb.aB ∧ eT < nd.e ∧ nd.e - eT ≤ jb.smax then
    if boxOkS (jLay jb nd.u) jb.lb (zPCS (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb
          (nd.e - eT)
          ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
          ((jLay jb nd.u).dims.getD 1 0) 0 nd.x).re &&
        boxOkS (jLay jb nd.u) jb.lb (zPCS (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb
          (nd.e - eT) ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
          ((jLay jb nd.u).dims.getD 1 0) 0 nd.x).im then
      some ⟨nd.u, 2 ^ jb.lb, eT,
        zPCS (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb (nd.e - eT)
          ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
          ((jLay jb nd.u).dims.getD 1 0) 0 nd.x,
        upAdd nd.r (pnormS W jb.q (jRedL jb nd.u) (jLay jb nd.u) nd.e
          (zResS n jb.LU0 (nd.e - eT) nd.x
            (zPCS (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb (nd.e - eT)
              ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
              ((jLay jb nd.u).dims.getD 1 0) 0 nd.x))),
        pnormS W jb.q (jRedN jb nd.u) (jLay jb nd.u) eT
          (zPCS (jLay jb nd.u).width (jLay jb nd.u).denseLen jb.lsb (nd.e - eT)
            ((jLay jb nd.u).stride.getD 0 0) ((jLay jb nd.u).dims.getD 0 0)
            ((jLay jb nd.u).dims.getD 1 0) 0 nd.x)⟩
    else none
  else none

/-- `jMul` with shifts. -/
def jMulS (a b : JNode α) (eT : ℕ) : Option (JNode α) :=
  if a.u || b.u then
    some ⟨a.u && b.u, mulLoad (jLay jb a.u) (jLay jb b.u) a.A b.A, a.e + b.e, pcMul a.x b.x,
      pmulRad a.nb a.r b.nb b.r, upMul a.nb b.nb⟩
  else jRedWS n W jb (mulLoad jb.Lb jb.Lb a.A b.A) (a.e + b.e) (pcMul a.x b.x)
    (pmulRad a.nb a.r b.nb b.r) eT

/-- `jLeaf` with shifts. -/
def jLeafS (u : Bool) (A : ℕ) (m : CertModel α) : Option (JNode α) :=
  match (jBoxTrunc W (jLay jb u) (CertModel.toDeg W pe 0 m)).poly.toMants cfg.toMant jb.P with
  | some (re, im) =>
    if (if u then decide (A ≤ jb.aC) else decide (A ≤ 2 ^ jb.lb)) &&
        packRepOk (jLay jb u) re A && packRepOk (jLay jb u) im A then
      some ⟨u, A, jb.P, ⟨packOf (jLay jb u) re, packOf (jLay jb u) im⟩,
        (jBoxTrunc W (jLay jb u) (CertModel.toDeg W pe 0 m)).rad,
        pnormS W jb.q (if u then jb.lc else jb.ln) (jLay jb u) jb.P
          ⟨packOf (jLay jb u) re, packOf (jLay jb u) im⟩⟩
    else none
  | none => none

end Defs

section Eq

variable {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (pe : PiEnclosure α)
  (cfg : ModelConfig α) (jb : JBook)

theorem jUnitS_eq (L : PackLayout) (k : ℕ) : jUnitS n L k = jUnit n L k := by
  simp only [jUnitS, jUnit, pcUnitS_eq] <;> rfl

theorem jUpS_eq (nd : JNode α) (u' : Bool) (e' : ℕ) : jUpS n jb nd u' e' = jUp n jb nd u' e' := by
  simp only [jUpS, jUp, jUnitS_eq] <;> rfl

theorem jAddS_eq (a b : JNode α) : jAddS n jb a b = jAdd n jb a b := by
  simp only [jAddS, jAdd, jUpS_eq] <;> rfl

theorem jRedWS_eq (A e : ℕ) (x : PC) (r : α) (eT : ℕ) :
    jRedWS n W jb A e x r eT = jRedW n W jb A e x r eT := by
  simp only [jRedWS, jRedW, boxOkS_eq, zPCS_eq, pnormS_eq, zResS_eq] <;> rfl

theorem jRedS_eq (nd : JNode α) (eT : ℕ) : jRedS n W jb nd eT = jRed n W jb nd eT := by
  simp only [jRedS, jRed, boxOkS_eq, zPCS_eq, pnormS_eq, zResS_eq] <;> rfl

theorem jMulS_eq (a b : JNode α) (eT : ℕ) : jMulS n W jb a b eT = jMul n W jb a b eT := by
  simp only [jMulS, jMul, jRedWS_eq] <;> rfl

theorem jLeafS_eq (u : Bool) (A : ℕ) (m : CertModel α) :
    jLeafS W pe cfg jb u A m = jLeaf W pe cfg jb u A m := by
  simp only [jLeafS, jLeaf, pnormS_eq] <;> rfl

end Eq

end KAM.CertificateSharp.Packed
