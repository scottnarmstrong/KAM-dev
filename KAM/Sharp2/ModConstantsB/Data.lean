/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstantsB.Defs

/-!
# The `let`s of `stepConstsB` and admissible inputs

`StepInB.OkF` is `StepInB.Ok` unfolded to one field per inequality (and the facts `positivity`
needs); `StepInB.Le` is `StepInB.Dom` as rewriting equations `p'.x = p.x`; one definition per `let`
of `stepConstsB` (`stepConstsB_eq` in `ModConstantsB` is `rfl`).
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

/-- `StepInB.Ok` with one field per inequality. -/
structure StepInB.OkF (p : StepInB) : Prop where
  n1 : 1 ≤ p.n
  nR : (0 : ℝ) ≤ p.n
  nR1 : (0 : ℝ) ≤ (p.n : ℝ) - 1
  κ1 : 1 ≤ p.κ
  κ0 : 0 ≤ p.κ
  M1 : 0 ≤ p.M1
  M2 : 0 ≤ p.M2
  cTh : 0 ≤ p.cTh
  cDTh : 0 ≤ p.cDTh
  Θ : 0 ≤ p.Θ
  y0 : 0 ≤ p.y0
  Mh2 : 0 ≤ p.Mh2
  ePer : 0 ≤ p.ePer
  sK : 0 < p.sK
  sLt : 0 < p.sLt
  sB : 0 < p.sB
  sN : 0 < p.sN
  sNt : 0 < p.sNt
  sT : 0 < p.sT
  ts : 0 < p.ts
  bF : 0 < p.bF
  c : 0 < p.c
  c1 : 0 < p.c1
  cavg : 0 ≤ p.cavg
  θ0 : 0 < p.θ
  θ1 : 0 < 1 - p.θ
  θξ0 : 0 < p.θξ
  θξ1 : p.θξ < 1
  θΩ0 : 0 < p.θΩ
  θΩ1 : p.θΩ < 1
  q0 : 0 < p.q
  q1 : 0 < 1 - p.q
  q2 : 0 < 1 - p.q ^ 2
  θN0 : 0 < p.θN
  θN1 : 0 < 1 - p.θN
  θω0 : 0 < p.θω
  θω1 : p.θω < 1
  a0 : 0 ≤ p.a
  a1 : 1 < p.a
  lam0 : 0 < p.lam
  lam1 : p.lam ≤ 1
  lamW0 : 0 < p.lamW
  lamW1 : p.lamW ≤ 1
  γb : 0 < p.γb
  δ0 : 0 < p.δ
  δ1 : p.δ ≤ 1

theorem StepInB.Ok.flat {p : StepInB} (h : p.Ok) : p.OkF := by
  obtain ⟨n1, κ1, ⟨M1, M2, cTh, cDTh, Θ, y0, Mh2, ePer⟩, ⟨sK, sLt, sB, sN, sNt, sT⟩, ⟨ts, bF⟩,
    ⟨c, c1, cavg⟩, ⟨θ0, θ1, θξ0, θξ1, θΩ0, θΩ1, q0, q1, θN0, θN1, θω0, θω1⟩, a1, ⟨lam0, lam1, lamW0,
      lamW1⟩, γb, δ0, δ1⟩ := h
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast n1
  exact ⟨n1, by linarith, by linarith, κ1, by linarith, M1, M2, cTh, cDTh, Θ, y0, Mh2, ePer, sK,
    sLt, sB, sN, sNt, sT, ts, bF, c, c1, cavg, θ0, by linarith, θξ0, θξ1, θΩ0, θΩ1, q0,
    by linarith, by nlinarith, θN0, by linarith, θω0, θω1, by linarith, a1, lam0, lam1, lamW0,
    lamW1, γb, δ0, δ1⟩

/-- `Dom` as rewriting equations (`p'.x = p.x`). -/
structure StepInB.Le (p p' : StepInB) : Prop where
  n : p'.n = p.n
  κ : p'.κ = p.κ
  M1 : p'.M1 = p.M1
  M2 : p'.M2 = p.M2
  cTh : p'.cTh = p.cTh
  cDTh : p'.cDTh = p.cDTh
  sK : p'.sK = p.sK
  sLt : p'.sLt = p.sLt
  sB : p'.sB = p.sB
  sN : p'.sN = p.sN
  sNt : p'.sNt = p.sNt
  sT : p'.sT = p.sT
  ts : p'.ts = p.ts
  bF : p'.bF = p.bF
  θ : p'.θ = p.θ
  θξ : p'.θξ = p.θξ
  θΩ : p'.θΩ = p.θΩ
  q : p'.q = p.q
  θN : p'.θN = p.θN
  θω : p'.θω = p.θω
  a : p'.a = p.a
  γb : p'.γb = p.γb
  selfcons : p'.selfcons = p.selfcons
  iso : p'.iso = p.iso
  Θ : p'.Θ = p.Θ
  y0 : p'.y0 = p.y0
  Mh2 : p'.Mh2 = p.Mh2
  δ : p.δ ≤ p'.δ
  c : p.c ≤ p'.c
  c1 : p.c1 ≤ p'.c1
  cavg : p.cavg ≤ p'.cavg
  lam : p.lam ≤ p'.lam
  lamW : p.lamW ≤ p'.lamW
  s0 : p.stage0 = false
  s0' : p'.stage0 = false

theorem StepInB.Dom.toLe {p p' : StepInB} (h : p.Dom p') : p.Le p' := by
  obtain ⟨⟨n, κ, M1, M2, cTh, cDTh, sK, sLt, sB, sN, sNt, sT, ts, bF, θ, θξ, θΩ, q, θN, θω, a, γb,
    sc, iso, Θ, y0, Mh2⟩, ⟨δ, c, c1, cavg, lam, lamW⟩, s0, s0'⟩ := h
  exact ⟨n.symm, κ.symm, M1.symm, M2.symm, cTh.symm, cDTh.symm, sK.symm, sLt.symm, sB.symm,
    sN.symm, sNt.symm, sT.symm, ts.symm, bF.symm, θ.symm, θξ.symm, θΩ.symm, q.symm, θN.symm,
    θω.symm, a.symm, γb.symm, sc.symm, iso.symm, Θ.symm, y0.symm, Mh2.symm, δ, c, c1, cavg, lam,
    lamW, s0, s0'⟩

/-! ### One definition per `let` of `stepConstsB` -/

def sg (p : StepInB) : ℝ :=
  p.γb * p.δ ^ p.κ

def sg1 (p : StepInB) : ℝ :=
  sg p * p.δ

def sKt (p : StepInB) : ℝ :=
  (1 + p.θ) * p.sK

def st (p : StepInB) : ℝ :=
  p.cTh * p.sNt * p.sN + p.ts

def saw (p : StepInB) : ℝ :=
  if p.iso then 1 + p.θω else 1

def sCΩ (p : StepInB) : ℝ :=
  2 * ((p.n : ℝ) - 1) * p.c1

def sCEL (p : StepInB) : ℝ :=
  (p.sK + p.sN * p.q) / (1 - p.q ^ 2)

def sCEN (p : StepInB) : ℝ :=
  (p.sN + p.sK * p.q) / (1 - p.q ^ 2)

def sCE0 (p : StepInB) : ℝ :=
  p.lam * sCEL p + sg p * sCEN p

def sCE (p : StepInB) : ℝ :=
  if p.stage0 then min (sCE0 p) p.ePer else sCE0 p

def sCDE0 (p : StepInB) : ℝ :=
  (p.n : ℝ) * (p.sK + p.sN) * (max p.lam (sg p) + (p.sLt + p.sNt) * sCE p) / (1 - p.q)

def sCDE (p : StepInB) : ℝ :=
  if p.stage0 then min (sCDE0 p) ((p.n : ℝ) * p.ePer) else sCDE0 p

def sCNN (p : StepInB) : ℝ :=
  (p.n : ℝ) * (p.lam + p.sNt * sCE p)

def sC0 (p : StepInB) : ℝ :=
  if p.iso then p.sT * max (p.lam + st p * p.cavg) (p.lamW + p.y0 * p.cavg)
  else p.sT * (p.lam + st p * p.cavg)

def sCxiN (p : StepInB) : ℝ :=
  sC0 p + p.c

def sCKt (p : StepInB) : ℝ :=
  p.sN * sCxiN p

def sCDLt (p : StepInB) : ℝ :=
  (p.n : ℝ) * p.sN * (sC0 p + p.c1)

def sCDLtT (p : StepInB) : ℝ :=
  2 * (p.n : ℝ) * p.sN * (sC0 p + p.c1)

def sCdN (p : StepInB) : ℝ :=
  (p.M1 * p.sK + p.n) * p.sB +
  p.sN * ((p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n)) * p.sB

def sCXN (p : StepInB) : ℝ :=
  p.M1 * p.sN + sCdN p

def sCEt (p : StepInB) : ℝ :=
  sCE p + sCXN p * sCxiN p + p.sN * sg p + p.M2 / 2 * sCKt p +
  (if p.iso then sKt p * p.Θ * sC0 p else 0)

def sQtN (p : StepInB) : ℝ :=
  sCDLtT p * sCEt p + sCNN p * sCxiN p + p.δ * p.sLt * (p.M2 / 2) * sCKt p ^ 2

def sCgL (p : StepInB) : ℝ :=
  p.lam + st p * sCxiN p + (if p.iso then p.Θ * sC0 p else 0)

def sCxiL (p : StepInB) : ℝ :=
  p.c * sCgL p

def sCDK (p : StepInB) : ℝ :=
  sKt p * sCxiL p + sg p * sCKt p

def sCEb (p : StepInB) : ℝ :=
  sCEt p + saw p * sKt p * sCgL p

def sCG (p : StepInB) : ℝ :=
  (p.n : ℝ) * p.sLt + 2 * (p.n : ℝ) * p.sK

def sCBb (p : StepInB) : ℝ :=
  p.sB ^ 2 * sCG p * sCDK p / (1 - p.θ)

def sCNb (p : StepInB) : ℝ :=
  (p.n : ℝ) * sCDK p * p.sB + p.sK * sCBb p

def sCNbT (p : StepInB) : ℝ :=
  sCBb p * p.sLt + 2 * (p.n : ℝ) * sCDK p * p.sB

def sw (p : StepInB) : ℝ :=
  2 * p.M1 * p.sLt * p.sK + 2 * (p.n : ℝ) * p.sK + (p.n : ℝ) * p.sLt

def sCab0 (p : StepInB) : ℝ :=
  p.cTh * (sCNbT p * p.sN + p.sNt * sCNb p) +
  p.cDTh * p.sNt * p.sN * sCDK p * p.δ

def sCab (p : StepInB) : ℝ :=
  if p.iso then max (sCab0 p + p.Θ * sC0 p * sg1 p) ((p.n : ℝ) * p.Θ * sC0 p * sg1 p)
  else sCab0 p

def sBsup (p : StepInB) : ℝ :=
  (p.sNt * p.sB * sCDE p + p.sB ^ 3 * sw p * sCΩ p) * sg p

def sBloc (p : StepInB) : ℝ :=
  if p.iso then max (sBsup p) ((p.n : ℝ) * sg1 p) else sBsup p

def sQbN (p : StepInB) : ℝ :=
  if p.iso then (1 + (p.n : ℝ) * p.θξ) * (1 + (1 + saw p) * p.θΩ) * sQtN p
  else (1 + (p.n : ℝ) * p.θξ) * (1 + p.θΩ) * sQtN p

def sQL1 (p : StepInB) : ℝ :=
  p.sNt * (p.M2 / 2) * sCKt p ^ 2 * sg1 p + p.sB ^ 2 * sCΩ p * sg p ^ 2 +
  (p.n : ℝ) * p.sNt * sCEt p * sCxiL p +
  saw p * p.sNt * sCgL p * ((p.n : ℝ) * sKt p * sCxiL p + sg p * sCDLt p) +
  (if p.iso then sC0 p * sCgL p * sg1 p + sC0 p * p.sNt * sCDLt p * p.Θ * sg p else 0)

def sQLc (p : StepInB) : ℝ :=
  sQL1 p + sCNbT p * sCEb p

def sQLs (p : StepInB) : ℝ :=
  if p.selfcons then
    min (sQLc p) ((sQL1 p + p.θN * (sCEN p / sCEL p) * sQbN p * sg p) / (1 - p.θN))
  else sQLc p

def sQw (p : StepInB) : ℝ :=
  p.Mh2 / 2 * sCKt p ^ 2 * sg1 p + (p.n : ℝ) * sQtN p * p.θξ * (p.Θ * sCΩ p + sg1 p)

def sQL (p : StepInB) : ℝ :=
  if p.iso then max (sQLs p) (sQw p) else sQLs p

def sQ (p : StepInB) : ℝ :=
  max (sQL p) (p.a ^ p.κ * sQbN p)

def sCnu (p : StepInB) : ℝ :=
  if p.iso then p.Θ * sC0 p else 0

theorem sCEL_eq {p p' : StepInB} (hl : p.Le p') : sCEL p' = sCEL p := by
  simp only [sCEL, hl.sK, hl.sN, hl.q]

theorem sCEN_eq {p p' : StepInB} (hl : p.Le p') : sCEN p' = sCEN p := by
  simp only [sCEN, hl.sK, hl.sN, hl.q]


end KAM.Sharp2

end
