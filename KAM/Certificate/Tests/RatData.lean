/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Tests.ToyLit

/-!
# Data of the toy certificate TR

Emitted by `scripts/spin_orbit/toy_lean_cert.py` from
`certificates/so-toys/TR.json` ; `toyTRCert` is the whole certificate.
-/

@[expose] public section

namespace KAM.Certificate

def toyTRParams : CertParams :=
  {tau := 1,rho := 9,rhoInf := 1,M := (89 / 50),σK := (89 / 50),σB := (89 / 50),σT := (89 / 50),μ
  := (1 / 100),γbar := (1 / 42),σω := 3,nuRay := (49 / 100),γ := (1 / 42),s := 2,err := 0,E0 :=
  0,disp := 0 }

def toyTRHam : HamExpr 2 :=
  .add (.action 1) (.mul (.const (1 / 2)) (.pow (.action 0) 2))

def toyTRWeightH : CertWeight :=
  ⟨(451 / 50), (2052684210367924024698804359963 / 500000)⟩

def toyTRWeight : CertWeight :=
  ⟨9, (905142768046211949085245961113 / 250000)⟩

def toyTRCentre : List ℚ :=
  [(1 / 2), (-1 / 8)]

def toyTRRadius : List ℚ :=
  [(1 / 50), (1 / 50)]

def toyTRBox : FreqBox :=
  [((1 / 4), 0), ((1 / 2), 0)]

def toyTREmb : CertEmbedding ℚ :=
  ⟨[0, 0], [⟨0, []⟩, ⟨0, []⟩], [0, 0], [⟨(1 / 2), []⟩, ⟨(-1 / 8), []⟩]⟩

def toyTRWit : Witnesses ℚ :=
  ⟨[], [], []⟩

def toyTRGramInv : List (List (CertPoly ℚ)) :=
  [[⟨[([0, 0], ⟨1, 0⟩)]⟩, ⟨[]⟩], [⟨[]⟩, ⟨[([0, 0], ⟨1, 0⟩)]⟩]]

def toyTRTorsInv : List (List (CC ℚ)) :=
  [[⟨1, 0⟩, ⟨(-1 / 2), 0⟩, ⟨0, 0⟩], [⟨(-1 / 2), 0⟩, ⟨(1 / 4), 0⟩, ⟨1, 0⟩], [⟨0, 0⟩, ⟨1, 0⟩, ⟨0,
  0⟩]]

def toyTRCfgFull : ModelConfig ℚ :=
  ⟨1000000, 24, 8, fun _ _ => none, []⟩

def toyTRCfgLow : ModelConfig ℚ :=
  ⟨1000000, 24, 8, fun _ _ => none, []⟩

def toyTRPi : PiEnclosure ℚ :=
  ⟨(toyQ 3314427442226971084353063282817081764744359895236591237306
  1055015021899892426313124618802400368315005057525634765625), (toyQ
  216697700653013966585122908521505070030082
  351320353613017790980061478122677445326342010498046875), 4, 4⟩

/-- The whole certificate. -/
def toyTRCert : TorusCertificate 2 ℚ where
  params := toyTRParams
  ham := toyTRHam
  weightH := toyTRWeightH
  centre := toyTRCentre
  radius := toyTRRadius
  freqBox := toyTRBox
  emb := toyTREmb
  weight := toyTRWeight
  wit := toyTRWit
  gramInv := toyTRGramInv
  torsInv := toyTRTorsInv
  cfgFull := toyTRCfgFull
  cfgLow := toyTRCfgLow
  piEnc := toyTRPi
  expHalvings := 8
  expOrder := 24

end KAM.Certificate
