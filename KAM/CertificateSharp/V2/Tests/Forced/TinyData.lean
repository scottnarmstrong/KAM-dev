/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.Format

/-!
# The forced toy `Tiny` (data)

The periodically forced toy `Tiny` of the V2-TOOLS regression suite,
`H = c (J + β p²/2 + Σ ε_j cos 2π k_j·θ)`, reference vector `κ (ν₋(8) - 1, 1)`, `κ = c/s`.
Emitted by `scripts/certifier/forced/forced_build.py Tiny`; the producer's report is
`scripts/certifier/fixtures/forced-toy/Tiny.json`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced

open KAM.Certificate

namespace Tiny

/-- The parameters. -/
def params : CertParams :=
  { tau := 1, rho := (1 / 8), rhoInf := (1 / 800), M := (57 / 50), σK := (103 / 100),
    σB := (103 / 100), σT := (29 / 25), μ := (1 / 100), γbar := (100000 / 1000001), σω := (2),
    nuRay := (1 / 10000000), γ := (100000 / 1000001), s := (1000001 / 1000000),
    err := (41 / 10000000000000), E0 := (0), disp := (1 / 1000) }

/-- The Hamiltonian. -/
def ham : HamExpr 2 :=
  (.mul (.const (1)) (.add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2)) (.add
    (.mul (.const (1 / 10000000)) (.cosMode [1, 0])) (.add (.mul (.const (1 / 5000000)) (.cosMode
    [1, 1])) (.const (0)))))))

/-- the half keys of angle 0, `u = 2π U` (degree -1) -/
def uHalf : List (CertKey × CC FB) :=
  [ft 0 1 0 28914612542022504, ft 1 0 0 294215801146370861942477, ft 1 1 0 10139351452291653532324,
  ft 2 0 0 (-273144469394377101), ft 2 1 0 (-50750936587771487)]

/-- angle 0, `u = 2π U` (degree -1) -/
def u : CertRealPoly FB := ⟨⟨0⟩, uHalf⟩

/-- the half keys of action 0, `p` -/
def pHalf : List (CertKey × CC FB) :=
  [ft 0 1 (-28914612542022504) 0, ft 1 0 34139549870706519354982 0,
  ft 1 1 (-8962824246025385806208) 0, ft 2 0 (-63389044357667609) 0, ft 2 1 38973091048052686 0]

/-- action 0, `p` -/
def p : CertRealPoly FB := ⟨⟨-9193298914542448669155068535⟩, pHalf⟩

/-- the half keys of action 1, `J` -/
def JHalf : List (CertKey × CC FB) :=
  [ft 0 1 (-29421580114637086) 0, ft 1 1 (-8962824246025385806208) 0, ft 2 1 38312915567024099 0,
  ft 2 2 573515920044282 0]

/-- action 1, `J` -/
def J : CertRealPoly FB := ⟨⟨-533375647355105016005742454⟩, JHalf⟩

/-- the character witness `exp(i 1 u)` -/
def E1Terms : List (CertKey × CC FB) :=
  [ft (-1) (-1) 10139351452291653532324 0, ft (-1) 0 294215801146370861942477 0,
  ft 0 0 79228162513170462116164992702 0, ft 1 0 (-294215801146370861942477) 0,
  ft 1 1 (-10139351452291653532324) 0]

/-- The character witness at the normalized key `(1, 0)`. -/
def E1 : CertKey × ExpWitness FB := ([1, 0], ⟨⟨E1Terms⟩, 0, 30⟩)

/-- the Gram inverse, entry `(0, 0)` -/
def B00 : List (CertKey × CC FB) :=
  [ft 0 0 79228162510733515485685481472 0]

/-- the Gram inverse, entry `(0, 1)` -/
def B01 : List (CertKey × CC FB) :=
  [ft 0 0 (-144115188075855872) 0]

/-- the Gram inverse, entry `(1, 0)` -/
def B10 : List (CertKey × CC FB) :=
  [ft 0 0 (-144115188075855872) 0]

/-- the Gram inverse, entry `(1, 1)` -/
def B11 : List (CertKey × CC FB) :=
  [ft 0 0 79228162514120222405468094464 0]

/-- The torsion inverse. -/
def torsInv : List (List (CC FB)) :=
  [[⟨⟨79228162521686269779450527744⟩, ⟨0⟩⟩, ⟨⟨9193298915419312232670953472⟩, ⟨0⟩⟩,
     ⟨⟨288230376151711744⟩, ⟨0⟩⟩],
    [⟨⟨9193298915347254638633025536⟩, ⟨0⟩⟩, ⟨⟨1066751294731853310126456832⟩, ⟨0⟩⟩,
     ⟨⟨79228162514264337593543950336⟩, ⟨0⟩⟩],
    [⟨⟨288230376151711744⟩, ⟨0⟩⟩, ⟨⟨79228162514336395187581878272⟩, ⟨0⟩⟩,
     ⟨⟨144115188075855872⟩, ⟨0⟩⟩]]

/-- The advice of the full stage. -/
def advFull : AdviceBook :=
  [([0, 10], .direct), ([1, 0, 0], .direct), ([1, 0, 1], .direct)]

/-- The advice of the low stage. -/
def advLow : AdviceBook :=
  [([3, 0, 0, 0, 0], .direct), ([3, 0, 0, 0, 2], .direct), ([3, 0, 0, 0, 3], .direct),
  ([3, 0, 0, 1, 0], .direct), ([3, 0, 0, 1, 2], .direct), ([3, 0, 0, 1, 3], .direct),
  ([3, 0, 1, 1, 0], .direct), ([3, 0, 1, 1, 2], .direct), ([3, 0, 1, 1, 3], .direct),
  ([0, 10], .direct), ([1, 0, 0], .direct), ([1, 0, 1], .direct), ([4, 1, 0, 0, 0], .direct),
  ([4, 1, 0, 0, 2], .direct), ([4, 1, 0, 0, 3], .direct), ([4, 1, 0, 1, 0], .direct),
  ([4, 1, 0, 1, 2], .direct), ([4, 1, 0, 1, 3], .direct), ([4, 1, 1, 0, 0], .direct),
  ([4, 1, 1, 0, 2], .direct), ([4, 1, 1, 0, 3], .direct), ([4, 1, 1, 1, 0], .direct),
  ([4, 1, 1, 1, 2], .direct), ([4, 1, 1, 1, 3], .direct), ([4, 2, 0, 0, 0], .direct),
  ([4, 2, 0, 0, 2], .direct), ([4, 2, 0, 0, 3], .direct), ([4, 2, 0, 1, 0], .direct),
  ([4, 2, 0, 1, 2], .direct), ([4, 2, 0, 1, 3], .direct), ([4, 2, 1, 0, 0], .direct),
  ([4, 2, 1, 0, 2], .direct), ([4, 2, 1, 0, 3], .direct), ([4, 2, 1, 1, 0], .direct),
  ([4, 2, 1, 1, 2], .direct), ([4, 2, 1, 1, 3], .direct), ([4, 6, 0, 0, 0], .direct),
  ([4, 6, 0, 0, 1], .direct), ([4, 6, 0, 1, 0], .direct), ([4, 6, 0, 1, 1], .direct),
  ([4, 6, 2, 0, 0], .direct), ([4, 6, 2, 0, 1], .direct), ([4, 6, 2, 1, 0], .direct),
  ([4, 6, 2, 1, 1], .direct), ([4, 6, 3, 0, 0], .direct), ([4, 6, 3, 0, 1], .direct),
  ([4, 6, 3, 1, 0], .direct), ([4, 6, 3, 1, 1], .direct), ([4, 7, 2, 0, 0], .direct),
  ([4, 7, 2, 0, 1], .direct), ([4, 7, 2, 1, 0], .direct), ([4, 7, 2, 1, 1], .direct),
  ([4, 7, 3, 0, 0], .direct), ([4, 7, 3, 0, 1], .direct), ([4, 7, 3, 1, 0], .direct),
  ([4, 7, 3, 1, 1], .direct), ([4, 8, 0, 0, 0], .direct), ([4, 8, 0, 0, 1], .direct),
  ([4, 8, 0, 0, 2], .direct), ([4, 8, 0, 1, 0], .direct), ([4, 8, 0, 1, 1], .direct),
  ([4, 8, 0, 1, 2], .direct), ([4, 8, 1, 0, 0], .direct), ([4, 8, 1, 0, 1], .direct),
  ([4, 8, 1, 0, 2], .direct), ([4, 8, 1, 1, 0], .direct), ([4, 8, 1, 1, 1], .direct),
  ([4, 8, 1, 1, 2], .direct), ([4, 9, 0, 0, 0], .direct), ([4, 9, 0, 0, 1], .direct),
  ([4, 9, 0, 0, 2], .direct), ([4, 9, 0, 1, 0], .direct), ([4, 9, 0, 1, 1], .direct),
  ([4, 9, 0, 1, 2], .direct)]

/-- The frequency box. -/
def box : FreqBox :=
  [((-255278640450004206071816526625374475291187 / 2200002200000000000000000000000000000000000),
    (1 / 2200002200000000000000000000000000000000000)),
   ((1000000 / 1000001),
    (0))]

/-- The whole certificate. -/
def cert : TorusCertificate 2 FB where
  params := params
  ham := ham
  weightH := ⟨(137 / 1000), (591260914609 / 250000000000)⟩
  centre := [(-63791325795 / 549755813888), (-925259257 / 137438953472)]
  radius := [(11 / 1000), (11 / 1000)]
  freqBox := box
  emb := ⟨[-1, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [p, J]⟩
  weight := ⟨(1 / 8), (1096640120341 / 500000000000)⟩
  wit := ⟨[], [], [E1], []⟩
  gramInv := [[⟨B00⟩, ⟨B01⟩], [⟨B10⟩, ⟨B11⟩]]
  torsInv := torsInv
  cfgFull := ⟨1000000, 30, 8, fun _ _ => none, advFull⟩
  cfgLow := ⟨4, 30, 8, fun _ _ => none, advLow⟩
  piEnc := ⟨⟨248902613312231085151526664211⟩, ⟨85070591735⟩, 6, 3⟩
  expHalvings := 8
  expOrder := 30

end Tiny

end KAM.CertificateSharp.V2.Forced

end
