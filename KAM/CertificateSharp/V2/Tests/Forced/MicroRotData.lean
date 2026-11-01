/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.Format

/-!
# The forced toy `Micro` in rotated coordinates (data)

The forced toy `Micro` in the rotated variables of the lunar client: the linear
symplectic unimodular change of variables `L ((Q₀, Q₁), (P₀, P₁)) = ((Q₀ + Q₁, Q₁), (P₀, P₁ - P₀))`
(`shearMap`, the lunar `soRotMap`). The Hamiltonian is `H ∘ L` (modes `k ↦ (k₀, k₀ + k₁)`, the
action `J` becomes `P₁ - P₀`); the torus is `L⁻¹ ∘ K ∘ S`, `S (φ₀, φ₁) = (φ₀ + φ₁, φ₁)`, whose
data are `Micro`'s mantissas at the sheared keys, the action `P₁ = p + J` merging the two
key-sorted lists; the character witness is `Micro`'s, relabelled; the box is the exact image of
`Micro`'s under `ω ↦ (ω₀ - ω₁, ω₁)` and `γ` is halved. The domain, `M`, the `σ`'s, the Gram and
torsion witnesses, `err` and the advice books are computed afresh by the mirror.
`MicroRotTransform` proves that these data are exactly the transforms (`ham_eq`, `emb_eq`,
`box_eq`). Emitted by `scripts/certifier/forced/forced_rot.py`; the producer's report is
`scripts/certifier/fixtures/forced-toy/MicroRot.json`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced

open KAM.Certificate

namespace MicroRot

/-- The parameters. -/
def params : CertParams :=
  { tau := 1, rho := (1 / 8), rhoInf := (1 / 800), M := (43 / 20), σK := (103 / 100),
    σB := (103 / 100), σT := (341 / 100), μ := (1 / 100), γbar := (50000 / 1000001), σω := (2),
    nuRay := (1 / 10000000), γ := (50000 / 1000001), s := (1000001 / 1000000),
    err := (791 / 100000000000000000000000000), E0 := (0), disp := (1 / 1000) }

/-- The Hamiltonian. -/
def ham : HamExpr 2 :=
  (.mul (.const (1)) (.add (.add (.action 1) (.mul (.const (-1)) (.action 0))) (.add (.mul (.const
    (1 / 2)) (.pow (.action 0) 2)) (.add (.mul (.const (1 / 1000000000000)) (.cosMode [1, 1]))
    (.add (.mul (.const (1 / 500000000000)) (.cosMode [1, 2])) (.const (0)))))))

/-- the half keys of angle 0, `u = 2π U` (degree -1) -/
def uHalf : List (CertKey × CC FB) :=
  [ft 0 1 0 2891461, ft 1 1 0 2942158011463708619, ft 1 2 0 101393514522916535,
  ft 2 2 0 (-27314447), ft 2 3 0 (-5075094), ft 2 4 0 (-32440)]

/-- angle 0, `u = 2π U` (degree -1) -/
def u : CertRealPoly FB := ⟨⟨0⟩, uHalf⟩

/-- the half keys of action 0, `p` -/
def pHalf : List (CertKey × CC FB) :=
  [ft 0 1 (-2891461) 0, ft 1 1 341395498707065194 0, ft 1 2 (-89628242460253858) 0,
  ft 2 2 (-6338904) 0, ft 2 3 3897309 0, ft 2 4 57352 0]

/-- action 0, `p` -/
def p : CertRealPoly FB := ⟨⟨-9193298914542448669155068535⟩, pHalf⟩

/-- the half keys of action 1, `P₁ = p + J` -/
def P1Half : List (CertKey × CC FB) :=
  [ft 0 1 (-5833619) 0, ft 1 1 341395498707065194 0, ft 1 2 (-179256484920507716) 0,
  ft 2 2 (-6338904) 0, ft 2 3 7728601 0, ft 2 4 114704 0]

/-- action 1, `P₁ = p + J` -/
def P1 : CertRealPoly FB := ⟨⟨-9726674561850379509557804841⟩, P1Half⟩

/-- the character witness `exp(i 1 u)` -/
def E1Terms : List (CertKey × CC FB) :=
  [ft (-1) (-2) 101393514522916535 0, ft (-1) (-1) 2942158011463708619 0,
  ft 0 0 79228162514264337593543950336 0, ft 1 1 (-2942158011463708619) 0,
  ft 1 2 (-101393514522916535) 0]

/-- The character witness at the normalized key `(1, 0)`. -/
def E1 : CertKey × ExpWitness FB := ([1, 0], ⟨⟨E1Terms⟩, 0, 30⟩)

/-- the Gram inverse, entry `(0, 0)` -/
def B00 : List (CertKey × CC FB) :=
  [ft 0 0 79228162514264337593543950336 0]

/-- the Gram inverse, entry `(0, 1)` -/
def B01 : List (CertKey × CC FB) :=
  []

/-- the Gram inverse, entry `(1, 0)` -/
def B10 : List (CertKey × CC FB) :=
  []

/-- the Gram inverse, entry `(1, 1)` -/
def B11 : List (CertKey × CC FB) :=
  [ft 0 0 79228162514264337593543950336 0]

/-- The torsion inverse. -/
def torsInv : List (List (CC FB)) :=
  [[⟨⟨79228162514264337593543950336⟩, ⟨0⟩⟩, ⟨⟨88421461428818958697759768576⟩, ⟨0⟩⟩, ⟨⟨0⟩, ⟨0⟩⟩],
    [⟨⟨88421461428818958697759768576⟩, ⟨0⟩⟩, ⟨⟨98681511637961317924026187776⟩, ⟨0⟩⟩,
     ⟨⟨79228162514264337593543950336⟩, ⟨0⟩⟩],
    [⟨⟨0⟩, ⟨0⟩⟩, ⟨⟨79228162514264337593543950336⟩, ⟨0⟩⟩, ⟨⟨0⟩, ⟨0⟩⟩]]

/-- The advice of the full stage. -/
def advFull : AdviceBook :=
  [([0, 16], .direct), ([1, 0, 0], .direct), ([1, 0, 1], .direct)]

/-- The advice of the low stage. -/
def advLow : AdviceBook :=
  [([3, 0, 0, 0, 0], .direct), ([3, 0, 0, 0, 2], .direct), ([3, 0, 0, 0, 3], .direct),
  ([3, 0, 0, 1, 0], .direct), ([3, 0, 0, 1, 2], .direct), ([3, 0, 0, 1, 3], .direct),
  ([3, 0, 1, 1, 0], .direct), ([3, 0, 1, 1, 2], .direct), ([3, 0, 1, 1, 3], .direct),
  ([0, 16], .direct), ([1, 0, 0], .direct), ([1, 0, 1], .direct), ([4, 1, 0, 0, 0], .direct),
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
  [((-245527864045000420607181652662537447529118763281 /
      220000220000000000000000000000000000000000000000),
    (1 / 220000220000000000000000000000000000000000000000)),
   ((1000000 / 1000001),
    (0))]

/-- The whole certificate. -/
def cert : TorusCertificate 2 FB where
  params := params
  ham := ham
  weightH := ⟨(137 / 1000), (591260914609 / 250000000000)⟩
  centre := [(-63791325795 / 549755813888), (-134984725645 / 1099511627776)]
  radius := [(11 / 1000), (11 / 1000)]
  freqBox := box
  emb := ⟨[-1, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [p, P1]⟩
  weight := ⟨(1 / 8), (1096640120341 / 500000000000)⟩
  wit := ⟨[], [], [E1], []⟩
  gramInv := [[⟨B00⟩, ⟨B01⟩], [⟨B10⟩, ⟨B11⟩]]
  torsInv := torsInv
  cfgFull := ⟨1000000, 30, 8, fun _ _ => none, advFull⟩
  cfgLow := ⟨4, 30, 8, fun _ _ => none, advLow⟩
  piEnc := ⟨⟨248902613312231085230521791627⟩, ⟨164990⟩, 8, 3⟩
  expHalvings := 8
  expOrder := 30

end MicroRot

end KAM.CertificateSharp.V2.Forced

end
