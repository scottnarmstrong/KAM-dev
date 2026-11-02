/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.StageZ
public import KAM.CertificateSharp.Packed.JetIngest
public import KAM.CertificateSharp.Packed.Tors

/-!
# Window-sized powers as shifts: the leaves

The kernel evaluates `Nat.pow` only for exponents up to `2^24` (Lean's `LEAN_NAT_MAX_SIZE`); shifts,
products, masks and divisions of larger numbers run at GMP speed (MAG-PACKED-GATE, step 0). The
packed checks spell the powers of their windows as `2 ^ (w * N)`, so they stop at windows of more
than `2^24` bits. This file gives the same functions with every window-sized power written as a
shift (`1 <<< e`), each with its equality lemma (`…S_eq`), so that the soundness theorems of the
landed definitions apply unchanged:
* the digit masks `periodicS`, `boxPatS`, `digitShiftS` and the box check `boxOkS`;
* the packed absolute values `packAbsS`, the weight table `weightRevS` (built by halving the row
  list, `rowsPackB`, so that the kernel keeps `O(log rows)` intermediates, not one per row: the
  landed `rowsPack` exceeds 4 GB at windows of 116k slots), the packed norm `packNormS`, `pcNormS`,
  `pnormS`;
* the units `pcUnitS`, `pcUnitSubS`, the reduce `zPartS`, `zPCS`, `zResS`, the digit `slotAtS`,
  `ptDigitS`;
* the ingestion `spreadStepS`, `spreadAuxS`, `jSpreadS`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-! ### Digit masks and the box check -/

/-- `periodic` with its window-sized power as a shift. -/
def periodicS (w N m : ℕ) : ℕ := m * (((1 <<< (w * N)) - 1) / ((1 <<< w) - 1))

theorem periodicS_eq : periodicS = periodic := by
  funext w N m
  simp only [periodicS, periodic, Nat.one_shiftLeft]

/-- `boxPat` with shifts. -/
def boxPatS (w S D0 D1 v : ℕ) : ℕ := periodicS (w * S) D0 (periodicS w D1 v)

theorem boxPatS_eq : boxPatS = boxPat := by
  funext w S D0 D1 v
  simp only [boxPatS, boxPat, periodicS_eq]

/-- `digitShift` with shifts. -/
def digitShiftS (w N s Y : ℕ) : ℕ := (Y - (Y &&& periodicS w N (2 ^ s - 1))) >>> s

theorem digitShiftS_eq : digitShiftS = digitShift := by
  funext w N s Y
  simp only [digitShiftS, digitShift, periodicS_eq]

/-- `boxOk` with shifts. -/
def boxOkS (L : PackLayout) (l : ℕ) (Z : ℤ) : Bool :=
  boxShapeOk L && decide (l + 1 ≤ L.width) &&
    decide (0 ≤ Z + (boxPatS L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
      (2 ^ l) : ℤ)) &&
    decide ((Z + (boxPatS L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
      (2 ^ l) : ℤ)).toNat < 1 <<< (L.width * boxLen (L.stride.getD 0 0) (L.dims.getD 0 0)
        (L.dims.getD 1 0))) &&
    ((Z + (boxPatS L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
      (2 ^ l) : ℤ)).toNat &&& boxPatS L.width (L.stride.getD 0 0) (L.dims.getD 0 0)
        (L.dims.getD 1 0) (2 ^ (l + 1) - 1) ==
      (Z + (boxPatS L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
        (2 ^ l) : ℤ)).toNat)

theorem boxOkS_eq : boxOkS = boxOk := by
  funext L l Z
  simp only [boxOkS, boxOk, boxPatS_eq, Nat.one_shiftLeft]

/-! ### The packed norm -/

/-- `packAbs` with shifts. -/
def packAbsS (w N l : ℕ) (Z : ℤ) : ℕ :=
  let Y := (Z + (periodicS w N (2 ^ l) : ℤ)).toNat
  let S := digitShiftS w N l Y
  let P := Y &&& (S * (2 ^ (l + 1) - 1))
  (P - S * 2 ^ l) + ((periodicS w N (2 ^ l) - S * 2 ^ l) - (Y - P))

theorem packAbsS_eq : packAbsS = packAbs := by
  funext w N l Z
  simp only [packAbsS, packAbs, periodicS_eq, digitShiftS_eq]

theorem rowsPack_append (w s0 Cpk : ℕ) :
    ∀ xs ys : List ℕ, rowsPack w s0 Cpk (xs ++ ys) =
      rowsPack w s0 Cpk xs + (rowsPack w s0 Cpk ys <<< (w * s0 * xs.length))
  | [], ys => by simp [rowsPack]
  | x :: xs, ys => by
    simp only [List.cons_append, rowsPack, rowsPack_append w s0 Cpk xs ys, List.length_cons,
      Nat.shiftLeft_eq]
    ring

/-- `rowsPack` by halving the row list (`fuel` levels, then the linear `rowsPack`): every
intermediate integer covers only its rows. -/
def rowsPackB (w s0 Cpk : ℕ) : ℕ → List ℕ → ℕ
  | 0, rs => rowsPack w s0 Cpk rs
  | f + 1, rs => if rs.length ≤ 1 then rowsPack w s0 Cpk rs else
      rowsPackB w s0 Cpk f (rs.take (rs.length / 2)) +
        (rowsPackB w s0 Cpk f (rs.drop (rs.length / 2)) <<< (w * s0 * (rs.length / 2)))

theorem rowsPackB_eq (w s0 Cpk : ℕ) :
    ∀ (f : ℕ) (rs : List ℕ), rowsPackB w s0 Cpk f rs = rowsPack w s0 Cpk rs
  | 0, rs => rfl
  | f + 1, rs => by
    unfold rowsPackB
    split_ifs with h
    · rfl
    · rw [rowsPackB_eq w s0 Cpk f, rowsPackB_eq w s0 Cpk f]
      conv_rhs => rw [← List.take_append_drop (rs.length / 2) rs]
      rw [rowsPack_append, List.length_take, min_eq_left (Nat.div_le_self _ _)]

/-- `weightRev` by halving the row list. -/
def weightRevS (W : CertWeight) (q : ℕ) (L : PackLayout) : ℕ :=
  rowsPackB L.width (L.stride.getD 0 0) (natPack L.width (colsRev W q L)) 12 (rowsRev W q L)

theorem weightRevS_eq : weightRevS = weightRev := by
  funext W q L
  simp only [weightRevS, weightRev, rowsPackB_eq]

/-- `packNorm` with shifts and the halved weight table. -/
def packNormS (W : CertWeight) (q l : ℕ) (L : PackLayout) (Z : ℤ) : ℕ :=
  ((packAbsS L.width L.denseLen l Z * weightRevS W q L) >>>
    (L.width * (L.dims.getD 0 0 * L.stride.getD 0 0 - 1))) &&& (2 ^ L.width - 1)

theorem packNormS_eq : packNormS = packNorm := by
  funext W q l L Z
  simp only [packNormS, packNorm, packAbsS_eq, weightRevS_eq]

/-- `pcNorm` with shifts. -/
def pcNormS (W : CertWeight) (q l : ℕ) (L : PackLayout) (x : PC) : ℕ :=
  packNormS W q l L x.re + packNormS W q l L x.im

theorem pcNormS_eq : pcNormS = pcNorm := by
  funext W q l L x
  simp only [pcNormS, pcNorm, packNormS_eq]

/-- `pnorm` with shifts. -/
def pnormS {α : Type} [CertArith α] (W : CertWeight) (q l : ℕ) (L : PackLayout) (e : ℕ) (x : PC) :
    α :=
  ofRatUp ((pcNormS W q l L x : ℚ) / 2 ^ (e + 2 * q))

theorem pnormS_eq {α : Type} [CertArith α] : (pnormS : _ → _ → _ → _ → _ → _ → α) = pnorm := by
  funext W q l L e x
  simp only [pnormS, pnorm, pcNormS_eq]

/-! ### Units, the reduce, digits -/

/-- `pcUnit` with a shift. -/
def pcUnitS (w p : ℕ) (c : ℤ) : PC := ⟨c * ((1 <<< (w * p) : ℕ) : ℤ), 0⟩

theorem pcUnitS_eq : pcUnitS = pcUnit := by
  funext w p c
  simp only [pcUnitS, pcUnit, Nat.one_shiftLeft, Nat.cast_pow, Nat.cast_ofNat]

/-- `pcUnitSub` with a shift. -/
def pcUnitSubS (w p : ℕ) (c : ℤ) (x : PC) : PC := ⟨c * ((1 <<< (w * p) : ℕ) : ℤ) - x.re, -x.im⟩

theorem pcUnitSubS_eq : pcUnitSubS = pcUnitSub := by
  funext w p c x
  simp only [pcUnitSubS, pcUnitSub, Nat.one_shiftLeft, Nat.cast_pow, Nat.cast_ofNat]

/-- `zPart` with shifts. -/
def zPartS (w Ns ls s S D0 D1 off : ℕ) (Z : ℤ) : ℤ :=
  ((((digitShiftS w Ns s
      (Z + (periodicS w Ns (2 ^ ls) : ℤ) + (periodicS w Ns (2 ^ (s - 1)) : ℤ)).toNat) &&&
        (boxPatS w S D0 D1 (2 ^ w - 1) <<< (w * off))) >>> (w * off) : ℕ) : ℤ) -
    (boxPatS w S D0 D1 (2 ^ (ls - s)) : ℤ)

theorem zPartS_eq : zPartS = zPart := by
  funext w Ns ls s S D0 D1 off Z
  simp only [zPartS, zPart, digitShiftS_eq, periodicS_eq, boxPatS_eq]

/-- `zPC` with shifts. -/
def zPCS (w Ns ls s S D0 D1 off : ℕ) (x : PC) : PC :=
  ⟨zPartS w Ns ls s S D0 D1 off x.re, zPartS w Ns ls s S D0 D1 off x.im⟩

theorem zPCS_eq : zPCS = zPC := by
  funext w Ns ls s S D0 D1 off x
  simp only [zPCS, zPC, zPartS_eq]

/-- `zRes` with a shift. -/
def zResS (n : ℕ) (Lu : PackLayout) (s : ℕ) (x x' : PC) : PC :=
  pcAdd x (pcNeg (pcMul x' (pcUnitS Lu.width (zslot n Lu) (2 ^ s))))

theorem zResS_eq : zResS = zRes := by
  funext n Lu s x x'
  simp only [zResS, zRes, pcUnitS_eq]

/-- `slotAt` with shifts. -/
def slotAtS (w p : ℕ) (Z : ℤ) : ℤ :=
  (Z.bmod (1 <<< (w * (p + 1))) - Z.bmod (1 <<< (w * p))) / ((1 <<< (w * p) : ℕ) : ℤ)

theorem slotAtS_eq : slotAtS = slotAt := by
  funext w p Z
  simp only [slotAtS, slotAt, Nat.one_shiftLeft, Nat.cast_pow, Nat.cast_ofNat]

/-- `ptDigit` with shifts. -/
def ptDigitS (n : ℕ) (L : PackLayout) (e : ℕ) (x : PC) : ℚ × ℚ :=
  ((slotAtS L.width (zslot n L) x.re : ℚ) / 2 ^ e, (slotAtS L.width (zslot n L) x.im : ℚ) / 2 ^ e)

theorem ptDigitS_eq : ptDigitS = ptDigit := by
  funext n L e x
  simp only [ptDigitS, ptDigit, slotAtS_eq]

/-! ### Ingestion -/

/-- `spreadStep` with shifts. -/
def spreadStepS (a b h k Y : ℕ) : ℕ :=
  Y + (Y &&& periodicS (b * (2 * h)) k (((1 <<< (a * h)) - 1) <<< (a * h))) *
    ((1 <<< ((b - a) * h)) - 1)

theorem spreadStepS_eq : spreadStepS = spreadStep := by
  funext a b h k Y
  simp only [spreadStepS, spreadStep, periodicS_eq, Nat.one_shiftLeft]

/-- `spreadAux` with shifts. -/
def spreadAuxS (a b : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, Y => Y
  | L + 1, k, Y => spreadAuxS a b L (2 * k) (spreadStepS a b (2 ^ L) k Y)

theorem spreadAuxS_eq (a b : ℕ) : ∀ L k Y, spreadAuxS a b L k Y = spreadAux a b L k Y
  | 0, _, _ => rfl
  | L + 1, k, Y => by
    simp only [spreadAuxS, spreadAux, spreadStepS_eq, spreadAuxS_eq a b L]

/-- `jSpread` with shifts. -/
def jSpreadS (D0 D1 S w wn L1 L2 Y : ℕ) : ℤ :=
  ((spreadAuxS (D1 * w) (S * w) L2 1 (spreadAuxS wn w L1 1 Y) : ℕ) : ℤ) -
    (boxPatS w S D0 D1 (2 ^ (wn - 1)) : ℤ)

theorem jSpreadS_eq : jSpreadS = jSpread := by
  funext D0 D1 S w wn L1 L2 Y
  simp only [jSpreadS, jSpread, spreadAuxS_eq, boxPatS_eq]

end KAM.CertificateSharp.Packed
