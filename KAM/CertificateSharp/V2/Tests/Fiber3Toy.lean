/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteAG
public import KAM.CertificateSharp.Freq.CubicNorm
public import KAM.Certificate.Tests.Toy3

/-!
# Three-frequency sharp sites in the kernel, on the toy T3

T3 (`toyCert3`): `n = 3`, `τ = 2`, `H = I₂ + I₀²/2 + I₁²/2`, the frequency
`cubicFreq = (∛2/2, ∛4/2, 1/2)` with every coordinate used, `ρ = 9`. The schedule of route A has
`kp = 2`: bites `δ₀ = 1`, `δ₁ = 1/2` and `b₀ = b₁ = 1`.

* **The premise.** `cubicDioOk` (`Freq/CubicNorm.lean`) proves `cubicFreq` `(0.198, 2)`-Diophantine
  (`cubicFreq_isDiophantine_norm`), against `1/12` for the landed special argument; the certificate's
  `γ = 1/12` follows by monotonicity.
* **The sites.** `fiberSiteOk` certifies `c(1) = 4.909·10⁻⁴` (12 fibres) and `c(1/2) = 2.853·10⁻³`
  (24 fibres), against the classical `c♮(3, 2, 1) = 0.0783` and `c♮(3, 2, 1/2) = 0.0629`: factors
  `159` and `22`.
* **The torus.** `toyCert3_refinedG_passes` runs the whole v2 certifier with `routeARefinedG` and
  these sites by `decide +kernel`; `toyCert3_refinedG_torus` is the soundness theorem at `cubicFreq`.
* **The threshold.** At the same certificate data with the invariance error raised to `5·10⁻¹²`
  (`X⋆ = 1.2·10⁻⁷`), the refined core passes with the fibered sites and fails with the classical
  ones; the classical sites pass at `5·10⁻¹⁴` (`toy3_threshold_*`). The mirror
  (`scripts/certifier/fiber3.py`, `v2_q.py`) puts the two thresholds at `6.1·10⁻¹²` and `5.6·10⁻¹⁴`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Fiber KAM.CertificateSharp.Cubic

/-! ### The Diophantine premise from the cubic norm -/

/-- `cubicFreq = ½ A (1, θ, θ²)`. -/
def t3A : Fin 3 → Fin 3 → ℤ := ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]

/-- The centre of the enclosure of `∛2`. -/
def t3θc : ℚ := (toyT3RootLo + toyT3RootHi) / 2

/-- The radius of the enclosure of `∛2`. -/
def t3θr : ℚ := (toyT3RootHi - toyT3RootLo) / 2

theorem t3_cubicDioOk : cubicDioOk (-2) 0 0 t3θc t3θr t3A 2 (99 / 500) = true := by
  decide +kernel

theorem cbrtTwo_cube_eq : cbrtTwo ^ 3 = 2 := by
  unfold cbrtTwo
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem cubicVec_t3A : cubicVec t3A 2 cbrtTwo = cubicFreq := by
  funext i
  fin_cases i <;> simp [cubicVec, t3A, cubicFreq]

/-- **The premise of T3 from the general cubic theorem**: `γ = 0.198`. -/
theorem cubicFreq_isDiophantine_norm : IsDiophantine (99 / 500) 2 cubicFreq := by
  have hx := rpow_mem_of_checkRootEnclosure (by norm_num)
    (show checkRootEnclosure 3 2 toyT3RootLo toyT3RootHi = true by decide +kernel)
  have hc : (((2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((3 : ℕ) : ℝ))) = cbrtTwo := by simp [cbrtTwo]
  rw [hc] at hx
  have hθ : |cbrtTwo - (t3θc : ℝ)| ≤ (t3θr : ℝ) := by
    rw [abs_le]
    simp only [t3θc, t3θr]
    push_cast
    constructor <;> linarith [hx.1, hx.2]
  have h := isDiophantine_of_cubicDioOk t3_cubicDioOk (θ := cbrtTwo)
    (by push_cast; rw [cbrtTwo_cube_eq]; ring) hθ
  rw [cubicVec_t3A] at h
  have e : ((99 / 500 : ℚ) : ℝ) = 99 / 500 := by norm_num
  rwa [e] at h

/-- The certificate's `γ = 1/12`, by monotonicity. -/
theorem cubicFreq_isDiophantine_twelfth : IsDiophantine (1 / 12) 2 cubicFreq :=
  isDiophantine_mono cubicFreq_isDiophantine_norm (by norm_num)

/-! ### The sites -/

/-- The fibered site at the bite `1`. -/
def t3Fib1 : FibWit :=
  { N := 2, l := 3, J := 45, P := 64, e := 64741242463817,
    D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 },
    B := 214029 / 5000000000 }

/-- The fibered site at the bite `1/2`. -/
def t3Fib2 : FibWit :=
  { N := 3, l := 3, J := 26, P := 64, e := 34558141335960960,
    D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 },
    B := 231331 / 10000000 }

theorem t3Fib1_ok : fiberSiteOk 3 2 toyT3Box (1 / 12) 1 (4909 / 10000000) t3Fib1 = true := by
  decide +kernel

theorem t3Fib2_ok : fiberSiteOk 3 2 toyT3Box (1 / 12) (1 / 2) (2853 / 1000000) t3Fib2 = true := by
  decide +kernel

/-- The fibered site rejects a constant below its bound. -/
theorem t3Fib1_rejects : fiberSiteOk 3 2 toyT3Box (1 / 12) 1 (44181 / 100000000) t3Fib1 = false := by
  decide +kernel

/-! ### The refined witness -/

/-- The claimed bounds on `H` and the frame of T3 (the disc pass and the majorants of C4). -/
def t3RefClaim : RefClaim :=
  { dh := 4, dx := 101 / 100, d2x := 1 / 100, d2h := 201 / 100
    bL := 101 / 100, bN := 101 / 100, bNt := 101 / 100, bT := 101 / 100 }

/-- The schedule data of T3 at `X⋆` with the constants `c`, `cbar`. -/
def t3Core (Xs : ℚ) (c cbar : List ℚ) : FrozenWit where
  Xs := Xs
  kp := 2
  th := 1 / 8
  c := c
  cbar := cbar
  ctail := 5351168 / 100000000
  sB := 161 / 20
  sT := 161 / 20
  sLt := 11 / 10
  sN := 11 / 10
  sNt := 11 / 10
  t := 11 / 10
  J := 2

/-- The witness with fibered sites. -/
def t3WitG (Xs : ℚ) : RefinedWitG where
  core := t3Core Xs [4909 / 10000000, 2853 / 1000000] [4909 / 10000000, 4909 / 10000000]
  R := t3RefClaim
  κ := 1 / 2
  sites := [(.fiber t3Fib1, .fiber t3Fib1), (.fiber t3Fib2, .fiber t3Fib1)]

/-- The witness with classical sites. -/
def t3WitClassical (Xs : ℚ) : RefinedWitG where
  core := t3Core Xs [7829898 / 100000000, 6286952 / 100000000]
    [7829898 / 100000000, 7829898 / 100000000]
  R := t3RefClaim
  κ := 1 / 2
  sites := []

theorem toyCert3_hamClaimG : checkHamClaim toyCert3 t3RefClaim = true := by decide +kernel

theorem toyCert3_refinedCoreG :
    refinedCoreG 3 toyCert3.params toyCert3.freqBox (t3WitG (1 / 10 ^ 30)) = true := by
  decide +kernel

/-- **The whole v2 certifier on T3, with three-frequency sites.** -/
theorem toyCert3_refinedG_passes :
    checkTorusCertificateV2 routeARefinedG toyCert3 (t3WitG (1 / 10 ^ 30)) = true := by
  decide +kernel

/-- **The toy 3-torus through route A with three-frequency sites.** -/
theorem toyCert3_refinedG_torus : CertifiedTorus toyCert3 cubicFreq :=
  checkTorusCertificateV2_sound routeARefinedG toyCert3_refinedG_passes toyCert3_freq (by
    have h : ((toyCert3.params.γ : ℚ) : ℝ) = 1 / 12 := by
      rw [show toyCert3.params.γ = 1 / 12 by decide +kernel]; norm_num
    have ht : ((toyCert3.params.tau : ℕ) : ℝ) = 2 := by
      rw [show toyCert3.params.tau = 2 by decide +kernel]; norm_num
    rw [h, ht]
    exact cubicFreq_isDiophantine_twelfth)

/-! ### The threshold -/

/-- The parameters of T3 with the invariance error `err` and the displacement `disp`. -/
def t3ParamsAt (err disp : ℚ) : CertParams := { toyCert3.params with err := err, disp := disp }

theorem toy3_threshold_fibered :
    refinedCoreG 3 (t3ParamsAt (5 / 10 ^ 12) (1 / 10 ^ 9)) toyCert3.freqBox
      (t3WitG (12 / 10 ^ 8)) = true := by
  decide +kernel

theorem toy3_threshold_classical_fails :
    refinedCoreG 3 (t3ParamsAt (5 / 10 ^ 12) (1 / 10 ^ 9)) toyCert3.freqBox
      (t3WitClassical (12 / 10 ^ 8)) = false := by
  decide +kernel

theorem toy3_threshold_classical :
    refinedCoreG 3 (t3ParamsAt (5 / 10 ^ 14) (1 / 10 ^ 9)) toyCert3.freqBox
      (t3WitClassical (11 / 10 ^ 10)) = true := by
  decide +kernel

end KAM.CertificateSharp.V2

end
