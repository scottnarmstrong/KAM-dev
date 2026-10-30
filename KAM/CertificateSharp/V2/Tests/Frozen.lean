/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAFrozen
public import KAM.Certificate.Tests.Toy2

/-!
# Stage 1 in the kernel

* The toy T2 passes the whole v2 certifier with `routeAFrozen`, by `decide +kernel`, and the
  soundness theorem is instantiated at its reference frequency. T2 has `ρ = 9`: the average bites
  are `min r_s 1 = 1`, the case the landed classical constants did not reach.
* The landed sharp engine runs through the same interface (`toyCert2_sharpV2_passes`), and the
  minimum over routes takes either witness.
* The design package R1 (`thresholds.package_R1`): `frozenCore` passes at `e = 1.15·10⁻²¹`, so
  stage 1 certifies `10^(-20.94)` on it, and fails at `e = 1.2·10⁻²¹` with the same witness. The
  test reads the parameters and the box only, so R1 needs no torus data here.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The witness of the toy T2. -/
def toyFrozenWit : FrozenWit where
  Xs := 1 / 10 ^ 30
  kp := 2
  th := 1 / 8
  c := [171 / 1000, 67 / 500]
  cbar := [171 / 1000, 171 / 1000]
  ctail := 111 / 1000
  sB := 111 / 25
  sT := 111 / 25
  sLt := 444 / 25
  sN := 8214 / 625
  sNt := 32856 / 625
  t := 6936467463771 / 2500000000
  J := 2

theorem toyCert2_frozenCore :
    frozenCore 2 toyCert2.params toyCert2.freqBox toyFrozenWit = true := by
  decide +kernel

/-- The whole v2 certifier on T2. -/
theorem toyCert2_v2_passes : checkTorusCertificateV2 routeAFrozen toyCert2 toyFrozenWit = true := by
  decide +kernel

/-- **The toy torus through route A at the frozen data.** -/
theorem toyCert2_v2_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeAFrozen toyCert2_v2_passes toyCert2_freq (by
    have h : ((toyCert2.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

/-- The landed sharp engine through the v2 interface. -/
theorem toyCert2_sharpV2_passes : checkTorusCertificateV2 sharpV2 toyCert2 () = true := by
  decide +kernel

/-- The minimum of the routes, with route A's witness. -/
theorem toyCert2_orElse_passes : checkTorusCertificateV2 (sharpV2.orElse routeAFrozen) toyCert2
    (Sum.inr toyFrozenWit) = true := by
  decide +kernel

/-- `c/s` of the design package R1. -/
def r1Kappa : ℚ := (7 / 4) / (1 + 1 / 10 ^ 6)

/-- The design package R1 (`thresholds.package_R1`). -/
def r1Params (err disp : ℚ) : CertParams where
  tau := 1
  rho := 1 / 70
  rhoInf := 1 / 70000
  M := 1924 / 1000
  σK := 105 / 100 * (1303 / 1000) + 1 / 160
  σB := 105 / 100 * (1833 / 1000) + 1 / 160
  σT := 105 / 100 * (1022 / 1000) / (7 / 4) + 1 / 160
  μ := 1 / 160
  γbar := r1Kappa / 42
  σω := 2
  nuRay := 1 / 10 ^ 6
  γ := r1Kappa / 42
  s := 1 + 1 / 10 ^ 6
  err := err
  E0 := 0
  disp := disp

/-- The box of the reference vector `κ (ν₋ - 1, 1)` of R1. -/
def r1Box : FreqBox :=
  [(-(79 - 2236067977 / 1000000000) / 3118 * r1Kappa, 1 / 10 ^ 12), (r1Kappa, 0)]

/-- The witness of R1. -/
def r1FrozenWit : FrozenWit where
  Xs := 120003 / 10000000000
  kp := 5
  th := 1 / 8
  c := [8173 / 100000, 8157 / 100000, 8149 / 100000, 1629 / 20000, 8143 / 100000]
  cbar := [521 / 6250, 8239 / 100000, 819 / 10000, 1633 / 20000, 8153 / 100000]
  ctail := 4071 / 50000
  sB := 481163 / 250000
  sT := 122647 / 200000
  sLt := 2736301 / 500000
  sN := 658303 / 250000
  sNt := 10532843 / 1000000
  t := 13675373 / 125000
  J := 4

theorem r1_frozen_passes :
    frozenCore 2 (r1Params (115 / 10 ^ 23) (1 / 10 ^ 3)) r1Box r1FrozenWit = true := by
  decide +kernel

theorem r1_frozen_rejects :
    frozenCore 2 (r1Params (12 / 10 ^ 22) (1 / 10 ^ 3)) r1Box r1FrozenWit = false := by
  decide +kernel

end KAM.CertificateSharp.V2

end
