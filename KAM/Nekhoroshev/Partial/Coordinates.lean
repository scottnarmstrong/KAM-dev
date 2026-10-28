/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow

/-!
# Coordinates of the partial setting (`bpN:p11:orbit`, Part 11, package N11-A)

The linear change of variables `theta` from a planetary phase point `(q, p)` of `n + k`
degrees of freedom to the extended coordinates (angles `fast q / 2π`, then fast actions, slow
positions and slow momenta), its inverse `thetaInv`, the converted Hamiltonian and the
theorem `orbit`: `z` solves the Hamiltonian equation iff `theta ∘ z` solves the weighted
one with weight `c = 2π`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

variable {n k : ℕ}

def theta (z : KAM.Planetary.Phase (n+k)) : ER n k :=
  (fun i => KAM.Planetary.fast (b := k) z.1 i / (2*Real.pi),
   Fin.append (KAM.Planetary.fast (b := k) z.2)
     (Fin.append (KAM.Planetary.slow (a := n) z.1) (KAM.Planetary.slow (a := n) z.2)))
def thetaInv (z : ER n k) : KAM.Planetary.Phase (n+k) :=
  (Fin.append (fun i => 2*Real.pi*z.1 i) (slowPair z).1,
   Fin.append (fastAction z) (slowPair z).2)
def converted (H : KAM.Planetary.Phase (n+k) → ℝ) (z : ER n k) : ℝ :=
  H (thetaInv z) / (2*Real.pi)

section eval

variable (z : KAM.Planetary.Phase (n+k)) (w : ER n k)

theorem theta_fst (i : Fin n) : (theta z).1 i = z.1 (Fin.castAdd k i) / (2*Real.pi) := rfl

theorem theta_fast (i : Fin n) : (theta z).2 (Fin.castAdd (k+k) i) = z.2 (Fin.castAdd k i) := by
  simp only [theta, Fin.append_left]; rfl

theorem theta_slowq (i : Fin k) :
    (theta z).2 (Fin.natAdd n (Fin.castAdd k i)) = z.1 (Fin.natAdd n i) := by
  simp only [theta, Fin.append_right, Fin.append_left]; rfl

theorem theta_slowp (i : Fin k) :
    (theta z).2 (Fin.natAdd n (Fin.natAdd k i)) = z.2 (Fin.natAdd n i) := by
  simp only [theta, Fin.append_right]; rfl

theorem thetaInv_q_fast (i : Fin n) :
    (thetaInv w).1 (Fin.castAdd k i) = 2*Real.pi*w.1 i := by
  simp only [thetaInv, Fin.append_left]

theorem thetaInv_q_slow (i : Fin k) :
    (thetaInv w).1 (Fin.natAdd n i) = w.2 (Fin.natAdd n (Fin.castAdd k i)) := by
  simp only [thetaInv, Fin.append_right]; rfl

theorem thetaInv_p_fast (i : Fin n) :
    (thetaInv w).2 (Fin.castAdd k i) = w.2 (Fin.castAdd (k+k) i) := by
  simp only [thetaInv, Fin.append_left]; rfl

theorem thetaInv_p_slow (i : Fin k) :
    (thetaInv w).2 (Fin.natAdd n i) = w.2 (Fin.natAdd n (Fin.natAdd k i)) := by
  simp only [thetaInv, Fin.append_right]; rfl

end eval

theorem thetaInv_theta (z : KAM.Planetary.Phase (n+k)) :
    thetaInv (n := n) (k := k) (theta z) = z := by
  have h2 : (2*Real.pi) ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [thetaInv_q_fast, theta_fst]; field_simp
    · rw [thetaInv_q_slow, theta_slowq]
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [thetaInv_p_fast, theta_fast]
    · rw [thetaInv_p_slow, theta_slowp]

/-- Case split of the second extended block into fast / slow-position / slow-momentum. -/
theorem ext_cases {P : Fin (n + (k + k)) → Prop} (h1 : ∀ i : Fin n, P (Fin.castAdd (k+k) i))
    (h2 : ∀ i : Fin k, P (Fin.natAdd n (Fin.castAdd k i)))
    (h3 : ∀ i : Fin k, P (Fin.natAdd n (Fin.natAdd k i))) (j : Fin (n + (k + k))) : P j := by
  refine Fin.addCases h1 (fun i => ?_) j
  exact Fin.addCases h2 h3 i

theorem theta_thetaInv (z : ER n k) : theta (thetaInv z) = z := by
  have h2 : (2*Real.pi) ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · funext i
    rw [theta_fst, thetaInv_q_fast]; field_simp
  · funext j
    refine ext_cases (P := fun j => _ = _) (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · rw [theta_fast, thetaInv_p_fast]
    · rw [theta_slowq, thetaInv_q_slow]
    · rw [theta_slowp, thetaInv_p_slow]

/-- `theta` as a continuous linear map. -/
def thetaCLM : KAM.Planetary.Phase (n+k) →L[ℝ] ER n k :=
  LinearMap.toContinuousLinearMap
    { toFun := theta
      map_add' := fun x y => by
        refine Prod.ext ?_ ?_
        · funext i
          simp only [theta_fst, Prod.fst_add, Pi.add_apply, add_div]
        · funext j
          refine ext_cases (P := fun j => _ = _) (fun i => ?_) (fun i => ?_) (fun i => ?_) j <;>
            simp only [theta_fast, theta_slowq, theta_slowp, Prod.snd_add, Pi.add_apply]
            <;> rfl
      map_smul' := fun c x => by
        refine Prod.ext ?_ ?_
        · funext i
          simp only [theta_fst, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
            mul_div_assoc]
        · funext j
          refine ext_cases (P := fun j => _ = _) (fun i => ?_) (fun i => ?_) (fun i => ?_) j <;>
            simp only [theta_fast, theta_slowq, theta_slowp, Prod.smul_snd, Pi.smul_apply,
              RingHom.id_apply] <;> rfl }

/-- `thetaInv` as a continuous linear map. -/
def thetaInvCLM : ER n k →L[ℝ] KAM.Planetary.Phase (n+k) :=
  LinearMap.toContinuousLinearMap
    { toFun := thetaInv
      map_add' := fun x y => by
        refine Prod.ext ?_ ?_
        · funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simp only [thetaInv_q_fast, Prod.fst_add, Pi.add_apply, mul_add]
          · simp only [thetaInv_q_slow, Prod.fst_add, Pi.add_apply, Prod.snd_add]
        · funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simp only [thetaInv_p_fast, Prod.snd_add, Pi.add_apply]
          · simp only [thetaInv_p_slow, Prod.snd_add, Pi.add_apply]
      map_smul' := fun c x => by
        refine Prod.ext ?_ ?_
        · funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simp only [thetaInv_q_fast, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
              RingHom.id_apply]; ring
          · simp only [thetaInv_q_slow, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]; rfl
        · funext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · simp only [thetaInv_p_fast, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
          · simp only [thetaInv_p_slow, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply] }

theorem thetaCLM_apply (z : KAM.Planetary.Phase (n+k)) : thetaCLM z = theta z := rfl

theorem thetaInvCLM_apply (z : ER n k) : thetaInvCLM z = thetaInv z := rfl

section basis

variable (i : Fin n) (i' : Fin k)


theorem thetaInv_single_fast :
    thetaInv ((0 : Fin n → ℝ), (Pi.single (Fin.castAdd (k+k) i) 1 : Fin (n + (k + k)) → ℝ)) =
      ((0 : Fin (n+k) → ℝ), (Pi.single (Fin.castAdd k i) 1 : Fin (n + k) → ℝ)) := by
  have hi := i.2
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_q_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_q_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_p_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_p_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))

theorem thetaInv_single_angle :
    thetaInv ((Pi.single i 1 : Fin n → ℝ), (0 : Fin (n + (k + k)) → ℝ)) =
      ((Pi.single (Fin.castAdd k i) (2*Real.pi) : Fin (n + k) → ℝ), (0 : Fin (n + k) → ℝ)) := by
  have hi := i.2
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_q_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_q_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_p_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_p_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))

theorem thetaInv_single_slowp :
    thetaInv ((0 : Fin n → ℝ),
      (Pi.single (Fin.natAdd n (Fin.natAdd k i')) 1 : Fin (n + (k + k)) → ℝ)) =
      ((0 : Fin (n+k) → ℝ), (Pi.single (Fin.natAdd n i') 1 : Fin (n + k) → ℝ)) := by
  have hi' := i'.2
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_q_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_q_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_p_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_p_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))

theorem thetaInv_single_slowq :
    thetaInv ((0 : Fin n → ℝ),
      (Pi.single (Fin.natAdd n (Fin.castAdd k i')) 1 : Fin (n + (k + k)) → ℝ)) =
      ((Pi.single (Fin.natAdd n i') 1 : Fin (n + k) → ℝ), (0 : Fin (n + k) → ℝ)) := by
  have hi' := i'.2
  refine Prod.ext ?_ ?_
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_q_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_q_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
  · funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · rw [thetaInv_p_fast]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))
    · rw [thetaInv_p_slow]; simp [Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;>
      (have := a.2; first | rfl | omega | (exfalso; omega))

end basis

theorem fderiv_converted {H : KAM.Planetary.Phase (n+k) → ℝ} {z : KAM.Planetary.Phase (n+k)}
    (hh : DifferentiableAt ℝ H z) (v : ER n k) :
    fderiv ℝ (converted H) (theta z) v = (2*Real.pi)⁻¹ * fderiv ℝ H z (thetaInv v) := by
  have hH : HasFDerivAt H (fderiv ℝ H z) (thetaInvCLM (theta z)) := by
    rw [thetaInvCLM_apply, thetaInv_theta]; exact hh.hasFDerivAt
  have h0 : HasFDerivAt (fun y => H (thetaInvCLM y)) ((fderiv ℝ H z).comp thetaInvCLM) (theta z) :=
    hH.comp (theta z) thetaInvCLM.hasFDerivAt
  have h1 := h0.const_mul (2*Real.pi)⁻¹
  have h2 : converted H = fun y => (2*Real.pi)⁻¹ * H (thetaInvCLM y) := by
    funext y; simp only [converted, thetaInvCLM_apply]; ring
  rw [h2, h1.fderiv]
  simp [thetaInvCLM_apply]

theorem realWfield_converted {H : KAM.Planetary.Phase (n+k) → ℝ} {z : KAM.Planetary.Phase (n+k)}
    (hh : DifferentiableAt ℝ H z) :
    realWfield (2*Real.pi) (converted H) (theta z) = theta (KAM.hamiltonianVectorField H z) := by
  have h2 : (2*Real.pi) ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · funext i
    rw [theta_fst]
    simp only [realWfield, fderiv_converted hh, thetaInv_single_fast, KAM.hamiltonianVectorField]
    field_simp
  · funext j
    refine ext_cases (P := fun j => _ = _) (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · rw [theta_fast]
      simp only [realWfield, Fin.append_left, fderiv_converted hh, thetaInv_single_angle,
        KAM.hamiltonianVectorField]
      have e : ((Pi.single (Fin.castAdd k i) (2*Real.pi) : Fin (n + k) → ℝ), (0 : Fin (n+k) → ℝ)) =
          (2*Real.pi) •
            ((Pi.single (Fin.castAdd k i) 1 : Fin (n + k) → ℝ), (0 : Fin (n+k) → ℝ)) := by
        ext <;> simp [Pi.single_apply]
      rw [e, map_smul, smul_eq_mul]; field_simp
    · rw [theta_slowq]
      simp only [realWfield, Fin.append_right, Fin.append_left, fderiv_converted hh,
        thetaInv_single_slowp, KAM.hamiltonianVectorField]
      field_simp
    · rw [theta_slowp]
      simp only [realWfield, Fin.append_right, fderiv_converted hh,
        thetaInv_single_slowq, KAM.hamiltonianVectorField]
      field_simp

theorem orbit (H : KAM.Planetary.Phase (n+k) → ℝ)
    (z : ℝ → KAM.Planetary.Phase (n+k)) (t : ℝ) (hh : DifferentiableAt ℝ H (z t)) :
    HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t ↔
    HasDerivAt (theta ∘ z) (realWfield (2*Real.pi) (converted H) (theta (z t))) t := by
  rw [realWfield_converted hh]
  refine ⟨fun h => thetaCLM.hasFDerivAt.comp_hasDerivAt t h, fun h => ?_⟩
  have h' := thetaInvCLM.hasFDerivAt.comp_hasDerivAt t h
  have e1 : (thetaInvCLM ∘ theta ∘ z) = z := by
    funext s; simp [thetaInvCLM_apply, thetaInv_theta]
  have e2 : thetaInvCLM (theta (KAM.hamiltonianVectorField H (z t))) =
      KAM.hamiltonianVectorField H (z t) := by
    rw [thetaInvCLM_apply, thetaInv_theta]
  rw [e2] at h'
  rwa [e1] at h'

end KAM.Nekhoroshev

end
