/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Types
public import KAM.EffectiveStability.Tube.Engine.Block

/-!
# The nested Horner of the Taylor coefficients (T2-CONF, N7)

`h_m = Σ_n T_n Π_j gb(n_j, m_j) P_j(n_j - 2 m_j)` (`gb n m = binom(n/2, m)`, `P_j(k) = √B_j^k`),
evaluated as in phase 1 (`scripts/sjsu/rigor/sr4_ball_mirror.py`) by three levels:
* `U n₁ n₂ m₃ = Σ_{n₃} gb(n₃, m₃) T_n P₂(n₃ - 2m₃)` (exact, in the kernel only);
* `V n₁ m₂ m₃ = Σ_{n₂} gb(n₂, m₂) U n₁ n₂ m₃ P₁(n₂ - 2m₂)` (a literal per `(n₁, m₂, m₃)`);
* `h m = Σ_{n₁} gb(n₁, m₁) V n₁ m₂ m₃ P₀(n₁ - 2m₁)` (a literal per `m`).
Mode indices follow the producer (`P₀, P₁, P₂` are the powers of `B₀, B₁, B₂`).

`HData` holds the ledger tables (literals and their claims); `Ut`, `Vt`, `Ht` are the true
functions built from abstract true functions `Tt` of the `T_n` and `Pt` of the powers. The block
checks `vBlock` (one `(n₁, m₃)`: every `U`, then every `V` literal) and `hBlock` (one `m`) are
kernel computations on packed integers only; `vBlock_sound` and `hBlock_sound` give the
certificates of the `V` and `h` literals from those of the `T_n` and the powers.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- `binom(n/2, m) = Π_{i<m} (n/2 - i)/(i + 1)`. -/
def gbQ (n m : ℕ) : ℚ := ((List.range m).map fun i => ((n : ℚ) / 2 - i) / (i + 1)).prod

/-- The ledger tables of the Horner stage. -/
structure HData where
  P : Prm
  CT : ℕ
  CP : ℕ
  M : ℕ
  Nmax : ℕ
  ns : List (ℕ × ℕ × ℕ)
  T : ℕ × ℕ × ℕ → LitD
  Tc : ℕ × ℕ × ℕ → Cl
  Pw : ℕ → ℤ → LitD
  Pc : ℕ → ℤ → Cl
  V : ℕ × ℕ × ℕ → LitD
  Vc : ℕ × ℕ × ℕ → Cl
  H : ℕ × ℕ × ℕ → LitD
  Hc : ℕ × ℕ × ℕ → Cl
  Tdat : ℕ × ℕ × ℕ → List ℚ
  Bdat : ℕ → List ℚ

/-- The parameters of the `U` of index `n₂`. -/
def uPrmOf (uprm : List (ℕ × UPrm)) (n2 : ℕ) : UPrm :=
  ((uprm.lookup n2).getD ⟨1, 0, 0, 0, 0, 0⟩)

namespace HData

variable (D : HData)

/-- The `n₂` of the groups with first index `n₁`, ascending. -/
def n2s (n1 : ℕ) : List ℕ :=
  (List.range (D.Nmax + 1)).filter fun n2 => D.ns.any fun n => n.1 == n1 && n.2.1 == n2

/-- The `n₁` of all groups, ascending. -/
def n1s : List ℕ := (List.range (D.Nmax + 1)).filter fun n1 => D.ns.any fun n => n.1 == n1

/-- The groups of a `U`. -/
def uIdx (n1 n2 m3 : ℕ) : List (ℕ × ℕ × ℕ) :=
  D.ns.filter fun n => n.1 == n1 && n.2.1 == n2 && gbQ n.2.2 m3 != 0 && decide (n.2.2 ≤ D.Nmax)

/-- The `n₂` of a `V`. -/
def vIdx (n1 m2 m3 : ℕ) : List ℕ :=
  (D.n2s n1).filter fun n2 => gbQ n2 m2 != 0 && !(D.uIdx n1 n2 m3).isEmpty

/-- The `n₁` of an `h`. -/
def hIdx (m : ℕ × ℕ × ℕ) : List ℕ :=
  D.n1s.filter fun n1 => gbQ n1 m.1 != 0 && !(D.vIdx n1 m.2.1 m.2.2).isEmpty

/-- The integer multiplier of a term: `ρ q_A q_B / Q` (an integer when the check passes). -/
def cOf (ρ qA qB Q : ℚ) : ℤ := (ρ * qA * qB / Q).num

/-- The terms of a `U`. -/
def uTerms (n1 n2 m3 : ℕ) (Q : ℚ) : List Term :=
  (D.uIdx n1 n2 m3).map fun n =>
    ⟨cOf (gbQ n.2.2 m3) (D.T n).q (D.Pw 2 ((n.2.2 : ℤ) - 2 * m3)).q Q, 0, gbQ n.2.2 m3,
      (D.T n).opd D.P, (D.Pw 2 ((n.2.2 : ℤ) - 2 * m3)).opd D.P, (D.Tc n).e₀, (D.Tc n).e₁,
      (D.Tc n).n, (D.Pc 2 ((n.2.2 : ℤ) - 2 * m3)).e₀, (D.Pc 2 ((n.2.2 : ℤ) - 2 * m3)).e₁,
      (D.Pc 2 ((n.2.2 : ℤ) - 2 * m3)).n, 2 ^ (D.P.b - 1), n⟩

/-- The exact `U` operand. -/
def uOpd (n1 n2 m3 : ℕ) (Q : ℚ) : Opd := combOpd D.CT D.CP false Q (D.uTerms n1 n2 m3 Q)

/-- The check of one `U`. -/
def uOk (n1 n2 m3 : ℕ) (u : UPrm) : Bool :=
  combCheck D.P.w D.P.S D.CT D.CP false u.Q (D.uTerms n1 n2 m3 u.Q) u.E₀ u.E₁ u.BX u.l u.n

/-- The terms of a `V`. -/
def vTerms (n1 m2 m3 : ℕ) (uprm : List (ℕ × UPrm)) (Q : ℚ) : List Term :=
  (D.vIdx n1 m2 m3).map fun n2 =>
    ⟨cOf (gbQ n2 m2) (uPrmOf uprm n2).Q (D.Pw 1 ((n2 : ℤ) - 2 * m2)).q Q, 0, gbQ n2 m2,
      D.uOpd n1 n2 m3 (uPrmOf uprm n2).Q, (D.Pw 1 ((n2 : ℤ) - 2 * m2)).opd D.P,
      (uPrmOf uprm n2).E₀, (uPrmOf uprm n2).E₁, (uPrmOf uprm n2).n,
      (D.Pc 1 ((n2 : ℤ) - 2 * m2)).e₀, (D.Pc 1 ((n2 : ℤ) - 2 * m2)).e₁,
      (D.Pc 1 ((n2 : ℤ) - 2 * m2)).n, 2 ^ (D.P.b - 1), (n1, n2, m3)⟩

/-- The check of one `V` literal. -/
def vOk (n1 m2 m3 : ℕ) (uprm : List (ℕ × UPrm)) (v : OPrm) : Bool :=
  litCheck D.P (D.CT + D.CP) D.CP false v.Q (D.vTerms n1 m2 m3 uprm v.Q) v.E₀ v.E₁ v.BX
    (D.V (n1, m2, m3)) v.aX v.aO v.lD v.F₀ v.F₁ (D.Vc (n1, m2, m3)).e₀ (D.Vc (n1, m2, m3)).e₁
    (D.Vc (n1, m2, m3)).n

/-- **The block of `(n₁, m₃)`**: every `U`, then every `V` literal. -/
def vBlock (n1 m3 : ℕ) (uprm : List (ℕ × UPrm)) (vprm : List (ℕ × OPrm)) : Bool :=
  decide (m3 ≤ D.M) && (D.n2s n1).all (fun n2 => (D.uIdx n1 n2 m3).isEmpty || D.uOk n1 n2 m3 (uPrmOf uprm n2)) &&
    (List.range (D.M + 1 - m3)).all fun m2 =>
      (D.vIdx n1 m2 m3).isEmpty ||
        D.vOk n1 m2 m3 uprm ((vprm.lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)

/-- The terms of an `h`. -/
def hTerms (m : ℕ × ℕ × ℕ) (Q : ℚ) : List Term :=
  (D.hIdx m).map fun n1 =>
    ⟨cOf (gbQ n1 m.1) (D.V (n1, m.2.1, m.2.2)).q (D.Pw 0 ((n1 : ℤ) - 2 * m.1)).q Q, 0, gbQ n1 m.1,
      (D.V (n1, m.2.1, m.2.2)).opd D.P, (D.Pw 0 ((n1 : ℤ) - 2 * m.1)).opd D.P,
      (D.Vc (n1, m.2.1, m.2.2)).e₀, (D.Vc (n1, m.2.1, m.2.2)).e₁, (D.Vc (n1, m.2.1, m.2.2)).n,
      (D.Pc 0 ((n1 : ℤ) - 2 * m.1)).e₀, (D.Pc 0 ((n1 : ℤ) - 2 * m.1)).e₁,
      (D.Pc 0 ((n1 : ℤ) - 2 * m.1)).n, 2 ^ (D.P.b - 1), (n1, m.2.1, m.2.2)⟩

/-- **The block of `m`**: the `h` literal. -/
def hBlock (m : ℕ × ℕ × ℕ) (o : OPrm) : Bool :=
  decide (m.1 + m.2.1 + m.2.2 ≤ D.M) && litCheck D.P D.CP D.CP false o.Q (D.hTerms m o.Q) o.E₀ o.E₁ o.BX (D.H m) o.aX o.aO o.lD o.F₀ o.F₁
    (D.Hc m).e₀ (D.Hc m).e₁ (D.Hc m).n

/-! ### True functions -/

variable (Tt : ℕ × ℕ × ℕ → (Fin 2 → ℝ) → ℝ) (Pt : ℕ → ℤ → (Fin 2 → ℝ) → ℝ)

/-- The true `U`. -/
noncomputable def Ut (n1 n2 m3 : ℕ) (φ : Fin 2 → ℝ) : ℝ :=
  ((D.uIdx n1 n2 m3).map fun n => (gbQ n.2.2 m3 : ℝ) * (Tt n φ * Pt 2 ((n.2.2 : ℤ) - 2 * m3) φ)).sum

/-- The true `V`. -/
noncomputable def Vt (n1 m2 m3 : ℕ) (φ : Fin 2 → ℝ) : ℝ :=
  ((D.vIdx n1 m2 m3).map fun n2 =>
    (gbQ n2 m2 : ℝ) * (D.Ut Tt Pt n1 n2 m3 φ * Pt 1 ((n2 : ℤ) - 2 * m2) φ)).sum

/-- The true `h`. -/
noncomputable def Ht (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) : ℝ :=
  ((D.hIdx m).map fun n1 =>
    (gbQ n1 m.1 : ℝ) * (D.Vt Tt Pt n1 m.2.1 m.2.2 φ * Pt 0 ((n1 : ℤ) - 2 * m.1) φ)).sum

/-! ### Soundness -/

/-- The power certificates on the range used by the Horner stage. -/
def PCerts (Pt : ℕ → ℤ → (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ j < 3, ∀ k : ℤ, -(2 * D.M + 1 : ℤ) ≤ k → k ≤ D.Nmax →
    ((D.Pw j k).opd D.P).Cert D.P.w D.P.S (Pt j k) (D.Pc j k).e₀ (D.Pc j k).e₁ (D.Pc j k).n ∧
      ((D.Pw j k).opd D.P).Mx (2 ^ (D.P.b - 1)) ∧
      symOk ((D.Pw j k).opd D.P).par ((D.Pw j k).opd D.P).l = true ∧
      ((D.Pw j k).opd D.P).l.length = Layout.len ((D.Pw j k).opd D.P).C D.P.S

/-- The input certificates of the `T_n`. -/
def TCerts : Prop :=
  ∀ n ∈ D.ns, ((D.T n).opd D.P).Cert D.P.w D.P.S (Tt n) (D.Tc n).e₀ (D.Tc n).e₁ (D.Tc n).n

theorem mem_uIdx {n1 n2 m3 : ℕ} {n : ℕ × ℕ × ℕ} (h : n ∈ D.uIdx n1 n2 m3) :
    n ∈ D.ns ∧ n.1 = n1 ∧ n.2.1 = n2 ∧ n.2.2 ≤ D.Nmax := by
  simp only [uIdx, List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1.1.1, h.2.1.1.2, h.2.2⟩

/-- **A `U` certificate.** -/
theorem uOk_cert {n1 n2 m3 : ℕ} {u : UPrm} (h : D.uOk n1 n2 m3 u = true) (hm3 : m3 ≤ D.M)
    (hT : D.TCerts Tt) (hP : D.PCerts Pt) :
    (D.uOpd n1 n2 m3 u.Q).Cert D.P.w D.P.S (D.Ut Tt Pt n1 n2 m3) u.E₀ u.E₁ u.n ∧
      (D.uOpd n1 n2 m3 u.Q).Mx u.BX := by
  have := comb_cert h (fun t => Tt t.tag) (fun t => Pt 2 ((t.tag.2.2 : ℤ) - 2 * m3))
    (fun t ht => by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ht
      exact hT n (D.mem_uIdx hn).1)
    (fun t ht => by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ht
      have hb := D.mem_uIdx hn
      exact hP 2 (by norm_num) _ (by push_cast; omega) (by push_cast; omega))
  have hfun : (fun φ => ((D.uTerms n1 n2 m3 u.Q).map fun t =>
      (t.ρ : ℝ) * (Tt t.tag φ * Pt 2 ((t.tag.2.2 : ℤ) - 2 * m3) φ)).sum) = D.Ut Tt Pt n1 n2 m3 := by
    funext φ
    simp only [uTerms, List.map_map, Ut]
    rfl
  rw [hfun] at this
  exact this

/-- **The certificates of the `V` literals of a block.** -/
theorem vBlock_sound {n1 m3 : ℕ} {uprm : List (ℕ × UPrm)} {vprm : List (ℕ × OPrm)}
    (h : D.vBlock n1 m3 uprm vprm = true) (hT : D.TCerts Tt) (hP : D.PCerts Pt) {m2 : ℕ}
    (hm2 : m2 < D.M + 1 - m3) (hv : D.vIdx n1 m2 m3 ≠ []) :
    ((D.V (n1, m2, m3)).opd D.P).Cert D.P.w D.P.S (D.Vt Tt Pt n1 m2 m3) (D.Vc (n1, m2, m3)).e₀
      (D.Vc (n1, m2, m3)).e₁ (D.Vc (n1, m2, m3)).n := by
  simp only [vBlock, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.isEmpty_iff, List.mem_range] at h
  obtain ⟨⟨hm3, hU⟩, hV⟩ := h
  have hv' := (hV m2 hm2).resolve_left hv
  have hc := lit_cert hv' (fun t => D.Ut Tt Pt n1 t.tag.2.1 m3)
    (fun t => Pt 1 ((t.tag.2.1 : ℤ) - 2 * m2))
    (fun t ht => by
      obtain ⟨n2, hn2, rfl⟩ := List.mem_map.mp ht
      simp only [vIdx, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
        List.isEmpty_eq_false_iff] at hn2
      have hu := (hU n2 hn2.1).resolve_left (by simpa [List.isEmpty_iff] using hn2.2.2)
      exact (D.uOk_cert Tt Pt hu hm3 hT hP).1)
    (fun t ht => by
      obtain ⟨n2, hn2, rfl⟩ := List.mem_map.mp ht
      have hn2' : n2 ≤ D.Nmax := by
        simp only [vIdx, n2s, List.mem_filter, List.mem_range] at hn2
        omega
      exact hP 1 (by norm_num) _ (by push_cast; omega) (by push_cast; omega))
  have hfun : (fun φ => ((D.vTerms n1 m2 m3 uprm ((vprm.lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩).Q).map
      fun t => (t.ρ : ℝ) * (D.Ut Tt Pt n1 t.tag.2.1 m3 φ * Pt 1 ((t.tag.2.1 : ℤ) - 2 * m2) φ)).sum) =
      D.Vt Tt Pt n1 m2 m3 := by
    funext φ
    simp only [vTerms, List.map_map, Vt]
    rfl
  rw [hfun] at hc
  exact hc

/-- The certificates of the `V` literals that the `h` blocks consume. -/
def VCerts : Prop :=
  ∀ n1 m2 m3 : ℕ, n1 ∈ D.n1s → m2 + m3 ≤ D.M → D.vIdx n1 m2 m3 ≠ [] →
    ((D.V (n1, m2, m3)).opd D.P).Cert D.P.w D.P.S (D.Vt Tt Pt n1 m2 m3) (D.Vc (n1, m2, m3)).e₀
      (D.Vc (n1, m2, m3)).e₁ (D.Vc (n1, m2, m3)).n

/-- **The certificate of an `h` literal.** -/
theorem hBlock_sound {m : ℕ × ℕ × ℕ} {o : OPrm} (h : D.hBlock m o = true) (hV : D.VCerts Tt Pt)
    (hP : D.PCerts Pt) :
    ((D.H m).opd D.P).Cert D.P.w D.P.S (D.Ht Tt Pt m) (D.Hc m).e₀ (D.Hc m).e₁ (D.Hc m).n := by
  simp only [hBlock, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hm, hl⟩ := h
  have hc := lit_cert hl (fun t => D.Vt Tt Pt t.tag.1 m.2.1 m.2.2)
    (fun t => Pt 0 ((t.tag.1 : ℤ) - 2 * m.1))
    (fun t ht => by
      obtain ⟨n1, hn1, rfl⟩ := List.mem_map.mp ht
      simp only [hIdx, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
        List.isEmpty_eq_false_iff] at hn1
      exact hV n1 m.2.1 m.2.2 hn1.1 (by omega) (by simpa [List.isEmpty_iff] using hn1.2.2))
    (fun t ht => by
      obtain ⟨n1, hn1, rfl⟩ := List.mem_map.mp ht
      have hn1' : n1 ≤ D.Nmax := by
        simp only [hIdx, n1s, List.mem_filter, List.mem_range] at hn1
        omega
      exact hP 0 (by norm_num) _ (by push_cast; omega) (by push_cast; omega))
  have hfun : (fun φ => ((D.hTerms m o.Q).map fun t =>
      (t.ρ : ℝ) * (D.Vt Tt Pt t.tag.1 m.2.1 m.2.2 φ * Pt 0 ((t.tag.1 : ℤ) - 2 * m.1) φ)).sum) =
      D.Ht Tt Pt m := by
    funext φ
    simp only [hTerms, List.map_map, Ht]
    rfl
  rw [hfun] at hc
  exact hc

/-- **All `V` certificates** from the checks of all blocks. -/
theorem VCerts_of {up : ℕ → ℕ → List (ℕ × UPrm)} {vp : ℕ → ℕ → List (ℕ × OPrm)}
    (h : (D.n1s.all fun n1 => (List.range (D.M + 1)).all fun m3 =>
      D.vBlock n1 m3 (up n1 m3) (vp n1 m3)) = true) (hT : D.TCerts Tt) (hP : D.PCerts Pt) :
    D.VCerts Tt Pt := by
  intro n1 m2 m3 hn1 hm hv
  simp only [List.all_eq_true, List.mem_range] at h
  exact D.vBlock_sound Tt Pt (h n1 hn1 m3 (by omega)) hT hP (by omega) hv

/-- **An `h` certificate** from the check of its block. -/
theorem HCert_of {hp : ℕ × ℕ × ℕ → OPrm} {ms : List (ℕ × ℕ × ℕ)}
    (h : (ms.all fun m => (D.hIdx m).isEmpty || D.hBlock m (hp m)) = true) (hV : D.VCerts Tt Pt)
    (hP : D.PCerts Pt) {m : ℕ × ℕ × ℕ} (hm : m ∈ ms) (hne : D.hIdx m ≠ []) :
    ((D.H m).opd D.P).Cert D.P.w D.P.S (D.Ht Tt Pt m) (D.Hc m).e₀ (D.Hc m).e₁ (D.Hc m).n := by
  simp only [List.all_eq_true, Bool.or_eq_true, List.isEmpty_iff] at h
  exact D.hBlock_sound Tt Pt ((h m hm).resolve_left hne) hV hP

end HData

end KAM.EffectiveStability.Tube

end
