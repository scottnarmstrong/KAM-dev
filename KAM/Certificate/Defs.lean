/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Torsion.Models
public import KAM.Certificate.Torsion.Average
public import KAM.Certificate.Gram
public import KAM.Certificate.Expr.Ball
public import KAM.Certificate.Expr.Compose
public import KAM.Certificate.NormBridge
public import KAM.Certificate.Constants
public import KAM.Certificate.Freq
public import KAM.Iso.Apost.Defs
public import KAM.Frozen.Defs.GramMatrix
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Iso.Defs.ExtendedTorsionAverage
public import KAM.Frozen.Iso.Defs.EnergyAverage

/-!
# The torus certificate and its checker

The certificate `TorusCertificate n α` (pure data: parameters, the Hamiltonian expression and its
domain, the frequency box, the embedding, witnesses, the Gram and torsion witnesses, two model
configurations and the `π` enclosure) and the black-box checker `checkTorusCertificate`, the
conjunction of eight `Bool` sub-checks (SO design §1, §4, Appendix A §G):

* `checkStatic`: shapes, positivity and orderings of the parameters, both weights, the `π`
  enclosure, and the frequency box: its lower bound `L = max_i (|c_i| - r_i)` of `‖ω*‖` is
  positive (so `ω* ≠ 0`) and pays both ray margins `ν ≤ (s - 1) L`, `ν ≤ (σω - s) L`;
* `checkHamBounds`: `Slp.balls` of the jet program of `H` on `D` (ℚ balls; success certifies every
  denominator) and the five bounds by sums of slot magnitudes `|re| + |im| + r` along the phase
  basis (the `NormBridge` forms);
* `checkEmbedding`: `ρ + ι_i + μ ≤ ρ_H` with `ι_i = min (sup |U_i|, ρ Σ_j sup |∂_j U_i|)`,
  `sup |A_i - c_i| + μ ≤ r_i`, and the row sums of the `DK` models `≤ σK - μ`;
* `checkInvariance`: the `2n` coordinates of `X_H ∘ K - DK (s ω)` (jet `d1` composed with `K` at
  full precision, the frequency as a ball from the box) have sup bound `≤ e`;
* `checkEnergy`: the zero mode of `H ∘ K - E₀` plus its radii is `≤ e`;
* `checkGram`: `gramCheck` with bound `σB - μ`;
* `checkTorsion`: `torsionModels` (with the Gram check's `(δ, β)`), then `torsionAvgCheck n`
  with bound `σT - μ`;
* `checkSmallness`: `isoC1Q e < γ⁴ ρ^{4τ}` and `isoC2Q e ≤ disp γ² ρ^{2τ}` (exact rationals).

Precision split: the Gram and torsion stages use `cfgLow`; invariance and energy use `cfgFull`.
Product keys of this module: `[5, a, l]` (invariance, row `a`, frequency coordinate `l`); the
composition, Gram and torsion keys are those of the landed engine (`[0, slot]`, `[3, …]`,
`[4, …]`). Ball arithmetic and the strip weights use the Taylor order `expOrder` and the halving
count `expHalvings` of the certificate.

`G1Hyps` lists every hypothesis of `g1_explicit`/`IG1Body` at the denoted data, and
`CertifiedTorus` is the black box's conclusion. The soundness contracts are in `Sound/*`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus CertArith

/-! ### The certificate -/

/-- Parameters of `g1_explicit` (exact rationals; `τ ∈ ℕ`). `nuRay` is the theorem's `ν`. -/
structure CertParams where
  tau : ℕ
  rho : ℚ
  rhoInf : ℚ
  M : ℚ
  σK : ℚ
  σB : ℚ
  σT : ℚ
  μ : ℚ
  γbar : ℚ
  σω : ℚ
  nuRay : ℚ
  γ : ℚ
  s : ℚ
  err : ℚ
  E0 : ℚ
  /-- claimed explicit displacement bound, checked `≥ isoC2Q e / (γ² ρ^{2τ})` -/
  disp : ℚ

/-- The certificate: problem data, numerical witnesses and controls (data only; no proofs, no
real numbers). -/
structure TorusCertificate (n : ℕ) (α : Type) where
  params : CertParams
  ham : HamExpr n
  /-- `D = T_{ρ_H} × polydisc(centre, radius)` -/
  weightH : CertWeight
  centre : List ℚ
  radius : List ℚ
  /-- rational box of the reference vector `ω*` -/
  freqBox : FreqBox
  emb : CertEmbedding α
  /-- weight of the strip `T_ρ` (its `rho` must equal `params.rho`) -/
  weight : CertWeight
  wit : Witnesses α
  gramInv : List (List (CertPoly α))
  torsInv : List (List (CC α))
  cfgFull : ModelConfig α
  cfgLow : ModelConfig α
  piEnc : PiEnclosure α
  expHalvings : ℕ
  expOrder : ℕ

section Denotation

variable {n : ℕ} {α : Type} [CertArith α]

def TorusCertificate.D (c : TorusCertificate n α) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  certDomain n c.weightH.rho c.centre c.radius

def TorusCertificate.H (c : TorusCertificate n α) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := c.ham.eval

def TorusCertificate.K (c : TorusCertificate n α) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := c.emb.eval n

end Denotation

/-! ### Helpers of the sub-checks -/

section Helpers

variable {α : Type} [CertArith α]

/-- A lower bound of `‖ω‖` (max norm) for every `ω` in the box: `max_i (|c_i| - r_i)`, and `0`
if no coordinate excludes `0`. -/
def freqNormLo (box : FreqBox) : ℚ :=
  box.foldr (fun b acc => max (|b.1| - b.2) acc) 0

/-- An upper bound of `|z|` on a ℚ ball `(c, r)`: `|re c| + |im c| + r`. -/
def ballMagQ (b : CC ℚ × ℚ) : ℚ := |b.1.re| + |b.1.im| + b.2

/-- The magnitude bound of slot `i` from the slot balls (`ballZero` off the list). -/
def slotMagQ (bs : List (CC ℚ × ℚ)) (i : ℕ) : ℚ := ballMagQ (bs.getD i ballZero)

/-- `Σ_{a < k} f a` in `ℚ`. -/
def sumRangeQ (k : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range k).map f).sum

/-- The five bounds on `D` from the slot balls `bs` of the jet `J` (`m := 2n` phase indices,
natural numbering `inl j ↦ j`, `inr j ↦ n + j`): `Σ_a |∂_a H| ≤ M` (`DH`), `|∂_a H| ≤ M` for
every `a` (`X_H`, whose coordinates are `± ∂_{swap a} H`), every row sum `Σ_b |∂_a ∂_b H| ≤ M`
(`DX_H`), every row sum `Σ_b Σ_c |∂_a ∂_b ∂_c H| ≤ M` (`D²X_H`), and `Σ_a Σ_b |∂_a ∂_b H| ≤ M`
(`D²H`). Rows run over all `a`, so the swap of the `X_H` bridges is covered. -/
def hamBoundsOk (m : ℕ) (J : HamJet) (bs : List (CC ℚ × ℚ)) (M : ℚ) : Bool :=
  decide (sumRangeQ m (fun a => slotMagQ bs (J.d1.getD a 0)) ≤ M) &&
    (List.range m).all (fun a => decide (slotMagQ bs (J.d1.getD a 0) ≤ M)) &&
    (List.range m).all (fun a =>
      decide (sumRangeQ m (fun b => slotMagQ bs ((J.d2.getD a []).getD b 0)) ≤ M)) &&
    (List.range m).all (fun a => decide (sumRangeQ m (fun b => sumRangeQ m (fun e =>
      slotMagQ bs (((J.d3.getD a []).getD b []).getD e 0))) ≤ M)) &&
    decide (sumRangeQ m (fun a => sumRangeQ m (fun b =>
      slotMagQ bs ((J.d2.getD a []).getD b 0))) ≤ M)

/-- The model of the angle displacement `(2π)^{dU_i} U_i` (the zero model if missing). -/
def angleModel (n : ℕ) (K : CertEmbedding α) (i : ℕ) : CertModel α :=
  realCompModel n (K.angleDeg.getD i 0) K.angle[i]?

/-- The model of `(2π)^{dA_i} A_i - c_i`. -/
def actionShiftModel (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α)
    (ci : ℚ) (i : ℕ) : CertModel α :=
  CertModel.addMixed W pe (realCompModel n (K.actionDeg.getD i 0) K.action[i]?)
    (constModel n (-ci) 0 0)

/-- `ι_i ≤ room`: either `sup |U_i| ≤ room` or `ρ Σ_j sup |∂_j U_i| ≤ room` (mean value
inequality from the real point, where `Im U_i = 0`). -/
def angleImOk (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α) (ρ room : ℚ)
    (i : ℕ) : Bool :=
  ble ((angleModel n K i).supBound W) (ofRatDown room) ||
    ble (upMul (ofRatUp ρ) (sumUp (fun j : Fin n =>
        (compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j.val).supBound W)
      (List.finRange n))) (ofRatDown room)

/-- The row sum `Σ_j sup |DK_{rj}|` of row `r < 2n` of the `DK` models. -/
def dkRowUp (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (pe : PiEnclosure α) (r : ℕ) : α :=
  sumUp (fun j : Fin n => (modelMatrixEntry (dkModels n K W pe) r j.val).supBound W)
    (List.finRange n)

/-- The jet slots of `∂_a H`, `a < 2n` (the slots read by the invariance check). -/
def d1Slots (n : ℕ) (J : HamJet) : List ℕ := (List.range (n + n)).map fun a => J.d1.getD a 0

/-- The model of `(DK (s ω))_a = Σ_l DK_{al} (s ω)_l` for every `ω` in the box (product key
`[5, a, l]`), at degree `0`. -/
def dkFreqModel (n : ℕ) (K : CertEmbedding α) (box : FreqBox) (s : ℚ) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (a : ℕ) : CertModel α :=
  CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun l : Fin n =>
    CertModel.mul W cfg [5, a, l.val] (freqModel n box s l.val)
      (modelMatrixEntry (dkModels n K W pe) a l.val)))

/-- The model of the coordinate `a < 2n` of `X_H ∘ K - DK (s ω)`, from the composed `∂_b H ∘ K`
models `ms` (in `d1Slots` order): `(X_H)_a = + ∂_{a+n} H` for `a < n`, `- ∂_{a-n} H` else. -/
def invarianceModel (n : ℕ) (K : CertEmbedding α) (box : FreqBox) (s : ℚ) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) (ms : List (CertModel α)) (a : ℕ) :
    CertModel α :=
  CertModel.addMixed W pe
    (if a < n then ms.getD (swapNat n a) zeroModel else (ms.getD (swapNat n a) zeroModel).negM)
    (dkFreqModel n K box s W cfg pe a).negM

/-- The bound `|⟨m⟩ - E₀| ≤ e` for the composed `H ∘ K` model `m`: zero-mode ball of
`m - E₀` at degree `0`, plus the model radius. -/
def energyOk (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (m : CertModel α) (E0 e : ℚ) :
    Bool :=
  let d := CertModel.addMixed W pe (CertModel.toDeg W pe 0 m) (constModel n (-E0) 0 0)
  d.deg == 0 &&
    ble (upAdd (upAdd (zeroModeBall n d).c.normUp (zeroModeBall n d).r) d.rad) (ofRatDown e)

end Helpers

/-! ### The sub-checks (each `Bool`, each provable by `decide +kernel` on its own) -/

/-- Shapes (`box.length = n`, list lengths), positivity, `2 ≤ n`, `n - 1 ≤ τ`, `ρ∞ < ρ`,
`1 < s < σω`, `γ ≤ γbar`, `0 ≤ e`, `weight.rho = rho`, both weights, the `π` enclosure, the box
excludes `0` in some coordinate, and the ray margins against the box's lower bound of `‖ω*‖`. -/
def checkStatic {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  let p := c.params
  (c.freqBox.length == n) && (c.centre.length == n) && (c.radius.length == n) &&
    decide (2 ≤ n) && decide (n ≤ p.tau + 1) &&
    decide (0 < p.rhoInf) && decide (p.rhoInf < p.rho) && decide (0 < p.M) &&
    decide (0 < p.σK) && decide (0 < p.σB) && decide (0 < p.σT) && decide (0 < p.μ) &&
    decide (0 < p.γbar) && decide (1 < p.σω) && decide (0 < p.nuRay) &&
    decide (1 < p.s) && decide (p.s < p.σω) && decide (0 < p.γ) && decide (p.γ ≤ p.γbar) &&
    decide (0 ≤ p.err) && decide (c.weight.rho = p.rho) &&
    checkWeight c.weight c.expHalvings c.expOrder &&
    checkWeight c.weightH c.expHalvings c.expOrder && checkPiEnclosure c.piEnc &&
    decide (0 < freqNormLo c.freqBox) &&
    decide (p.nuRay ≤ (p.s - 1) * freqNormLo c.freqBox) &&
    decide (p.nuRay ≤ (p.σω - p.s) * freqNormLo c.freqBox)

/-- Ball arithmetic of the jet on `D` (every denominator certified) and the five bounds
`‖DH‖, ‖X_H‖, ‖DX_H‖, ‖D²X_H‖, ‖D²H‖ ≤ M` on `D`. -/
def checkHamBounds {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  match c.ham.jet.prog.balls n c.weightH c.centre c.radius c.expOrder with
  | some bs => hamBoundsOk (n + n) c.ham.jet bs c.params.M
  | none => false

/-- `ball (K θ) μ ⊆ D` on `T_ρ` and `‖DK‖ ≤ σK - μ` (row sums of `DK` models). -/
def checkEmbedding {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  let p := c.params
  (List.range n).all (fun i =>
      angleImOk n c.emb c.weight c.piEnc p.rho (c.weightH.rho - p.rho - p.μ) i) &&
    (List.range n).all (fun i =>
      ble ((actionShiftModel n c.emb c.weight c.piEnc (c.centre.getD i 0) i).supBound c.weight)
        (ofRatDown (c.radius.getD i 0 - p.μ))) &&
    (List.range (n + n)).all (fun r =>
      ble (dkRowUp n c.emb c.weight c.piEnc r) (ofRatDown (p.σK - p.μ)))

/-- `sup_{T_ρ} ‖X_H(K) - DK (s ω)‖ ≤ e` at full precision, uniformly for `ω` in the box. -/
def checkInvariance {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  match Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) with
  | some ms => (List.range (n + n)).all fun a =>
      ble ((invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms a).supBound
        c.weight) (ofRatDown c.params.err)
  | none => false

/-- `‖⟨H ∘ K⟩ - E₀‖ ≤ e` (zero mode of the composed model ± radius). -/
def checkEnergy {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  match Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      [c.ham.jet.v0] with
  | some [m] => energyOk n c.weight c.piEnc m c.params.E0 c.params.err
  | _ => false

/-- The Gram certificate (`gramCheck`) with bound `σB - μ`. -/
def checkGram {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  (gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ)).isSome

/-- `torsionModels` at `s` and the box, then `torsionAvgCheck n` (exact `(n+1)×(n+1)` shapes of
`T` and the witness `c.torsInv`) with bound `σT - μ`. -/
def checkTorsion {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  match gramCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc (c.params.σB - c.params.μ) with
  | some δβ =>
    match torsionModels n c.ham c.emb c.wit c.gramInv δβ c.freqBox c.params.s c.weight c.cfgLow
        c.piEnc with
    | some T => torsionAvgCheck n T c.torsInv (c.params.σT - c.params.μ)
    | none => false
  | none => false

/-- `isoC1Q e < γ⁴ ρ^{4τ}` and `isoC2Q e ≤ disp γ² ρ^{2τ}`. -/
def checkSmallness {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  let p := c.params
  decide (isoC1Q n p.tau p.rho p.rhoInf p.M p.σK p.σB p.σT p.μ p.nuRay p.γbar * p.err <
      p.γ ^ 4 * p.rho ^ (4 * p.tau)) &&
    decide (isoC2Q n p.tau p.rho p.rhoInf p.M p.σK p.σB p.σT * p.err ≤
      p.disp * (p.γ ^ 2 * p.rho ^ (2 * p.tau)))

/-- **The black-box checker.** -/
def checkTorusCertificate {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c && checkEnergy c &&
    checkGram c && checkTorsion c && checkSmallness c

section Black

variable {n : ℕ} {α : Type} [CertArith α]

/-- Every hypothesis of `KAM.Iso.Apost.g1_explicit` and of `IG1Body`, verbatim, at the data
denoted by `c` and the exact reference vector `ωstar` (`IsDiophantine` excepted). -/
structure G1Hyps (c : TorusCertificate n α) (ωstar : Fin n → ℝ) : Prop where
  hn : 2 ≤ n
  hτ : (n : ℝ) - 1 ≤ (c.params.tau : ℝ)
  hρinf : (0 : ℝ) < c.params.rhoInf
  hρinfρ : (c.params.rhoInf : ℝ) < c.params.rho
  hM : (0 : ℝ) < c.params.M
  hσK : (0 : ℝ) < c.params.σK
  hσB : (0 : ℝ) < c.params.σB
  hσT : (0 : ℝ) < c.params.σT
  hμ : (0 : ℝ) < c.params.μ
  hγbar : (0 : ℝ) < c.params.γbar
  hσω : (1 : ℝ) < c.params.σω
  hν : (0 : ℝ) < c.params.nuRay
  hωstar : ωstar ≠ 0
  hopen : IsOpen c.D
  htransl : ∀ z ∈ c.D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ c.D
  hholo : DifferentiableOn ℂ c.H c.D
  hper : ∀ z ∈ c.D, ∀ k : Fin n → ℤ, c.H (z.1 + (fun i => (k i : ℂ)), z.2) = c.H z
  hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ c.D →
    (c.H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
  hbd : ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧ ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M
  hK : DifferentiableOn ℂ c.K (complexStrip n c.params.rho)
  hKp : IsPrimaryOnStrip c.K c.params.rho
  hKr : IsRealOnReals c.K
  hball : ∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D
  hDK : ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ
  hG : ∀ θ ∈ complexStrip n c.params.rho, IsUnit (gramMatrix c.K θ).det ∧
    ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ
  hTu : IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det
  hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
    (c.params.σT : ℝ) - c.params.μ
  hs1 : (1 : ℝ) < c.params.s
  hsσ : (c.params.s : ℝ) < c.params.σω
  hν1 : (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * ‖ωstar‖
  hν2 : (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖
  hγ : (0 : ℝ) < c.params.γ
  hγγbar : (c.params.γ : ℝ) ≤ c.params.γbar
  he0 : (0 : ℝ) ≤ c.params.err
  hE : ∀ θ ∈ complexStrip n c.params.rho,
    ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err
  hEn : ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err
  hC1 : Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1
  hdisp : Iso.Apost.isoC2 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp

/-- The output of the black box: the conclusion of `IG1Body` for the denoted data, with the
explicit rational displacement bound `disp` in place of `C₂ e/(γ²ρ^{2τ})`. -/
def CertifiedTorus (c : TorusCertificate n α) (ωstar : Fin n → ℝ) : Prop :=
  ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
    1 < sinf ∧ sinf < c.params.σω ∧ DifferentiableOn ℂ Kinf (complexStrip n c.params.rhoInf) ∧
    IsPrimaryOnStrip Kinf c.params.rhoInf ∧ IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, invarianceError c.H Kinf (sinf • ωstar) θ = 0) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, c.H (Kinf θ) = ((c.params.E0 : ℝ) : ℂ)) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, Metric.ball (Kinf θ) ((c.params.μ : ℝ) / 2) ⊆ c.D) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf,
      ‖fderiv ℂ Kinf θ‖ ≤ (c.params.σK : ℝ) - (c.params.μ : ℝ) / 2) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, ‖Kinf θ - c.K θ‖ ≤ c.params.disp) ∧
    ‖sinf • ωstar - (c.params.s : ℝ) • ωstar‖ ≤ c.params.disp

end Black

end KAM.Certificate
