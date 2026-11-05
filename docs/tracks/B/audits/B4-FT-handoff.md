# Handoff B4-FT (Fourier–Taylor polynomials)

## Files (new; nothing else touched)
`KAM/EffectiveStability/FT/{Basic,Deriv,Bracket,Bound}.lean` (569/346/226/298 lines) and facade `KAM/EffectiveStability/FT.lean`.
All items 1–6 are delivered, including item 4 (bracket, ad powers, Lie sum).

## Approach
- `FTMono ⟨k α e c s⟩`, `FTPoly := List FTMono`. One generic evaluation `ftEvalG cf sf p` over a field of char 0, plus a
  Prop bundle `FTTrig cf sf` (cos 0 = 1, sin 0 = 0, addition formulas, cos even, sin odd). `ftEvalR := ftEvalG Real.cos Real.sin π`,
  `ftEvalC := ftEvalG Complex.cos Complex.sin (π:ℂ)`. All algebra (add/neg/sub/smul/mul/const/jVar/cos-,sin-mode, normalize,
  eqCheck) is proved once generically and specialized, so ℝ and ℂ share proofs; `ftEvalC_ofReal` links them.
- mul = product-to-sum (two monomials, `k+k'` and `k-k'`, tags add). `ftNormalize` = trim, canonical sign (first nonzero
  entry of `k` positive, flipping `s`; `s := 0` when `k = 0`), merge by `(k,α,e)`, drop zero terms.
- Derivatives/smoothness/fderiv are proved for any `RCLike 𝕜` from `HasDerivAt`/`ContDiff` hypotheses on `cf, sf`
  (line-derivative + uniqueness, as in B2-POLY), then instantiated for ℝ and ℂ.
- Bounds: `norm_cos/sin_le_exp_im` (new), `‖cos(2π k·φ)‖ ≤ exp(|Im|) ≤ lam^{|k|₁}`; real version uses |cos|≤1.

## Main signatures
```
structure FTMono where k : List ℤ; α : List ℕ; e : ℕ; c s : ℚ        abbrev FTPoly := List FTMono
def ftEvalR (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ
def ftEvalC (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ
theorem ftEvalC_ofReal (P) (x) : ftEvalC P (fun i => (x.1 i : ℂ), fun i => (x.2 i : ℂ)) = ((ftEvalR P x : ℝ) : ℂ)
ftAdd ftNeg ftSub ftSmul ftMul ftConst ftJVar ftCosMode ftSinMode; ftEvalR_/ftEvalC_{add,neg,sub,smul,mul,const,jVar,normalize}
def ftNormalize ; def ftEqCheck (P Q) : Bool
theorem ftEvalR_eq_of_eqCheck {P Q} (h : ftEqCheck P Q = true) (x) : ftEvalR P x = ftEvalR Q x   (and ftEvalC_…)
def FTFits (n) (P) : Prop ; def ftFitsCheck (n) (P) : Bool ; ftFits_of_check ; ftFits_{add,neg,sub,smul,mul,const,jVar,cosMode,sinMode,dφ,dJ,bracket,adPow,lieSum}
theorem ftEvalR_add_period (P) (x) (m : Fin n → ℤ) : ftEvalR P (x + ((fun i => (m i : ℝ), 0) : _)) = ftEvalR P x   (ftEvalC_add_period)
def ftDφ (i : ℕ) (P) ; def ftDJ (i : ℕ) (P)
theorem ftEvalR_fderiv_dφ (P x) (i : Fin n) : fderiv ℝ (fun x => ftEvalR P x) x (Pi.single i 1, 0) = ftEvalR (ftDφ i P) x
theorem ftEvalR_fderiv_dJ … (0, Pi.single i 1) = ftEvalR (ftDJ i P) x ; ftEvalC_fderiv_dφ / dJ
theorem ftEvalR_contDiff (P) (k : WithTop ℕ∞) : ContDiff ℝ k (fun x => ftEvalR P x) ; ftEvalC_contDiff ; ftEvalC_differentiable
def ftBracket (P Q) ; def ftAdPow (χ) (k) (P) ; def ftLieSum (χ H) (L)
theorem ftEvalC_bracket_complex (P Q) (hP : FTFits n P) z : ftEvalC (ftBracket P Q) z = KAM.Canonical.poissonBracket (fun z => ftEvalC P z) (fun z => ftEvalC Q z) z
theorem ftEvalR_bracket_real (P Q) (hP) x : ftEvalR (ftBracket P Q) x = fderiv ℝ (fun x => ftEvalR P x) x (KAM.hamiltonianVectorField (fun x => ftEvalR Q x) x)
theorem ftEvalC_adPow_complex (χ P) (hχ hP) k : (fun z => ftEvalC (ftAdPow χ k P) z) = KAM.Canonical.adPow (fun z => ftEvalC χ z) k (fun z => ftEvalC P z)
theorem ftEvalC_lieSum_complex (χ H) (hχ hH) L z : ftEvalC (ftLieSum χ H L) z = ∑ j ∈ range L, ((j ! : ℂ)⁻¹) * KAM.Canonical.adPow … j … z
def ftPiUB : ℚ := 31416/10000 ; theorem pi_le_ftPiUB : Real.pi ≤ ((ftPiUB:ℚ):ℝ)   (from Real.pi_lt_d4)
def ftSupBound (P) (πub lam : ℚ) (b : List ℚ) : ℚ ; def ftAngleDriftBound (P) (j : ℕ) (πub : ℚ) (b : List ℚ) : ℚ
theorem norm_ftEvalC_le_supBound (P) (hP : FTFits n P) {πub lam} (b) (hπ : Real.pi ≤ πub) (hlam : 0 < lam) (z)
    (hφ : ∀ i, |(z.1 i).im| ≤ Real.log lam / (2 * Real.pi)) (hJ : ∀ i, ‖z.2 i‖ ≤ b.getD i 0) : ‖ftEvalC P z‖ ≤ ftSupBound P πub lam b
theorem abs_ftEvalR_le_supBound (P) (hP) {πub} (b) (hπ) (x) (hJ : ∀ i, |x.2 i| ≤ b.getD i 0) : |ftEvalR P x| ≤ ftSupBound P πub 1 b
theorem abs_fderiv_ftEvalR_le (P) (hP) {πub} (b) (hπ) (x) (hJ) (j : Fin n) :
    |fderiv ℝ (fun x => ftEvalR P x) x (Pi.single j 1, 0)| ≤ ftAngleDriftBound P j πub b
```
(`lam` is any positive rational; `lam ≥ 1` is not needed.)

## Checks
- `b_build.sh` for FT.Basic, FT.Deriv, FT.Bracket, FT.Bound, FT: all succeed, no warnings from my files.
- `sh scripts/lint_sources.sh`: OK (25 tests, frozen-anchor guard, ABI hashes). Line-length script: `[]`.
- `main_shortname_check.py` (all 5 modules): "short-name check OK".
- `#print axioms` (ftEvalC_mul, ftEvalR_mul, *_eq_of_eqCheck, ftEvalC_ofReal, *_add_period, fderiv_dφ/dJ, ftEvalC_bracket_complex,
  ftEvalR_bracket_real, ftEvalC_lieSum_complex, norm_ftEvalC_le_supBound, abs_ftEvalR_le_supBound, abs_fderiv_ftEvalR_le):
  all `[propext, Classical.choice, Quot.sound]`.
- Smoke tests (`decide +kernel`, in `FT/Bound.lean`): bracket of cos-mode with J₀ (both orders), sin²=(1−cos2·)/2, cos²+sin²=1,
  sin(−x)=−sin x, Leibniz-type bracket, two-mode bracket, `ftFitsCheck`, a negative `ftEqCheck … = false`. The whole file elaborates in ≈4 s.

## Deviations / notes
- No requested signature changed. `ftDφ`/`ftDJ` take `i : ℕ` (coerced from `Fin n`), as in B2-POLY.
- `ftEvalG` is an extra generic layer (names `ftEvalG*`, `FTTrig`, `ftTrig_real/complex`); the ℝ/ℂ lemmas are one-line corollaries.
- The ℝ bracket statement is against `hamiltonianVectorField` (frozen def, read only); no frozen file touched.
- `ftDφ i P` keeps zero-coefficient monomials (when `k_i = 0`); `ftNormalize` removes them.
- Not provided: real-valued `ftAdPow` ≙ fderiv version (only ℂ `adPow`, as requested) and a complex-strip drift bound.
- Design signals: none (no heartbeat issue; every file elaborates at default heartbeats). Errata: none found.

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; OD-B11, OD-B12). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B4-FT.md and
brief-B1-common.md. Mirrors the landed, audited B2-POLY (Poly/*.lean) for period-one Fourier–Taylor polynomials;
plan §3.2 (/root/code/KAM/docs/explorations/program-b-plan.md lines 355-375: ‖P‖_{σ,b}, η^poly = 2π Σ|k_j||c|b^α; σ is a
geometric period-one strip width). Consumer: the torus checker ending in B1-T (Torus.lean drift form
|fderiv ℝ R w (Pi.single j 1, 0)| ≤ η_j). Check: (1) SOUNDNESS of ftNormalize / ftEqCheck (canonical sign flip of k with s
negated, k = 0 sin terms dropped, merging by (k, α, e)) — a true check must imply equal evaluations over ℝ and ℂ;
(2) product-to-sum multiplication and the (2π)^e tag bookkeeping in ftDφ; (3) bracket/adPow/Lie-sum correctness vs
KAM.Canonical.poissonBracket / adPow and the real bracket; (4) majorants: the complex strip bound
‖cos(2πk·φ)‖ ≤ lam^{|k|₁} under |Im φ_i| ≤ log lam/(2π) (any lam > 0 — check lam < 1 cases), the rational π bound,
abs_fderiv_ftEvalR_le exactly B1-T's drift form; (5) periodicity; (6) smoke tests by kernel evaluation only;
(7) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
