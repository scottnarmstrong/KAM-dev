# APOST-SHARP-V2-DELTA: signature changes after SHARP2-FIX, per package

30 October 2026, branch `sharp-fix`. New signatures: `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt`.
- It is a copy of `.drafts/sharp2fix/Signatures.lean` and elaborates on top of the merged B1, B2, B3, B5 and B9 (17 `sorry`, no
  error).
- Every new declaration lives in a **new** module. Nothing merged is edited.
- Reasons: design document §11 (dispositions F1–F9, iso F1–F8, the B2/B3/B5/B9/B10D signals) and the blueprint
  (`bp:p2s2:*`, `bpI:p2s2:*`).

Notation: "old" is the SHARP-PLUS signature file; "new" is the replacement.

## Merged packages

### B1 SmallDiv (merged): unchanged; three additions
Every B1 signature stays verbatim (`SDConst`, `sdConst_of_cohData`, `sdConst_classical`, `cohConstC_mono`, `sdConst_freq`,
`norm_avg_mul_cohR_le`). New module `KAM/Sharp2/SmallDiv/Scale.lean`:
- `SDConst.of_le_gamma` (`hc : SDConst n κ γ δ c Ω`, `0 < γ'`, `γ' ≤ γ` → `SDConst n κ γ' δ c Ω`): iso F1, ray certificates at γ̄
  serve every body scale.
- `sdConst_classical_of_le` (`b ≤ b' ≤ 1` → `SDConst n τ γ b (cohConstC n τ b') {ω | IsDiophantine γ τ ω}`): F9, the tail's
  full-bite constant.
- `fullBite_ratio_mono` (`x/min (ρ∞ + c x) 1` is nondecreasing): F9, validity of the tail average for all later stages.

B9 already has `sdConst_mono` (larger constant) and `sdConst_subset` (smaller set) in `RouteA/Frozen.lean`; reuse them, and move
them to `Scale.lean` at integration if wanted.

### B2 Data, Geometry (merged)
- **`norm_lagrangeMat_le_etaN` (old, unprovable: B2's design signal) → `norm_lagrangeMat_le_etaN_of_standing` (B2's proved
  theorem, adopted verbatim).** The changes are: `hh` replaced by `Standing`, `K(T_r) ⊆ 𝔅` and `1 ≤ n`; `hG` and `hKr` dropped.
  Blueprint `bp:p2s2:omega` now states these hypotheses and the sign ∂_ωΩ_K = −(Dηᴺ − (Dηᴺ)ᵀ).
- `norm_invarianceError_le_eta`: unchanged. It is pointwise frame algebra, and option L10 applies it to the new torus K̄ on T_{r−3δ}.
- `RefData`, `RefHyp`, `refHyp_ofV1`: unchanged but **not used by the final route-B theorem**. Route B uses `InitB` + `RefHypB`
  (initial values and the commutator data c_Th, c_DTh), as B9 uses `InitA` + `RefHypA`.
- New, for option L10: `norm_lagrangeMat_comp_le` (the pullback Ω_{K̃∘φ} = Dφᵀ(Ω_K̃∘φ)Dφ, bound (1+b)²·|Ω_K̃|), module
  `KAM/Sharp2/TorsionRef.lean`.

### B3 ModConstants (merged): superseded by a new module `KAM/Sharp2/ModConstantsB.lean`
`StepIn`, `StepConsts`, `stepConsts`, `stepCond` stay in place but are not used by the final theorem. New: `StepInB`,
`StepConstsB`, `stepConstsB`, `stepCondB`, `StepInB.Ok`, `StepInB.Dom`, `stepConstsB_nonneg`, `stepConstsB_mono`,
`stepCondB_anti`. The proofs follow B3's pattern (`positivity`/`gcongr` per helper).

**`StepIn` → `StepInB`.**

| Old | New | Why |
|---|---|---|
| `t` (torsion cap, input) | — | Derived: `t = cTh·sNt·sN + ts`. |
| — | `ts` | Torsion slack. |
| — | `bF` | Local torsion budget (F8). |
| — | `cTh`, `cDTh` | Certified c_Th, c_DTh (B10D flag; old hard-coded 2M₁, 2M₂). |
| `cbar`, `r` | `cavg` | One average constant: c̄(δ/min(r,1))^κ in the prefix, c̄_∞(δ_k/min(r_k,1))^κ in the tail (F9, B9 flag). |
| — | `θN` | L10 ratio. |
| — | `θω` | iso F5 ratio. |
| — | `a` | Schedule ratio. |
| — | `selfcons` | L10 switch. |
| — | `stage0`, `ePer` | The stage-0 replacements C_E → e/μ₀, C_DE → n·e/μ₀, previously only in the mirror. |
| `δ` | `δ` | Now the bite value used in the constants; the actual bite may be any δ′ ≤ δ (as B9's `StepInA`). |

**`stepConsts` → `stepConstsB`.** The new fields are `CEL`, `CEN`, `Cab`, `Bsup`, `Bloc` and `Cnu`; `CDT` and `CNN` are removed.
- `CDT` = C_ab + 2g(σ_Nᵀσ_B C_DE + σ_B³ w C_Ω) (+ iso) becomes **`Cab`** = c_Th(C_N̄ᵀσ_N + σ_NᵀC_N̄) + c_DTh·σ_Nᵀσ_N·C_ΔK·δ (iso:
  max{Cab + ΘC₀g₁, nΘC₀g₁}).
- **`Bsup`** = (σ_Nᵀσ_B C_DE + σ_B³ w C_Ω)g and **`Bloc`** = Bsup (iso: max{Bsup, n g₁}) are the local torsion parts, bounded at each
  stage by that stage's data.
- `CEb` = C_Ẽ + σ̃_K C_gL becomes C_Ẽ + **a_ω**·σ̃_K C_gL, with a_ω = 1 + θω for iso and 1 otherwise (iso F5).
- `QbN`:
  - fixed: unchanged;
  - iso: the old (1+nθξ)(1+θΩ)Q̃_N + (1+nθξ)ΘC_ΩQ̃_N C₀θξ/C_ξL becomes **(1+nθξ)(1+(1+a_ω)θΩ)Q̃_N**, a polynomial (B3 signal, option b).
- `QL`: the composition term σ_NᵀC_gL(nσ̃_K C_ξL + gC_DL̃) is multiplied by a_ω (iso F5).
  - With `selfcons`: QL = min{QL, (QL′ + θN(CEN/CEL)Q̄_N g)/(1 − θN)}, where QL′ = QL − C_N̄ᵀC_Ē (L10).
- `Q`: max{QL, **2**^κ QbN} becomes max{QL, **a**^κ QbN}.
- `Cnu` = ΘC₀ (iso; 0 otherwise), the frequency rate.

**`stepCond` → `stepCondB`.**
- Removed:
  - `sT·CDT·X ≤ θ` (Neumann for ⟨T̄⟩, replaced by the reference Neumann, `inv_le_of_ref`);
  - `2^(κ+1)·Q·X ≤ 1` (the local contraction: not used by the repaired step, F8).
- Added:
  - `Bsup·X ≤ ts` (derived torsion cap);
  - `Bloc·X ≤ bF` (torsion budget);
  - iso: `C0·g₁·X ≤ θω`;
  - L10: `CNbT·CEL·X ≤ θN` and `max 1 sB²·(1+nθξ)²·CΩ·QtN·g·X² ≤ q`.
- The other eight conditions are unchanged.

`stepConstsB_mono` now covers iso too: the old `stepConsts_mono` excluded `QbN`, `Q` for iso.

### B5 Engine (merged): `converge_checked` kept; a generalisation in a new module `KAM/Sharp2/EngineRatio.lean`
`StageScheme`, `StageConsts`, `IsNewton`, `xSeq`, `stageBall` and `converge_checked` stay verbatim. `converge_checked` is the
instance a = 2, ȳ = 1/2. New:

| Old (B5) | New |
|---|---|
| `bite0 = min 1 ((ρ−ρ∞)/6)` | `bite0R a ρ ρ∞ = min 1 ((ρ−ρ∞)(a−1)/(3a))` |
| `biteS = bite0/2^s` | `biteSR = bite0R/a^s` |
| `stripS = ρ − 6δ₀(1−2^{−s})` | `stripSR = ρ − 3δ₀(1−a^{−s})/(1−a^{−1})` |
| `xSeq κ` (factor 2^{κ+1}) | `xSeqR a p` (factor a^p, p = κ+1) |
| `stageBall` (tail factor 2) | `stageBallR` (tail factor 1/(1−ȳ)) |
| `hJ2 : … ≤ 1/2` | `hJ2 : a^(κ+1)·Ctail.Q·X_kpre ≤ ȳ` |
| `hJ3` tail term `2·rate·wt·X` | `rate·wt·X/(1−ȳ)` |

The new theorem is `StageScheme.converge_ratio`: `1 < a`, `0 < ȳ < 1`, plus B5's `hnn`, `hcondT`, `hball` verbatim. Its proof is
B5's with 2 → a and 1/2 → ȳ. `IsNewton` is ratio-agnostic and unchanged. Reason: the fair comparison (the ratio and decay levers,
§11.3) and route A's normalisation (F5).

### B9 Route A (merged, proved): no change required
- B9's `g1_v2A`, `g1_v2A_frozen`, `iso_g1_v2A`, `iso_g1_v2A_frozen`, `NumA`, `NumA.Cert`, `InitA`, `RefHypA` and `routeAOk` are used
  verbatim by the combined theorem `KAM.Sharp2.g1_v2` (min over v1, A, B).
- Route B's packages mirror B9's (`NumB` ↔ `NumA`, `NumB.Cert` ↔ `NumA.Cert`, `InitB` ↔ `InitA`, `RefHypB` ↔ `RefHypA`,
  `routeBOk` ↔ `routeAOk`, `G1BodyB` ↔ `G1BodyA`).
- B9's F5 engine (`SchemeA`, 2^{4κ}, geometric δ-weights, y ≤ 1) is consistent with the repaired blueprint (`bp:p2s2:constantsA`,
  last paragraph).

Optional improvements, a follow-up package if wanted:
1. **L8′, torsion against the initial torus** for route A (k ≥ 1). R1: −11.18 → −10.71 fixed, −11.37 → −10.95 iso. PlasmaLean
   cA-like: −17.27 → −17.02.
   - It needs `TorsionRef` (`norm_torsionAB_le`, `norm_torsion_sub_torsionAB_le`, `inv_le_of_ref`), shared with route B.
   - Replace route A's rate `rT` (and the Neumann condition for ⟨T̄⟩) by the `Tab` rate C_Δab·C_ΔK/η, the local bound
     C_T1 γ̄⁴δ^{2a−1} + C_T2 γ̄³δ^{2a−κ−1}, and the cap β_T − 2b_F.
   - Mirror: `stageA(..., tref=True)`.
2. B9's flag (`Cert.bar` at bite r with r > 1): use the full bite min(r,1), as route B's `NumB.bfull`; the mirror is fixed.
3. (R3) as a required field of `RefHypA`: route B derives the torsion and needs no (R3). A combined theorem with route A's (R3)
   must keep `RefHypA.tors`; `g1_v2` uses the literal-frozen forms, where B9 derives it under `TorsionOk`.

### B10D ℓ¹ design (merged)
- **Corrected PlasmaLean target**: PlasmaLean's proved tolerance stays 10^{−18.24}.
  - v2 under the corrected constants (cA-like, sup norms, frequency-specific): route A 10^{−17.27} (+0.97) as proved by B9, and
    10^{−17.02} (+1.22) with L8′.
  - B10's ℓ¹ entry step (current code): 10^{−15.65} (+2.59), and 10^{−15.20} (+3.04) with the ℓ¹ frame increment.
- What the repairs change in B10D's design:
  - The local contraction premise is no longer needed by the sup step. B10D keeps it in its `l1` option (`entryCondB`), which is
    harmless.
  - In route B, K's own Lagrangian defect (B10D's C_OmK) now enters the local torsion bound `Bsup` and the Ω_N term. There is no
    "K and K̄" factor 2 in the torsion any more.
  - The ℓ¹ entry stage should use `StepInB` (with `cTh`, `cDTh`, `cavg`), the `Tab` cap and `bF` instead of `CDT`/`Tinv`.
  - The tail average uses the certified c̄_∞ (F9).

## Planned packages (not yet assigned)

### B4 Modified step: `modified_step` → `modified_stepB` (module `KAM/Sharp2/ModStepB.lean`)
Hypotheses added:
- `p.Ok`;
- the standing hypotheses of h (`hopen`, `htransl`, `hholo`, `hper`, `hreal`; F4);
- the actual bite `δ ≤ p.δ`;
- a split certificate (`0 < s < 1`, `SDConst … (s·δ) c'`, `c'/(s^κ(1−s)) ≤ p.c1`) in place of `c1/2^(κ+1)` at δ/2;
- a full-bite certificate (`δ ≤ b ≤ r`, `SDConst … b cb`, `cb(δ/b)^κ ≤ p.cavg`) in place of the certificate at r;
- the commutator data `hcomm`, `hlip`;
- current frame values `m : Fin 5 → ℝ` with room for the increments (`hroom`, needed by L10).

`hT` becomes `‖T‖ ≤ cTh·sNt·sN + ts`.

Conclusions removed:
- `‖T(K̄) − T(K)‖ ≤ CDT·X` and the ⟨T̄⟩⁻¹ estimate (F8: unjustified).

Conclusions added:
- `‖𝒯_ab(K̄) − 𝒯_ab(K)‖ ≤ Cab·X` on T_{r−3δ};
- `‖T(K) − 𝒯_ab(K)‖ ≤ Bsup·X` on T_{r−δ};
- the Lᵀ increment.

The iso bordered step (B7) is the same with the `StepInB` iso fields (Definition `bpI:p2s2:constants`).

New lemmas (`KAM/Sharp2/TorsionRef.lean`): `hamComm`, `torsionAB`, `torsionABAverage`, `norm_torsionAB_le`,
`norm_torsion_sub_torsionAB_le`, `inv_le_of_ref`, `norm_lagrangeMat_comp_le`.

### B6 Route B theorem: `stageInB`, `routeBOk`, `ballSumB`, `closenessV2`, `c1V2`, `g1_v2` → `RouteB.*` and `KAM.Sharp2.g1_v2`

| Old | New |
|---|---|
| `stageInB` (arbitrary arrays `c c' cbar`, `t` fixed outside the body) | `NumB n` (numbers: schedule ratio `a`, decay `ybar`, `kp`, certificates `c` at δ_s, `c'` at the split bite, `cbar` at min(r_s,1), `ctail`, `cbtail`, L10 switch, stage-0 weights), `NumB.inp` (one `StepInB` per stage, the tail record for s ≥ kp) |
| no certificate premise (F3, iso F1) | `NumB.Cert γ Ω`, a hypothesis inside the body with `ω ∈ Ω` |
| `RefHyp rd` (no initial values) | `InitB` (initial Lᵀ, N, Nᵀ) + `InitB.Wf` + `RefHypB` (M₁, M₂, commutator, Lipschitz, Lᵀ, N, Nᵀ) |
| `routeBOk` (prefix and tail conditions, sums for DK, ball, ⟨T⟩⁻¹, frequency only) | `routeBOk N σ m₀ β Xs` with J1 (prefix), J1t (tail on [0, X_kp]), J2 (≤ ȳ), J3 over **seven caps** with initial values, J4 (ball < β) |
| `closenessV2` with γ̄² (F6) | `c2B` (and `c3B`), no γ̄², with the clipped weight |
| `c1V2` | `c1B = ρ^{4τ} max{iLt·γ̄², pN·γ̄³δ₀^τ}/(X⋆δ₀^{2τ+1})` (pN = iNt, iso max{iNt,1}) |
| `g1_v2` (→ `G1BodyRef`, the F1 counterexample) | `g1_v2B` (→ `G1BodyB`, the refined body) and `g1_v2B_frozen` (→ literal `G1Body`, default data) |
| — | `NumB.Fits` (stage-0 weights valid at every γ ≤ γ̄, clipped: iso F4) |
| — | `KAM.Sharp2.g1_v2`: literal `G1Body` with C₁ = min{C₁♯, c1A, c1B}, C₂ = max{C₂♯, c2A, c2B} (B9's route A + route B) |

`c1V2_le_sharpC1` becomes `c1B_min_le_sharpC1` (`min_le_left`).

### B7 Iso: `iso_g1_v2` → `iso_g1_v2B_frozen` (module `KAM/Iso/Sharp2/RouteB.lean`)
- The conclusion is the literal `IG1Body` with C₁ = min{C₁♯, c1B}, C₂ = max{C₂♯, c2B}, C₃ = max{C₃♯, c3B}.
- The hypotheses mirror B9's `iso_g1_v2A_frozen`: Θ = σ_ω‖ω*‖, y₀ = Mσ_N, M₁ = M₂ = M_h2 = M, the frequency cap ν/2 in `capB`.
- New: `NumB.Cert.of_le_gamma`. A combined iso theorem (min over v1, A, B) follows the fixed-frequency `g1_v2` pattern.

### B8 Hybrid: unchanged
Numbers are labelled "heuristic extrapolation assuming certified first-step transfer". The corollary requires enclosures of the
first-step remainders, the new caps and displacement, and budgets reduced by the measured stage-0 increments
(`bp:p2s2:hybrid`).
