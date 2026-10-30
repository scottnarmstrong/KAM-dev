# APOST-SHARP-V2-L1: the weighted-ℓ¹ entry step (package B10, design SHARP2-B10D)

30 October 2026. Branch `sharp-b10` (from `sharp-v2` at b52d6b71). Design work: blueprint, signatures, Python; no Lean proof.
Every number comes from `scripts/apost_sharp/` (untrusted design tooling). Numbers measured on a candidate are labelled
heuristic until enclosed.

**Contents.** §0 summary; §1 the decision; §2 the mathematics; §3 numbers; §4 Lean signature deltas; §5 package split;
§6 coordination with B3, B4, B5, B9; §7 risks; §8 reproduction.

## 0. Summary

- **What B10 is.** The first Newton step solves its two cohomological equations, takes its average and bounds the
  Lagrangian defect of the *initial* torus from weighted-ℓ¹ data of that torus. It uses
  Γ_∞(ω, δ) = sup_k e^{−2πδ|k|₁}/(2π|k·ω|) (SHARP-L9, proved). Every other estimate of that step, and every later step,
  stays the sup-norm v2 scheme. The conclusion is the frozen `G1Body`/`IG1Body`.
- **Why only the entry.** At later stages the errors are abstract. Their ℓ¹ bounds would need the Hamiltonian composed
  with the new torus. With the frozen sup data of h (D12) that costs a sup → ℓ¹ conversion coth(πσ)ⁿ ≥ 10³, against a
  small-divisor gain of at most 6–18. So no conversion is used anywhere (§1).
- **PlasmaLean's example** (its proved tolerance 10⁻¹⁸·²⁴, at its declared, pessimistic bounds):

  | Reading | Best v2 (route A + entry + ℓ¹ frame increment) | Margin | Sup-norm v2 |
  |---|---:|---:|---:|
  | (a) ℓ¹ error vs its ℓ¹ error (like for like) | 10⁻¹⁵·⁴⁰ | **+2.84** | +0.97 |
  | (b) sup error, ℓ¹/sup = 3.6 | 10⁻¹⁵·⁹³ | **+2.31** | +0.97 |

  The owner's requirement (match PlasmaLean, ≥ +1 order at its pessimistic norms) holds in both readings. The entry
  alone, without the frame increment, gives +2.33 and +1.80.
- **R1** (measured ℓ¹ data, heuristic until enclosed). Route A goes 10⁻¹¹·¹⁸ → 10⁻¹⁰·¹³ (fixed) and 10⁻¹¹·³⁷ → 10⁻¹⁰·³²
  (iso), +1.05 orders. Route B gains 0.08–0.09. The gain stays ≥ +0.89 for an ℓ¹/sup ratio up to 8.
- **Lean.**
  - The probe `.drafts/sharp2/L1Signatures.lean` (copy: `APOST-SHARP-V2-L1-SIGNATURES.lean.txt`) elaborates: 1110
    lines, of which 304 are verbatim copies of `sharp-v2` declarations; 22 `sorry` declarations; no error.
  - The two body splits (`g1Body_iff_split`, `ig1Body_iff_split`) are proved.
  - About 2.6k Lean lines in five packages (§5). The largest dependency is the solve-bounds form of the B4 step and of
    B9's route-A step.

## 1. The decision: what is measured in ℓ¹ and what in sup

**Measured in ℓ¹, on the initial torus only:**
- ηᴺ and ηᴸ on T_ρ;
- the torsion T on T_{ρ−δ₀};
- optionally the frames L, N on T_ρ (route A).

Then u = 𝓡ηᴺ, ξᴺ, ξᴸ and ΔK₀ are known in ℓ¹.

**Measured in sup:** the Hamiltonian bounds, the frame and torsion caps, ⟨T⟩⁻¹, E, every object of the tori K_s for
s ≥ 1, and the intermediate tori.

**Price of a sup → ℓ¹ conversion.** It is ϱ = coth(πσ)ⁿ (Lemma `bp:p2s2l1:convert`). For n = 2:

| Package | σ = δ₀ | σ = 3δ₀ | σ = ρ |
|---|---:|---:|---:|
| R1 (δ₀ = 0.00238) | 1.8·10⁴ | 2.0·10³ | 5.0·10² |
| PlasmaLean (δ₀ = 0.00333) | 9.1·10³ | 1.0·10³ | 2.5·10² |

**The small-divisor gain.** c_freq/c_∞ is 5.9 for R1 (0.0030/0.00051) and 6.0 for PlasmaLean (0.0075/0.00126).

| Object | Feeds | Norm used | Conversion |
|---|---|---|---|
| ηᴺ₀, ηᴸ₀ | u, gᴸ | ℓ¹, certificate | none |
| T₀ | gᴸ = ηᴸ − Tξᴺ | ℓ¹, certificate | none |
| ξᴺ₀, u, ξᴸ₀ | gᴸ, ΔK₀ | ℓ¹, from the solves | none |
| ηᴺ_s, ηᴸ_s, s ≥ 1 | u_s, gᴸ_s | sup | none (ℓ¹ would cost ϱ ≥ 10³) |
| Δ²X, X_Nξᴺ, K̃∘φ | new error | sup | none (ℓ¹ would cost ϱ, or h in a Fourier–Taylor norm) |
| frames, T_s, ⟨T⟩⁻¹ | caps | sup (L, N also ℓ¹ at stage 0, route A) | none |

**Why stage s ≥ 1 does not pay.** On R1 with the v2 levers, the Taylor term is 16, 23, 33, 52 and 68 % of route A's C_E
at stages 0–4 (`stageA`). Its ℓ¹ norm costs ϱ ≥ 2·10³. So the ℓ¹ error fed to stage s+1 is ≥ 300× its sup bound,
against a solve gain ≤ 18. The alternative, h in a Fourier–Taylor norm, is a new hypothesis outside D12, a new
certificate primitive, and about 1.5k lines of composition Lean. It would add at most the stage-1 share of the gain.

**Mixed products** never occur in an ℓ¹ estimate. The only ℓ¹ products are Tξᴺ, Lξᴸ and Nξᴺ, all ℓ¹ × ℓ¹ with
certified ℓ¹ factors.

**Each ingredient takes the smaller of its sup and ℓ¹ bounds.** Both bound the same objects, at the same bites. So the
entry is never worse than the sup stage (Lemma `bp:p2s2l1:never-worse`). On R1 the full-strip average is the one
ingredient where sup wins: c(ρ) = 0.0067 against a_N c_∞(ρ) = 4.1 · 0.0020.

## 2. The mathematics (blueprint `p2s2-l1hybrid`, `p2s2-iso-l1hybrid`)

- **Norms** `bp:p2s2l1:norms`: componentwise for vectors, row sums for matrices. A bound always includes summability and
  A ≥ 0.
- **Toolkit** `bp:p2s2l1:toolkit`:
  - sup ≤ ℓ¹;
  - Wiener products;
  - constants;
  - removing the zero mode;
  - the **row-sum ℓ¹ Cauchy estimate** |Df| ≤ ‖f‖_{1,r}/(eδ) (the sup estimate has n/δ), its transpose (factor p),
    and its antisymmetric part (factor n).
- **Solves** `bp:p2s2l1:solve`:
  - SHARP-L9 for 𝓡;
  - the full bite at real points (radius 0);
  - the ray: Γ_∞(sω) ≤ Γ_∞(ω) for s ≥ 1.
- **Defect** `bp:p2s2l1:defect`: Ω_K = −(Du − (Du)ᵀ) with u = 𝓡ηᴺ (sign of B2). This gives |Ω_K| ≤ (n/(eδ'))Γ_∞(δ)ε¹_N,
  where the sup lemma has factor 2(n−1) and a second bite constant.
- **Entry data** `bp:p2s2l1:data`, each a bound on an explicit object, none conclusion-shaped:
  - (L1) ‖ηᴺ‖_{1,ρ} ≤ a_N σ_{Lᵀ} e and ‖ηᴸ‖_{1,ρ} ≤ a_L σ_{Nᵀ} e;
  - (L2) ‖T‖_{1,ρ−δ₀} ≤ t₁, and |T| ≤ t_ℝ on ℝⁿ;
  - (L3) Γ_∞(ω, δ₀) ≤ G₀, Γ_∞(ω, δ₀/2) ≤ G₀′ and Γ_∞(ω, ρ) ≤ G_ρ, for the actual ω (audit F3, F9);
  - (L4) optional: ‖L‖_{1,ρ} ≤ ν_K and ‖N‖_{1,ρ} ≤ ν_N;
  - (L5) the sup `SDConst` premises at every bite.
- **Entry constants**: `bp:p2s2l1:constA` (route A, with the optional ℓ¹ frame increment, Lemma `bp:p2s2l1:frame`) and
  `bp:p2s2l1:constB` (route B). C_Ω is split into the defect of K (ℓ¹ allowed) and the defects of K̃ and K̄ (sup only).
  The iso cubic term keeps the sup denominator.
- **Engine** `bp:p2s2l1:engine`:
  - (a) the entry by hand, then `StageScheme.converge_checked` from ρ₁ = ρ − 3δ₀, whose first bite is δ₀/2;
  - (b) route A embedded in the route-B-normalised engine: X = x = ε/(γ⁴δ^{4κ}), μ = ε/(γ³δ^{3κ−1}),
    Q = 2^{3κ−1}C_E. So 2^{κ+1}Q = 2^{4κ}C_E (audit F5). Displacement constant γ²δ^{2κ−1}C_ΔK, frame weights
    γ²δ^{2κ−1};
  - (c) closeness without γ̄²: C₂ = ρ^{2τ}S̃/(X⋆δ₀^{4τ}) for route A, and ρ^{2τ}σ_{Lᵀ}S/(X⋆δ₀^{2τ+1}) for route B
    (audit F6).
- **Theorems** `bp:p2s2l1:g1A` (route A, the PlasmaLean route), `bp:p2s2l1:g1B` (route B, pays little) and
  `bp:p2s2l1:frozen` (the disjunction with the v2 routes; the minimum of the C₁ proved by cases), plus the iso theorem
  `bpI:p2s2l1:g1`.
- **Audit lessons applied:**
  - F1: the well-formedness package `L1Data.WF` and the positivity of the refined data;
  - F3/F9: SDConst and Γ_∞ premises at the actual bites, for the actual ω, inside the body;
  - F3/iso-F2: all caps, with initial values, in the smallness predicate;
  - F4: the standing periodicity and reality of h in the entry theorems;
  - F5: route A uses 2^{4κ};
  - F6: no γ̄² in the closeness;
  - F8: the local contraction at the entry stage;
  - iso-F4: the clipped stage-0 weight λ₀ = σ_{Nᵀ}/p;
  - B5: the engine is `converge_checked`, with `hnn`, `hcondT` and `hball` in the predicate;
  - F6 (heuristic label): R1's ℓ¹ data are labelled heuristic until enclosed.

## 3. Numbers

`thresholds_v2.py --l1`, `dominance.py --plasmalean`.
- **Sup stages.** c_freq is computed at every bite: 0.00754 → 0.00752 for PlasmaLean, whose table in design §10.1 used
  a flat value. The tail uses the classical constant c♮(δ₅).
- **The entry.** c_∞ at δ₀, δ₀/2 and ρ: 0.00126, 0.00127 and 0.0021 for PlasmaLean; 0.00051, 0.00049 and 0.0020 for R1.
- **The default tables are unchanged.** The default output of `thresholds_v2.py` is byte-identical to the committed
  version's. The new rows of route A are computed under the conditions of the Lean predicate (`b5`: local contraction
  at every prefix stage, tail decay ≤ 1/2); no number changes.

**PlasmaLean's example** (ω = (ι, 1), γ = 0.0687, ρ = 0.02; its tolerance 10⁻¹⁸·²⁴). Transposes are at the
conservative defaults. Route B gets the torsion cap 19.84 × 1.05, as route A does.

| Norms | Variant | (a) ℓ¹ vs ℓ¹ | Margin | (b) ×3.6 | Margin |
|---|---|---:|---:|---:|---:|
| cA-like | A7 (sup) | −17.27 | +0.97 | −17.27 | +0.97 |
| cA-like | A7 + entry | −15.91 | +2.33 | −16.44 | +1.80 |
| cA-like | A7 + entry + ℓ¹ frame increment | **−15.40** | **+2.84** | **−15.93** | **+2.31** |
| cA-like | B6 (sup, torsion cap) | −18.10 | +0.14 | −18.10 | +0.14 |
| cA-like | B6 + entry | −17.12 | +1.12 | −17.65 | +0.59 |
| R1-like | best (A + entry + frame) | −12.06 | +6.18 | −12.51 | +5.73 |

- **Reading (a)** compares our threshold on ‖E‖_{1,ρ} with PlasmaLean's tolerance on its own ℓ¹ error norm: every
  candidate it accepts, we accept.
- **Reading (b)** is the threshold on sup|E| for an error with ℓ¹/sup = 3.6.
- **The emulation of design §10.1** (c_∞ at every stage, ×3.6) gave −16.24. The entry alone gives −16.44, with no
  conversion. The frame increment, absent from the emulation, gives −15.93.
- **Not like for like:** PlasmaLean's field is non-canonical, with 1½ degrees of freedom.

**R1** (`l1_entry_r1.py`; heuristic, sampled FFT, grid 1024 × 256):

| Measured | Value |
|---|---:|
| ‖E‖₁/sup | 4.28 (the certifier's 4.28 ✓) |
| a_N | 3.92 |
| a_L | 0.26 |
| ‖T‖_{1,ρ−δ₀} | 3.55 (sup 3.31) |
| ‖L‖₁ | 1.36 |
| ‖N‖₁ | 1.42 (1.04 × sup) |

The theorem data are these × 1.05.

| Variant | Fixed | Iso | Binding |
|---|---:|---:|---|
| A7 (sup) | −11.18 | −11.37 | ⟨T⟩⁻¹ cap sum |
| A7 + entry | −10.42 | −10.60 | ⟨T⟩⁻¹ cap sum |
| A7 + entry + ℓ¹ frame increment | **−10.13** | **−10.32** | ⟨T⟩⁻¹ cap sum |
| B6 (sup) | −12.25 | −12.39 | tail decay |
| B6 + entry | −12.16 | −12.31 | tail decay |

**Sensitivity** (R1, fixed, route A with all levers), as a function of a = a_N = a_L:

| a | log₁₀ threshold |
|---:|---:|
| 1 | −9.67 |
| 2 | −9.91 |
| 3.6 | −10.11 |
| 8 | −10.29 |

**Route B pays little** (it is bound by the tail decay, where stage 0 carries half of the log-weight, and its Q̃_N is
dominated by C₀, not by the solves). It is kept as an optional theorem because the solve-bounds form of B4 makes it
cheap (§5).

## 4. Lean signature deltas

The probe is `.drafts/sharp2/L1Signatures.lean`, copied to `docs/campaign/design/APOST-SHARP-V2-L1-SIGNATURES.lean.txt`.
- **Command:** `nice -n 5 lake env lean .drafts/sharp2/L1Signatures.lean`.
- **Result:** exit 0, 22 warnings "declaration uses `sorry`", no other diagnostic.
- **Part 0** (lines 1–304) is a verbatim copy of the `sharp-v2` declarations it uses, at 17ea3c67: B1 `SDConst`, `ray`;
  B2 `RefData`, `RefHyp`; B3 `StepIn`, `StepConsts`, `stepConsts`, `stepCond`; the planned B4 `modXiN0` … `modNewton`;
  B5 `xSeq`, `StageScheme`, `StageConsts`, `IsNewton`, `bite0`, `biteS`, `stripS`, `stageBall`, and `converge_checked`
  (statement, `sorry`). These modules are not built in this worktree. Part 0 is not a delta.

| Planned module | Declarations (B10 deltas) |
|---|---|
| `KAM/Sharp2/L1/Norms.lean` | `coeffR`, `L1Vec`, `L1Mat`, `jac`, `L1Vec.norm_le`, `L1Mat.norm_le`, `L1Mat.mulVec`, `L1Vec.const`, `L1Vec.add`, `L1Vec.mono`, `L1Vec.norm_jac_le`, `L1Vec.norm_jac_transpose_le`, `L1Vec.norm_jac_antisymm_le` |
| `KAM/Sharp2/L1/Solve.lean` | `l1_cohR`, `l1_cohR_real`, `smallDivisorSup_smul_le`, `lagrangeMat_eq_neg_antisymm`, `norm_lagrangeMat_le_l1` |
| `KAM/Sharp2/L1/Data.lean` | `L1Data`, `L1Data.WF`, `L1Hyp` |
| `KAM/Sharp2/L1/EntryB.lean` | `EntryNumB`, `entryConstsB` (full definition, mirror of `stageB(l1=…)`), `entryCondB`, `entryNumB`, `entry_step_B` |
| `KAM/Sharp2/L1/RouteA.lean` | `StepInA`, `EntryNumA`, `EntryNumA.sup`, `StageConstsA`, `stageConstsA` (full definition, mirror of `stageA(l1=…)`), `stageCondA`, `capsA`, `engineConstsA` (the embedding), `entryNumA`, `norm_fderiv_newtonMap_sub_le_l1`, `AdmA`, `entry_step_A`, `routeAScheme`, `schedIdx`, `stageInAt`, `routeA_isNewton` (B9-owned, consumed) |
| `KAM/Sharp2/L1/G1.lean` | `G1Hyps`, `G1Concl`, `g1Body_iff_split` (**proved**), `G1BodyL1`, `stageInA`, `routeAOkL1`, `ballSumA`, `g1_l1A`, `routeBOkL1`, `g1_l1B` |
| `KAM/Iso/Sharp2/L1/G1.lean` | `IG1Hyps`, `IG1Concl`, `ig1Body_iff_split` (**proved**), `IG1BodyL1`, `iso_g1_l1A` |

**Interfaces reused unchanged:**
- SHARP-L9: `KAM.cohomological_l1`, `smallDivisorSup`, `summableWeighted_solve_sup`,
  `norm_le_weightedNorm_of_summableWeighted`, `eq_fourierSum_of_summableWeighted`, `smallDivisorSup_snoc_le` (the
  certificate).
- `KAM.Fourier.weightedNorm_convolution_le`, `weightedNorm_partialCoeff_le`.
- B2's `fderiv_lagrangeMat_eq_etaN`.
- v1's `newtonMap`, `correction`, `triXi*`, `Standing`, `Admissible`.
- `KAM.Sharp.G1Body` and `KAM.Iso.Charts.IG1Body`, through the proved splits.

## 5. Package split

Files ≤ 800 lines each.

| Package | Content | Lines | Depends on |
|---|---|---:|---|
| B10a SHARP2-L1-NORMS | `L1/Norms`: the bridges (a product of absolutely convergent Fourier series has the convolution coefficients; the coefficients of `fderiv` of a Fourier series), sup bounds, Wiener products, row-sum Cauchy | 450 | SHARP-L9, `KAM/Fourier` |
| B10b SHARP2-L1-SOLVE | `L1/Solve`, `L1/Data`: the L9 wrappers, the real-point full bite, the ray, the defect identity and bound | 350 | B10a, B2 (`fderiv_lagrangeMat_eq_etaN`) |
| B10c SHARP2-L1-A | `L1/RouteA`: route-A stage constants with `EntryNumA` (joint with B9), positivity and monotonicity, the ℓ¹ frame increment, `entry_step_A`, the engine embedding | 750 | B10a, B10b, B9 (route-A step in solve-bounds form), B5 |
| B10d SHARP2-L1-B | `L1/EntryB`: `entryConstsB`, never-worse monotonicity, `entry_step_B` | 450 | B10a, B10b, B3, B4 (in solve-bounds form) |
| B10e SHARP2-L1-G1 | `L1/G1`, `Iso/Sharp2/L1/G1`: the bodies, the predicates, `g1_l1A`, `g1_l1B`, `iso_g1_l1A`, the frozen form by cases | 650 | B10c, B10d, B5, B6, B7 |

**Totals.** About 2.65k lines (2.2k without route B). The design document §10.2 estimated 1.5–2k for a "parallel
norm layer for the step". The entry design needs no step layer in ℓ¹ beyond stage 0; the extra lines are theorem
assembly.

**Order.**
1. B10a and B10b now: they are independent of the open v2 packages.
2. B10c and B10d after B9 and B4.
3. B10e last.

**Recommendation.** Fund B10a, B10b, B10c and B10e first: route A is the PlasmaLean route. B10d is optional.

## 6. Coordination (signature deltas requested of other packages)

1. **B4 (modified step).**
   - State the step from **solve bounds**: `modified_step_of_solve`, with the bounds of u = 𝓡ηᴺ on T_{r−δ}, of u on ℝⁿ
     (the average), of D(Nu), of ξᴸ and of Ω_K as hypotheses on these explicit objects (a conditional helper with a
     distinct name).
   - `modified_step` (sup) and `entry_step_B` (ℓ¹) are then two producers. This is also where audit F8's split of C_Ω
     (defect of K against the defects of K̃, K̄) lands.
2. **B9 (route A).** The route-A stage constants should be a function of a solve record. `stageConstsA (q : StepInA)
   (l : EntryNumA)` in the probe is the reference transcription of `stageA`, with the levers of A7. Route A enters the
   B5 engine through the reparametrisation of `bp:p2s2l1:engine`(b). `routeA_isNewton` is B9's step as an engine
   instance; B10 consumes it.
3. **B3 (constants).** `StepIn` has no certified c_Th or c_DTh, but the design's B-rows (B1–B6) use the certified c_Th.
   `stepConsts` hardcodes 2M₁ and 2M₂, so the B3 mirror differs from `stageB` whenever `cTh` is passed. `EntryNumB`
   carries `cTh` and `cDTh`; B3 should add them to `StepIn`.
4. **B5 (engine).** `converge_checked` takes the stage constants as a function of the bite. The route-A instance defines
   them piecewise through `schedIdx` (prefix bites, then the uniform tail with absorbed powers, `stageInAt`). The entry
   runs by hand before the engine; no change to B5 is needed.

## 7. Risks and open points

- **The bridges of B10a** (products and derivatives of absolutely convergent Fourier series on strips) are the main new
  analysis. The Fourier–Taylor analogue exists in `KAM/Weighted` (`coeff_mul`, `cauchy_theta`) and is the template.
- **Inherited gaps.**
  - Audit F8 (the torsion of the new torus at the stage transition) applies unchanged to the K̄ part of the entry.
  - Audit iso-F5 (moving-frequency factors) applies to the iso entry.
  - Their repairs change the sup constants; the entry inherits them.
- **Data.** R1's ℓ¹ data are sampled. The certificate must enclose ‖ηᴺ‖₁, ‖ηᴸ‖₁ and ‖T‖₁, and certify Γ_∞ at δ₀, δ₀/2
  and ρ: 752, 1518 and fewer entries for R1 (`smallDivisorSup_snoc_le`). PlasmaLean's bounds are its declared numbers,
  read as sup and ℓ¹ bounds.
- **Not done.** No ℓ¹ data for H50 (no rows). No dominance grid with the entry: the competitors are sup-norm theorems,
  and the grid uses no measured objects.

## 8. Reproduction

```
python3 -I scripts/apost_sharp/l1_entry_r1.py            # R1 weighted-l1 data (6 s; heuristic)
python3 -I scripts/apost_sharp/thresholds_v2.py --l1     # R1 tables and sensitivity (12 s)
python3 -I scripts/apost_sharp/dominance.py --plasmalean # PlasmaLean, incl. the B10 table (12 s)
python3 -I scripts/apost_sharp/thresholds_v2.py          # the v2 tables, unchanged (byte-identical)
nice -n 5 lake env lean .drafts/sharp2/L1Signatures.lean # the signature probe
```
