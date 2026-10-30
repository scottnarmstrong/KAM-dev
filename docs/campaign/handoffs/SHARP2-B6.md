# SHARP2-B6 handoff: the route-B theorem and the combined v2 theorem

Branch `sharp-b6`, from `sharp-v2` at `b933c88e`. `sharp-v2` was merged at `19d96238` (allowed; it brings
B4B, B5R and DOMPLUS). Ten package commits, `f50cfb17` to `26fe976d` and this handoff.

Results:
- **All Lean targets are proved verbatim**, with no `sorry` and no signature change:
  - in `KAM.Sharp2.RouteB`: `NumB` (with `inp`, `stage`, `ballSum`, `freqSum`), `NumB.Wf`, `NumB.Cert`, `NumB.Fits`, `InitB`,
    `InitB.Wf`, `RefHypB`, `initB`, `capB`, `routeBOk`, `pN`, `c1B`, `c2B`, `c3B`, `defaultInitB`;
  - `G1BodyB`, `g1_v2B` (refined), `g1_v2B_frozen` (literal `KAM.Sharp.G1Body`), `c1B_min_le_sharpC1`;
  - the combined `KAM.Sharp2.g1_v2` (literal `G1Body`, C₁ = min{C₁♯, c1A, c1B}, C₂ = max{C₂♯, c2A, c2B}).
- **Wiring.** `modified_stepB` (B4B) is wired into `StageScheme.converge_ratio` (B5R) unchanged. The torsion is taken against
  the initial torus: the state carries the drift of ⟨𝒯_ab⟩, and `inv_le_of_ref` is applied at each stage. `hS` comes from the
  frozen G1 hypotheses, and `hE0` from the frozen |E| ≤ e at stage 0.
- **Mirror.** On R1 (fixed), the exact rational mirror of `routeBOk` gives **e\* = 10^−12.224**, against the design's −12.245
  (−12.25 in the B6 rows). The binding field is the same in both: J2, tail decay. Stages 1–5 agree exactly with `stageB`.
  The +0.021 is log₁₀ 1.05 (see "Mirror").
- **DOMPLUS fold-in done.** `CDK := p.sK * CxiL + g * CKt` in `ModConstantsB`; the displacement in `ModStepB/Comp.lean` now goes
  through K∘φ − K.

## Files

All modules: copyright, `module`, `public import`, module docstring, `public section`. No line exceeds 100 characters; no file
exceeds 800 lines (largest 690). No `sorry`, `axiom`, `admit`, `unsafe`, `opaque` or `set_option`.

| File | Lines | Content |
|---|---|---|
| `KAM/Sharp2/RouteB/Data.lean` | 248 | the verbatim `RouteB/Data.lean` block of the signature file (token-identical, lines wrapped at 100) |
| `KAM/Sharp2/RouteB/Sched.lean` | 288 | the schedule under `NumB.Wf` (unclipped since ρ ≤ 1): `δ0_eq`, `δ_succ`, `r_succ`, `r_eq`, `δ_le_bfull`, `ratio_anti`; the split; the stage inputs: `inp_tail`, `inp_ok`, `δ_le_inp`; `NumB.Cert.at` (the three certificates of stage `s`) |
| `KAM/Sharp2/RouteB/Local.lean` | 690 | `LocHyp`, B4B's `ModStepB.Hyp` without the torsion/average/certificate fields, and B4B's geometry chain on it: `E_le`, `DE_le`, `torsion_sub_le` (\|T − 𝒯_ab\| ≤ B_sup X), … |
| `KAM/Sharp2/RouteB/Scheme.lean` | 208 | `StB` = ℕ × Bool × torus, `Good`, `Junk`, `schemeB`, `stageOf`, `stageC` (+ `stageC_sched`, `stageC_tail`); ⟨𝒯_ab⟩ facts (`norm_torusAverage_sub_le`, `torsionABAverage_eq`) |
| `KAM/Sharp2/RouteB/Newton.lean` | 263 | `RunBase` (numbers, standing data, Hamiltonian data, certificates), `RunHyp extends RunBase` (reference data of K₀); `RunBase.loc`, `locpart`; `RunHyp.tors` (local torsion + reference Neumann) |
| `KAM/Sharp2/RouteB/Step.lean` | 250 | `RunHyp.mu_succ_le`, `RunHyp.good_step` (one stage: `modified_stepB` at a flagged state gives the next flagged state, plus the displacement) |
| `KAM/Sharp2/RouteB/Run.lean` | 230 | `RunHyp.isNewton` ((N1), (N2) of `IsNewton` for `schemeB`), `iterB`, `iterB_spec` (the flag along the run), `xS_mono`, `xS_scale`, `ballSum_mono`, `ballSum_scale`, `tendsto_fderiv_of_uniform` |
| `KAM/Sharp2/RouteB/Core.lean` | 231 | `RunHyp.core`: limit torus on T_{ρ∞}, holomorphic, primary, real, E = 0, \|DK∞\| ≤ N.sK, \|K∞ − K₀\| ≤ ballSum(X_i) |
| `KAM/Sharp2/RouteB/G1.lean` | 362 | `G1BodyB` (verbatim), `xinit`, `init_le_caps`, `g1_branch_B`, `g1_v2B` (verbatim), `c1B_min_le_sharpC1` (verbatim) |
| `KAM/Sharp2/RouteB/Frozen.lean` | 139 | `norm_hamComm_le`, `norm_hamComm_sub_le`, `g1_v2B_frozen` (verbatim) |
| `KAM/Sharp2/G1.lean` | 102 | `G1V2.g1Body_mono`, `g1_v2` (verbatim) |
| `KAM/Sharp2/ModConstantsB/Defs.lean`, `Data.lean` | ±1 | DOMPLUS: `CDK := p.sK * CxiL + g * CKt`, `sCDK` (nonneg/mono lemmas unchanged) |
| `KAM/Sharp2/ModStepB/Comp.lean`, `Normal.lean` | ±25 | DOMPLUS: `Kb_sub_le` via the mean value inequality for K on T_{r−δ} (\|DK\| ≤ σ_K) plus `Kt_sub_le` at φθ; one positivity term in `Kt_scale` |
| `scripts/apost_sharp/route_b_lean_mirror.py` | 307 | exact rational mirror of `routeBOk`, `c1B`, `c2B`, `NumB.Wf`, `InitB.Wf`, `NumB.Fits` (new) |
| `KAM.lean`, `KAM/Root/Sharp2.lean` | — | regenerated (`python3 -I scripts/gen_root_imports.py`); `KAM.lean` itself unchanged |

There are 3010 new Lean lines in `RouteB/` and `G1.lean`.

## Approach

### The engine and the stage-indexed data (design signal 1)

B5R's `IsNewton` asks (N1), (N2) for **every** strip r and bite δ ≤ δ_max, with constants `C δ` that depend on the bite only.
Route B's data are indexed by stage:
- λ₀ and the frozen bound on E serve stage 0 only (`stage0`, `ePer`);
- the average certificate at the full bite `bfull s = min (r_s) 1` needs the strip r_s of the stage.

I resolved this without changing any signature:
- **State.** `StB n := ℕ × Bool × torus`: a stage counter, a validity flag and the torus.
- **Step (`schemeB`).** At the matched pair (r_s, δ_s) of a flagged state of stage s, the step is `modNewton`. At every other
  pair the torus is unchanged and the flag is cleared.
- **Admissibility.** Flagged states must satisfy `Good`; cleared ones only `Junk` (regularity, which is trivially preserved).
  `Good` records:
  - r = r_s and μ ≤ μ̄_s = γ δ_s^{τ+1} X_s;
  - the frame bounds by the cap values;
  - the drift ‖⟨𝒯_ab(K)⟩ − ⟨𝒯_ab(K₀)⟩‖ ≤ the Tab cap value;
  - at stage 0, the frozen bound on E.
- **Constants per bite.** `stageC N δ = N.stage (stageOf N δ)`, where `stageOf` is the `Nat.find` of the s < kp with δ = δ_s,
  and kp otherwise (the tail record). This works because δ_s is injective (`δ_inj`).
- **Along the run.** `iterB_spec` shows the iterates are (s, true, K_s), so the engine's admissibility of the iterates is `Good`.

`converge_ratio`'s conclusion gives no bound on μ_s (design signal 2). It is recovered from `Good.μ_le` through `iterB_spec`.

### One stage (`RunHyp.good_step`)

- **Local data at entry to the stage (design signal 3).** `RunBase.loc` builds a `LocHyp` for the stage torus, with the weights
  λ_s and γδ_s^τ. The torsion bound and the average are what this lemma must produce, so `ModStepB.Hyp` cannot be used here:
  it assumes them. `LocHyp` is B4B's `Hyp` without those fields, and B4B's geometry (`Geo.lean`) is copied onto it.
  It gives:
  - `torsion_sub_le`: ‖T − 𝒯_ab‖ ≤ B_sup X on T_{r−δ};
  - `E_le`: ‖E‖ ≤ C_E μ.
- **Reference Neumann (`RunHyp.tors`).** ‖⟨T_s⟩ − ⟨T₀⟩‖ is bounded by three terms:
  - the local part at stage s, B_loc,s X_s ≤ b_F (J1);
  - the drift ‖⟨𝒯_ab(K_s)⟩ − ⟨𝒯_ab(K₀)⟩‖ ≤ m_Tab ≤ β_T − 2b_F (J3 on the Tab cap of `capB`);
  - the local part at stage 0, ≤ b_F (`RunHyp.loc0`, built by `RunBase.locpart` from the J1 condition of stage 0).

  The sum is at most β_T = (σ̂_T − m_T)/(σ̂_T m_T), with m_T = σ_T − μ ≥ ‖⟨T₀⟩⁻¹‖. Then `inv_le_of_ref` gives
  ‖⟨T_s⟩⁻¹‖ ≤ σ̂_T = N.sT.
- **The step.** `modified_stepB` is applied at stage s:
  - `hS` (`Standing`) is built once from the frozen hypotheses at the caps;
  - `hE0` holds at stage 0 from the frozen |E| ≤ e ≤ ePer₀ μ₀ (`NumB.Fits`) and is vacuous later.

  The new state is flagged at stage s+1. Its frame bounds come from the cap updates, and its Tab drift from the C_ab X_s
  increment. The weighted error with the stage-(s+1) weights is ≤ Q_s μ²/(γδ_s^{τ+1}) ≤ μ̄_{s+1} (`mu_succ_le`, using a^τ Q̄_N).

### The run and the frozen form

- **`RunHyp.core`.** `converge_ratio` is applied to `schemeB` with `stageC N` and `capB N σT μ 0`.
  - The ball sum is (J4).
  - `lim_invariance` gives E(K∞) = 0, with ε_s = C_E,s μ̄_s → 0. The step conditions hold along the run (`cond_run`), so
    `LocHyp.E_le` applies at every stage.
  - The derivatives converge by Cauchy estimates on the difference (`tendsto_fderiv_of_uniform`).
- **Run at the actual X₀ (`g1_branch_B`).** The run starts at
  `xinit = e·max(iLt, pN γ̄ δ₀^τ)/(γ²δ₀^{2τ+1})`. This bounds the weighted error of K with the stage-0 weights of `NumB.Fits`.
  - The smallness c1B e/(γ⁴ρ^{4τ}) < 1 gives xinit < X⋆, using γ ≤ γ̄.
  - J1–J4 transfer from X⋆ to xinit by monotonicity (`xS_mono`, `ballSum_mono`).
- **Closeness.** By homogeneity (`xS_scale`), ballSum(X₀) ≤ (X₀/X⋆) ballSum(X⋆) = c2B e/(γ²ρ^{2τ}). No γ̄² appears (audit F6).
- **`g1_v2B`.** By cases on the minimum: the v1 branch uses `g1_sharp`, the route-B branch uses `g1_branch_B`.
- **`g1_v2B_frozen`.** `RefHypB` with `defaultInitB` is built from `frame_bounds`, `norm_hamComm_le` (‖AΩ₀ − Ω₀A‖ ≤ 2M) and
  `norm_hamComm_sub_le` (mean value inequality with ‖D²X_h‖ ≤ M); the certificates come from `hcert`.
- **`g1_v2`.** By cases on min{min{C₁♯, c1A}, c1B}. Route A's branch uses `g1_v2A_frozen` (B9). Route B's branch uses
  `g1_v2B_frozen`, after rewriting with `hτB`, `hρB`, `hρinfB`. In both, C₂ is enlarged through
  `G1V2.g1Body_mono` (it needs 0 < ρ).

## Checks

- **Targeted build.** `nice -n 5 lake build KAM.Sharp2.G1` builds every new module: `Build completed successfully (3332 jobs).`
  The only warnings are unused-variable warnings in files outside this package.
- **Signature probe.** `.drafts/b6_sig.lean`, generated by `.drafts/b6_probe_gen.py` from `APOST-SHARP-V2-SIGNATURES.lean.txt`;
  run with `nice -n 5 lake env lean`.
  1. *Token comparison* (whitespace-insensitive) of the landed sources against the verbatim blocks:
     ```
     RouteB/Data.lean namespace block                IDENTICAL (2095 tokens)
     G1BodyB statement (KAM/Sharp2/RouteB/G1.lean)   IDENTICAL (468 tokens)
     g1_v2B statement (KAM/Sharp2/RouteB/G1.lean)    IDENTICAL (211 tokens)
     g1_v2B_frozen statement (.../RouteB/Frozen.lean) IDENTICAL (282 tokens)
     c1B_min_le_sharpC1 statement (.../RouteB/G1.lean) IDENTICAL (58 tokens)
     g1_v2 statement (KAM/Sharp2/G1.lean)            IDENTICAL (404 tokens)
     ```
     The Data block includes every structure (`NumB`, `NumB.Wf`, `NumB.Cert`, `InitB`, `InitB.Wf`, `RefHypB`, `NumB.Fits`,
     `routeBOk`) and every def.
  2. *Lean re-elaboration.* The verbatim `RouteB/G1.lean` and `G1.lean` blocks are elaborated against the landed library, with
     the declarations renamed `*_sig`:
     - `example : @G1BodyB_sig = @G1BodyB := rfl`;
     - `g1_v2B_sig`, `g1_v2B_frozen_sig` and `g1_v2_sig` are closed by `apply <landed> <;> assumption`;
     - `c1B_min_le_sharpC1_sig` keeps its verbatim body `min_le_left _ _`;
     - the verbatim `initB`, `capB`, `pN`, `c1B`, `c2B`, `c3B`, `defaultInitB` are re-elaborated as `*_sig` and checked with
       `rfl`.

     Result: **no error, no warning**.
- **Axioms** (`#print axioms` in the probe). All 29 lines read `depends on axioms: [propext, Classical.choice, Quot.sound]`:
  ```
  KAM.Sharp2.RouteB.{NumB, NumB.Wf, NumB.Cert, NumB.Fits, NumB.inp, NumB.stage, NumB.ballSum, InitB, InitB.Wf, RefHypB,
    routeBOk, initB, capB, pN, c1B, c2B, c3B, defaultInitB, G1BodyB, g1_v2B, g1_v2B_frozen, c1B_min_le_sharpC1,
    G1BodyB_sig, g1_v2B_sig, g1_v2B_frozen_sig, c1B_min_le_sharpC1_sig}
  KAM.Sharp2.g1_v2, KAM.Sharp2.g1_v2_sig, KAM.Sharp2.G1V2.g1Body_mono
  ```
- **Name clashes.** Every new declaration is in `KAM.Sharp2.RouteB` (or its sub-namespaces `NumB`, `NumB.Wf`, `NumB.Cert`,
  `LocHyp`, `RunBase`, `RunHyp`), in `KAM.Sharp2.G1V2`, or is `KAM.Sharp2.g1_v2`. Grep of every `.lean` file of this branch,
  `sharp-v2` and `main`:
  - no other file opens or names `KAM.Sharp2.RouteB`;
  - no other file opens `G1V2` or declares `g1_v2`.

  (I did not import all of `KAM`: that would build modules this worktree's snapshot lacks.)
- **Lint** (`sh scripts/lint_sources.sh`): `check_lean_modules: PASS (1638 Lean files, 0 comparator configurations)` and
  `FROZEN-ANCHOR GUARD OK`. The ABI scratch reports that the frozen `FixedSunPlanetaryKAM.olean` "does not exist". This is
  environmental and the same as in earlier packages.
- **Roots.** `python3 -I scripts/gen_root_imports.py`; `KAM/Root/Sharp2.lean` adds the ten new modules and is committed.
- **Mirror.** `python3 -I scripts/apost_sharp/route_b_lean_mirror.py` (below).

## Mirror

`scripts/apost_sharp/route_b_lean_mirror.py` evaluates the Lean declarations literally, in exact Fractions:
- the schedule (`bite0R`, `biteSR`, `stripSR`);
- `NumB.inp s`, and every constant of `stepConstsB` through B3B's helpers (parsed from `ModConstantsB/Data.lean` by
  `check_modconstb_v2.py`'s evaluator);
- `stepCondB`, `xSeqR`, `rate`, `wt`, `ballSum`, `capB`, `initB`;
- J1, J1t, J2, J3 over the seven caps, and J4;
- `c1B`, `c2B`, and the Boolean parts of `NumB.Wf`, `InitB.Wf`, `NumB.Fits`.

The threshold is the largest X⋆ with `routeBOk`, and e\* = γ⁴ρ^{4τ}/c1B. The data are design variant B6 of `run_routeB`: L1 data,
c_Th, frequency-specific constants (k = 5), free budgets, anisotropic stage 0, fixed frequency.

| package | design `thresholdB` (B6) | Lean: log₁₀ X⋆ | Lean: log₁₀ e\* | Lean − design | exact certificate X⋆ | b_F | binding just above |
|---|---:|---:|---:|---:|---|---:|---|
| R1 fixed | −12.245 | −1.449 | **−12.224** | +0.021 | 3559/100000 | 1.07e−5 | J2 tail decay |
| H50 fixed | −13.044 | −1.786 | −13.023 | +0.021 | 327/20000 | 9.26e−6 | J2 tail decay |

At the certificate X⋆, `routeBOk` holds in exact arithmetic, and so do `NumB.Wf`, `InitB.Wf` and `NumB.Fits`.
R1 values: c1B = 0.210331, c2B = 0.0176758, δ₀ = 333/140000, λ₀ = 1.02984e−4, ePer₀ = 7.11393e−5.

How N and I are built from the design data:
- **Caps.** N.sK = σ_K − μ/2 (hypothesis `hsK`; the design's `dk_cap`); the other caps are those of `with_caps(D, 1/20)`.
- **Initial values.** I = the measured initial values (σ − μ for Lᵀ, N, Nᵀ). `InitB.Wf` needs I strictly below the caps, and
  J3 needs room.
- **Stage-0 weights.** λ₀ and ePer₀ are the least values `NumB.Fits` allows.
- **Slack.** t_s = 1/10, the design's torsion slack.
- **b_F.** The free local torsion budget, which no constant uses, is set to max_s B_loc,s X_s. That reproduces the design's
  "2 max_s B_loc,s X_s charged to the Tab sum".

Where the 0.021 comes from:
- **e\*.** Lean's p̄ = max{iNt, iLt/(γ̄δ₀^τ)} uses the measured initial values. The design's `per_e` uses the caps, which are
  1.05 × measured. So Lean's p̄ is the design's divided by 1.05, and e\* is larger by log₁₀ 1.05 = 0.021.
- **Constants.** On stages 1–5 the Lean and design constants are exactly equal: `sQ`, `sCDK`, `sBloc`, `sCBb`, `sCNb`,
  `sCNbT`, `sCab` all have ratio − 1 = 0. At stage 0 only Q and B_loc differ (relative 1.1e−5, 6.8e−6). The cause is
  ePer₀ = 1.05/p̄_design, the least value `Fits` allows given the measured I; the design uses 1/p̄_design. Stage 0 does not bind.

No Lean rational mirror (`NumBQ.ok_sound`, as in PLCERT's `MirrorQ.lean`) was written; see "Uncertainties".

## Uncertainties

- **No certified Lean instance.** No Lean-side decidable mirror of `routeBOk` exists yet, so no R1 instance of `g1_v2B` /
  `g1_v2` is certified in Lean. The Python mirror is exact but untrusted. At τ = 1 every quantity is rational, so a
  `MirrorQ`-style `NumBQ` with `cast_*` lemmas would work. It would mean about 60 helper casts.
- **The numbers in the mirror are design numbers.** The small-divisor constants (`c_freq`, classical) and the sampled sups are
  inputs to the mirror. In the theorem they are the hypotheses `N.Cert` and `RefHypB`.
- **Fixed frequency only** (`hfix`). The iso fields of `NumB` and the frequency cap are unused here; B7 will instantiate them.
- **Duplicated geometry.** `LocHyp` duplicates about 600 lines of B4B's `Hyp`/`Geo` (renamed). A later refactor could make
  `ModStepB.Hyp` extend `LocHyp`, but that edits B4B's files, which this package's additive rule forbids.
- **Engine consistency check.** J1t is checked at X = X_kp; every clause of `stepCondB` is monotone in X ≥ 0
  (`stepCondB_anti`), so this is the same as checking all of [0, X_kp].

## Suspected errata, deviations and design signals

1. **B3B's `scripts/apost_sharp/check_modconstb_v2.py` now reports `R1 cross-check: MISMATCH`.** This is not a Lean defect.
   Since SHARP2-DOMPLUS, `thresholds_v2.stageB` takes `sK − μ/2` by default (`dk_cap`, "the |DK| cap of the theorem is
   sigma_K - mu/2"). The checker's `mkp` passes `sK = D["sK"]`. With `dk_cap=False` all 112 constant comparisons are equal
   again (checked). Fix: `"sK": D["sK"] - D["mu"] / 2` in `mkp`, or pass `dk_cap=False`. I did not edit the script (additive
   rule).
2. **Design signal (engine, B5R).** `IsNewton` is bite-uniform, while route B's data are stage-indexed: λ₀, ePer and the
   full-bite certificate at `min (r_s) 1`. I resolved this with the flagged state `ℕ × Bool × torus`. No signature changed.
3. **Design signal (engine, B5R).** `converge_ratio`'s conclusion gives no bound on μ_s along the run. The invariance of the
   limit needs μ_s → 0. I recovered it from the admissibility (`Good.μ_le`) through `iterB_spec`. A field "μ_s ≤ γδ_s^{κ+1}X_s"
   in the engine's conclusion would remove this step.
4. **Design signal (B4B).** At entry to each stage, the torsion needs a version of the geometry that does not already assume
   the torsion bound: `LocHyp`, a renamed copy of B4B's `Hyp`/`Geo`. See "Uncertainties".
5. **Deviation (orchestrator ruling, SHARP2-DOMPLUS).** `CDK := p.sK * CxiL + g * CKt` (was `sKt * CxiL`), in
   `ModConstantsB/Defs.lean`, `Data.lean` and the displacement proof in `ModStepB/Comp.lean`. These existing files were edited
   with permission.
6. **Lean-only free number b_F.** The design has no b_F; it charges 2 max_s B_loc,s X_s to the Tab sum. In Lean, b_F is a
   number of `NumB`: the J1 clause `B_loc X ≤ b_F` plus the −2b_F in `capB`'s Tab entry. A user must choose it; the optimum is
   max_s B_loc,s X⋆_s. Equivalent at the optimum; not an erratum.
7. **Design mirror is slightly conservative.** The design's stage-0 coefficient `per_e` uses the caps, where the theorem
   (`NumB.Fits`, `c1B`) uses the initial values. It costs 0.021 orders. Not a defect.

No defect found in the pinned blueprint or in the signature file: every B6 signature was provable as written.
