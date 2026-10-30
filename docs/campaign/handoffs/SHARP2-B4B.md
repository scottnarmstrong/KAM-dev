# SHARP2-B4B handoff: the repaired modified Newton step (route B) and the torsion against the initial torus

Branch `sharp-b4b`, from `sharp-v2` at `ba8e923f`, with `sharp-b3b` merged (`905e7014`, the merge the brief allows).
Ten package commits, `816cd6c8` to `b824ea3e`. No file outside the new ones was modified except the regenerated `KAM.lean`.

Results:
- **`TorsionRef`**: every declaration is proved verbatim (signature probe below).
- **`modified_stepB`**: proved under the name `modified_stepB`, with two signature changes. Both are design signals; see "Deviations".
  1. **Stage 0.** The hypothesis `hE0` is added: `p.stage0 = true → |E| ≤ p.ePer · μ on T_r`. This is the audit finding AUDIT-SHARP2-FIX-iso-1 F1 and follows the orchestrator's ruling.
  2. **Standing data.** The five hypotheses `hopen htransl hholo hper hreal` are replaced by `hS : KAM.Apost.Standing n τ M σK σB σT 𝔅 h ω γ₀`, as SHARP2-B2 did. The cause is that the library proves the regularity and the cohomological equation of `𝓡` only for Diophantine `ω`.

## Files

All modules: copyright, `module`, `public import`, module docstring, `public section`. No line exceeds 100 characters and no file
exceeds 800 lines.

| File | Lines | Content |
|---|---|---|
| `KAM/Sharp2/TorsionRef.lean` | 217 | `hamComm`, `torsionAB`, `torsionABAverage`, `norm_torsionAB_le`, `norm_torsion_sub_torsionAB_le`, `inv_le_of_ref`, `norm_lagrangeMat_comp_le` (verbatim) |
| `KAM/Sharp2/ModStepB/Defs.lean` | 142 | `modXiN0`, `modXiN`, `modKtilde`, `modXiL`, `modNewton` (verbatim); bridges `modXiN0_eq`, `modXiN_eq`, `modXiL_eq` to v1's `triXi0`, `triXiN`, `triXiL` (`cohR_neg`: `𝓡(-g) = -𝓡g`) |
| `KAM/Sharp2/ModStepB/Hyp.lean` | 309 | `ModStepB.Hyp`, the bundled hypotheses; `mu`, `xX`; scale facts; caps; unpacked step conditions |
| `KAM/Sharp2/ModStepB/Geo.lean` | 508 | current torus on `T_{r-δ}`: `Ω_K`, `Ω_N` (B2), `E` (B2 recovery), per-column `DE` bound (FH24 route), `(Nᵀ Ω₀ DE)ᵀ`, `W`, `T - 𝒯_ab ≤ B_sup X`, `∂_ω N ≤ C_dN`, `X_N ≤ C_XN` |
| `KAM/Sharp2/ModStepB/Normal.lean` | 414 | normal correction: `𝓡ηᴺ` (sup and full-bite real bounds), `ξᴺ₀ ≤ C_0 μ`, `ξᴺ ≤ C_ξN μ`; `K̃` holomorphic/primary/real, `|K̃ - K| ≤ C_K̃ μ`; `D(N ξᴺ)` columns, `L̃ - L`, `L̃ ≤ σ̃_K` |
| `KAM/Sharp2/ModStepB/Inter.lean` | 272 | `Ẽ = E + X_N ξᴺ + Δ²X + N ηᴺ`, `|Ẽ| ≤ C_Ẽ μ`, `η̃ᴺ` identity and `≤ Q̃_N μ²/δ`, `Ω_K̃` on `T_{r-2δ}` |
| `KAM/Sharp2/ModStepB/Comp.lean` | 189 | `gᴸ ≤ C_gL μ`, `ξᴸ ≤ C_ξL μ/(γδ^κ) ≤ ϑ_ξ δ`, `K̄ = K̃∘(id+ξᴸ)` holomorphic/primary/real, `|K̄ - K| ≤ C_ΔK μ/(γδ^κ) < β` |
| `KAM/Sharp2/ModStepB/Frames.lean` | 287 | on `T_{r-3δ}`: `L̄ - L`, `Ḡ`/`B̄` (Neumann), `N̄ - N`, `N̄ᵀ - Nᵀ`, `𝒯_ab(K̄) - 𝒯_ab(K) ≤ C_ab X` |
| `KAM/Sharp2/ModStepB/NewErr.lean` | 422 | `L̄ = (L̃∘φ)(I+Dξᴸ)`, `Ē = Ẽ∘φ - (L̃∘φ) g`, `η̄ᴺ ≤ Q̄_N μ²/δ`, tangential decomposition `Nᵀ Ω₀ Ē ≤ Q'_L μ X`, crude `η̄ᴸ` bound |
| `KAM/Sharp2/ModStepB/SelfCons.lean` | 239 | L10: pointwise recovery, `|Ω_K̄| ≤ (1+nϑ_ξ)² C_Ω Q̃_N g X²`, self-consistent `η̄ᴸ`, `η̄ᴸ ≤ Q_L μ²/(γδ^{κ+1})` |
| `KAM/Sharp2/ModStepB.lean` | 136 | `modified_stepB` |
| `KAM.lean` | +11 | regenerated (`python3 -I scripts/gen_root_imports.py`) |

There are 3135 Lean lines in total. The design estimated about 1500.

## Approach

Every intermediate lemma takes `H : ModStepB.Hyp p …` together with the standing data `hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀`. The final theorem rebuilds `hS` at the caps from the user's `Standing`; its `σ`'s are inert positivity parameters.

Constants are B3B's helpers (`sCΩ p`, `sCE p`, …, `stepConstsB_eq` is `rfl`), with their nonnegativity lemmas `nn_*`. The actual bite `δ ≤ p.δ` and scale `γ ≤ γ̄` enter through the scale facts:

| Fact | Lean name |
|---|---|
| `γδ^κ ≤ g` | `Hyp.gd_le` |
| `γδ^{κ+1} ≤ g₁` | `gd1_le` |
| `μ/δ = γδ^κ X ≤ g X` | `mu_div_δ`, `mu_div_δ_le` |
| `μ ≤ g₁ X` | `mu_le` |
| `μ/(γδ^κ) = δX` | `mu_div_gd` |

### Reused from earlier packages

- **v1 (`KAM.Apost`, `KAM.Sharp`, SHARP-A4):**
  - `triangular`: regularity, periodicity, the two cohomological equations and reality of `ξᴺ`, `gᴸ`, `ξᴸ`. The step objects coincide with the triangular ones (`Defs`).
  - `frame_basic`, `periodicity`, `exactness`, `torsion_identity` (`T` as torsion polynomial, `∂_ω N`).
  - Frame identities `fi_LtON`, `fi_NtOL`, `fi_NtON`, `fi_LtOXN`, `fi_QP`, `fi_QE`, `fi_symDefect`; `FrameSharp.linMat_transpose`.
  - Tools: `neumann_ratio`, `norm_mul_sub_mul_le`, `tAB`/`tF`/`tC`, `torsionPoly_split`, `norm_W_le`, `norm_tC_le`; `taylor_iteratedFDeriv`; `cauchy_strip`.
- **B2:** `norm_lagrangeMat_le_etaN_of_standing`, applied to `K` and to `K̃`; `norm_invarianceError_le_eta`; `frame_surj`, `frame_proj`.
- **B1:** `SDConst`.
  - `sol` at the bite `δ`, at the split bite `sδ`, and on `T_{r-δ}` for `ξᴸ`.
  - `real` at the full bite `b`, for `⟨T 𝓡ηᴺ⟩`.

### Points where the blueprint needed an interpretation

1. **`DE` on `T_{r-δ}`.**
   - The bounds `|Ω_K|, |Ω_N| ≤ q` are available only on `T_{r-δ}`, so `|E| ≤ C_E μ` is known only there, and plain Cauchy on `E` would lose a strip.
   - I used FH24's route, `DE = -P S⁻¹ (Dη + (DR) E)` with `R = -Ω₀ Pᵀ Ω₀`, `R P = S = I - Ω₀ E_sym` and `|S⁻¹| ≤ 1/(1-q)`.
   - With Cauchy on `η` and on `R` from `T_r`, this gives a per-column bound `(C_DE/n) μ/δ`, which is the stated constant divided by `n`.
   - The per-column form is needed: it gives both `|DE| ≤ n` and `|(DE)ᵀ| ≤ 2n`, and the second is used by `C_dN` and by `w`. See erratum E1.
   - At stage 0, Cauchy on `E` from `T_r` uses `hE0`.
2. **`L̃ - L` ("Cauchy on `N ξᴺ₀` and Corollary rc on `N u`").**
   - `N u` is handled with the solution clause at the split bite `sδ` on `T_{r-sδ}`, then Cauchy with the bite `(1-s)δ`. This gives exactly `C_DL̃ = n σ_N (C_0 + c₁)`.
   - A product-rule route would add a `c` term.
3. **L10.**
   - The self-consistent bound is proved pointwise: recovery for `K̄` at one point (`norm_invarianceError_le_eta_pt`, B2's proof at a point). So no supremum `A < ∞` is needed.
   - `Ω_K̄` is the pullback `Dφᵀ (Ω_K̃∘φ) Dφ` (`norm_lagrangeMat_comp_le`), with `|Dφ|, |Dφᵀ| ≤ 1 + n ϑ_ξ`, `Ω_N̄ = B̄ Ω_K̄ B̄`.
4. **`ηᴸ - T ξᴺ` cancelling against `∂_ω ξᴸ` (step `st-etal`).** This is the identity `NtO_Et_eq`: `Nᵀ Ω₀ Ẽ - Nᵀ Ω₀ L g = Nᵀ Ω₀ Δ²X + Ω_N ηᴺ`, from `Nᵀ Ω₀ X_N = T` (`torsion_eq_mat`) and `Nᵀ Ω₀ L = I`.

## Deviations (design signals) and the corrected statement

1. **Stage 0: the verbatim `modified_stepB` is false.**
   - With `p.stage0 = true` the constants use `C_E = min {C_E⁰, e/μ₀}` and `C_DE = min {C_DE⁰, n·e/μ₀}`, but the step assumes only the bounds on `ηᴸ`, `ηᴺ`.
   - I found this independently: with `n = 1` and `ePer = 0` the claim reduces to `T = 𝒯_ab`, which fails.
   - The audit AUDIT-SHARP2-FIX-iso-1 F1 gives the same counterexample (`h = ωI + I²/2 + ε cos 2πθ`).
   - Fix, per the orchestrator's ruling: hypothesis `hE0 : p.stage0 = true → ∀ θ ∈ T_r, ‖invarianceError h K ω θ‖ ≤ p.ePer * μ`, under the name `modified_stepB`.
   - It is satisfiable at stage 0: with `εL = λ₀ μ₀` and `εN = γ δ₀^κ μ₀` one has `μ = μ₀`, and `|E| ≤ e = (e/μ₀) μ₀`. It is vacuous when `stage0 = false`.

2. **Standing data replaces `hopen htransl hholo hper hreal`.**
   - **Why it is needed.**
     - The step needs `𝓡ηᴺ` and `𝓡gᴸ` holomorphic, periodic and real, and the equations `∂_ω 𝓡g = g`.
     - In the library these are `differentiableOn_cohSolution`, `fderiv_cohSolution` and `Apost.cohomological`/`triangular`, and they assume `IsDiophantine γ τ ω`. `SDConst` gives only bounds.
     - The blueprint's Proposition `bp:p2s2:step` does assume "`ω ∈ Dio_{γ,τ}`"; the Lean signature dropped it.
     - Every frame identity, `exactness`, `torsion_identity`, `frame_basic`, `periodicity` and B2's Lagrangian lemma are stated under `Standing`.
   - **What `hS` adds.** Beyond the five standing hypotheses (which it contains verbatim), `hS` adds `n ≥ 2`, `τ ≥ n-1`, `‖X_h‖, ‖DX_h‖, ‖D²X_h‖ ≤ M` on `𝔅` and `ω ∈ Dio_{γ₀,τ}`.
   - **Cost to the consumer.** B6 builds this from the frozen G1 hypotheses, exactly as B9's route A does for `step_A`. `Standing`'s `σ`'s and `γ₀` are free.
   - **The precedent.** SHARP2-B2's `norm_lagrangeMat_le_etaN_of_standing`, adopted by SHARP2-FIX.
   - **A `Standing`-free form (`n ≥ 1`) is provable in principle.**
     - `SDConst.apriori` applied to single modes gives a divisor lower bound, hence summability and hence the regularity of `𝓡`.
     - The library lemmas would then need weak-hypothesis copies.
     - I estimate about 1000 more lines, and did not do it.
   - **Probe.** The verbatim signature with `hS` and `p.stage0 = false` added (and the five hypotheses kept) is closed by `modified_stepB` (`modified_stepB_sig0` in the probe below).

## Checks

- **Targeted builds:** one niced `lake build` at a time.
  - `nice -n 5 lake build KAM.Sharp2.TorsionRef`: ✔.
  - `nice -n 5 lake build KAM.Sharp2.ModStepB`: `Build completed successfully (3269 jobs)`.
  - Each new file elaborated by `lake env lean` gives no messages: no warnings, no `sorry`.
  - Every proof runs at default heartbeats; the largest file elaborates in about 10 s.
- **Signature probe** (`.drafts/b4b_sig.lean`). The verbatim TorsionRef and ModStepB blocks of `APOST-SHARP-V2-SIGNATURES.lean.txt` are extracted programmatically, with declarations renamed `*_sig`:
  - the four TorsionRef theorems are closed by the landed ones;
  - `example : @hamComm_sig = @hamComm := rfl`, and likewise for `torsionAB`, `torsionABAverage`, `modXiN0`, `modXiN`, `modKtilde`, `modXiL`, `modNewton`;
  - `modified_stepB_sig0` (the verbatim step plus `hS` and `hs0 : p.stage0 = false`) is closed by `modified_stepB … (fun h0 => by simp [hs0] at h0) …`;
  - result: no errors, only "variable not referenced" warnings for the five redundant hypotheses.
- **Axioms** (from the probe):
  ```
  'KAM.Sharp2.norm_torsionAB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Sharp2.norm_torsion_sub_torsionAB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Sharp2.inv_le_of_ref' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Sharp2.norm_lagrangeMat_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Sharp2.modified_stepB' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Sharp2.modified_stepB_sig0' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- **Lint** (`sh scripts/lint_sources.sh`):
  - `check_lean_modules: PASS (1544 Lean files, 0 comparator configurations)` and `FROZEN-ANCHOR GUARD OK`.
  - Two failures remain, neither from this package:
    - "Lean files over 1500 lines: KAM.lean". It was already 1547 lines on `sharp-v2` before this package and is 1558 now. It is generated; I may not edit it or its generator.
    - ABI scratch: the frozen object `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean` "does not exist". This is environmental and is the same as in earlier packages.
  - An earlier hit, "forbidden admit", was the English word "admit" in a docstring of `Frames.lean`; it has been reworded.

## Uncertainties

- The theorem is for fixed frequency only (`hfix : p.iso = false`), as signed. The iso bordered step (B7) is not covered: the iso fields of `StepInB` and the frequency rate `Cnu` are unused.
- `torsionABAverage` is defined verbatim but nothing about it is proved. The reference Neumann `inv_le_of_ref` is stated for arbitrary matrices; B6 instantiates it with `⟨T_s⟩`, `⟨T_0⟩`.
- **L10 (AUDIT-SHARP2-FIX-iso-1 passes it).**
  - The self-consistent bound is proved only on `T_{r-3δ}`.
  - It uses `|Ω_K̃|` on `T_{r-2δ}` at `φ(θ)` and recovery with the caps `σ_K`, `σ_N` (as in `sCEL`, `sCEN`).
  - It needs the cap room for `L̄` and `N̄`, which `hroom` provides.

## Suspected errata and blueprint remarks

| # | Location | Quoted text | Why it is wrong, or what it needs |
|---|---|---|---|
| E1 | `blueprint/parts/p2s2-modified.tex`, Prop. `bp:p2s2:step`, step `st-int` (line 273); also `w` in Def. `bp:p2s2:constantsB` | "`∂_ω N` is bounded by `C_dN` when `\abs{DE}\le n`" | `C_dN` (term `(σ_{Lᵀ} M₁ + 2n) σ_K`) and `w` (term `2n σ_K`) need `\|(DE)ᵀ\| ≤ 2n`. An operator-norm bound `\|DE\| ≤ n` gives only `\|(DE)ᵀ\| ≤ 2n²`. The constants are right once recovery is used in its per-entry form, `\|∂_j E_s\| ≤ (C_DE/n) μ/δ`, which the same proof gives; Lemma `bp:p2s2:recovery` should state that form. |
| E2 | same step, line 274 | "`L^\top\Omega_0X_N=(DE)^\top\Omega_0N`" | The sign is `-(DE)ᵀ Ω₀ N` (Lean `fi_LtOXN`). Norms are unaffected. |
| E3 | `APOST-SHARP-V2-SIGNATURES.lean.txt`, `modified_stepB` | (no Diophantine or `Standing` hypothesis) | The blueprint's step assumes "`with ω∈Dio_{γ,τ}`". The signature omits it, and without it the library cannot give the regularity or the cohomological equation of `𝓡` (Deviation 2). |
| E4 | same signature, stage 0 | (no `E` bound) | False for `stage0 = true` (Deviation 1; audit iso F1). |

## What remains

- **B6.**
  - Supply `hS` from the frozen G1 hypotheses, as in B9's `RouteA/G1.lean`.
  - Supply `hE0` at stage 0: `εL = λ₀ μ₀`, `εN = γ δ₀^κ μ₀` and the frozen `|E| ≤ e`.
  - Use `inv_le_of_ref`, `norm_torsionAB_le` and the conclusions `𝒯_ab(K̄) - 𝒯_ab(K) ≤ C_ab X` and `T - 𝒯_ab ≤ B_sup X` for the `Tab` cap and the reference torsion.
- **B7 (iso).** The bordered version of this step.
- **Optional.** The `Standing`-free (`n ≥ 1`) form of the step, if wanted (Deviation 2).
