# W8-FINAL handoff

Package W8-FINAL (blueprint `blueprint-W/parts/w8-assembly.tex`, `bpW:w8`), worktree `/root/code/KAM-inp-wpr`,
branch `inp-w8f` (base: W6-TORI `3a236d01` merged with W8-ASM `inp-w8a`; at the orchestrator's request
`inp-w6t @ d88a5e0a` was merged in (`cc27e845`); `inp-w5aa` (`71852201`) was already contained). Off the frontier:
source-faithful infrastructure used by several nodes; the dependency graph is still being built.

**Result: `KAM.Wave.nlw2_proof` proves the frozen statement of `KAM.Wave.nlw2` verbatim**
(module `KAM/Wave/Assembly/Nlw2Proof.lean`), with `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
No module imports `KAM.Frozen.Wave.Theorems.Nlw2` or any `KAM.Provider.*`; `KAM/Provider/*`, `KAM/Frozen/**`,
`manifest/**` untouched. No `sorry`/`axiom`/`admit`/`opaque`/`unsafe`, no heartbeat or other budget override.

## Statement identity check (scratch file, deleted, never committed)

`.drafts/W8Check.lean` importing `KAM.Wave.Assembly.Nlw2Proof` and `KAM.Frozen.Wave.Theorems.Nlw2`:
```
example : type_of% @KAM.Wave.nlw2 := @KAM.Wave.nlw2_proof          -- elaborates
example : (type_of% @KAM.Wave.nlw2) = (type_of% @KAM.Wave.nlw2_proof) := rfl   -- elaborates
run_meta … (getConstInfo ``KAM.Wave.nlw2).type == (getConstInfo ``KAM.Wave.nlw2_proof).type
  -- output: "syntactically equal types: true; levels [] []"
#print axioms KAM.Wave.nlw2_proof
  -- 'KAM.Wave.nlw2_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(checked with `w_lean.sh`; the file was then deleted.)

## Step 0

* `ShellIter`: `w8ShellToriKam_of_stepSmooth hS hSm H` → **`w8ShellToriKam H`** (W6's unconditional
  `W6PrepHyp.w6ToriKam`, the replacement listed in `W6-TORI-handoff.md`); no other W8 module used an
  `*_of_stepSmooth` helper.
* `ShellIter`: the shell family now uses W6-TORI's blueprint-constant family `w6WaveFamilyJ` and exclusion
  `w6ExclusionJ`; `w8_w6General` states `bpW:w6:freq-lip` with `ε₁ = 3γα_n`, `ε₂ = 4ε_{0,n}` (the blueprint's),
  i.e. W8-ASM deviation D2 is removed. `w8_shell_defect`/`w8_density` rebuilt unchanged.
* All `KAM/Wave/Assembly/*` rebuilt on the merged base.

## Labels and declarations

| label | status | module | declarations |
|---|---|---|---|
| `shell-data` (iii), (iv) (source instance) | done | `ShellTorus` | **`w8HW hm n : W8ShellPrep m hm n (w6InP m hm) (w6InX m hm)`** (prep-step hypotheses of shell `n` for W5's initial perturbation, via W6-TORI `w6PrepHyp_initial` + W8-ASM `w8_shellData_init`, `w8_shellData_prep`); `w8_shellPi_bounds`, `w8_shellRho1`, `w8_toriData` |
| `w6-general` (tori) | done | `ShellIter`, `ShellTorus` | `w8ShellToriKam` (KAM coords); local macro `w8tori hm n` = `(w8HW hm n).w6Tori …` (Birkhoff coords, `bpW:w6:tori` (i)–(v)) |
| `shell-iter` (`Ψ̃^{(n)}_ξ`) | done | `ShellTorus` | `w8Psi hm n ξ θ = Ψ̃^{(n)}_ξ(θ)`, `w8TK`, `w8Phase` (`θ+X`), `w8Xang` (`X`), `w8Yact` (`y`), `w8XC` (`X` on the strip) |
| `torus-shape` | done | `ShellTorus`, `ShellEmbed` | (i) **`w8_torusShape_bounds`**, `w8TK_close`; (ii) **`w8_torusShape_real`**, **`w8_torusShape_coord`**, `w8TK_real`, `w8XC_real`, `w8_coord_true`; (iii) **`w8Xang_periodic`**, `w8XC_periodic`, `w8Psi_periodic`; (iv) **`w8_torusShape_deriv`**, **`w8Xang_lipschitz`**; (v) **`w8Psi_ball`**; `w8_shell_consts` |
| `Kshell` | done (instance) | `ShellEmbed` | `w8AA` (`𝒜_ξ = aaMap 1 1`), **`w8Kshell_eq`** (`K^{(n)}_ξ = w8KOfBirk m hm (w8Psi hm n ξ)`, rfl) |
| `shell-embedding` | done | `ShellEmbed` | **`w8_shellEmbedding`**; `w8Kshell_analytic` (se-an), `w8Kshell_injMod` (se-inj), `w8_phase_int_of_eq`, `w8Kshell_leftInv`, `w8Kshell_leftInv_hasFDerivAt`, `w8Kshell_fderiv_injective` (se-der) |
| `shell-close` | done | `ShellClose` | **`w8_shellClose`**; `w8_shellDist` (sc-tan, sc-dist), `w8_gammaR_bounds`, `w8_gamma_arith` (sc-gamma), `w8_tan_arith`, `w8_tanDiff_hasSum`, `w8_tanDiff_norm_le`, `w8_tan_weights`, `w8_coord_diff_le`, `w8_birkPi_linearTorus` |
| `shell-inv` | done | `ShellFamily` | (i) **`w8_shellInv`** (via W8-ASM `w8_shellInv_of_birk` + `bpW:w6:tori` (iii)), `w8ShellNu_eq`, `w8_birkEmbed_comp`; (ii) **`w8_shellInvCont`** |
| `patch-cont` (K part) | done | `ShellFamily` | **`w8_patchContK`**; `w8HF` (source family), `w8_patch_of_mem` |
| `injective` | done | `ShellFamily` | **`w8_injective`** (via W8-ASM `w8_injective_of_pieces`); `w8_shell_freq_eq` (in-birk, in-freq), `w8TK_continuous_real`, `w8_patchEmb`, `w8_patchInv` |
| `nlw2-proof` | **done** | `Nlw2Proof` | **`KAM.Wave.nlw2_proof`**; `w8_patchClose` (p-close, p-size), `w8_tn_le_two_sum`, `w8_close_arith`, `w8_size_arith` |

Witnesses (frozen order): `r₀ = w8R0 m hm (w8Upstream m hm)`, `C` = the constant of W2's `reconWave_clause5`
(`= max 1 M_m * C₃`, `C₃ = w8C3 = 4√c_A`), `τ = w8Tau = 24`, `η = w8Eta m hm (w8Upstream m hm)`,
`Γ = w8GammaW (w8HF hm)`, `ν = w8NuW (w8HF hm)`, `K = w8KW w8AA (w8HF hm)`.

## Not done

Nothing in the package. (W8-ASM's helpers `w8ShellPrep_of_initial`, `w8_famBound_sharp_of_initial` are no longer
used: `w8HW` uses W6-TORI's `w6PrepHyp_initial` directly; they remain as named helpers.)

## AUDIT FOCUS

1. **`nlw2_proof` statement**: copied from the frozen file; syntactic `Expr` equality checked (above).
2. **`w8HW`** (no premise): all hypotheses of `w6PrepHyp_initial` come from `w8_shellData_init`
   (`hPar`, `hρ₁`, `ε_in(1 + 4λ/ρ_ξ) ≤ ε^♯_n`; `w8EpsIn`/`aaEpsIn`, `w8cA`/`aaCA`, `w8Rho1 m`/`birkRho1 m 1` are
   definitionally equal) and `w8_shellData_prep`.
3. **`w8Kshell_fderiv_injective`** (deviation D1 below): `x = G ∘ K` with `G = Π ∘ Γ_{-1} ∘ 𝒵_ℝ`
   (`birkGammaR_inv`), `G` differentiable at `K(θ)` (`birkGamma_hasFDerivAt` at `t = -1`,
   `40C_F‖𝒵K(θ)‖² < 1` from `‖K‖ ≤ (10/9)√2‖x‖`, `‖x‖² < ρ₁²/2`); the `+i` coordinate times
   `e^{2πiφ}` is real (`= w_l √(ξ_i + y_i)`), so `Re(h_i + DX_i h) = 0`; `‖DX(θ)‖ ≤ 1/2` (Cauchy).
4. **`w8_shellDist` constants**: `|Δ_{±i}| ≤ (1/4 + 2π)√t e` (D2), `‖tan diff‖ ≤ 22·` (`2(e² + 4e⁴) ≤ 484`),
   normal part `≤ r e ≤ √t e`; `22(1/4 + 2π) + 1 ≤ 162` (`π < 3.15`).
5. **`w8_gamma_arith`** (D3): `‖Γ^ℝx - x‖ ≤ ‖𝒵ψ‖ ≤ √2·6√2 C_F‖x‖³`, `‖x‖² ≤ 2c_A t`,
   `√2 t^{3/2} ≤ t^{33/64}` (`t^{63/64} ≤ t^{1/2}`, `√(2t) ≤ 1`).
6. **`w8_patchClose`**: `t_n ≤ 2(I₀ + I₁)` from `shellSet_norm_ge` (`t_{n+1} ≤ ‖I‖ ≤ I₀ + I₁`);
   `E₇ t^{33/64} ≤ 2^{33/64} E₇ r^{1/32} r` (`r = √(I₀+I₁)`); `2ρ_n ≤ C₃ r`.
7. **`w8_shellInv`**: W6's (iii) is `ι_{p→p-1}DΨ̃ν = X_Λ + ι_{p+1→p-1}(X_Ḡ + X_{G^{nor}} + X_K)`; W8-ASM's
   reduction wants `X_Λ + ι_{p→p-1}(birkRestField)`, `birkRestField = Σ ι_{p+1→p}(…)`; matched by
   `w8_birkEmbed_comp` (`ι_{p→p-1}ι_{p+1→p} = ι_{p+1→p-1}`); `ν^{(n)}_* = w6NuStar` (`w8ShellNu_eq`).
8. **Step 0 family switch** (`w6WaveFamilyJ`): `w8_density` consumes only `w8_w6General`'s exclusion and the
   family's admissibility.
9. Inherited from W8-ASM (unchanged): `τ_E = id`, `w8KOfBirk` totalized by `0` off `B^E_{r₁}` (never used off
   it: `w8Psi_ball` gives `𝒵⁻¹Ψ̃(θ) ∈ B^E_{r₁}` for every real `θ`).

## Deviations (none adds a premise; none strengthens a hypothesis)

* **D1** (`shell-embedding`, Step `se-der`): injective derivative via the left inverse
  `𝒵⁻¹Γ_{-1}𝒵Γ^ℝ = id` (W3 `bpW:w3:gamma-real` (iii)) instead of the invertibility of `DΓ`
  (`bpW:w3:flow` (iii)) and `DΓ ∘ ϱ = ϱ ∘ DΓ`; the vanishing of the bracket's imaginary part is obtained from
  the reality of `Ψ̃_{+i}e^{2πiφ_i} = √(ξ_i + y_i)` along the line (no differentiability of `√(ξ_i+y_i)`
  needed). Same conclusion.
* **D2** (`shell-close`, Step `sc-tan`): `|y_i|/√ξ_i ≤ (ξ_i/4)e/√ξ_i ≤ √t_n e/4` (from `r_n² ≤ α_n/4 < ξ_i/4`)
  instead of `r_n²/√α_n ≤ √t_n`; constant `(1/4 + 2π)` instead of `(1 + 2π)`; final constant `162` unchanged.
* **D3** (`shell-close`, Step `sc-gamma`): W3's Lean form gives `ψ` with `𝒵Γ^ℝx = 𝒵x + ι𝒵ψ`, so the bound
  passes through `‖𝒵ψ‖ ≤ √2‖ψ‖`; the extra `√2` is absorbed (`√2 t^{3/2} ≤ t^{33/64}`); `E₆`, `E₇` unchanged.
* **D4** (`torus-shape` (ii), (iii)): reality of `X`, `y` at real `θ` read from W6's `StepReal(Φ_PΦ_*(θ))`
  (`bpW:w6:tori` (i) in KAM coordinates), and periodicity of `X` from `Φ_PΦ_*(z + e_i) = Φ_PΦ_*(z) + τ_i`,
  instead of the blueprint's phase arguments through `ϱΨ̃ = Ψ̃`; same statements. `torus-shape` (iv) is stated
  for the complex derivative `DX(θ)` at real `θ` (`‖DX(θ)‖ ≤ 128e/7 ≤ 1/2`) plus the real `½`-Lipschitz bound.
* **D5** (`nlw2-proof`, witness `C`): taken as the `C` produced by `reconWave_clause5` (its first conjunct,
  `C = max 1 M_m * C₃`, discarded), i.e. the blueprint's `C`.
* `torus-shape` is split into several theorems (one per clause) rather than one conjunction.

## Suspected errata

None. Remarks (not defects): `sc-tan`'s `r_n²/√α_n = t_n^{97/128}` is correct but the route via `α_n ≤ ξ_i`
(D2) is simpler; `sc-gamma`'s `‖·‖_E ≤ ‖·‖_{E_{1,2}}` is fine, W3's Lean interface just exposes `ψ` through `𝒵`.

## Checks

* Gate builds (`/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpr <Module>`, one per call):
  `KAM.Wave.Assembly.ShellIter`, `…Clauses`, `…InjAssembly`, `…ShellInv`, `…ShellTorus`, `…ShellEmbed`,
  `…ShellClose`, `KAM.Wave.Recon2.Main`, `…ShellFamily`, `…Nlw2Proof` (last: `✔ [3795/3795] Built
  KAM.Wave.Assembly.Nlw2Proof`, `Build completed successfully (3795 jobs).`); no warning in the new files.
* `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpr`: **exit 0**; tail
  `check_lean_modules: PASS (4037 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (177 frozen declarations of KAM; …)`.
* `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-wpr
  KAM.Wave.Assembly.{ShellTorus,ShellEmbed,ShellClose,ShellFamily,Nlw2Proof,ShellIter}`:
  `short-name check OK (no reused public short name)`, exit 0.
* `KAM/Root/Wave.lean` regenerated by `scripts/gen_root_imports.py` (5 new modules), not hand-edited.
* Line counts: ShellTorus 375, ShellEmbed 333, ShellClose 343, ShellFamily 213, Nlw2Proof 205, ShellIter 280.
* `#print axioms` (scratch via `w_lean.sh`, deleted), all `[propext, Classical.choice, Quot.sound]`:
  `nlw2_proof`, `w8HW`, `w8_torusShape_bounds`, `w8_torusShape_real`, `w8_torusShape_coord`, `w8Xang_periodic`,
  `w8Psi_periodic`, `w8_torusShape_deriv`, `w8Xang_lipschitz`, `w8Psi_ball`, `w8_shellEmbedding`,
  `w8_shellClose`, `w8_shellInv`, `w8_shellInvCont`, `w8_patchContK`, `w8_injective`, `w8_w6General`,
  `w8ShellToriKam`.

## Design signals

One: the first version of `w8_shellClose` hit the default-heartbeat limit (`whnf`); it was split into
`w8_gammaR_bounds`, `w8_gamma_arith`, `w8_tan_arith` and a short assembly (no budget override). Every module now
elaborates in well under 30 s under the 4 GB cap.

## Commits (W8-FINAL)

`e9ab2937` step 0; `02dc7e32` torus-shape; `47ba92af` Kshell + shell-embedding; `cc27e845` merge `inp-w6t`;
`4d11d530` shell-close; `eea1bb86` shell-inv, patch-cont K, injective; `d22e0f43` nlw2-proof; `fea1ccf2` root;
`4a01d680` line wrap.
