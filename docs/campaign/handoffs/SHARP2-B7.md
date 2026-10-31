# SHARP2-B7 handoff: the isoenergetic route B (bordered modified step and iso theorem)

Branch `sharp-b7`, from `sharp-v2` at `b933c88e`, with `sharp-b6` merged four times (`df0d0910`, `df042399`, `aa0362ad`,
`5a47f934`, the last at B6 commit `42b88b7e`). That is the one merge the brief allows, repeated as B6 committed more of its
scheme. B6 has no handoff yet, so see "What remains".

Results:

- **`KAM.Iso.Sharp2.modified_stepIB`**: proved. Target of the brief; there is no verbatim signature for it (see "Signature").
- **`KAM.Iso.Sharp2.RouteB.iso_g1_v2B_frozen`**: proved, literal `IG1Body`, verbatim signature (probe below).
- **`KAM.Iso.Sharp2.RouteB.NumB.Cert.of_le_gamma`**: proved, verbatim signature.
- **`KAM.Iso.Sharp2.iso_g1_v2`** (added, listed for B7 in `APOST-SHARP-V2.md` and the delta doc): the combined literal
  `IG1Body`, `C₁ = min {C₁♯, C₁ᴬ, C₁ᴮ}`, `C₂`, `C₃` the maxima, mirroring B6's `g1_v2`.
- **Route B in the v2 certifier: not done.** The brief makes it conditional on time. It needs a rational mirror of
  `stepConstsB` (about forty constants) with its soundness proof, and it would not help the current target: the blueprint's
  R1 numbers are route A 10^{-10.95}, route B 10^{-12.33}.

`iso_g1_v2B_frozen` is conditional on `routeBOk` and the certificates, as the signature says. I ran no numerics: no iso system
has been checked against it.

## Files

All modules: copyright, `module`, `public import`, module docstring, `public section`. No line over 100 characters, no file
over 800 lines (largest 608). No existing tracked file was changed except the regenerated `KAM/Root/Iso.lean` and
`KAM/Root/Sharp2.lean`. Check: `git diff --stat 42b88b7e HEAD -- . ':!KAM/Iso/Sharp2'` lists only those two and this handoff.

| File | Lines | Content |
|---|---|---|
| `KAM/Iso/Sharp2/ModStepB/Defs.lean` | 93 | `xiNI`, `tilK`, `gLI`, `xiLI`, `newK`, `xw`, `newOmega`; `newOmega_smul` (`ω̄` is on the ray) |
| `KAM/Iso/Sharp2/ModStepB/Hyp.lean` | 313 | the bundle `ModStepB.Hyp`: the two-term `μ` of B4B with `ε_L = λμ`, `ε_N = γδ^κμ`, and `ηω` |
| `KAM/Iso/Sharp2/ModStepB/Geo.lean` | 488 | the current torus (port of B4B) |
| `KAM/Iso/Sharp2/ModStepB/Normal.lean` | 443 | the bordered system (`bord`, from `border_solve`), `ξᴺ`, `ξ^ω`, `K̃`, `L̃` |
| `KAM/Iso/Sharp2/ModStepB/Inter.lean` | 288 | `Ẽ_ω`, `η̃ᴺ`, `Ω_K̃`, with the increment `σ̃_K Θ C₀` of `C_Ẽ` |
| `KAM/Iso/Sharp2/ModStepB/Comp.lean` | 203 | `gᴸ`, `ξᴸ`, `K̄` (with the `C_ΔK` of SHARP2-DOMPLUS) |
| `KAM/Iso/Sharp2/ModStepB/Frames.lean` | 270 | `L̄`, `B̄`, `N̄`, `𝒯_ab` |
| `KAM/Iso/Sharp2/ModStepB/NewErr.lean` | 608 | the errors at `ω̄`: `EW_eq`, `Eb_eq`, `etaNb_eq`, the identity `NtOEb_key`, one lemma per term |
| `KAM/Iso/Sharp2/ModStepB/SelfCons.lean` | 188 | L10 at `ω̄`; `etaLb_le` |
| `KAM/Iso/Sharp2/ModStepB/Energy.lean` | 217 | new: `|⟨H ∘ K̄⟩ - E₀| ≤ Q_ω μ²/(γδ^{κ+1})` |
| `KAM/Iso/Sharp2/ModStepB.lean` | 263 | `muI`, `xI`, `bordAvg_eq_extended`, `newOmega_sub_le`, **`modified_stepIB`** |
| `KAM/Iso/Sharp2/RouteB/Scheme.lean` | 407 | `StI`, `GoodI`, `schemeIB`, `RunBaseI`, `RunHypI`, `local_parts`, the bordered Neumann `tors` |
| `KAM/Iso/Sharp2/RouteB/Step.lean` | 409 | `drift_incr`, `good_step` |
| `KAM/Iso/Sharp2/RouteB/Run.lean` | 243 | `isNewton`, `iterI_spec`, `exists_limit_of_incr`, `tendsto_weighted_zero`, `iso_energy_limit_B` |
| `KAM/Iso/Sharp2/RouteB/Core.lean` | 275 | `freqSum_scale`, `RunHypI.core` |
| `KAM/Iso/Sharp2/RouteB.lean` | 385 | `iso_g1_branch_B`, **`iso_g1_v2B_frozen`**, **`NumB.Cert.of_le_gamma`** |
| `KAM/Iso/Sharp2/G1.lean` | 114 | `IsoG1V2.ig1Body_mono`, **`iso_g1_v2`** |
| `KAM.lean`, `KAM/Root/*` | | regenerated (`python3 -I scripts/gen_root_imports.py`) |

## Approach

**The step.** B4B's lemmas all hang off a bundle that contains `⟨T⟩` invertible and `p.iso = false`. In the bordered system
only `⟨𝖳⟩` is invertible, and LOCAL-COMMON forbids refactoring B4B. So the step is a parallel bundle in
`KAM.Iso.Sharp2.ModStepB` (see Deviations 1); bundle-independent lemmas of B4B are reused through `open`. The trick that keeps
B4B's two-term weighted error: with `ε_L = λμ`, `ε_N = γδ^κμ`, B4B's `max(ε_L/λ, ε_N/(γδ^κ))` is the blueprint's three-term `μ`,
and the energy error is the separate field `‖E^ω‖ ≤ λ_ω μ`.

The new identities are steps `st-w`, `st-l`, `st-en` of the blueprint. The tangential one is `NtOEb_key`:
`Nᵀ Ω₀ Ē = Nᵀ Ω₀(Ẽ_ω̄∘φ - Ẽ_ω̄) - a Nᵀ Ω₀(L̃∘φ - L̃)g - a Nᵀ Ω₀(L̃ - L)g + x g + (Nᵀ Ω₀ Δ²X + Ω_N ηᴺ) + x Nᵀ Ω₀(L̃ - L)ω`. A heartbeat
timeout on the single bound `NtOEb_le` was treated as a design signal and split into `term_E`, `term_L1`, `term_L2`, `term_x1`,
`term_x2`, `term_R`, which elaborate at once. No override anywhere.

**The energy.** `⟨H∘K̃⟩ - E₀ = ⟨Δ²H⟩` by the last bordered row, and `|H∘K̄ - H∘K̃| ≤ n(|η̃ᴺ| + Θ|Ω_K̃|)|ξᴸ|` by the mean value
inequality for `H∘K̃` on the convex strip `T_{r-2δ}` (`norm_fderiv_comp_le`).

**The bordered reference (`RunHypI.tors`, step `st-t`).** `⟨𝖳⟩ - ⟨𝖳₀⟩ = bordMat(⟨T⟩ - ⟨T₀⟩, ω - ω₀, ⟨Y⟩ - ⟨Y₀⟩)`, bounded by
`norm_bordMat_le` with `Y = ω - ηᴸ`. `GoodI` carries the drift in the two forms the two kinds of row need,
`|⟨𝒯_ab(K)⟩ - ⟨𝒯_ab(K₀)⟩| + |ςω* - ς₀ω*| ≤ m₅` and `n|ςω* - ς₀ω*| ≤ m₅`, whose increments are exactly the two entries of
`C^𝖳_ab = max {C_ab + ΘC₀g₁, nΘC₀g₁}` (`drift_incr`), so a single cap serves both. The stage-0 local parts are proved at stage `0`
(`Rb.local_parts`), not assumed.

**The frequency limit.** `converge_ratio` says nothing about the parameter (Errata 1). The state therefore keeps the previous
scale, `GoodI.incr` records `|ς_{s+1} - ς_s||ω*| ≤ C_ν γ δ_s^{τ+1} X_s`, and `exists_limit_of_incr` gives `ς_s → ς∞` within exactly
`N.freqSum X_i`. The energy limit runs from a late iterate on the ball that `J4` leaves around the limit (`iso_energy_limit_B`).

## Checks

Builds, each one niced and targeted:

```
$ nice -n 5 lake build KAM.Iso.Sharp2.ModStepB KAM.Iso.Sharp2.RouteB KAM.Iso.Sharp2.G1
Build completed successfully (3396 jobs).
```

No warning from any file of this package at the last build of those modules.

Axioms and signature probe (`.drafts/b7sig.lean`, the text of the signature document for B7 with the bodies replaced by the
proved theorems, so each verbatim statement elaborates and closes):

```
'KAM.Iso.Sharp2.modified_stepIB' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.iso_g1_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.RouteB.iso_g1_branch_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.RouteB.RunHypI.core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.RouteB.RunHypI.good_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.RouteB.iso_g1_v2B_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.RouteB.NumB.Cert.of_le_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.RouteBProbe.probe_iso_g1_v2B_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.RouteBProbe.probe_Cert_of_le_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lint, `sh scripts/lint_sources.sh`: exit 1. Not clean, for these reasons, none from this package's files:

- `KAM/Sharp2/RouteB/Newton.lean:229` and `KAM/Sharp2/RouteB/Step.lean:22` are 101 characters. Both are B6's files.
- The ABI-scratch step stops on a missing frozen olean of this snapshot (`KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM`),
  as in the C6 handoff.
- `check_lean_modules: PASS (1655 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`.

Forbidden tokens: a scan of this package's files for `sorry`, `admit`, `axiom`, `maxHeartbeats`, `maxRecDepth`, `synthInstance`,
`unsafe`, `opaque` found nothing.

Name clashes:

- `.drafts/b7clash.lean` imports `KAM.Iso.Sharp2.G1`, `KAM.Iso.Sharp2.RouteA.Frozen`, `KAM.Sharp2.G1`, `KAM.Sharp2.RouteB.Frozen`,
  `KAM.Sharp2.RouteA.Frozen`, `KAM.Sharp2.ModStepB` and `KAM.CertificateSharp.V2.RouteARefinedEngine`: `lake env lean` prints nothing.
- The all-modules probe was **not** run: it needs the whole library built, which is forbidden here. Instead:
  `grep -rln "namespace KAM.Iso.Sharp2" KAM` finds only files under `KAM/Iso/Sharp2/`, so the only possible fully qualified
  clashes are with B9's `RouteA`, which is in the probe.
- All declarations are under `KAM.Iso.Sharp2.ModStepB`, `KAM.Iso.Sharp2.RouteB`, `KAM.Iso.Sharp2.IsoG1V2`, or are the two names
  `KAM.Iso.Sharp2.modified_stepIB` and `KAM.Iso.Sharp2.iso_g1_v2`.

## Signature of `modified_stepIB`

It is `modified_stepB` with `hiso : p.iso = true` for `hfix`, plus:

- `hTa` on the frozen `KAM.Iso.extendedTorsionAverage` instead of `torsionAverage`;
- `hdH : ∃ A, ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ A`, `hd2H`, `hY : ∑ b, ‖energyRow h K θ b‖ ≤ p.y0` on `T_{r-δ}`, `hΘ : ‖ω‖ ≤ p.Θ`,
  `hηω : ‖energyAverage h K - E₀‖ ≤ εω`;
- `hE0`, `hcond`, `hβ`, `hroom` at `muI`, `xI`, the three-term error.

Conclusions: those of `modified_stepB` for `(newK, newOmega)`, plus `‖ω̄ - ω‖ ≤ Cnu μ` and
`‖energyAverage h K̄ - E₀‖ ≤ sQw p · μ²/(γ δ^{κ+1})`.

## Deviations

1. **Duplication.** The eight parts `Hyp` to `SelfCons` are a 2801-line near-copy of B4B's 2645, forced by the bundle
   (`ModStepB.Hyp` contains `fix` and `⟨T⟩⁻¹`) and the additive rule. A later refactor could factor the geometry through a bundle
   without the twist, as B6's `LocHyp` already does for `Geo`; I use `LocHyp` itself on the iso side in `RunBaseI.loc`.
2. **Rate of `𝒯_ab`.** `modified_stepIB` concludes at rate `sCab0 p`, the blueprint's `C_ab`, not `(stepConstsB p).Cab`, which at
   `p.iso = true` is the bordered rate `C^𝖳_ab`. The former is sharper and is what `drift_incr` needs.
3. **State of the scheme.** `StI` has one more real than the blueprint's `(K, s)`: the previous scale, for Errata 1.
4. **`iso_energy_limit_B` replaces `iso_energy_limit_A`.** Route A's lemma wants a ball of radius `μ/2` around every iterate,
   which route A's ball cap gives. Route B has no ball cap (`J4` is a separate condition), so the ball is taken around the limit.
5. **`RunHypI` assumes `loc0`, `Y0`, `form0`.** They are facts about the initial pair, and all three are proved in
   `iso_g1_branch_B` from `local_parts` at stage `0`. Nothing of the kind reaches the frozen signature.
6. **Small local copies.** `norm_smul_le_of_margin'` copies route A's lemma, which is stated on `Fin N.n` for `N : NumA` and so
   cannot be applied at `Fin n`. `inv_le_of_ref_bord` is `inv_le_of_ref` over any index type (the original is `Fin n`).
7. **`hsB` in `iso_g1_v2B_frozen` is unused**, as in B6's `g1_v2B_frozen`. It is in the verbatim signature.
8. **Merges.** `sharp-b6` was merged four times, which also brought in what B6 had taken from `sharp-v2` (the root split, the
   `o*` renaming, SO data). B6's change of `C_ΔK` (SHARP2-DOMPLUS) was ported to `Comp.Kb_sub_le` and `Normal.Kt_scale`.

## Errata (suspected defects, for the orchestrator)

1. **`StageScheme.converge_ratio`, `KAM/Sharp2/EngineRatio.lean:146`** (and `converge_checked`). Quoted: `∃ (Kinf : ...) (pinf : ℝ),`
   followed by conclusions none of which mention `pinf`. So the existential is vacuous, and the proof supplies the witness `0`
   (line 395: `refine ⟨L, 0, hholo, ...`). The engine proves no limit of `S.par`: both uses of `hS.step` (lines 298, 325) discard
   the third clause, `|S.par (S.step r δ x) - S.par x| ≤ (C δ).Cp * μ`, and `Cp` occurs only in the unused part of `htail`.
   The admissible-state conclusion is an unstructured `∃ r β μ m`, so a client cannot re-run the step either (no ball or cap room).
   For the fixed-frequency scheme this does not matter (`par = 0`). For iso it does, and `iso_g1_v2B_frozen` works around it inside
   the scheme (Deviation 3), so nothing is unproved. A stronger engine conclusion (`Tendsto (par ∘ iter) (𝓝 pinf)` and
   `|pinf - par x₀| ≤` the parameter sum) would make that device unnecessary.
2. **`blueprint-I/parts/p2s2-iso-modified.tex:21`.** Quoted: "`y_0:=M_{h1}\sigma_N\ge\abs Y` on `\R^n`". The proof uses a stronger
   fact: `border_solve` needs the row sum `∑_b |Y_b| ≤ y₀` on `T_{r-δ}`, not only on the real torus. It holds with the same `y₀`
   (`sum_norm_energyRow_le_ref`), so no constant changes. This is wording only.

No other defect found. By hand and then in Lean, the iso fields of `stepConstsB` (`C₀`, `C_gL`, `C_Ẽ`, `C_Ē`, `Q'_L` with `a_ω`, the
polynomial `Q̄_N`, `Q_ω`, `C^𝖳_ab`, `B^𝖳_loc`, `ϱ_ν`, `C₀g₁X ≤ ϑ_ω`) are exactly what the identities need.

## Uncertainties

- B6 has no handoff and may still change `routeBOk`, `capB`, `NumB`, `RunBase` or `g1_v2B_frozen`. This branch is on `42b88b7e`.
- `iso_g1_v2`'s hypotheses are my mirror of `g1_v2`: the signature document has no verbatim form of it.
- `modified_stepIB` keeps `∃ A` for `DH`, from `Standing`'s lack of that bound. `iso_g1_v2B_frozen` uses `A = M`.

## What remains

- If B6 changes after `42b88b7e`, merge it again and rebuild `KAM.Iso.Sharp2.G1`.
- Route B as an `orElse` engine in the v2 certifier, if a target ever favours route B over route A.
- The two 101-character lines in B6's files, in B6.
