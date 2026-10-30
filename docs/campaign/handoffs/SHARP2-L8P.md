# SHARP2-L8P: lever L8′ of route A

Branch `sharp-plnv`, with `sharp-v2` merged at 63d96f65 (B4B, the split root). Opus 5.5. Item 2 of
the brief SHARP2-PLNV.

## Result

- `KAM.Sharp2.RouteA.g1_v2A'` and `KAM.Iso.Sharp2.RouteA.iso_g1_v2A'`: route A with the torsion against
  the initial torus, fixed and isoenergetic. They conclude the same bodies as `g1_v2A` and `iso_g1_v2A`
  (`G1BodyA`, `IG1BodyA`), with the same constants `c1A`, `c2A`, `c2I`, `c3I`.
- `KAM.Sharp2.Examples.plasmaLean_torus'`: the certified threshold at PlasmaLean's data rises from
  1.93·10⁻¹⁷ to **e\* = 372/10¹⁹ = 3.72·10⁻¹⁷ = 10^(−16.43)**, under the same hypotheses `CALike` and the
  same small-divisor certificates. That is 65 times PlasmaLean's 5.7·10⁻¹⁹, and it gains 0.285 orders
  over `plasmaLean_torus`. Closeness: `‖Kinf - K‖ ≤ 20269337 * e`.

Mirror rows (`python3 -I scripts/apost_sharp/route_a_lean_mirror.py`, floats, not a Lean certificate):

| package | design `thresholdA` (L8′) | Lean `routeAOk` | Lean `routeAOkR` (L8′) | difference |
|---|---:|---:|---:|---:|
| R1 fixed | −10.71 | −11.18 | −10.71 | +0.00 |
| R1 iso | −10.95 | −11.37 | −10.95 | +0.00 |
| H50 fixed | −11.73 | −12.29 | −11.73 | +0.00 |
| H50 iso | −11.90 | −12.44 | −11.90 | +0.00 |
| PlasmaLean cA-like | −17.02 | −17.27 | −17.02 | +0.00 |
| PlasmaLean R1-like | −13.57 | −13.87 | −13.57 | +0.00 |

Only `plasmaLean_torus'` is a certified number. The R1 and H50 rows are mirror evaluations: no Lean
instance of `routeAOkR` exists for them.

## The statement

```lean
theorem g1_v2A' (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs bF bT : ℝ} (I : InitA) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hμ : 0 < μ) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hOk : routeAOkR N bF (N.capR (μ / 2) bT) (initR I σK σB μ) Xs)
    (hB : Ref.Budget N (σT - μ) I.iH bF bT) (hXpos : 0 < Xs) :
    0 < min (sharpC1 ...) (c1A N Xs) ∧ 0 < max (sharpC2 ...) (c2A N Xs) ∧
      G1BodyA N I M σK σB σT μ γbar (min (sharpC1 ...) (c1A N Xs)) (max (sharpC2 ...) (c2A N Xs))
```

`iso_g1_v2A'` is the same with `routeAOkRI`, `capRI`, `initRI`, against `iso_g1_v2A`.
`Ref.Budget N mT iH bF bT` is arithmetic only: `0 < mT < N.sT`, `bT + 2 bF ≤ (N.sT - mT)/(N.sT mT)` and
`iH + bT + 2 bF ≤ N.t`.

`plasmaLean_torus'` is `plasmaLean_torus` with `e ≤ 372 / 10 ^ 19` and `20269337 * e`.

## What L8′ does in Lean

Admissibility no longer carries `T` and `⟨T⟩⁻¹`. It carries `Ref.AdmR`: `‖𝒯_ab(K) - 𝒯_ab(K₀)‖ ≤ m_ab`,
against the fixed initial torus. At the entry to each stage, `Ref.AdmR.entry` derives the bounds of `T`
and `⟨T⟩⁻¹` from `Ref.RefT` (the data of `K₀`), the local bound `Ref.local_bound`
(`|T - 𝒯_ab| ≤ B_loc x ≤ b_F`, stage conditions `NumA.CondR`), and `inv_le_of_ref`. So no property of the
new torus enters the step, and there is no Neumann condition for `⟨T̄⟩`. `ϑ` now only controls the Gram
Neumann condition, which is why the optimum moves to ϑ = 1/100.

Iso: `Ref.AdmRI` tracks `‖𝒯_ab(K) - 𝒯_ab(K₀)‖ + ‖ω - ω₀‖` and `n ‖ω - ω₀‖`, and `T̃ - T̃₀` is treated
blockwise, with the row `Y = ω - ηᴸ`. This matches `rate_ab` and `B_loc` of `stageA(..., tref=True)`.

## Certified data of `plasmaLean_torus'`

Prefix 3, the constants and certificates of `freqVar` unchanged (`L8.var_cert`). Caps: sB 2.0002, sT 5.4,
sLt 12.4002, sN 6.2004, sNt 24.801, t 19.875, ϑ 1/100. X⋆ = 85/10⁵ (true edge 8.503·10⁻⁴), b_F = 10⁻⁶
(actual maximum 7.9·10⁻⁸), b_T = 0.0348 (the sum is 0.03407). The local term is negligible: the binding
quantity is the `𝒯_ab` sum, as the blueprint says for R1.

Kernel cost: `L8.var_ok` and `L8.var_close` are each under 0.3 s (the slower took 0.26 s; the profile did
not say which). No new small-divisor `decide`.

## Files

Fixed, namespace `KAM.Sharp2.RouteA.Ref` unless noted:
- `KAM/Sharp2/RouteA/Ref/Constants.lean`: `StepInA.rAb`, `bLoc0`, `bLoc`, `Cond0`, `NumA.stageR`, `capR`,
  `CondR`, `routeAOkR` (these in `KAM.Sharp2.RouteA`, for dot notation).
- `KAM/Sharp2/RouteA/Ref/Local.lean`: `Adm0`, `torsionAB_sub_le`, `local_bound`, `RefT`, `AdmR`,
  `AdmR.entry`.
- `KAM/Sharp2/RouteA/Ref/Step.lean`: `StepInA.Cond0.facts`, `step_core`.
- `KAM/Sharp2/RouteA/Ref/Scheme.lean`: `schemeR`, `Budget`, `strip_sub`, `schemeR_isNewton`.
- `KAM/Sharp2/RouteA/Ref/G1.lean`: `g1_core_R`, `g1_branch_R`, `g1_v2A'`.

Iso, namespace `KAM.Iso.Sharp2.RouteA.Ref`: `KAM/Iso/Sharp2/RouteA/Ref/{Step,Scheme,G1}.lean`
(`inv_le_of_ref_fintype`, `RefTI`, `AdmRI`, `step_coreI`, `schemeRI`, `routeAOkRI`, `iso_g1_core_R`,
`iso_g1_branch_R`, `iso_g1_v2A'`).

Examples: `KAM/Sharp2/Examples/MirrorQRef.lean` (`NumQ.okR`, `okR_sound`),
`KAM/Sharp2/Examples/PlasmaLean/Ref.lean` (namespace `L8`, and `plasmaLean_torus'`).

Tooling: `scripts/apost_sharp/route_a_lean_mirror.py` (`route_a_ok_ref`, the new column).
`KAM.lean`, `KAM/Root/*`: regenerated.

## Checks

- `nice -n 5 lake build KAM.Sharp2.Examples.PlasmaLean.Ref KAM.Iso.Sharp2.RouteA.Ref.G1
  KAM.Sharp2.Examples.PlasmaLean.NonVacuous`: `Build completed successfully (3444 jobs).`
- `#print axioms` (`.drafts` probe) on `g1_v2A'`, `iso_g1_v2A'`, `plasmaLean_torus'`, `L8.var_ok`,
  `NumQ.okR_sound`, `Ref.g1_core_R`, `Ref.iso_g1_core_R`: `[propext, Classical.choice, Quot.sound]`.
- `sh scripts/lint_sources.sh`: exit 1 from the known causes only (siblings' long lines, ABI scratch
  probe). No line of the new modules. `check_lean_modules: PASS (1637 Lean files)`,
  `FROZEN-ANCHOR GUARD OK`. All new files are under 800 lines (largest 406).
- Name clashes (orchestrator's rule): a parse of the fully qualified declarations of all of `KAM/`
  against those of the 19 files of `KAM/Sharp2/RouteA/Ref`, `KAM/Iso/Sharp2/RouteA/Ref` and
  `KAM/Sharp2/Examples`: 340 names, 0 clashes. This is the grep form of the rule. The full-import probe
  was not run, since it needs the whole library built, which is forbidden here. The parser does not see
  structure fields or auto-generated names.
- No `set_option`, no `sorry`, no frozen file touched. `step_A`, `step_IA` and the existing route-A
  theorems are unchanged.

## Deviations

1. One sum for two caps. The blueprint and the mirror list caps `Tab` and `Tsup` with the same rate;
   Lean has seven rates, one tracker `m_ab`, and `Ref.Budget` requires the sum below both. Equivalent,
   and the mirror rows agree.
2. The cap of `|T|`. The second half of `bp:p2s2:torsion-ref` (route B) has `t = c_Th σ_{Nᵀ} σ_N + t_s`.
   Route A uses `|T_s| ≤ |T₀| + m_ab + 2 b_F`, as `stageA` does (`rates["Tsup"] = rate_ab`), so no `c_Th`
   enters. The local bound `B_loc` is the blueprint's route-A one in (L8′).
3. `ch`, the constant at the bite `δ_s/2`, is `N.cS (s + 1)`: no new data, since `δ_s/2 = δ_{s+1}`.
4. `Ref.step_core` and `step_coreI` repeat the set-up of `step_A` and `step_IA` instead of factoring it,
   to leave the audited proofs untouched. This is about 200 duplicated lines.
5. The analogue of `g1_v2A_default` for L8′ was not asked for and does not exist: (R3) stays a required
   hypothesis, as in the audit's decision.

## Uncertainties

- None of this has been audited. `g1_v2A'` has no conclusion-shaped premise by construction
  (`routeAOkR`, `Ref.Budget` are numbers), but an independent read is due, as for B9.
- `plasmaLean_torus'` inherits every limit of `plasmaLean_torus`: canonical flows only, not PlasmaLean's
  field, a different norm from PlasmaLean's, and the norm set "cA-like" is a guess. Non-vacuity carries
  over, since `CALike` is unchanged.
- A prefix of 4 would give about +0.04 orders in the float model, at the cost of the bites δ₃ (N = 2¹²)
  and r₃. I did not do it.
- `blueprint/parts/p2s2-modified.tex` is not updated for the implementation choices 1–3 above.

## Suspected errata

None in pinned sources.
