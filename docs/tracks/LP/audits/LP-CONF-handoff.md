# LP-CONF handoff (MAIN L14, sharp first exit, conditional helper) — track LP, non-frozen

## Files
- NEW `KAM/Planetary/StrongAMD/Confinement.lean` (267 lines).
- GENERATED (via `scripts/gen_root_imports.py`): `KAM/Root/Planetary.lean` (one import line added).

## Main declaration (distinct name; NOT the public theorem)
`KAM.Planetary.StrongAMD.strongFirstExit_of_stopped_drift` (`LP:MAIN L14 (468–500)`, N2, N6):
```
{ν} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) {U} (hUc : IsCompact U) (hUch : U ⊆ chamber ν)
{μ δ r T : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hT : 0 < T)
(hbudget : n * r + strongThresholdModulus ν U r ≤ δ / 4)
{z₀} (hphys₀ : IsPhysicalState ν z₀)
(hball : ∀ I, ‖I - actionVector ν z₀‖ ≤ r → I ∈ U)
(hC₀ : strongAMD ν z₀ ≤ strongThreshold ν (actionVector ν z₀) - δ)
(hstop : ∀ J, J.OrdConnected → 0 ∈ J → ∀ z, IsMovingSolutionOn ν μ J z → z 0 = z₀ →
   ∀ t ∈ J, |t| ≤ T →
   (∀ u ∈ uIcc 0 t, IsPhysicalState ν (z u) ∧ ‖Λ(z u) - Λ z₀‖ < r ∧
       strongAMD ν (z u) < strongThreshold ν (Λ(z u)) - δ/2) →
   ‖Λ(z t) - Λ z₀‖ ≤ r/2) :
∃ z, z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Icc (-T) T) z ∧ MovingUniqueOn ν μ (Icc (-T) T) z ∧
  ∀ t ∈ Icc (-T) T, IsPhysicalState ν (z t) ∧ ‖Λ(z t) - Λ z₀‖ ≤ r/2 ∧
    strongAMD ν (z t) ≤ strongThreshold ν (Λ(z t)) - δ/2 ∧ BarrierState ν U (δ/2) (z t)
```
(`Λ = actionVector ν`; full elaborated signature obtained with `#check`.) The only extra premise is
`hstop`, in the STRICT form (review round 1): drift `< r` and margin `< B - δ/2` (both strict come for free, since `hstop` is applied only inside the open `firstExitTube`). This is a weaker requirement on `hstop` than the briefed non-strict form, so the theorem is stronger. Supporting (public) lemmas:
`firstExitTube`, `firstExitCore` (sets), `firstExitCore_subset_tube`, `isOpen_firstExitTube`,
`firstExitCore_closed`, `continuousAt_{actionVector,strongAMD,keplerEnergy',strongGap}`,
`continuous_totalMomentum'`, `movingSolutionOn_mono`.

## Approach
Maximal solution `z` of the moving field on `collisionFreeDomain n` from `z₀` (`gen_maximal`; `z₀` is in the
domain since it is a `BarrierState ν U (δ/2)`, via `exists_barrierCompact`). On `J = eIoo Tm Tp ∩ Icc (-T) T`
run `amd_exit_forward`/`amd_exit_backward` with `V = firstExitTube` (open: physical, drift `< r`, margin
`> δ/2`), `C = firstExitCore` (drift `≤ r/2`, margin `≥ 3δ/4`), `N` = positive radii. `hloc`: inside `V`,
`hstop` gives drift `≤ r/2`; (17) `strongAMD_le_of_tube` with radius `r/2` and `hbudget` (+ monotone modulus)
gives margin `3δ/4`. Closedness of `C` among limits in `N`: the physical clause (strict negative energy) comes
from the uniform `E_i ≤ -c` of `strongBarrier_physical` for barrier states with `m = δ/2`, energy continuity
where radii are positive, then continuity of `Λ`, `strongAMD`, `B∘Λ` (`B` continuous on the open chamber).
`maximal_global_of_barrier` (applied to `C ⊆` barrier states) gives `Tp > T`, `Tm < -T`. Uniqueness:
`gen_uniqueness_inter` in the frozen `MovingUniqueOn` form.

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-conf KAM.Planetary.StrongAMD.Confinement`: "Build completed successfully (9128 jobs)", no warning in my file.
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK) after `gen_root_imports.py`.
- `main_shortname_check.py … KAM/Planetary/StrongAMD/Confinement.lean`: exit 0.
- `#print axioms` (via `lp_lean.sh`, `.drafts/axioms-conf.lean`): `strongFirstExit_of_stopped_drift`, `firstExitCore_closed`,
  `isOpen_firstExitTube`, `continuousAt_strongAMD`: each only `[propext, Classical.choice, Quot.sound]`.

## Not done
Nothing in scope omitted. Out of scope (as briefed): discharging `hstop` (LP-PS/NRR/LIFT), chart, Newtonian reconstruction, osculating clauses.

## AUDIT FOCUS
1. `hstop` is quantified over every `OrdConnected J ∋ 0` and every solution from `z₀` (not just the maximal one);
   it is used only at `J = eIoo ∩ Icc(-T,T)`, with `uIcc 0 t` (so backward times use `Icc t 0`). Check this matches the
   LP-PS discharge (stopped membership for both time directions).
2. `hμ : 0 ≤ μ` is NOT needed and omitted (any real `μ`); `hn`, `hν` as in LP-MOD.
3. Improvement margin: the budget gives `n r/2 + Ω(r/2) ≤ δ/4`, using `Ω` monotone (only `n r/2 ≤ n r`), so `3δ/4` is attained with room.
4. `hball` is the literal closed-ball (sup norm) `⊆ U` about `Λ z₀`; also used to place `Λ(z t) ∈ U`.
5. Open/closed pair: tube uses strict `< r`, `> δ/2`; core `≤ r/2`, `≥ 3δ/4`; core ⊆ tube needs `r>0, δ>0`.

## Source defects / deviations / design signals
- No errata found in MAIN L14 for this helper. N6 route used (r → r/2, margin 3δ/4). MAIN's prose "improves to r/4" is superseded by N6.
- Deviation: the stopped-conditions are stated pointwise over `uIcc 0 t` rather than on the connected interval (equivalent).
- No design signals: default heartbeats, file 267 lines, build ~10 s.
