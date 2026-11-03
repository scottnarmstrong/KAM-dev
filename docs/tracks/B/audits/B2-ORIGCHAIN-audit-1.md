# B2-ORIGCHAIN independent audit 1

Verdict: **PASS WITH NOTES** for `KAM.EffectiveStability.oscillatorChain_physical` and the B2-ORIGCHAIN package. No mathematical blocking finding. This is an ordinary Track B theorem package, not a frozen-anchor seal: there is no assigned frozen theorem or provider. The generic I/N/P brief's frozen-type and seal-body checks are therefore inapplicable, rather than silently treated as passed.

Audited 2026-11-03, worktree `/root/code/KAM-inp-b2ogchain`, HEAD `106ed9570474d3bc5196edd0b40827cc81ac1eef`. Baseline `inp` was `8e5aa1f4bb9321ad4eee6794427274d6f08bf792`; three-dot merge base `f7c71d50cb9f583c77a9dde89ba7dacd993c1a53`. `git diff inp...HEAD` contains exactly the two new Lean files and `docs/tracks/B/audits/B2-ORIGCHAIN-handoff.md` (370 insertions). No production file was edited during this audit.

Read AGENTS, PLAN, DECISIONS, the package-audit brief, handoff/AUDIT FOCUS, B2-ORIGCHAIN and B1-common briefs, Track B SPEC, FREEZE-PROPOSAL and OWNER-DECISIONS (including OD-B7), plan §2.2/B1-transfer, both new modules, and their chain/physical interfaces and relevant frozen definitions. Track B's package brief and these statements supply the contract; there is no B2-ORIGCHAIN I/N/P blueprint node or frozen anchor to compare. The owner-approved oscillator action and Hamiltonian vector field retain the specified carriers and conventions.

## Declaration review

Names below are in `KAM.EffectiveStability`. Locations refer to the two new files, abbreviated Physical and Smoke.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| Inverse radius budget, Physical:32 | `OscPhysDom` | PASS | Finite recursion on the list, strict radius checks with the correct accumulated prefix displacement. |
| Step casts, Physical:41 | `oscStep_cast` (private) | PASS | Replicated rational radius cast, no extra analytical premise. |
| Step smallness, Physical:45 | `oscStep_epsHalf` (private) | PASS | Cast of `OscStepOK.ε_le`. |
| Step positivity, Physical:49 | `oscStep_eps0` (private) | PASS | Cast of `OscStepOK.ε_nonneg`. |
| One-step forward displacement, Physical:53 | `oscStep_chart_sub_le` | PASS | Exact specialization of the landed physical displacement bound using the step's finite majorants. |
| One-step inverse displacement, Physical:62 | `oscStep_inv_sub_le` | PASS | Same specialization for time minus one; full real-interior premise retained. |
| One-step right inverse, Physical:70 | `oscStep_chart_chartInv` | PASS | Uses the real-flow inverse result on the stated domain, not a presumed chain identity. |
| Triangle inequality, Physical:79 | `abs_sub_add_le` (private) | PASS | Elementary scalar inequality. |
| Chain forward displacement, Physical:88 | `oscChainMap_sub_le` | PASS | Each inner image fits the next real-interior domain by `OscDomOK`; coordinate bounds sum to `oscTail`. |
| Chain inverse and coverage, Physical:109 | `oscChainInv_sub_le` | PASS | Generalizes over `c,z`, updates the prefix budget, proves both displacement and `Ψ(Ψinv z)=z`. |
| Action-to-coordinate bound, Physical:144 | `chainCoord_abs_le` (private) | PASS | Uses nonnegative radius and the exact factor two in the oscillator action. |
| Coordinate transfer, Physical:151 | `chain_coord_add` (private) | PASS | Triangle inequality; no conclusion-shaped premise. |
| Physical confinement, Physical:161 | `oscillatorChain_physical` | PASS | Exact requested physical initial condition, ODE, B1-E uniqueness, endpoint-inclusive drift and level bounds. |
| Empty polynomial majorant, Smoke:23 | `chainPhysSmoke_supBound_nil` (private) | PASS | Reduction of the zero polynomial's majorant. |
| Two-generator smoke, Smoke:28 | `chainPhysicalSmoke_zeroDrift` | PASS WITH NOTES | Actually instantiates the main theorem with two zero generators and harmonic `H`; exported smoke conclusion retains only initial value and zero drift, and its initial box is the origin. |

## Definition classification and proof obligations

`OscPhysDom` is the only new definition; no new abbreviation, structure, instance, or carrier is introduced. On every finite list and every real `c`, its body is precisely a finite conjunction of radius inequalities, with `True` at the empty list. It contains no trajectory, inverse identity, confinement result, hidden analytical assumption, or fallback object. Positivity and small-field validity come separately from `OscStepOK`, as required.

For a two-step list `[a,b]`, the budget is exactly

```
(∀ i, s i + c + a.δ < a.ρ) ∧
(∀ i, s i + (c + a.ε * a.δ) + b.δ < b.ρ).
```

Rational quantities here are cast to real numbers. A scratch Lean example checked this expansion. This is the correct order: `oscChainMap (a::l) = Φa ∘ oscChainMap l`, while `oscChainInv (a::l) = oscChainInv l ∘ Φa⁻¹`. The inverse proof first sets `z' = Φa⁻¹ z`, bounds its coordinates by `s+c+a.ε*a.δ`, applies the induction hypothesis with that increased offset, and then applies the one-step right inverse. Forward displacement instead uses the suffix tail, correctly matching the opposite composition order.

The main theorem preserves every premise of `oscillatorChain_confinement` before its initial-data binders, then adds only `a',s,d`, `hs0`–`hs3`, and `hd`, as authorized in the package brief. The initial data are physical `z₀` with `I(z₀) ≤ a'`. From `2a' ≤ s²` it proves coordinate bounds, then uses the inverse theorem to obtain `w₀=Ψinv z₀`, `Ψw₀=z₀`, and `I(w₀)≤(s+e)²≤a`, where `e=oscTail l`. Thus the original physical box is covered by the chart; it is not merely renamed as a chart image. The strict chart-domain inclusion follows from `a≤b`, `εb>0`, `2(b+εb)≤r²`, and `osc_subset_oscBox`.

The existing chain theorem supplies the ODE and uniqueness in all of real phase space. Rewriting its actual initial value with the proved right inverse gives `z 0=z₀` and the requested uniqueness clause with no change of interval or regularity. For `|t|≤T`, its chart-action level is below `b`; this places `u=Ψinv(z t)` in `oscBox r 0`, so forward displacement applies. The oscillator-action transfer bound at both `t` and `0` is `e(2r_j+e)≤d_j`. Adding these two errors to chart drift gives `2d_j+η_j|t|`; using only the time-`t` error gives `a_j+η_jT+d_j`. All constants, coordinate order, factors two, endpoint quantifiers, and dependencies agree with the brief.

No requested signature was weakened and no proof obligation was added as a hypothesis. The generalized inverse helper covers arbitrary offset `c`, a useful stronger scope than the main theorem's `c=0` use. Forward displacement retains the pre-existing full `OscDomOK` budget (including its Cauchy condition); this is permitted by the deliverable and already supplied by the main theorem.

## Independent mechanical checks

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and the required 4 GB/no-swap scope. The common wrapper was:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1
```

1. Targeted gated build (wrapper followed by the command below), exit **0**:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b2ogchain KAM.EffectiveStability.OscillatorChainPhysicalSmoke
```

Output:

```
[inp-gate] slot 1 acquired 02:10:39 for KAM.EffectiveStability.OscillatorChainPhysicalSmoke
Build completed successfully (2994 jobs).
```

The gate runs `nice -n 5 lake build <Module>`; building the smoke module checks both new modules through its import dependency. No full-library build or cache mutation was requested.

2. Scratch probe `.lake/abi-scratch/B2OrigChainAudit.lean`, run with the wrapper followed by `nice -n 5 lake env lean .lake/abi-scratch/B2OrigChainAudit.lean`, exit **0**. It copied the entire main declaration signature under `audit_physical_signature` and used `exact oscillatorChain_physical hH hN hP hA hok hδc a b η εb T hεb hT rl r hrl hr0 hdom1 hdom hη hdrift hmargin a' s d hs0 hs1 hs2 hs3 hd z₀ hz₀`, listing all explicit binders in order. It also checked the two-step radius expansion above and printed axioms for every new public theorem:

```
'KAM.EffectiveStability.oscStep_chart_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscStep_inv_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscStep_chart_chartInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChainMap_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscChainInv_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillatorChain_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.chainPhysicalSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is an ordinary-theorem application/body receipt, not a frozen/provider type-equality receipt.

3. One kernel replay, wrapper followed by:

```sh
nice -n 5 lake env leanchecker --verbose \
  KAM.EffectiveStability.OscillatorChainPhysical \
  KAM.EffectiveStability.OscillatorChainPhysicalSmoke
```

Exit **0**, complete output:

```
replaying KAM.EffectiveStability.OscillatorChainPhysicalSmoke
replaying KAM.EffectiveStability.OscillatorChainPhysical
```

4. Source lint: receipt recorded below after completion.

5. `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b2ogchain KAM.EffectiveStability.OscillatorChainPhysical KAM.EffectiveStability.OscillatorChainPhysicalSmoke`, exit **0**:

```
short-name check OK (no reused public short name)
```

Independent Unicode line counts: Physical **254**, Smoke **67**; over-100-character lists both **[]**. Both files have copyright, `module`, `public import`, module docstring and exposed public section. No forbidden escape, resource override, or `EuclideanSpace` occurs in either file.

6. `git diff --check inp...HEAD`, exit **0**, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`, exit **0**, no output. The complete three-dot path list also confirms no generated roots, lakefile, application, or other protected path changed.

7. Recursive source-import walk from the smoke module visits **83 KAM modules** and finds **[]** for provider imports, frozen theorem modules, or LambdaDrift modules. Frozen definitions are imported legitimately; no DRAFT_SORRY theorem is in this chain. This independently supports the standard-only axiom receipts.

## Notes, errata, deviations and limits

- **N1, documentation only:** Physical:17 names `` `oscChainMap_oscChainInv`: `Ψ (Ψinv z) = z` ``. No such separate export is declared; the actual identity is the second conjunct of `oscChainInv_sub_le`. The promised mathematics is present and consumed. Correct the docstring in a later implementation change.
- **N2, documentation only:** Physical:30–31 starts with `` `|z_i| ≤ s i + c` `` but describes the later coordinate bound as `` `s i + (∑_{j<k} ε_j δ_j)` ``. For general starting offset it is `s i + c + ∑_{j<k} ε_j δ_j`. The definition and proof retain `c` correctly; the main theorem starts at `c=0`.
- **N3, smoke scope:** Smoke:28–33 exports no ODE clause, and `a'=0` forces the physical initial point to the origin. Its proof nevertheless calls the full theorem for two actual zero-generator steps of `H=cartAction 0`, `Nact=cartQVar 0`, `P=[]`, so it satisfies the requested smoke instantiation. Do not cite this corollary alone as a nonzero-box or standalone harmonic-ODE result.

No suspected defect was found in the controlling source/blueprint mathematics or frozen definitions. N1/N2 are package documentation inaccuracies for the handoff, not mathematical source errata. No implementation deviation was introduced by this audit. No heartbeat failure, OOM, or unproved analytic invoice was encountered. This audit does not certify a numerical instance, B3 data, headline freeze, or campaign closure.
