# P23-12 prover handoff (branch inp-p2312, 73df686; contains inp-p2310 (P23-10, P23-05; audited); offloaded package run by the main orchestrator; prover on claude-12)


Branch `inp-p2312` (worktree /root/code/KAM-inp-p2312), all work committed. `nfb` and `avg` proved with signatures
**verbatim** from `.drafts/design/P23Signatures.lean` (whitespace-normalised text comparison of both statements: equal).

## Files (all new, 9 modules, 1856 lines total, each < 320 lines)
- `FiniteSchedule.lean`: `Sched` (loss schedule), `Sched.R/S/seq/G/F/Φ`, `homRes_zero`, `homRes_stage`, `iterHyp_two`.
- `FiniteStep.lean`: `IterSetup`, `Inv`, `StepConc`; `step_conc` (one stage: `direct_step` + `split` + N `iterative_direct_a`
  translation law on the same flow), `inv_all`.
- `FiniteChain.lean`: `Sched.Ψ`, `chain_trans'`, `chain_real`, `chain_ident`; `finite_struct`, `finite_ident`, `finite_disp`
  (N6-4 `telescope` with block seminorms).
- `FiniteGen.lean`: θ-independent `g`, holomorphy, reality, `G_eq_gI`, `gen_tail` (class and weighted bound of `g - f̂₀`).
- `FiniteNumerics.lean`: pure real lemmas (`step_first`, `step_single`, `step_big`, geometric sum, `N = ⌊κ/(12 ln 2)⌋`).
- `FiniteSetup.lean`: `GoodSched`, `setup_of_avg`, `goodSched_single` (single doubled-loss step).
- `FiniteMulti.lean`: Case A schedule `multiSched`, closed forms, star-norm weights, `Q/256`, `Q/16`, displacement sums.
- `FiniteCaseA.lean`: `goodSched_multi`.
- `Finite.lean`: `NfbConcl`, `goodSched_of_avg`, `nfb_core`, **`nfb`**, **`avg`** (facade module; imports the chain).

## Approach
Source proof of `bpP:p2:nfb` followed. Generic machinery (`Sched.seq`): `f₀=f`, `g₀=0`,
`g_{i+1} = iterG K {0} g_i f_i`, `f_{i+1} = iterF ... g_i f_i`; `IterSetup` bundles the admissibility data plus claimed bounds
`ε`, with the per-stage numerical inequality (`hstep`, the exact `(1-2u)⁻¹(...)δ ≤ ε_{i+1}` of `direct_step`) as a hypothesis;
`step_conc` uses `direct_step` (iterative_direct_b-e), `split` (componentwise displacement) and `iterative_direct_a`
(integer translation) with the same `IterHyp` (`iterHyp_two`, copy of the one inside `direct_step`). The telescope gives the
composition; the Hamiltonian identity is `H_i∘Φ_i = H_{i+1}` (definitional from `iterF`); `g` is `∑_j coeff (F j) · 0`
(`homRes K {0} f = f̂₀` on the domain, `homRes_zero`). The loss budget: `y₀ = E/(2πα₂(r/8)(s/6)) ≤ 3/(8κ)`.
 - `y₀ < e^{-κ/6}` (this includes `N = 0`, where e^{-κ/6} > 1/4 > y₀): single step, losses `(r/4, s/3)` (source Case B). 
 - else (Case A, forces `N ≥ 2`): `ε₁ = 3E/(4κ)` (source (2.1)), then `N` steps with ratio 1/4, `ρ=r/(8N)`, `σ=s/(4N)`.
 No Lipschitz or other extra premise; no hypothesis of the form of a conclusion.

## Checks
- Gate build: `inp_lake_build.sh /root/code/KAM-inp-p2312 KAM.Planetary.Averaging.Finite` → `Build completed successfully (9138 jobs)`;
  only warning: `Finite.lean:160:5 Variable name hstrict is not explicitly referenced` (see deviation 1).
- `sh scripts/lint_sources.sh`: exit 0; remaining message `KAM.lean is out of date; run scripts/gen_root_imports.py`
  (generated file, not edited; orchestrator to regenerate to include the 9 new modules); `check_lean_modules: PASS`,
  `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- `#print axioms KAM.Planetary.nfb` and `KAM.Planetary.avg`: `[propext, Classical.choice, Quot.sound]` (both).
- No `sorry`/`axiom`/`set_option`; no provider or DRAFT_SORRY import; only frozen Defs through `Averaging/Setting`.
  Every elaboration is at default heartbeats (no design signal).

## Deviations / notes
1. `avg`: the premise `hstrict : 64 e K E < α₂ r` is **unused** (as in the signature): `AvgHyp.small` (`E ≤ α₂ r/(128K)`) is already a
   field and is all the proof needs (the audit's note "strict 64e implies the bundled 128 bound" is consistent). No statement change.
2. `nfb` is proved via `nfb_core`, which adds the pointwise bound `‖g I - f̂₀(I)‖ ≤ E/(2πKs)` on `actionNbhd D (r/2)` (from
   `sup_le_wbound`); `avg` uses it. `NfbConcl` is a definition equal to the body of `nfb`.
3. Final domain: the construction's own domain is `Dom R_{m+1} S_{m+1} ⊇ Dom (r/2) (sbar+s/6)` (equal in Case A; strictly larger in
   the single-step case); results are restricted to `V`.
4. In Case B/N=0 the source's displacement constant for the first block uses the doubled loss: `3E/e < 3E`, `4E ≤ 9E`.
5. `step` constants: the induction is closed with `ε_{i+1} ≤ ε_i/4` via `Q/256 ≥ δ`, `star ≤ Q/16`, `e^{-2πKσ} ≤ 1/8` (these are
   the source's numbers up to a slightly cruder weight bound: the weight of `g_j` for `j ≥ 1` is bounded by 1/3).

## Suspected source errata (blueprint p2-averaging.tex, none affecting truth)
- Source step "Number of steps": claims `N=0` after Case A; in fact Case A (`e^{-κ/6} ≤ y₀ ≤ 1/16`) forces `κ ≥ 24 ln 2`, i.e. `N ≥ 2`,
  so `N = 0` is subsumed by Case B (harmless).
- Source (2.2)/Induction: weights for `j ≥ 1` are stated `≤ ½(⅓+⅓) ≤ ½` where `⅓` is the exact bound; no gap.
- Uncertainties: none known.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-12 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean): (1) statements = design signatures (nfb, avg; the full N _a lattice law on the same flow; tail/quadratic cases, N = 0, loss-budget schedule); consumes P23-10, P23-02 and the N telescope exactly; (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/Averaging/Finite*.lean (compare with branch inp-p2310).
