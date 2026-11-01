# Package LP3-CELL: the sealed partial-convexity theorem applied uniformly over a finite cell family, forward and backward in time (generic in `k`)

LP3. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff; module
docstrings carry the SPEC §4 sentence). Base: `inp-lp-lp3cell` = `inp-lp-lp3kep` (LP3-KEP) + `inp-lp-lp3cp`
(LP3-COVERPERT; its `isPartialPerturbation_neg_nekCell` already covers `−P` for the LP perturbation) + `inp-lp`.

This is the plan's recommended option "share the cellwise application" (`docs/tracks/LP/lp3/LP3-PLAN.md` §5, after
the table): one generic theorem in `k` that the planar (`k = n`) and spatial (`k = n + n`) drift suppliers both
consume. It is also the early interface test of the frozen theorem (the role of LP3-ONE), but without any LP domain
data, so it does not wait for LP3-COVERPERT.

## Import ruling (D58 in docs/DECISIONS.md, main 56e4a2c4)

LP modules MAY import the **sealed** frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` and the
frozen definitions. Never import any `KAM/Provider/*` module.

## Read first

- The frozen theorem `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:48–77` and its definitions in
  `KAM/Frozen/Nekhoroshev/Defs/` (`IsSolutionOn`, `IsPartialPerturbation`, `innerCore`, `HasDefiniteFastPart`).
- The plan, §2.1 (the interface read exactly), §2.4 steps 6–8 (forward and backward application) and §6 (risks).
- Track P's `KAM/Planetary/Exponential/Stopped.lean`: `stopped_hamiltonian_neg` (≈180–189),
  `stopped_isSolutionOn_reverse` (≈216–241), and the forward/backward application of the frozen theorem (≈300–365).
  Generalize them; do not import `Stopped.lean`. If a needed lemma there is public and fits exactly, you may import its
  defining module only if that module does not import a provider (check).
- LP3-KEP: `KAM/Planetary/StrongAMD/Nek/Kepler.lean` (`lp3_kepler_data`, `keplerC_clauses`, `keplerCNeg_clauses`).

## Statements (`hn : 2 ≤ n`, `hk : 1 ≤ k`, a `Fintype ι`)

1. **Uniform threshold over a finite family.** Given cells `j : ι` with data `G j, G' j : Set (Fin n → ℝ)`,
   `D j : Set (Phase k)`, `ρ j`, all satisfying the frozen theorem's domain premises (open, convex `G`, `G'`, open `D`,
   `0 < ρ j`, collar), and fast data `h` with the premises `hhol … hdef` on every `actionNbhd (G' j) (ρ j)` **for both
   `h` and `−h`**: `∃ μ₀ > 0` such that for every `μ ∈ (0, μ₀)`, every `j`, and every `P` with
   `IsPartialPerturbation (G' j) (D j) (ρ j) P`, the frozen conclusion holds for `(h, P)` **and** for `(−h, −P)`. That
   is, the minimum over `ι × {±}` of the frozen thresholds. Check that `IsPartialPerturbation … (−P)` follows from
   `… P` (prove it if so; if not, report the exact obstruction).
2. **Time reversal.** If `w` solves the field of `degenerateHamiltonian (realPart h) (fun _ x => (P (complexifyPhase
   x)).re) μ` on an interval containing `[t, 0]` (`t < 0`), then `s ↦ w (−s)` solves the `(−h, −P)` field on
   `Icc 0 (−t)`, in the exact `IsSolutionOn` shape (fast actions in `G j`). State it with the sign convention used
   by the frozen `degenerateHamiltonian` and `hamiltonianVectorField`; reuse the repository's negation lemmas.
3. **Two-sided drift corollary** `cell_drift_two_sided`: for `μ ∈ (0, μ₀)`, a cell `j`, `P` as above, and `w` solving
   the `(h, P)` field on an open interval containing `uIcc 0 t`, with `|t| ≤ μ⁻¹ exp(μ^{−partialTimeExponent n})`,
   `fast (w 0).2 ∈ innerCore (G j) (μ ^ partialDriftExponent n)`, fast actions in `G j` and slow pairs in
   `innerCore (D j) (μ ^ partialDriftExponent n)` on `uIcc 0 t`: `‖fast (w t).2 − fast (w 0).2‖ ≤ μ^{b_n}/2`.
   The hypotheses are exactly the frozen theorem's orbit premises transported to `uIcc 0 t`; nothing else. This is a
   conditional helper with a distinct name, not a source result.
4. **Kepler instance** `kepler_cell_drift`: statement 3 with `h = planetaryKeplerC ν`, the fast premises discharged
   by LP3-KEP for cells with `G' j ⊆ cthickening ρ₀ U`, `ρ j ≤ ρ₀` (`ρ₀` from `lp3_kepler_data`, chosen from
   `(ν, U)` only).

## Owned files

`KAM/Planetary/StrongAMD/Nek/Cells.lean` (split into `Nek/Cells/*.lean` with a facade if it grows past about 400
lines). Do not edit other files (the generated `KAM/Root/Planetary.lean` excepted).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of statements 1–4: exactly `[propext, Classical.choice, Quot.sound]`. The sealed anchor's proof
  currently ends in its provider; if `#print axioms` shows `sorryAx` through the frozen anchor, REPORT it exactly
  (do not work around it): the orchestrator checks the seal status.

If a frozen premise cannot be met as stated, STOP and report the exact mismatch. Expected size 200–400 lines.

## Handoff

`docs/tracks/LP/audits/LP3-CELL-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP3-CELL.md`, then
`touch .drafts/READY-LP3-CELL`.
