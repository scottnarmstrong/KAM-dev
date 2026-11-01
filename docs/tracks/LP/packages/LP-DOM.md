# Package LP-DOM: the whole-sublevel planar analytic domain (MAIN Lemma 8)

Wave 2. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
Base: `inp-lp-w1b`. It contains THR, MOM (landed), GEOMOD and DICT (under audit LP-W1B), with handoffs in
`docs/tracks/LP/audits/`.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 8, lines 244–271, with `source/AMENDMENTS.md`:
- **N2:** one shared compact `U`, containing the closed `4r_g`-tube about `L_δ`, with `Ω_B(4r_g) ≤ δ/16`.
- **N3:** `r_* ≤ 4r_g` explicitly. Every point of (22) is within sup distance `max(r_*, 4s, 4b)` of the compact
  set `K′`, which is what `tube` needs.

Roadmap §3 row 8 and the "representative analytic signature" in §3.

## Reuse (do NOT rebuild): track P's analytic packaging

- `KAM/Planetary/Exponential/ComplexTube.lean`: `tube` (holomorphic, fast-shift-periodic extension of a real
  analytic periodic function on a thin `complexTube K r` around a compact `K ⊆ W`), and `complexTube`.
- `KAM/Planetary/Exponential/Perturbation.lean`: the template. It applies `tube` to its core set inside
  `chartSafe`, takes `rho = min κ (r/2)`, and gets a sup bound `B₀` by compactness of a thickening.
  - Copy the method, with the sharp core below in place of the `AMDBox` core.
  - Do not use any `AMDBox` statement.
  - Never import `Exponential/Stopped.lean` (it imports a frozen theorem anchor).
- `Exponential/Setting.lean` (`chartSafe`, `chartAMD`), `Exponential/Dictionary.lean`, `Exponential/Lift.lean`
  (`liftChartHam`), `chart_perturbation_analytic` (in `Perturbation.lean`: the moving perturbation
  `fMov 1 1 ν ∘ poincareProd ν 1` is real analytic on `chartSafe ν`), and `fMov_poincareProd_shift`.
- LP: `Geometry.lean` (`BarrierState`, `exists_barrierCompact`), `Modulus.lean` (`strongThresholdModulus`,
  `tendsto_strongThresholdModulus`, `exists_cthickening_compact`), `PlanarDictionary.lean`
  (`lpChart_strongAMD`: `strongAMD ν (poincareProd ν 1 w) = chartAMD w`).

## Owned files

`KAM/Planetary/StrongAMD/AnalyticDomain.lean` (facade) and parts `KAM/Planetary/StrongAMD/AnalyticDomain/*.lean`.
Nothing else.

## Statements

Standing premises: `hν : ∀ i, 0 < ν i`, `2 ≤ n`, a compact `L ⊆ chamber ν`, `0 < δ`. MAIN's `𝓛` is the
image of `𝒜` under `a ↦ (ν_i √a_i)_i`. Also prove (D0) that this image is compact and inside `chamber ν` when
`𝒜` is compact and positive strictly ordered, in the form `PositiveStrictlyOrdered` you define (literal).
Write `Lδ := {I ∈ L | δ ≤ strongThreshold ν I}`.

1. **D1 (shared U, N2).** `Lδ` is compact. `∃ r_g > 0` with `U := Metric.cthickening (4 * r_g) Lδ` compact,
   `U ⊆ chamber ν`, and `strongThresholdModulus ν U (4 * r_g) ≤ δ / 16`. State the result with `U` and `r_g`
   exported, so later packages use exactly this `U`.
2. **D2 (core).** Define the sharp core `strongCore ν L δ r_g : Set (Phase (n + n))`: chart points `w` with
   - fast angles in `[0, 2π]`;
   - `∃ I⁰ ∈ Lδ` with `‖fast w.2 − I⁰‖ ≤ 4 r_g`;
   - `chartAMD w ≤ strongThreshold ν I⁰ − δ/4` (MAIN (21): `|z|²/2 = Σ Γ_i`).
   Prove it is compact, and that every core point lies in `poincareProdDom n`. The latter needs `Γ_i < I_i`:
   from `ΣΓ ≤ B(I) − 3δ/16` and `B ≤ I_i`, via MAIN line 251: `ΣΓ ≤ B(I⁰) − δ/4 ≤ B(I) − 3δ/16`.
3. **D3 (safety).** For `w ∈ strongCore`, `poincareProd ν 1 w` is a `BarrierState ν U (3δ/16)`. Hence
   `strongCore ⊆ chartSafe ν` (by `exists_barrierCompact` ⊆ collision-free).
4. **D4 (analytic extension and bound).** `∃ R > 0, ∃ M, ∃ fc`, all independent of `I⁰` and `μ`, such that:
   - `fc` is holomorphic on `complexTube (strongCore …) R`;
   - `fc` is periodic under the complexified fast shifts;
   - its real trace on the tube is `fMov 1 1 ν (poincareProd ν 1 w)`, with the real point in `chartSafe ν`;
   - `‖fc z‖ ≤ M` on `complexTube (strongCore …) (R/2)`.
   This is `tube` plus a compactness sup bound, as in `perturbation`.
5. **D5 ((22) containment, N3).** For `0 < r_* ≤ 4 r_g` and `s, b > 0` with `max r_* (max (4s) (4b)) < R/2`,
   and every `I⁰ ∈ Lδ`: every complex chart point whose
   - complex actions are within `r_*` of `I⁰`,
   - fast angles have imaginary parts `< 4s`,
   - complex slow coordinates are within sup distance `4b` of a real point of the ball
     `{x | (Σ_i (ξ_i² + η_i²))/2 ≤ B(I⁰) − δ/4}`
   lies in `complexTube (strongCore …) (R/2)`. State the three conditions literally (MAIN (22)).
6. **D6 (exact split).** On `chartSafe ν`, `movingHamiltonian 1 1 ν μ ∘ poincareProd ν 1 = h + μ · f`, with
   `h(Λ) = −Σ ν_i³/(2Λ_i²)` and `f = fMov 1 1 ν ∘ poincareProd ν 1` (no truncation; MAIN line 254). Reuse the
   existing identity (`movingHamiltonian_poincareProd` or `liftChartHam`).

Out of scope: the period-one rescaling and the engine's `ExtNFHyp` (package LP-NRR), and the Kepler-part
bounds `L`.

## Checks and stop condition

- `lp_build.sh` on each module (import order).
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of D0–D6.

Stop when done or blocked: report, never add a hypothesis silently. Expected size 800–1,800 lines. If `tube`'s
`Phase (n+n)` packaging forces an awkward restatement, report the exact shape you used.

## Handoff

`docs/tracks/LP/audits/LP-DOM-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-DOM.md`, then
`touch .drafts/READY-LP-DOM`.
