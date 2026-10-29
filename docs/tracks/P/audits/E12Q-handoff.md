# E12Q prover handoff (branch inp-p14-e12, e240f38f; track P P14, run by the main orchestrator)


Branch `inp-p14-e12`, worktree `/root/code/KAM-inp-p14-e12`. Commits: `75c5ac70` (E12), `551a981b` (Q).
Working tree clean. KAM.lean not edited; no frozen or manifest file touched; no merge or push.

## Files
- NEW `KAM/Planetary/Exponential/Safety.lean` (231 lines). Module E12, namespace `KAM.Planetary`. Imports only
  Mathlib, frozen Defs (AMDBoxAdmissible, KeplerAxis, PlanetaryDriftExponent, PlanetaryTimeExponent,
  StoppedActionBound) and the implementation module `KAM.Planetary.AMD.Confinement` (A6, `amd`). It imports no
  provider, no frozen theorem anchor, and no `Exponential/Stopped`.
- CHANGED `KAM/Provider/Planetary/PlanetaryExponentialSafety.lean` (stub -> 91 lines). Namespace
  `KAM.Provider.Planetary`. Imports Mathlib and `KAM.Planetary.Exponential.Safety`. As the brief asks, the provider
  theorem `planetaryExponentialSafety` itself is NOT declared.

## Declarations
| Blueprint node | Lean declaration | Notes |
|---|---|---|
| `bpP:p14:expsafe` (parametric in `bpP:p14:stopped`) | `KAM.Planetary.expsafe_of_stopped` | binders `{n} (hn) (hstop) (B) (hB)` |
| `stepP:p14:es-const` (margin) | `KAM.Planetary.amdBox_exists_margin` | θ > 0 below every inner action gap; n·θ ≤ A₁ − A₀ |
| `stepP:p14:es-axis` | `KAM.Planetary.keplerAxis_drift_le`, `keplerAxis_eq_action_div_sq` | aᵢ = (Λᵢ/mᵢ)² when Λᵢ > 0 |
| exponent facts | `planetaryTimeExponent_pos`, `planetaryDriftExponent_pos` | 0 < a, 0 < b |
| Q (provider, parametric) | `KAM.Provider.Planetary.planetaryExponentialSafety_of_expsafe` | binders `{n} (hn) (hexpsafe) (B) (hB)` |

- `hstop` is the signed `stopped` proposition verbatim for the given `n`, `hn`:
  `∀ (B : AMDBox n), B.Admissible → ∃ B0 nu0 : ℝ, …`. Text copied from P14Signatures.lean lines 363–369 (sha256
  `24916d59…33f88`). The conclusion is the signed `expsafe` conclusion verbatim (lines 547–572).
- `hexpsafe` is the signed `expsafe` proposition verbatim for the given `n`, `hn`:
  `∀ (B : AMDBox n), B.Admissible → ∃ muStar c C : ℝ, …`. The conclusion is the frozen type of
  `planetaryExponentialSafety` verbatim. Its proof is `hexpsafe B hB`. The signed `expsafe` type equals the frozen
  type exactly (checked below).

## Planned one-liners (for the orchestrator, after E11 lands)
- In `Exponential/Safety.lean`, after adding `public import KAM.Planetary.Exponential.Stopped`, or in any module
  that imports both Safety and Stopped:
  `theorem expsafe {n : ℕ} (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible) : <signed type> :=`
  `expsafe_of_stopped hn (stopped hn) B hB`
- In the provider:
  `theorem planetaryExponentialSafety {n : ℕ} (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible) : <frozen type> :=`
  `planetaryExponentialSafety_of_expsafe hn (KAM.Planetary.expsafe hn) B hB`

Both one-liners were elaborated in a scratch file against verbatim sorry copies of `stopped` and `expsafe` (see
Checks). The results have exactly the signed `expsafe` type and the frozen type (`Expr.equal` true).

## Approach (blueprint p14a L295–311 and the design's provider-assembly row)
1. Take `B0 ≥ 1`, `nu0 ∈ (0,1]` and the stopped implication from `hstop B hB`. Take θ from `amdBox_exists_margin`
   (via `Finite.exists_min` over `Fin n`, which is nonempty because n ≥ 2).
2. Constants, all chosen before μ and z₀:
   - μ* = B0⁻¹ · min(nu0/2, (θ/2)^(b⁻¹));
   - c = B0^(−a);
   - C = B0^b · ∑ᵢ upperᵢ/massᵢ².
3. For 0 < μ < μ*, set ν = B0·μ. Then:
   - ν < nu0/2 < nu0 ≤ 1;
   - ν^b < θ/2, by `Real.rpow_lt_rpow` and `Real.rpow_inv_rpow`;
   - T := exp(c·μ^(−a)) = exp(ν^(−a)) ≤ ν⁻¹·exp(ν^(−a)), by `Real.mul_rpow` and ν ≤ 1;
   - δ := ν^b/2, which satisfies the stopped premise `ν^b/2 ≤ δ` by `le_rfl`.
   So `StoppedActionBound B μ T δ z₀` holds.
4. Margins: lowerᵢ + 2δ < innerLowerᵢ and innerUpperᵢ + 2δ < upperᵢ, because ν^b < θ ≤ each gap. Also
   A₀ + 2nδ < A₁, because n·ν^b < n·θ ≤ A₁ − A₀. Apply the sealed library theorem `amd` (A6) with T set to the
   literal `Real.exp (c * mu ^ (-planetaryTimeExponent n))`, so its clause group matches the target verbatim.
5. Axis drift: for |t| ≤ T, `abs_le` gives t ∈ Icc(−T, T). Both actions lie in (0, upperᵢ): z(t) is in the outer
   region and z₀ in the inner one, with 0 < lower < innerLower and innerUpper < upper. Then
   aᵢ(z t) − aᵢ(z₀) = (Λ − Λ₀)(Λ + Λ₀)/mᵢ², so the drift is at most 2(upperᵢ/mᵢ²)·δ = B0^b·(upperᵢ/mᵢ²)·μ^b ≤ C·μ^b.

## Checks (exact output)
- Gate build: `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e12
  KAM.Planetary.Exponential.Safety KAM.Provider.Planetary.PlanetaryExponentialSafety`
  ```
  [inp-gate] slot 2 acquired 15:27:04 for KAM.Planetary.Exponential.Safety KAM.Provider.Planetary.PlanetaryExponentialSafety
  ✔ [9129/9130] Built KAM.Planetary.Exponential.Safety (5.8s)
  ✔ [9130/9130] Built KAM.Provider.Planetary.PlanetaryExponentialSafety (4.5s)
  Build completed successfully (9130 jobs).
  ```
  There are no warnings and no `sorry` in either file. The only warnings in the log come from pre-existing modules
  (Closure, Kepler/Energy, ODE/Exit).
- `sh scripts/lint_sources.sh` (exit 1, for the expected reason only):
  ```
  KAM.lean is out of date; run scripts/gen_root_imports.py
  check_lean_modules: PASS (1333 Lean files, 0 comparator configurations)
  FROZEN-ANCHOR GUARD OK
  ABI HASHES OK (144 frozen declarations)
  ```
  The generator's pending diff is exactly one line, `+public import KAM.Planetary.Exponential.Safety`. The provider
  is quarantined and correctly skipped. The orchestrator must regenerate KAM.lean.
- `python3 -I main_shortname_check.py /root/code/KAM-inp-p14-e12 KAM.Planetary.Exponential.Safety
  KAM.Provider.Planetary.PlanetaryExponentialSafety` gives `short-name check OK (no reused public short name)`
  (exit 0).
- Line width ≤ 100 in both files; no `maxHeartbeats` or other override; no `native_decide`, axiom or
  EuclideanSpace.
- Scratch statement check (not committed;
  `/tmp/claude-0/-root-code-KAM-inp-p14-e12/c92de78c-baf0-43fd-84fd-80c770b6e29b/scratchpad/CheckE12Q.lean`).
  It holds verbatim sorry copies of the signed `stopped` and `expsafe`. A meta check builds
  `∀ {n} hn, (signed hyp for n hn) → (signed concl for n hn)` and compares it with each parametric theorem's type:
  ```
  KAM.Planetary.expsafe_of_stopped: eqv true, equal false, defeq true
  KAM.Provider.Planetary.planetaryExponentialSafety_of_expsafe: eqv true, equal false, defeq true
  Scratch.expsafe vs KAM.Planetary.planetaryExponentialSafety: eqv true, equal true
  Scratch.expsafe' vs Scratch.expsafe: eqv true, equal true
  Scratch.planetaryExponentialSafety' vs KAM.Planetary.planetaryExponentialSafety: eqv true, equal true
  ```
  `eqv` is alpha-equivalence. `equal false` on the first two lines comes only from the hypothesis binder names
  (`hstop`, `hexpsafe` against the anonymous arrow that the check builds). `expsafe'` and
  `planetaryExponentialSafety'` are the two planned one-liners, elaborated against the exact types.
- `#print axioms` (scratch file):
  ```
  'KAM.Planetary.expsafe_of_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Provider.Planetary.planetaryExponentialSafety_of_expsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Planetary.amdBox_exists_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Planetary.keplerAxis_drift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Planetary.planetaryTimeExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Planetary.planetaryDriftExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Planetary.keplerAxis_eq_action_div_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

## Uncertainties
- None mathematical. The only extra hypotheses are `hstop` (the signed `stopped`) and `hexpsafe` (the signed
  `expsafe`), both verbatim. `amd` (A6) is used as the already-proved library theorem, not assumed.
- `hn` is otherwise unused in `planetaryExponentialSafety_of_expsafe`, so it is referenced via `have _hn := hn`,
  the same idiom as `amd`. It is kept so that the binder order is `hn (expsafe hn) B hB`.
- Heartbeats: no design signal. Safety builds in 5.8 s and the provider in 4.5 s.

## Suspected errata and deviations
- Errata: none.
- Deviation 1 (constant choice, harmless): C = B0^b · ∑ᵢ upperᵢ/massᵢ² replaces the blueprint's
  B0^b · maxᵢ upperᵢ/massᵢ² (p14a `es-const`). The new C is larger and positive and still depends only on (n, B).
  The frozen statement is existential in C and is unchanged.
- Deviation 2 (θ): θ = min(minᵢ gaps, (A₁ − A₀)/n), without the blueprint's κ and ε_D. Those terms are used only
  inside the proof of `stopped`, which is a hypothesis here. μ* uses the exponent b⁻¹ (= 1/b).

ORCHESTRATOR NOTE: the helpers planetaryTimeExponent_pos / planetaryDriftExponent_pos were renamed safety_timeExponent_pos / safety_driftExponent_pos (E11's Stopped.lean, still proving on inp-p14-e11, declares planetaryDriftExponent_pos).

CONTEXT: the last frozen theorem of the original project, planetaryExponentialSafety (manifest planetary.d25.planetaryExponentialSafety.v1, DRAFT_SORRY), is assembled as E11 stopped -> E12 expsafe -> Q provider. E11 is still proving; this package is PARAMETRIC in stopped (the parametric-critical-path pattern used to seal fixedSunPlanetaryKAM on 2026-10-29): expsafe_of_stopped's only extra hypothesis hstop must be the signed stopped proposition VERBATIM (P14Signatures.lean lines 363-369), and planetaryExponentialSafety_of_expsafe's only extra hypothesis hexpsafe the signed expsafe proposition VERBATIM (lines 547-572); such a hypothesis is not a conclusion-shaped premise, any other added hypothesis is. Design docs/tracks/P/design/P14-LEAN-DESIGN.md (E12 and Q rows, provider assembly near line 439) and its audits.

AUDIT FOCUS: (1) hstop and hexpsafe are byte-for-byte the signed propositions (compare against the signature file); (2) the conclusions are exactly the signed expsafe type and the FROZEN type of planetaryExponentialSafety (KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean; check with an exact-type probe); (3) the quantifier order of the frozen statement is respected (n, hn, B, hB fixed BEFORE muStar, c, C; every positive mu < muStar; every z0 in the inner region; design line 439); (4) no other premise, no provider import outside the provider, no import of a DRAFT_SORRY anchor; (5) hygiene: names (KAM and Mathlib), lines <= 100, no native_decide or axiom. Audit ONLY KAM/Planetary/Exponential/Safety.lean and KAM/Provider/Planetary/PlanetaryExponentialSafety.lean.
