# Handoff W0-NORMAL (branch inp-wpc, worktree /root/code/KAM-inp-wpc)

Hard rules observed: no `set_option maxHeartbeats` (or any override); every file < 1500 lines
(largest 389); modules per AGENTS.md; no sorry/axiom/admit/unsafe/opaque; frozen files untouched.

## Files (all new, `KAM/Wave/Normal/`)
- `QuarticCoeff.lean`, `NonresAux.lean`, `Nonresonance.lean`, `AngleAvg.lean`, `ActionCoeff.lean`,
  `FinsuppAbs.lean`, `Nondegeneracy.lean`; plus generated `KAM/Root/Wave.lean`, `KAM.lean`
  (output of `scripts/gen_root_imports.py`, not hand-edited).
- Only imports: Mathlib, frozen `Lam`/`SineMode` definitions. No other W package.

## Blueprint labels proved
- `bpW:w0n:quartic-coeff` (QuarticCoeff.lean): `sineQuarticCoeff` (g_{ijkl} = ∫₀^π of four frozen `sineMode`);
  `sineQuarticCoeff_eq` (Iverson closed form); `sineQuarticCoeff_perm` (symmetry under all of S4);
  `quarticSel_of_quarticCoeff_ne_zero` / `sineQuarticCoeff_eq_zero_of_not_sel` (selection rule, `QuarticSel`);
  `sineQuarticCoeff_diag` (3/(2π)); `sineQuarticCoeff_diag_pair` (1/π, i≠j).
- `bpW:w0n:g-signed`: `sineQuarticCoeff_signed` (sum over ε∈{±1}³ coded by Bool, `signedSign`, `boolSign`);
  `abs_quarticCoeff_le` (the bound).
- `bpW:w0n:nonres` (NonresAux.lean + Nonresonance.lean): `quartic_nonresonance` for all m>0, all
  indices: g≠0, σ∈(ℤˣ)⁴, Σσ_t lam(v_t)=0 ⇒ `signSide σ v 1 = signSide σ v (-1)` (multisets).
  Proof follows the blueprint (31-case, 22-case types (1)(2)(3)) with these analytic lemmas:
  `lamExt_add_lt`, `lamExt_convex`, `lamExt_super`, `lamExt_pair_eq`, `lamExt_cross_eq`,
  `lamExt_big_lt`, `lamExt_three_ne`, `lamExt_two_two`. Type (1) uses an algebraic argument
  (ab=cd) instead of strict convexity; type (3) uses supermodularity f(x)+f(y) ≤ f(x+y)+f(0)
  (from convexity) instead of the derivative argument. Same statement, different proof route.
- `bpW:w0n:AB` / avgG (AngleAvg.lean, ActionCoeff.lean): stated as an identity of the genuine
  angle-averaged polynomial in the actions. `avgG` = average of G over the torus [0,2π]^N
  (product probability measure `angleMeasure`), q_j = √(2I_j)cos φ_j, I_j ≥ 0, G = ¼Σ g q̂q̂q̂q̂.
  - `avgG_eq`: ⟨G⟩ = 3/(16π)(4(Σ I_j/λ_j)² − Σ I_j²/λ_j²) (= (bpW:w0n:avgG)).
  - `partial_avgG_eq` (J={1,2}, N=2+n modes, I=(I_1,I_2), Z normal actions via `Fin.append`):
    avgG(I,Z) − avgG(0,Z) = ½Σ A_ii' I_i I_i' + Σ B_ji I_i Z_j with the CORRECTED
    `actionA` (A_ii=9/(8πλ_i²), A_12=A_21=3/(2πλ_1λ_2)) and `actionB` (3/(2πλ_jλ_i)).
    "avgG(I,Z)−avgG(0,Z)" is the part of ⟨G⟩ containing ≥1 tangential action, i.e. Ḡ.
  - Intermediate: `angleAvg_cos_four` (E[cos⁴-product] formula), `sum_quartic_moment`.
  - NOT formalized: the complex-coordinate resonant-monomial definition of Ḡ (Definition Qdef)
    and the step "resonant = averaged" of `stepW:w0n:resavg`; the brief asked for the averaged
    polynomial identity, so Ḡ is identified with the tangential part of ⟨G⟩ directly.
    `quartic_nonresonance` is the ingredient that would link them.
- `bpW:w0n:nondeg` (Nondegeneracy.lean, FinsuppAbs.lean), for every m>0, J={1,2}:
  - (i) `det_actionA`: det A = −63/(64π²(1+m)(4+m)) = −63/(64π²λ_1²λ_2²) ≠ 0; also `actionA_eq`
    (A = 3/(8π) D(4·11ᵀ−Id)D).
  - (ii) `pairing_ne_zero`: ⟨l,λ_N⟩ ≠ 0 for 1 ≤ |l| ≤ 2 (l : ℕ →₀ ℤ, index ν = mode−3, `l1Norm`).
  - (iii) `A3_holds`: for all k∈ℤ², l with 1≤|l|≤2, ∃ I, affineForm k l I ≠ 0 (affine in I, ω=λ_J+AI,
    Ω=λ_N+BI); `nondegeneracy` bundles (i)-(iii). Proof follows the blueprint (|l|=1, |l|=2).

## Labels NOT done
- `bpW:w0n:kappa`: it is a Remark (asymptotic O(j⁻³) claim), not a stated theorem; not formalized.
- Not in my package (not attempted): recon-bounded, gradient, algebra, cubic-bound, pde-equiv,
  formal-birkhoff, duffing.

## Checks
- Gate build (one call, all 7 modules): `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh
  /root/code/KAM-inp-wpc KAM.Wave.Normal.QuarticCoeff KAM.Wave.Normal.NonresAux
  KAM.Wave.Normal.Nonresonance KAM.Wave.Normal.AngleAvg KAM.Wave.Normal.ActionCoeff
  KAM.Wave.Normal.FinsuppAbs KAM.Wave.Normal.Nondegeneracy` → "Build completed successfully
  (2843 jobs)", no warnings.
- Lint: `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpc` exit 0; tail: "check_lean_modules: PASS (1630 Lean files, 0 comparator configurations) / FROZEN-ANCHOR GUARD OK / ABI HASHES OK (158 frozen declarations)" (root files regenerated with gen_root_imports.py first).
- `#print axioms` (file `.drafts/axioms_W0N.lean`): sineQuarticCoeff_eq, sineQuarticCoeff_signed,
  sineQuarticCoeff_perm, sineQuarticCoeff_diag, sineQuarticCoeff_diag_pair, abs_quarticCoeff_le,
  quartic_nonresonance, avgG_eq, partial_avgG_eq, det_actionA, pairing_ne_zero, A3_holds,
  nondegeneracy: all `[propext, Classical.choice, Quot.sound]`.

## Blueprint defects / deviations
- None found in the statements proved. Corrected coefficients (A, B) used as instructed; the
  printed P96-W factor 16 does not appear anywhere.
- Deviation (formulation): signed form uses `signedSign ε = (-1)^(1+#minus)` over Bool-coded ε;
  nonresonance multisets are `signSide` (Multiset sum); |l| is `l1Norm` over `ℕ →₀ ℤ`.
- Blueprint nondeg Step "A_3 |l|=2": the "s≠0" claim is proved by the explicit classification of
  l with |l|=2 (±2e_ν or ±e_a±e_b), consistent with the blueprint's argument.

## Design signals
- None: no proof near the default heartbeat limit; `grind` closes the combinatorial cases in
  `AngleAvg.prod_cosMoment_idxCount`.

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is off the frontier: source-faithful infrastructure (blueprint W0 normalization) used by several nodes
(W3, W5, W7). It has no provider and no seal, so skip audit item 1 and the seal-body probe.
1. Fidelity to blueprint-W/parts/w0-normalization.tex for `quartic-coeff`, `g-signed`, `nonres`, `AB`/`avgG` and
   `nondeg`. Coefficients must be the CORRECTED ones (A_ii = 9/(8πλ_i²), A_ij = B_ji = 3/(2πλ_iλ_j); errata E-PDE-W-1/2).
2. PRIORITY, the `AB` deviation: the package identifies Ḡ with the part of the angle average ⟨G⟩ containing at least
   one tangential action (`partial_avgG_eq`), instead of the blueprint's resonant-monomial definition (Definition
   Qdef together with step resavg). Is that a faithful realization of `bpW:w0n:AB` as consumed downstream (W3
   `quartic-ident`, W5 normal form, W7 frequency map)? Or is it a different statement that the consumers cannot use?
   Say exactly what is missing, if anything.
3. Angle convention: the average is over [0,2π]^N with q = √(2I)cos φ. Check it matches W0's actions convention
   (period-one campaign angles: φ = 2πθ).
4. `nondeg` (iii), `A3_holds`: is it the exact (A₃) the blueprint states, with the right affine form ω = λ_J + AI,
   Ω = λ_N + BI and the index set 1 ≤ |l| ≤ 2?
5. Hygiene. This is a SLIM worktree, so run lint only via `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpc`.
   Run the kernel replay of the 7 modules. Frozen, manifest and README must be untouched.

## Round 2 (response to audit 1, finding F1/F2)

Merged `inp` (root conflict resolved only by re-running `scripts/gen_root_imports.py`).

**F1 (missing Qdef / resavg bridge): attempted and done for finitely many modes.** New modules
`KAM/Wave/Normal/ResonantBalance.lean` and `KAM/Wave/Normal/ResonantPart.lean` (generic
`signSide` in `Nonresonance.lean`, now polymorphic in the index type; nothing else changed
semantically).
- `quarticG_eq_complex`: `G(q)` equals the complex quartic `quarticGComplex` in
  `z = (q + i p)/√2` (prefactor 1/16, sum over all 16 sign patterns of `quarticMonomial`).
- `resonantQuarticPart S m hm z` (Definition Qdef, finite modes): sum over tuples satisfying `S`
  of the monomials with vanishing divisor `quarticDivisor` (`∑ ± λ`), with coefficient
  `normQuarticCoeff = g/√(λλλλ)`. `Ḡ` is `S = tangentialQuarticTuple` (at least one of the first
  two modes), `G^nor` is `S = normalQuarticTuple`.
- `signBalanced_of_resonant` consumes `quartic_nonresonance` (g ≠ 0 and divisor 0 ⇒ plus/minus
  indices balanced); `signBalanced_sum_zero` (balanced ⇒ divisor and phases cancel; also the
  converse used for "paired ⇒ resonant"); `signBalanced_count` (4(P1+P2+P3) − 6 P4 balanced
  patterns, via `signBalancedCond`).
- `resonantQuarticPart_polar`: on `z_j = r_j e^{-iφ_j}` (any real `r`, any angles) the resonant part
  is the real polynomial `resonantQuarticReal`, independent of `φ` (resavg).
- `resonantQuarticReal_all`: full resonant part = `3/(16π)(4(Σ r_j²/λ_j)² − Σ (r_j²/λ_j)²)` (equals
  `avgG` via `avgG_eq`).
- **`resonantQuarticPart_tangential_eq` (bpW:w0n:AB)**: for `I ∈ ℝ₊²`, `Z ∈ ℝ₊ⁿ`, all `φ`,
  `Ḡ(z) = ½Σ A I I + Σ B I Z` (as a complex number, `z_j = √(I_j,Z_j) e^{-iφ_j}`).
  `partial_avgG_eq` and `avgG_eq` docstrings now state that they are the angle-averaged helper
  identity, not the definition of `Ḡ`.
- Axioms of the four main new results: `propext, Classical.choice, Quot.sound`.
- Renamed distinctive public names: `signBalanced*`, `quarticMonomial`, `quarticDivisor`,
  `normQuarticCoeff`, `isTangentialMode`, `resonantQuarticPart`, etc. (no short names).

**Still PARTIAL (F2, remains for the full source node):** (a) extension from finitely many modes
to the weighted sequence space ("extended by the absolutely convergent formula"), (b) the
statement for arbitrary complex `w_j w_{-j}` (here `|z_j|² = I_j ≥ 0` with arbitrary phases),
(c) G^nor is defined only as the all-normal tuple sum without the resonance filter (not needed).

Checks: gate build of `KAM.Wave.Normal.{ActionCoeff,Nonresonance,Nondegeneracy,ResonantBalance,
ResonantPart}` successful, no warnings; lint see below.
Lint: w_lint.sh exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
