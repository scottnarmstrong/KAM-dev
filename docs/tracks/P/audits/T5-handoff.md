# T5 prover handoff (branch inp-p11c-t5, 8aebe598; offloaded package run by the main orchestrator)


Worktree `/root/code/KAM-inp-p11c-t5`, branch `inp-p11c-t5`.  Not merged, not pushed; `KAM.lean` and
`README.md` untouched (the new modules need `scripts/gen_root_imports.py` by the orchestrator).

## Files (all new)

`KAM/Planetary/PlanarTorsion/PairJet.lean` (facade, contains `pair_jet`) and
`KAM/Planetary/PlanarTorsion/PairJet/`:

| file | lines | content |
|---|---:|---|
| `Defs` | 37 | `p11c_pairAverage`, `p11c_pairJet` (verbatim from `P11CSignatures.lean`) |
| `Average` | 240 | `stepP:p11b:pj-avg`: mean over `[0,2π]²` of `e^{ipλ₀}e^{irλ₁}g(λ₀-λ₁)` (`p11cPJ_cell`, `…_neutral`, `…_charged`), Laplace identification `p11cPJ_laplace` |
| `Terms` | 188 | finite Fourier sums `PJTerm`, `p11cPJsum`, `p11cPJ_sum_integral_{neutral,charged}` |
| `Reduction` | 347 | `pj-red`: explicit table `p11cPJtab_j_k` of `b_{s}^{(k)}` (`s=3/2..9/2`, `k≤6`) in `b_{1/2}^{(0,1)}` |
| `Rot` | 88 | `pj-bin`: rotated jet `p11cPJN`, the 7 pieces `p11cPJq*` of the binomial expansion |
| `Piece22`, `Piece4a/b/c` | 328/995/630/852 | generated: Fourier expansion of each piece (neutral/charged lists), exact `ring` identity, torus average |
| `Combine2`, `Combine4` | 134/294 | `pj-red`: degree-2 / degree-4 averages equal the displayed `A,B,p₁..p₆` (`p11cPJ_avg2/4`) |
| `Ray` | 298 | `pj-formal`/`pj-bin`: jet of the integrand along a line, `p11cPJ_ray` (inverse norm of a jet by uniqueness) |
| `Diag` | 215 | diagonal derivatives vs jets (`p11cPJ_diag_coeff`), polarization (`p11cPJ_jetEq_of_diag`) |
| `Diff` | 365 | `pj-formal`: joint analyticity of the integrand, differentiation under the integral (`p11cPJ_diag_integral`) |
| `Bridge` | 286 | analyticity and evenness of `p11c_pairAverage` via the Part-8 secular average |
| `PolyJet` | 104 | `p11c_pairJet` is an even analytic polynomial, exact line jet |

## Node → declaration

* `bpP:p11b:pair-jet` (the integral part, T5 share): `pair_jet` (`PairJet.lean`).  The coefficient part
  (`p11c_pairCoeffs`, `pair_series`, `pair_quadratic_consistency`) is T4's and is only *used* here.
* `stepP:p11b:pj-formal`: `Bridge` (`p11cPJ_pairAverage_analyticAt`, `…_even`), `Diff`
  (`p11cPJ_diag_integral`, `p11cPJF_analyticAt`), `Diag`, `Ray` (`p11cPJ_ray`).
* `stepP:p11b:pj-bin`: `Rot`, `Ray` (`p11cPJrot`, `p11cPJcJet_sq`), `Piece*_eq`.
* `stepP:p11b:pj-avg`: `Average`, `Terms`, `Piece*_avg`.
* `stepP:p11b:pj-red`: `Reduction`, `Combine2`, `Combine4` (`p11cPJ_mu2_i`, `p11cPJ_mu4_i`, `p11cPJ_avg2/4`).
* `stepP:p11b:pj-cons`: T4 (`pair_quadratic_consistency`); here `p11cPJ_avg2` reproduces the same `A, B`.

## Approach

1. `Bridge`: for `D = (G=m₀=m₁=m₂=1)`, axes `(a,1)`, the slow variable `x(z)=(ξ,Λ,η)` with
   `(ξ,η)_i = √(2Λ_i/(1+√(1-|v_i|²))) v_i` has `poincareV = v` (`p11cPJ_poincareV`), the chart gives
   `q_i = Λ_i² p11c_orbit(λ_i, v_i)` (`p11cPJ_position`), so `secular D false (x z) = -p11c_pairAverage a z`.
   Part 8 `perturbation_analytic` and `evenness` then give analyticity at `0` and evenness near `0`.
2. `Diff`: `p11cPJF` is analytic jointly on an open neighbourhood of `[0,2π]²×{0}`; `SecularForm.e_diff`
   (through `p11cPJequiv : (Fin 4 → ℝ) ≃L Phase 2`) gives `D^j W(0)(w,…,w) = (2π)⁻² ∫ D^j F_l(0)(w,…,w) dl`.
3. `Ray`: along `t ↦ t w`, `F_l = N^{-1/2}`, `N = |αO₁-O₂|²` has the jet `N̂ = U·Ū` (T2 `orbit_line_isJet`);
   `P = N^{-1/2}`-jet is checked by `P²N̂ = 1 (mod t⁵)` and uniqueness (`p11cPJ_isJet_inv_norm`), no Taylor
   series of `(1+x)^{-1/2}` is used.  `Diag` turns line jets into diagonal derivatives.
4. Rotated variables `η=ζe^{-iλ}` make the orbit jet coefficients constant rationals (`Rot`); every piece
   `S^{2ℓ+1}·(N̂_i…)` is expanded (generated code, one `ring` identity each) into `Σ coef·E₀^…E₁^…S^e`, the
   charged terms (`b-a+d-c ≠ 0`) integrate to `0` and the neutral ones to `(2π)²b_{e/2}^{(k)}`.
5. `Reduction` + `Combine*`: after the explicit table, each of the 4+9 monomial coefficients is a rational
   identity in `α, b₀, b₁` matched (by `field_simp; ring`) with the displayed `p11c_pairCoeffs`.
6. Orders `1,3,5`: both sides are even (`iteratedFDeriv_odd_eq_zero`); orders `0,2,4` by 3–5.
   Hence only the 4-jet of the orbit (T2) is needed, not a 5-jet.

## Checks run

* gate: `inp_lake_build.sh /root/code/KAM-inp-p11c-t5 KAM.Planetary.PlanarTorsion.PairJet`: `Build completed successfully (9158 jobs)` (final build after the whitespace wrapping; all 17 modules ✔/⚠, warnings are unused-simp-argument linter notes only)
* `scripts/lint_sources.sh`: only `KAM.lean is out of date; run scripts/gen_root_imports.py` (expected: new modules, KAM.lean not edited); `check_lean_modules: PASS (842 Lean files)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`; no sorry/axiom/override/long-line/size finding
* `#print axioms KAM.Planetary.pair_jet`: `[propext, Classical.choice, Quot.sound]`
* No `sorry`, no `maxHeartbeats`/`maxRecDepth` override anywhere; largest file 995 lines.

## Design signals (default heartbeats; no override used)

* Elaborating a literal list of more than ~130 `PJTerm` structures with symbolic complex coefficients, and an
  avg-statement containing the full coefficient sums, exceeded 200000 heartbeats.  Remedy: lists split into
  chunks of ≤ 36 entries and the coefficients factored into defs `p11cPJC_*`.
* The 517-term `ring` identity (`p11cPJ_q4114_eq`) and the `field_simp; ring` of the 9 degree-4 monomial
  identities pass at default heartbeats.  Piece4c needs ≈ 10 min wall time on a loaded machine.
* The design's estimate (750 lines) was far too low: 17 files, ≈ 5600 lines (≈ 4000 of them generated).

## Deviations / notes

* New names only (prefix `p11cPJ`, `PJTerm`); `PJTerm.fourierIdx` was renamed from `freq` after a short-name
  clash check.  Duplicate-name grep over `KAM/` found no clash.
* `e_diff_slice` of Part 8 is specialised to `k=2`, `Vec 2×Vec 2`; `Diff` re-proves the slice lemma for
  `k=4`, `Vec 2×Vec 4` (`p11cPJ_iteratedFDeriv_slice`, `p11cPJ_e_diff`), then reuses `SecularForm.e_diff`.
* `pair_jet` needs neither `U8a laplace_def` nor the Part-8 Laplace series; it uses `p11c_laplace` (T3) only.
* Generators (Python/sympy, in the session scratchpad, not committed) were used to *write* the expansions;
  every identity is checked by Lean (`ring`/`field_simp`), no numerical or CAS output is assumed.

## Suspected errata

None found in the pinned sources: the displayed coefficients `A,B,p₁..p₆` of `bpP:p11b:pair-jet` reproduce
exactly the averaged binomial expansion (this is now a theorem, `Combine2/4`).

## Uncertainties

* `KAM.lean` must be regenerated for the 17 new modules (`scripts/gen_root_imports.py`).
* `Piece4*` rebuild time is long (≈ 25 min total under load).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T5 (the actual averaged interaction pair_jet; T2/T4, U8a differentiation, U8b symmetries) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/PlanarTorsion/PairJet*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
