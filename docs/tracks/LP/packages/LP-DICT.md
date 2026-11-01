# Package LP-DICT: the planar regular chart as MAIN Lemma 7 (dictionary, no second chart)

Wave 1. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 7, lines 193–242 (N1 typo fixed at 238), with `AMENDMENTS.md`; §1 (2) for
`C`. Roadmap §1 (sign convention: MAIN `(x, y)` = repository `(ξ, −η)`, i.e. repository `(ξ, η) = (x, −y)`),
§3 row 7, §5. The chart already exists: `KAM/Planetary/Poincare/{Chart,Symplectic,Bijective,Product}.lean`
(`poincare`, `poincareDom`, `poincare_elements`, `poincare_image`, `poincareInv`, `poincare_symplectic`,
`analyticOnNhd_poincare`, `poincare_periodic`, `poincareProd`, `poincareProdDom`, `regionProd`,
`poincareProd_symplectic`, `poincareProd_image`, `movingHamiltonian_poincareProd`). **Do not build a second planar
chart**: prove that the existing one, at `κ = 1` and masses `ν`, is MAIN's chart and export the identities the
later packages consume.

## Owned files

`KAM/Planetary/StrongAMD/PlanarDictionary.lean` (split with a facade if needed). Nothing else.

## Theorems to prove (premises: `∀ i, 0 < ν i`; `κ = 1`)

1. **Region.** `regionProd ν 1` equals the set of `z : Phase (n * 2)` with, for every `i`,
   `0 < planeLength (bodyVector z.1 i)`, `keplerEnergy ν z i < 0`, and `0 < L_i` (i.e. `ProgradeElliptic ν z`,
   frozen definition), so `poincareProd ν 1 '' poincareProdDom n` is exactly MAIN's
   "positive-angular-momentum negative-energy region" (line 195).
2. **Dictionary per planet** (`w ∈ poincareDom`, `z = poincare ν 1 w`), in the frozen per-body notation:
   `keplerAction ν · = w.2 0` (`I = Λ`), `keplerEnergy = −ν³/(2I²)`, `L = I − Γ` with `Γ = poincareGamma w`,
   eccentricity vector `keplerEccVector = poincareV w`, `e² = 1 − (1 − Γ/I)²`, and MAIN's `(k, l) = b_e (x, −y)`
   matches `poincareV w = b_e (ξ, η)` under `(ξ, η) = (x, −y)` (state it as an explicit identity; MAIN line 199).
   Reuse `poincare_elements`; this item is mostly restatement in `bodyVector`/`keplerAction` form for
   `Phase (n * 2)` via `poincareProd`.
3. **AMD in the chart.** For `w ∈ poincareProdDom n`: `strongAMD ν (poincareProd ν 1 w) = ∑ i, poincareGamma
   (planetBlock w i)` and `physicalAMD ν (poincareProd ν 1 w)` equals the same sum (`L > 0` on the chart), i.e.
   `C = Σ Γ_i = |slow|²/2`, which is what MAIN (21) uses. `strongAMD` is defined by package LP-MOM (in flight);
   until it lands, prove the statement for `physicalAMD` and for the literal expression
   `(∑ i, keplerAction ν z i) - |totalMomentum z|`, and report; the orchestrator joins the names at landing.
4. **Hamiltonian and symplectic form.** Re-export, at `κ = 1`, `movingHamiltonian 1 1 ν μ ∘ poincareProd ν 1 =
   hProd 1 ν + μ · (disturbing part)` on `poincareProdDom n`, symplecticity, real analyticity, periodicity in the
   fast angles, and the inverse on `regionProd ν 1`, as one-line corollaries with MAIN-facing docstrings (L7
   "real analytic symplectic diffeomorphism … onto"). Do not reprove what exists.

## Checks and stop condition

`lp_build.sh` on the new module; `lp_lint.sh` exits 0; `#print axioms` of items 1–4. Stop when done or blocked
(report; never add a hypothesis silently). Expected size 200–600 lines.

## Handoff

`docs/tracks/LP/audits/LP-DICT-handoff.md` (committed) and `.drafts/handoff-LP-DICT.md`, then
`touch .drafts/READY-LP-DICT`.
