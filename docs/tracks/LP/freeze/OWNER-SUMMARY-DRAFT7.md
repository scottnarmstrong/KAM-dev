# Track LP freeze, draft 7: owner summary

This summary accompanies the exact text in `docs/tracks/LP/FREEZE-PROPOSAL.md` (draft 7 revision 1, branch
`inp-lp-freeze7`) and its 128 file texts in `docs/tracks/LP/freeze/draft7/`. The text passed two independent statement
audits on codex-2 (Sol medium):
- audit 1: RETURN FOR REVISION (F1, F2), both fixed;
- the delta audit of revision 1: PASS WITH NOTES, with 0 blocking findings. Its three editorial notes are being
  applied. Nothing is frozen until the owner approves that exact text. D59 approved the rulings
only.

The source is the LP manuscript `docs/tracks/LP/source/MAIN.md` with `AMENDMENTS.md`: sharp Laskar–Petit
strong-AMD stability, with exponentially long safety for planetary systems.

## What each anchor says

Setting: `n ≥ 2` planets with mass ratios `ν_i > 0` (normalized so that `max ν = 1`) and small parameter `μ`, around
a star, in the plane (LP0, LP1) or in space (LP2). `Λ` are the canonical actions, `a`, `e` the Kepler axes and
eccentricities, and `C = ΣΛ_i − |L|` the strong angular momentum deficit (AMD). `B(Λ)` is MAIN's sharp threshold
(3): the minimum over adjacent pairs and the star of the AMD needed for a collision or orbit crossing.

- **LP0, the sharp barrier (MAIN Lemma 5).** For a compact set `U` of action vectors in the chamber
  `Λ₁ < … < Λ_n`, and a margin `m > 0`, there are fixed distances `d⋆` and `d_pair` with the following property.
  Every planar state whose actions lie in `U` and whose strong AMD is at most `B(Λ) − m` has:
  - its perihelia at least `d⋆` from the star;
  - adjacent orbits radially separated by at least `d_pair`, and all body–body distances at least `d_pair`;
  - every planet's angular momentum at least `m` in size, all with the sign of the total.

  These states form a compact, collision-free set. No dynamics is involved.
- **LP1, planar exponential safety (MAIN Theorem 15 with Lemma 16).** Fix a compact set `A` of ordered positive axes,
  a margin `δ > 0`, and Diophantine constants `γ > 0`, `τ > n − 1`. The constants are chosen first; then for every
  `0 < μ ≤ μ₀` and every initial state, the theorem below holds.
  - **Hypotheses on the initial state:** negative Kepler energies, axes in `A`, Diophantine frequencies
    `ν_i³/Λ_i³`, and strong AMD at most `B(Λ) − δ`.
  - **Conclusion:** the unique solution of the planetary equations exists on `[−T, T]` with
    `T = T₀ exp(c μ^(−1/(2(τ+1))))`. It is the actual Newtonian `(1+n)`-body motion. Throughout that time:
    - the orbits stay elliptic, and the strong AMD stays below `B − δ/2`;
    - the actions and axes drift by `O(√μ)`, and the AMD by at most `n A_Λ √μ`;
    - star and body–body distances stay at least `d⋆` and `d_pair`, so there are **no collisions and no orbit
      crossings**;
    - the actual-velocity osculating ellipses are valid and stay close to the canonical ones, with their own perihelia
      and gaps at least `d⋆/2` and `d_pair/2`.

  No assumption is made on the secular dynamics, and there is no prograde assumption.
- **LP1-H** is LP1 at `τ = n − 1/2`, with the explicit headline time `T₀ exp(c μ^(−1/(2n+1)))`.
- **LP2, spatial exponential safety (MAIN Theorem 19).** The same statement in three dimensions. The strong AMD uses
  the Euclidean length of the total angular momentum. There is **no** prograde, small-inclination, nonzero total
  angular momentum, alignment or secular premise; the frame alignment is done inside the proof.
- **LP2-H** is LP2 at `τ = n − 1/2`, with exponent `1/(2n+1)`.

The general-mass versions, which have no `max ν = 1`, are proved too and stay ordinary theorems (OD-3).

## Choices embedded in the text

1. **(OD-1)** The AMD is `ΣΛ − |L|`, orientation-free, as in MAIN (2). It is not the frozen signed `physicalAMD`.
2. **(OD-2, OD-11 (b))** Every meaning-carrying quantity lives on its source carrier:
   - thresholds are taken on ordered actions, with `2 ≤ n`;
   - the strong AMD, the Kepler elements and the osculating elements go through source subtypes (negative-energy
     states; valid osculating states);
   - each has a characterization theorem, frozen with it (34 theorems in all).

   The total formulas stay internal helpers in the frozen closure, certified only on their carriers. The planar
   theorems keep the already-frozen `keplerAxis/keplerAction/keplerEccVector`. The spatial theorems use
   `spatialSource*` throughout.
3. **(OD-3)** The anchors keep MAIN's normalization `max ν = 1`. LP0 has no `μ`, so it is stated for any positive
   masses.
4. **(OD-4)** `τ > n − 1` is free. The two `τ = n − 1/2` corollaries are separate anchors in the explicit-exponent
   form. *This is a proposal; the owner decides.* They add no content but put the headline exponent `1/(2n+1)` on
   record.
5. **(OD-5, OD-9)** "No crossing" means three things:
   - canonical annuli: perihelia `≥ d⋆`, adjacent gaps `≥ d_pair`;
   - all star and all pair distances;
   - actual-velocity osculating annuli with half gaps.

   The two inequalities between `μ₀` and the osculating constant are displayed; the order of choice is internal.
6. **TEXT CHANGE: the Diophantine condition (option C).** LP1, LP1-H, LP2 and LP2-H state MAIN (5) as the
   already-frozen `KAM.IsDiophantine γ τ ω` (D20), with the exact frequency vector `ω_i = ν_i³/Λ_i³`. Draft 7 had
   written the condition out with a separately frozen ℓ¹ mode size `modeSize`. Freezing that definition would have
   forced a rebuild of a shared core module and of all the lunar certificate data.
   - **Why the two are the same condition.** `IsDiophantine γ τ ω` says `γ / (Σ_i |k_i|)^τ ≤ |Σ_i k_i ω_i|` for every
     integer vector `k ≠ 0`. That uses the same ℓ¹ size of `k`, the same `γ`, the same `τ` and the same `ω`. For
     `k ≠ 0` the size `s = Σ|k_i|` is positive, so `γ s^(−τ) = γ / s^τ`.
   - A proved bridge lemma gives the pointwise equivalence, and the delta audit checks it as a literal equivalence.
   - The half-integer corollaries use `τ = n − 1/2` inside the same predicate.
7. **Spatial reconstruction** (statement audit, F1). The Newtonian reconstruction in LP2 goes through guarded maps
   that take the proofs of `ν_i > 0` and `μ > 0` (`spatialSourceBarycentric*`). The positivity of `μ` is therefore
   named as a binder; it is the same hypothesis, not a new one. The planar maps were frozen earlier and are
   unchanged.
8. **LP0 under (b)** writes the AMD of a physical state through the source carrier, as LP1 does. Its deficit clause
   applies the threshold formulas to abstract actions `I ∈ U` and eccentricities `e ∈ [0,1]ⁿ`, never to a physical
   state.
9. **Names and paths:**
   - anchors: `KAM.Planetary.StrongAMD.planar_strongAMD_{barrier,exponentialSafety,exponentialSafety_halfInteger}`
     and `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety{,_halfInteger}`;
   - frozen paths mirror the namespaces, under `KAM/Frozen/Planetary/{StrongAMD,Spatial}/`;
   - frozen definition names equal the implementation names, so no proved theorem changes at freeze time.
10. **What is frozen:** exactly the Lean-computed closure of the anchors and characterizations, plus three listed source
   quantities (`sourceOscVelocity`, `sourceOscParam`, `spatialSourceOscVelocity`). That is 89 new definitions and
   34 characterization theorems, so 128 new frozen files with the 5 anchors. 20 already-frozen definitions are reused
   unchanged, now including `KAM.IsDiophantine`. 19 already-frozen definitions are reused unchanged.
11. **Not frozen:** P-EXP-SAFE and every existing frozen file are untouched (OD-6).

## What the owner approves

The 128 file texts byte for byte. At freeze time only the approval date and decision placeholders are filled in, and
the manifest hashes are computed.
