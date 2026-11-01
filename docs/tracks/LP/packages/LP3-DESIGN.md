# LP3-DESIGN: paper-level proof plan for the sharp strong threshold with NO arithmetic hypothesis

Stretch goal LP3 of the track-LP brief ("the sharp strong threshold with NO arithmetic hypothesis, via the
resonance-tolerant route already used by track P's `planetaryExponentialSafety` (Nekhoroshev 1977 partial convexity;
worse exponent)"), started per the owner's strongest-version mandate (root-b8, 2026-11-01). **This phase writes a
plan, not Lean.** Nothing is frozen. The plan is then reviewed independently (refute-first) before any Lean package.

## Inputs (read in full)

- `docs/tracks/LP/source/MAIN.md` with `source/AMENDMENTS.md`: the nonresonant proof (LP1/LP2). Its sharp barrier
  (L2–L6), charts (L7, L17), whole-sublevel domains (L8, L18), first exit (L14) and osculating bridge (L16) carry
  over. Only the drift supplier (L12/L13, the Diophantine condition (5)) changes.
- `/root/code/KAM/docs/explorations/amd-crossing/A4-proof-plan.md` §7 (the sketch of this route) and §2–§4.
- The frozen theorem `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean` (`partialConvex_nekhoroshev`:
  partial convexity with `n` fast actions and `k` slow pairs; the stopped fast drift `μ^{partialDriftExponent n}/2`
  up to `μ^{-1} exp(μ^{-partialTimeExponent n})`; its premises `HasDefiniteFastPart`, `IsPartialPerturbation`,
  `innerCore` erosions), with its definitions in `KAM/Frozen/Nekhoroshev/Defs/`.
- How track P consumes it: `KAM/Planetary/Exponential/{Stopped,Perturbation,Setting,Enlargement}.lean`, the frozen
  `planetaryExponentialSafety`, and `KAM/Frozen/Planetary/Defs/{PlanetaryTimeExponent,PlanetaryDriftExponent}.lean`.
- The LP Lean packages already landed or proved: `KAM/Planetary/StrongAMD/*` (planar), `KAM/Planetary/Spatial/*`.
- `docs/DECISIONS.md`: the rules on consuming sealed frozen theorems from implementation modules (track P's
  `Stopped.lean` imports `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev`; establish exactly what is
  permitted, and cite the decision).

## Deliverable

`docs/tracks/LP/lp3/LP3-PLAN.md`: a line-addressable, self-contained proof plan with:

1. **The target statements** (planar LP3-1 and spatial LP3-2), in the same shape as LP1/LP2 but with the
   Diophantine premise removed, and the exponents of the time and of the drift
   (`partialTimeExponent n`, `partialDriftExponent n`; or the planetary ones). State precisely what is weaker:
   the time, and the action drift `O(μ^{b_n})` instead of `O(√μ)`.
2. **What replaces L12/L13.** How `partialConvex_nekhoroshev` is applied per fast box:
   - the convex open fast boxes `G ⊂ G'`, with a finite cover of the compact `𝓛_δ`-neighbourhood;
   - the slow domain `D`: the open full slow ball of the sharp sublevel ((21)/(47)), with a reserved collar so
     that `innerCore D` contains the stopped slow states;
   - `HasDefiniteFastPart` for `h = −Σν³/(2I²)` (negative definite: the sign/time-reversal adapter of track P);
   - `IsPartialPerturbation` via the normalized perturbation `P = fc/B₀` from the LP whole-sublevel tube (DOM/DOMX,
     SP-DOM/SP-DOMX), with `ν = B₀ μ`;
   - the period convention (radian vs period one) and the physical-time conversion;
   - spatial: `k = 2n` slow pairs, `Phase (n + (n + n))`.
3. **How the whole AMD sublevel enters** (no common-eccentricity `AMDBox`). Why the partial-convex theorem's slow
   domain `D` may be the curved sharp ball. How the stopped first exit (L14 / CONF with `hstop`) is discharged
   with the drift `μ^{b_n}/2` (budget `n r + Ω_B(r) ≤ δ/4` with `r ∼ μ^{b_n}`).
4. **The provider chain reused**, and the import-policy answer from `DECISIONS.md` (can an LP implementation module
   import the sealed frozen `partialConvex_nekhoroshev`, as track P does?). If not, give the compliant
   alternative (e.g. the track-N implementation theorem behind the provider).
5. **The Lean package list** (reusing the LP packages; only the drift supplier and assembly are new), with sizes.
6. **Risks and open points**, honestly stated (e.g. the erosion `innerCore` vs the reserved collar; uniformity of
   `μ₀` over the finite cover; the sign adapter for time reversal).

## Rules

Write mathematics, not Lean (short Lean-shaped statements where useful). Cite file:line for every repository
claim. No repository code changes; write only `docs/tracks/LP/lp3/LP3-PLAN.md` and a handoff. Never run Lean/Lake
except capped single-file checks through `/root/code/KAM-inp/.drafts/LP/lp_lean.sh` if you need to elaborate a
statement. Never search the whole filesystem. Never kill processes by name.

## Handoff

`docs/tracks/LP/lp3/LP3-DESIGN-handoff.md` (committed: summary, the key decisions, open risks) and
`.drafts/handoff-LP3-DESIGN.md`, then `touch .drafts/READY-LP3-DESIGN`.
