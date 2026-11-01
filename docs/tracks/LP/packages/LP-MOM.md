# Package LP-MOM: orbital identities and angular momentum, planar (MAIN Lemmas 2–3, d = 2)

Wave 1. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (read it first; it carries the hard rules,
the capped build wrappers and the handoff format).

## Source

`docs/tracks/LP/source/MAIN.md`: definitions §1 lines 26–45 ((1), (2)), Lemma 2 lines 110–128, Lemma 3 lines
130–139. Conventions and the repository dictionary: `docs/tracks/LP/SPEC.md` §1 (mass argument `m := ν`; `C` uses
`|L|`, overnight default OD-1). Roadmap §3 rows 2–3, §5.

## Owned files

`KAM/Planetary/StrongAMD/Orbital.lean`, `KAM/Planetary/StrongAMD/Momentum.lean`,
`KAM/Planetary/StrongAMD/Reflection.lean` (split further if needed, with facades). Nothing else; do not edit
`KAM/Planetary/AMD/*` (reuse it: `elements`, `ang_mom`, `interval_constancy`; the private `planeSq_ecc_aux` of
`Elements.lean` cannot be imported, so re-prove what you need under a distinct name).

## Definition

`strongAMD (ν : Fin n → ℝ) (z : Phase (n * 2)) : ℝ := (∑ i, keplerAction ν z i) - |totalMomentum z|`
(namespace `KAM.Planetary.StrongAMD`, `@[expose]`). Write `L_i := planeCross (bodyVector z.1 i) (bodyVector z.2 i)`,
`Λ_i := keplerAction ν z i`, `e_i := planeLength (keplerEccVector ν z i)`.

## Theorems to prove

**Lemma 2, planar, with NO prograde premise** (premises only `0 < ν i`, `0 < planeLength (bodyVector z.1 i)`,
`keplerEnergy ν z i < 0`; the radial case `e_i = 1`, `L_i = 0` is included):
1. `0 < keplerAxis ν z i`, `0 < Λ_i`, `Λ_i ^ 2 = ν i ^ 2 * keplerAxis ν z i`.
2. (11): `e_i ^ 2 = 1 - L_i ^ 2 / Λ_i ^ 2`, hence `e_i ≤ 1`; `|L_i| = Λ_i * √(1 - e_i ^ 2)`; `|L_i| ≤ Λ_i`.
3. (12): `keplerAxis * (1 - e_i) ≤ planeLength q_i ≤ keplerAxis * (1 + e_i)` and
   `planeSq p_i = ν i ^ 2 * (2 / planeLength q_i - 1 / keplerAxis ν z i)`.

**Lemma 3, planar** (`C := strongAMD ν z`):
4. Conservation: for `hJ : J.OrdConnected` and `IsMovingSolutionOn ν μ J z`, `totalMomentum (z t)` is constant
   (reuse `ang_mom`), and, when every `z t` (`t ∈ J`) has negative energies and nonzero positions,
   `strongAMD ν (z t) - strongAMD ν (z s) = ∑ i, (keplerAction ν (z t) i - keplerAction ν (z s) i)` (13).
5. `0 ≤ strongAMD ν z` on negative-energy nonzero-position states.
6. If `strongAMD ν z < Λ_k` for some `k`, then `totalMomentum z ≠ 0`. Projection bounds: if `0 < totalMomentum z`
   then `∀ i, Λ_i - strongAMD ν z ≤ L_i`; if `totalMomentum z < 0` then `∀ i, Λ_i - strongAMD ν z ≤ -L_i`.
   Corollary in MAIN's form: if `strongAMD ν z ≤ Λ_i - m` for all `i` (i.e. `C ≤ B_⋆ - m`) with `0 < m`, then every
   `L_i` has the sign of `totalMomentum z` and `m ≤ |L_i|`.
7. Deficit (13): `∑ i, Λ_i * (1 - √(1 - e_i ^ 2)) ≤ strongAMD ν z` (write the deficit literally as
   `1 - Real.sqrt (1 - e ^ 2)`; LP-THR's `eccDeficit` is defined the same way and is joined later).
8. When `0 ≤ totalMomentum z`: `strongAMD ν z = physicalAMD ν z`.

**Orientation (MAIN line 137, "choose the plane's orientation so that L > 0")**, in `Reflection.lean`:
9. `reflectPhase : Phase (n * 2) → Phase (n * 2)`, negating the second component of every body vector of both `q`
   and `p` (a linear symplectic isometry). Prove: `keplerEnergy`, `keplerAxis`, `keplerAction`, `e_i`,
   `planeLength` of body vectors and of their differences, `NoCollision`, `movingHamiltonian 1 1 ν μ` and
   `strongAMD` are invariant; `L_i` and `totalMomentum` change sign; `reflectPhase` is an involution; and
   `IsMovingSolutionOn ν μ J z ↔ IsMovingSolutionOn ν μ J (reflectPhase ∘ z)`. If the last equivalence turns out
   to cost more than about 500 lines, stop after the invariance lemmas and report the remaining gap.

## Checks and stop condition

Build every new module with `lp_build.sh` (import order); `lp_lint.sh` exits 0; `#print axioms` of items 1–9. Stop
when items 1–9 are proved, or when an item is blocked (report; never add a hypothesis silently). Expected size
500–1,200 lines.

## Handoff

`docs/tracks/LP/audits/LP-MOM-handoff.md` (committed) and `.drafts/handoff-LP-MOM.md`, per the prover brief, then
`touch .drafts/READY-LP-MOM`.
