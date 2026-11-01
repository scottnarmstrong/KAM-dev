# LP3-PLAN review 1 (independent, refute-first)

Object: `docs/tracks/LP/lp3/LP3-PLAN.md` (495 lines, commit `dfa1bbad`) and `LP3-DESIGN-handoff.md`.
Reviewer: independent Opus 5.5 reviewer (did not write the plan). Method: files read only, no Lean/Lake run.
Every claim below cites `file:line`. Paths are relative to the worktree `/root/code/KAM-inp-lp-lp3` unless
marked `spsafe:` (branch `inp-lp-spsafe`, commit `c9553935`, read with `git show`).

## Verdict: **PASS WITH NOTES**

There is no BLOCKING finding. I tried to break the mathematics at every premise of the frozen theorem. I also
checked the finite-cover arithmetic, the exact `hstop` shape, time reversal, the time horizon and the exponents.
Every check went through, and the arithmetic is exactly as stated. Five CHANGE-REQUIRED findings remain. They
concern governance and the statement surface, not the drift argument. They should be fixed before the phase-2
briefs are written.

---

## 1. Premise-by-premise check of `partialConvex_nekhoroshev` (task item 1)

Frozen statement: `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:48-77`.
Plan choices (`LP3-PLAN.md:180-192`): `rs = min(4r_g, R/4)`, `s = b = rs/4`, `η = rs/4`, `ρ = rs/8`,
`G_j = ball(c_j, η)`, `G′_j = ball(c_j, 2η)` (sup norm), `D_j = slowBall n (B(c_j) − 5δ/16)`, `P = fc/B₀` on
`complexTube(strongCore, R)` and `0` elsewhere, and parameter `ν = B₀μ`.

| Premise (frozen line) | Check | Result |
|---|---|---|
| `hn`, `hk` (:49) | `k = n ≥ 2` (planar), `k = n+n` (spatial) | OK |
| `hG hGc hG' hGc'` (:51-52) | open sup-norm balls are open and convex | OK |
| `hD` (:52) | `isOpen_slowBall` (`KAM/Planetary/Exponential/Stopped.lean:62-63`); `D` need not be convex | OK |
| `hcollar` (:54) | `‖x−c_j‖ ≤ ρ + ‖I−c_j‖ < rs/8 + rs/4 < rs/2 = 2η` | OK |
| `hhol hC2 hreal hHess` on `actionNbhd G′_j ρ` (:56-60) | `z` in it has `|z_i − c_{j,i}| < 2η+ρ = 5rs/8 < rs`; `c_j − rs·e_i ∈ cthickening(4r_g) 𝓛_δ = U` because `rs ≤ 4r_g`, so `Re z_i > a_min > 0`; Hessian `≤ Σ 3ν_i³/‖z_i‖⁴ ≤ Σ 3ν_i³/a_min⁴` (`KAM/Planetary/Exponential/KeplerData.lean:134-135`); reality (`:212-213`) | OK |
| `hdef : HasDefiniteFastPart G′ ρ g m h` (:61) | definition `KAM/Frozen/Nekhoroshev/Defs/HasDefiniteFastPart.lean:33-39`: `σ = −1` is allowed (:37); `ω_i = ν_i³/I_i³ > ν_i³/(I_max+rs)³ ≥ g`; `−D²h(v,v) = Σ 3ν_i³v_i²/I_i⁴ ≥ m|v|²` (`KeplerData.lean:224-235`) | OK |
| `−h` data | `hasDefiniteFastPart_neg` is generic (`KeplerData.lean:181-210`); the other four `−h` facts are trivial (see N4) | OK |
| order of quantifiers (:62-64) | `∃ μ₀` after `G G′ D ρ g m Mcomplex h`, before `P`, `C`, `z`: uniform in `P` | OK |
| `IsPartialPerturbation G′_j D_j ρ P` (:64; def `IsPartialPerturbation.lean:34-42`) | `partialComplexDomain G′_j D_j ρ ⊆ complexTube(strongCore ν 𝓛 δ r_g)(R/2)` by `strongCore_containment` (`KAM/Planetary/StrongAMD/AnalyticDomain/Containment.lean:135-144`), with `I0 := c_j ∈ 𝓛_δ`. `hact`: `|z_i − c_{j,i}| ≤ |Re| + |Im| < 2η+ρ < rs`. `hang`: `|Im| < ρ < 4s = rs`. `hslow`: witness `y = Re(slow z) ∈ D_j ⊆ secularBall ν δ c_j` (`Containment.lean:131-132`; `< B(c_j)−5δ/16` gives `≤ B(c_j)−δ/4`), `‖slow z − y‖ = max|Im| < ρ < 4b`. `hmax`: `max(rs,4s,4b) = rs ≤ R/4 < R/2`. `hrg`: `rs ≤ 4r_g`. The four clauses follow as in track P's `perturbation` (`Exponential/Perturbation.lean:290-306`): holomorphy by `congr`, `‖fc‖ ≤ M ≤ B₀` (`Extension.lean:46`), reality (`:39-42`), periodicity (`:43-45`) | OK |
| `IsSolutionOn H {I | fast I ∈ G_j} (Icc 0 C) w` (:66-69; def `IsSolutionOn.lean:31-35`) | `C := t`. Fast in `G_j`: `‖Λ(z u) − c_j‖ < r + η/2 ≤ 3η/4`. `H = liftChartHam` on the open `V_j` (plan :228-238): `complexify w ∈ PCD ⊆ R/2-tube ⊆ R-tube` gives `w ∈ chartSafe` and `fc(complexify w) = fMov(Ψ w)` (`Extension.lean:39-42`), then `movingHamiltonian_poincareProd_split` (`Extension.lean:87-92`) and `realPart_planetaryKeplerC` (`KeplerData.lean:216-219`). Two-sided `HasDerivAt` on the open lift interval `⊇ uIcc 0 t` (`ChartLift/Lift.lean:147-149`). `V_j ∋ w u` needs `chartAMD(w u) < A_j`, which step 4 supplies | OK |
| initial fast erosion (:70) | `closedBall(I⁰, ν^b) ⊆ ball(c_j, η/2 + η/4) ⊆ G_j` | OK |
| horizon (:71-72) | `|t| ≤ exp(ν^{−a}) ≤ ν⁻¹exp(ν^{−a})` because `ν ≤ ν₀/2 ≤ 1/2` | OK |
| stopped slow erosion (:73-75) | `stopped_slow_erosion` (`Stopped.lean:111-114`) with `A₁ = B(c_j) − 3δ/8`, `A = B(c_j) − 5δ/16`, `ν^b < ε_D` | OK |
| conclusion (:76-77) | `‖fast(w t).2 − fast(w 0).2‖ ≤ ν^b/2 = r/2`; `fast(w u).2 = Λ(z u)` by `lpChart_action` (`PlanarDictionary.lean:64`); `fast(w 0).2 = Λ z₀` (`ChartLift/Lift.lean:151`) | OK |
| canonical order and signs | the lift and the frozen theorem both use `KAM.hamiltonianVectorField` (`KAM/Frozen/Defs/HamiltonianVectorField.lean`), radian `fastShift` (`KAM/Frozen/Planetary/Defs/FastShift.lean:38-39`) and physical time. The `(x, −y)` sign issue of MAIN L13 (`MAIN.md:446`) does not arise | OK |

## 2. Finite cover and margins (task item 2)

* **`μ₀` is uniform.** The cover `{c_j} ⊆ 𝓛_δ` is fixed from `(n, ν, 𝒜, δ)` before `μ`. Each cell has a
  threshold for `(h,P)` and one for `(−h,−P)`. `ν₀` is the minimum of finitely many positive numbers
  (`LP3-PLAN.md:240-243`). Every per-cell datum (`ρ, g, m, Mc`) is common to all cells.
* **Landing.** Every admissible `I⁰ = Λ(z₀) ∈ 𝓛_δ` (`PlanarSafety/Prograde.lean:119-122`;
  `PlanarSafety/Constants.lean:96-107`) lies in some `ball(c_j, η/2)`.
* **Sharpened stopped bound** (`LP3-PLAN.md:270-277`). Write `C = C(z u)`, `B = strongThreshold`, `U` = the
  shared tube.
  1. `StoppedOn` gives `C < B(Λ(z u)) − δ/2` (`ChartLift/Stopped.lean:60-64`).
  2. `Λ(z u), I⁰ ∈ U` and `‖Λ(z u) − I⁰‖ < r ≤ 4r_g`, so `B(Λ(z u)) ≤ B(I⁰) + Ω_B(U, 4r_g)`
     (`Modulus.lean` `abs_strongThreshold_sub_le_modulus`, monotone in the radius).
  3. `I⁰, c_j ∈ 𝓛_δ ⊆ U` and `‖I⁰ − c_j‖ < η/2 ≤ r_g/2`, so `B(I⁰) ≤ B(c_j) + Ω_B(U, 4r_g)`.
  4. `Ω_B(U, 4r_g) ≤ δ/16` (`AnalyticDomain/Core.lean:87-88`).
  5. Hence `C < B(c_j) − δ/2 + 2δ/16 = B(c_j) − 3δ/8 = A′_j`, with the `δ/16` gap below
     `A_j = B(c_j) − 5δ/16`.

  `A′_j ≥ 5δ/8 > 0`, since `B(c_j) ≥ δ`. So `√(2A_j) > √(2A′_j)` and `ε_D > 0`. **Verified.** The plan is also right
  that the whole-ball bound `C ≤ B(I⁰) − δ/4` (`ChartLift/Stopped.lean:98-103`) only gives
  `C ≤ B(c_j) − 3δ/16 > A_j`, which is not enough.
* **Ordering** (`LP3-PLAN.md:338-340`). `B(c_j) − 3δ/8 < B(c_j) − 5δ/16 ≤ B(c_j) − δ/4`. **Verified.**
* **Boundary of the chamber or of `𝓛_δ`.** There is no loss. `U` is compact inside the chamber
  (`Core.lean:85-86`), and the centres on `∂𝓛_δ` still have `A_j ≥ 11δ/16`.

## 3. `hstop`, budget, time reversal and horizon (task item 3)

* The `hstop` antecedent (`Confinement.lean:177-181`) is literally `StoppedOn` (`ChartLift/Stopped.lean:60-64`),
  and its consequent is `≤ r/2` (`Confinement.lean:182`). With `r = ν^b` the frozen bound `ν^b/2` matches
  exactly.
* Budget: `exists_budget_radius` holds for every `0 < r ≤ r₁` (`PlanarSafety/Constants.lean:35-38`). `hball`
  holds from `r ≤ 4r_g` and `I⁰ ∈ 𝓛_δ`. In fact `r < η/4 ≤ r_g/4`, so the `(4r_g)^{1/b}` entry of `ν₀` is
  redundant (N2).
* **Negative times.** The reversed curve on `[0, −t]` solves the field of `(−h, −P)`. This is the pattern of
  `stopped_isSolutionOn_reverse` (`Exponential/Stopped.lean:216-241`), together with `stopped_hamiltonian_neg`
  (`:181-189`) and `hamiltonianVectorField_neg` (`Exponential/Hamiltonian.lean:116-120`). The erosion sets are the
  same; the reversed curve's time-0 point is `w 0`. **Verified.**
* **Horizon.** `T(μ) = exp(c μ^{−a})` with `c = B₀^{−a}` equals `exp((B₀μ)^{−a})` (`Real.mul_rpow`, both factors
  nonnegative). This is at most `ν⁻¹exp(ν^{−a})` for `ν ≤ 1`. The strict `ν < ν_j^±` follows from
  `μ ≤ ν₀/(2B₀)`. **Verified.**

## 4. Exponents (task item 4)

* `partialTimeExponent n = 2/(6n²−3n+14)` (`KAM/Frozen/Nekhoroshev/Defs/PartialTimeExponent.lean:32`).
* `partialDriftExponent n = 3/(6n²−3n+14)` (`PartialDriftExponent.lean:31`).
* `planetaryDriftExponent n = 3·planetaryTimeExponent n / 2` (`KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean:36`).
* The bridges are proved (`Exponential/Stopped.lean:76-84`).
* The table values (`LP3-PLAN.md:70-75`) for `n = 2..5` are correct (denominators 32, 59, 98, 149).
* The frozen exponents depend only on the fast dimension `n` (`PartialConvexNekhoroshev.lean:49`, `{n k}`), so
  the spatial `k = n+n` changes nothing. **Verified.**

## 5. Spatial (`LP3-PLAN.md:297-319`)

* The typing `Phase (n + (n + n))` is native (`spsafe:KAM/Planetary/Spatial/Product/Defs.lean:66-69`).
* `spatialStrongCore_containment` has the same hypotheses as the planar one
  (`spsafe:…/AnalyticDomain/Containment.lean:40-50`).
* `exists_spatialStrongTube` has the four clauses with `fastShift (a := n) (b := n+n)`
  (`spsafe:…/AnalyticDomain/Extension.lean:66-80`).
* `spLiftChartSafe` and `spatialChartSafe` have identical bodies (`spsafe:…/ChartLift/Setting.lean:46-47`,
  `spsafe:…/AnalyticDomain/Safety.lean:36-37`).
* `spLiftChartHam = spatialHProd + μ·fSpatial∘Ψ` is defined globally (`Setting.lean:54-55`), and
  `spatialHProd` is the Kepler sum on `fast w.2` (`spsafe:…/Product/Split.lean:46-47`).

The spatial `hstop` (`spsafe:…/Spatial/Confinement.lean:223-237`) has the same shape as the planar one.
**Verified**, with note N8.

## 6. Hidden assumptions (task item 5)

There is none of the following:

* **A Diophantine-like condition.** `HasDefiniteFastPart` asks only `‖ω‖ ≥ g`, and the Kepler frequencies are
  positive.
* **A confinement assumption.** The fast-in-`G` and slow-in-`innerCore D` premises are discharged from the strict
  stopped conditions only.
* **A uniformity failure at the boundary.** See §2.

The orientation premise `0 < totalMomentum z₀` is inside `LiftData` (`ChartLift/Stopped.lean:56`). It is supplied
by the prograde assembly, after the reflection of `Main.lean:116-134`, exactly as in LP1. It is not new.

---

## Findings

### BLOCKING

None.

### CHANGE-REQUIRED

**C1. The import ruling that §4 rests on is not recorded anywhere in the repository.**

*Location.* `LP3-PLAN.md:45-46` and `:367-388`; handoff `:40-42`.

*Evidence.*
* The plan cites a "root-b8 ruling, 2026-11-01". Outside `lp3/`, `grep` finds no such ruling:
  * `docs/tracks/LP/OWNER-DECISIONS.md:20` (OD-12) is an FYI that does not mention imports;
  * `docs/DECISIONS.md` D11 (`:45-51`) and D25 (`:153-166`) say nothing about consumers importing a sealed
    theorem anchor.
* The common brief still forbids it (`/root/code/KAM-inp/.drafts/briefs/inp-prover-common.md:18-20`).
* The real authorities are AGENTS.md rule 9 (`AGENTS.md:29`) and the track-P precedent
  (`KAM/Planetary/Exponential/Stopped.lean:9`). Rule 9 quarantines only providers and `DRAFT_SORRY` anchors. The
  manifest marks the anchor `SEALED` (`manifest/frozen-anchors.json:9020`).

*Repair.*
* Record the ruling in `OWNER-DECISIONS.md` (or `DECISIONS.md`) with time and wording, before phase 2.
* Cite AGENTS rule 9, the manifest state and that record as the authority.
* Amend the common brief's Quarantine bullet to "sealed theorem anchors may be imported; providers and
  `DRAFT_SORRY` anchors never", or give an explicit LP3 exception.

**C2. Overclaim relative to track P.**

*Location.* `LP3-PLAN.md:138-140`. It reads: "LP3 is stronger than track P's `planetaryExponentialSafety` on its
domain".

*Evidence.* This is not established.
* The frozen P theorem (`KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean`) concludes facts that LP3
  does not state:
  * confinement in `LowAMDRegion … B.outerAMD`;
  * `e_i < B.ecc`;
  * `B.distance ≤ |q_i| ≤ B.radius`;
  * `PairBounds`.
* Its initial set, `LowAMDRegion` of an `Admissible` box, is not shown to satisfy LP3's premises (axes in a
  compact ordered `𝒜` and `strongAMD ≤ B − δ` for one `δ`).
* A4 itself says the two are not corollaries of each other (`/root/code/KAM/docs/explorations/amd-crossing/A4-proof-plan.md:254`).

*Repair.* Replace the sentence with: "Same exponents. The domain (the sharp curved sublevel) and the conclusion
set are not comparable with `planetaryExponentialSafety`. Neither implies the other." Also make §1.4 and any later
README input consistent with this.

**C3. The statement surface is behind `inp`, and the source-carrier restatement is missing.**

*Location.* `LP3-PLAN.md:77-118` (LP3-1 copies the total-formula `Main.lean:44-91`); the §5 package table
`:422-434`.

*Evidence.*
* LP1 is now also stated through the OD-11(b) source carriers (`docs/tracks/LP/FREEZE-PROPOSAL.md:143-175`, §3b).
* That code landed on `inp` (`/root/code/KAM-inp/KAM/Planetary/StrongAMD/SourceCarrier.lean`; merge `51be2456`).
* `51be2456` is not an ancestor of the lp3 branch (`git merge-base --is-ancestor` fails).
* A spatial source-carrier brief exists (`0adc3da5`, LP-SP-SRCB).

*Repair.*
* Rebase the LP3 work onto current `inp` before phase 2.
* Add §1.5 "LP3-1/LP3-2 through the source carriers (if OD-11(b))" and a cheap package each (LP3-SRC, LP3-SP-SRC),
  mirroring LP-SRC (restatement from the total form).
* Note the dependency in O-3.

**C4. The symbol `ν` is used for two different objects.**

*Location.* `LP3-PLAN.md:38`, `:197`, `:231-232`, `:240-249`, `:253-292`, and the handoff `:33-34`.

*Evidence.* `ν : Fin n → ℝ` is the mass vector (the LP binder, e.g. `Main.lean:44`). The plan also sets
`ν := B₀μ`, a scalar. Line 232 mixes them in one equation:
`degenerateHamiltonian … ν w = −Σ νᵢ³/(2Iᵢ²) + μ·fMov(Ψ w) = liftChartHam ν μ w`.
This is a trap for the Lean briefs.

*Repair.* Rename the scalar to `nu` (track P's name, `Exponential/Stopped.lean:288`) or to `ε`, throughout the
plan and the handoff.

**C5. §2.3 names the wrong headline `μ₀`.**

*Location.* `LP3-PLAN.md:243`: "`μ₀ := ν₀/(2B₀)`".

*Evidence.* That is only the drift threshold. The headline `μ₀` must also contain the osculating and separation
restrictions of LP1, `min(μ2, dS1/(2Aosc), dP1/(4Aosc))` (`PlanarSafety/Prograde.lean:83-104`). Those give the
headline conjuncts `Aosc·μ₀ ≤ dStar/2` and `2Aosc·μ₀ ≤ dPair/2`. §3 says "copy `planar_safety_of_prograde`",
which implies this, but §2.3 states it otherwise.

*Repair.* Write `μ₀ := min(ν₀/(2B₀), μ2, dS1/(2Aosc), dP1/(4Aosc))`. LP1's `r2²` entry is replaced by the
`ν₀` entries.

### NOTE

* **N1. Size figures disagree.** `LP3-PLAN.md:47` says "about 2,100 new lines". §5 (`:434`) and the handoff
  (`:44`) say about 2,300, and the table sums to 2,310. Make them consistent.
* **N2. One `ν₀` entry is redundant.** In `ν₀` (`:241`), `(4r_g)^{1/b}` adds nothing, since
  `r = ν^b < η/4 = rs/16 ≤ r_g/4`. It is harmless; keep it or drop it.
* **N3. The empty cover can be handled without a case split.** F4 (`:182-185`) splits off `𝓛_δ = ∅`. A uniform
  construction avoids the split and keeps one proof path: `ν₀ := min 1 (finite min)`, for example
  `(insert 1 S).min'`. The `a_min`/`I_max` data then need a nonempty `U`, or default values. If the split is
  kept, the barrier and osculating constants must still be produced in the empty case (they can be, with
  `U = ∅` compact).
* **N4. The LP3-KEP row should list all the `−h` data.** The row (`:424`) lists `HasDefiniteFastPart` for
  `±h`. The frozen call for `−h` also needs `hhol`, `hC2`, `hreal` and `hHess` for `−h`. Track P's
  `keplerDataNeg_*` (`KeplerData.lean:376-407`) are typed for `fastBox`, so ball versions are needed. They are
  trivial, but list them.
* **N5. The real-part margin.** In F6 (`:200-202`) the sharp statement is `Re z_i > c_{j,i} − 5rs/8 > c_{j,i} − rs
  ≥ a_min`. The last step uses `c_j − rs·e_i ∈ U`, which needs `rs ≤ 4r_g`. That holds by (F3).
* **N6. The frozen call takes 23 explicit arguments, not 20** (R9, `:465`): `hn` … `hdef`, `PartialConvexNekhoroshev.lean:49-61`.
  This does not affect the risk assessment.
* **N7. R10 (`:466`) should also require no `sorryAx`.** The handoff should check that `#print axioms` of the
  LP3 headlines shows exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. The anchor imports its
  provider privately (`PartialConvexNekhoroshev.lean:22`), so the axioms of the whole provider closure flow in.
* **N8. Spatial: say where the AMD identity along the orbit comes from.** The spatial lift does not export
  `spatialChartAMD (w u) = C(z u)`. The LP3-SP-DRIFT adapter must derive it with
  `spatialChartAMD_eq_of_aligned` (`spsafe:…/ChartLift/Lift.lean:47-53`), using alignment along the stopped
  interval from `spLift_prograde_of_stopped` (`spsafe:…/ChartLift/Stopped.lean:123`, clause `.2.1`), as the lift
  itself does (`spsafe:…/ChartLift/Lift.lean:222-224`). Cite both in §2.5 (`:314-316`). Planar analogue:
  `lpChart_strongAMD` on `poincareProdDom` (`PlanarDictionary.lean:156`) needs no alignment.
* **N9. Recommend the shared generic-in-`k` cellwise lemma** (`:436-439`). Every per-cell premise above is
  independent of `k` except the slow erosion constant `√(2k)`, which `stopped_slow_erosion` already handles
  generically (`Exponential/Stopped.lean:111`).
* **N10. Errata.** The A4 clarifications in §7 (`:482-491`) are accurate: A4:246 "sign" adapter and A4:251
  "uniform levels". I found no defect in MAIN.md or AMENDMENTS.md that bears on LP3. MAIN L13/N6 are simply
  not used.

## Summary

The LP3 plan is mathematically sound. Applied once per cell of a finite cover by sup-norm balls centred in `𝓛_δ`,
with local sharp slow levels `B(c_j) − 5δ/16` and the normalized global perturbation `fc/B₀`, the sealed
`partialConvex_nekhoroshev` meets every one of its premises. I checked each against the exact frozen text. Its
conclusion `ν^{b_n}/2` is literally the `hstop` consequent of `strongFirstExit_of_stopped_drift` with
`r = (B₀μ)^{b_n}`.

The new step, the sharpened stopped bound `C < B(c_j) − 3δ/8`, is correct and necessary. The arithmetic of the
collars, the widths, `ε_D`, the time reversal and the horizon conversion all check out. The exponents are the
frozen ones and depend only on the fast dimension.

The five CHANGE-REQUIRED items are:

* record the import ruling and fix the common brief (C1);
* remove the "stronger than P" claim (C2);
* rebase onto `inp` and add the source-carrier restatements (C3);
* rename the scalar `ν` (C4);
* state the full headline `μ₀` (C5).

None of them changes the proof route.
