# SO-PYALIGN: the Python certificate mirror aligned with the landed Lean checker (2026-10-29)

The toy mirror (`scripts/spin_orbit/toy_model.py`, `toy_check.py`) is now a transcription of the landed checker
(`KAM/Certificate/Defs.lean` and the engine below it) over the exact backend `ℚ`. Every rounding error is 0 there,
so what remains is the structure of the Lean computation, and the mirror now follows it exactly:

- term lists are kept in Lean list order, with no dict merging;
- equal keys merge only where `mergeErrTerms` meets them;
- keys are literal lists (`packAddZ`, no padding), and zero coefficients are kept;
- sums use the balanced `sumUp` / `modelSum` / `CertBall.listSum` trees;
- `toDeg` uses the Machin bounds;
- the scalar route applies to constant factors;
- an advice lookup with a missing key gets the Lean fallback.

The verdicts now coincide with Lean's except for two deliberately stricter shape tests (§2). The mirror is never
more optimistic than Lean.

The generator (`toy_gen.py`) first runs the mirror in GENERATE mode, where every advice lookup answers `direct`
and is recorded. It then emits exactly the recorded keys and re-runs the mirror in CHECK mode, where a missing
key gets Lean's fallback, asserting that no key is missing. `toy_keys.py` is an independent key-coverage test (§4).

## 1. Alignment table

Status: **aligned** = transcribed and identical to before; **was different** = the mirror changed (what
changed); **stricter** = deliberately stricter than Lean.

| Lean declaration (file:line) | mirror function | status |
|---|---|---|
| `checkStatic` Defs.lean:220, `freqNormLo` :134 | `toy_check.check_static`, `freqNormLo` | was different: `n ≤ τ+1`, `L` = foldr max with base 0, list-length tests on centre/radius split out as in Lean. **Stricter**: box radii ≥ 0, embedding list lengths = n (`mirrorOnly`; Lean reads missing data as 0, F2) |
| `checkHamBounds` :237, `hamBoundsOk` :151 | `ball_bounds`, `check_ham_bounds` | was different: `Slp.balls` at `c.expOrder` (the mirror used `cfgFull.taylorN`; equal, 24, in every toy); `getD` defaults (`d1.getD a 0`, a missing slot reads slot 0, not 0); the five sums use `sumUp` |
| `checkEmbedding` :243, `angleImOk` :173, `actionShiftModel`, `dkRowUp` | `check_embedding` | was different: `sup|∂_j U|` via `compDerivModel` (`toDeg 0` of `ofDeriv`, not degree d+1); action via `addMixed(realCompModel, constModel(−c_i))`; DK row-by-row `≤ σK − μ` (each row, not the max) |
| `checkInvariance` :254, `invarianceModel` :198, `dkFreqModel` :190, `d1Slots` :186 | `check_invariance`, `dkFreqModel` | was different: `DK(sω)` is `toDeg 0 (modelSum [mul [5,a,l] freqModel DK_al])` (the old mirror used `m_scale_ball`, same radius in ℚ); `addMixed(± ms[swap a], −dkFreq)`; each coordinate `≤ e` |
| `checkEnergy` :263, `energyOk` :207 | `check_energy`, `zeroModeBall` | was different: `addMixed(toDeg 0 m, constModel(−E0))`; requires `deg == 0`; zero mode from `zeroModeBall` (the first n key entries zero) |
| `checkGram` :270, `gramCheck` Gram.lean:175 | `gram_check`, `check_gram` | was different: only `a ≤ b` entries computed (`(b, a)` recomputed for `a > b`); keys `[3,0,a,b,r]` with r over angle then action rows; diagonal defect `oneSubSupUp`; `maxCandidate` (base 0); `gramBoundsOk` (`0 ≤ δ < 1`, `0 ≤ σ`, `β + σδ ≤ σ`) |
| `gramEntryModel` :112, `gramBGModel` :136, `modelSum` :83, `CertModel.addMixed` :63 | `gramModels`, `Mo.modelSum`, `Mo.addMixed` | was different: balanced pairwise `addMixed` (the mirror folded left with `m_add`); the zero-summand rule (an empty summand adds only its radius) |
| `checkTorsion` :275, `torsionModels` Torsion/Models.lean:152, `modelMatMul` :58, `dkwModels` :110 | `check_torsion`, `torsion_models`, `matMul` | was different: every matrix entry is `toDeg 0 (modelSum …)`; `D_{sω}DK` via scalar `mul [4,10,i,j,l]` with `freqModel` and `d2kModel` (`ofDeriv2` then `toDeg 0`); frequency radius `|s|·r` |
| `gramInvRadius` :117 | `gramInvRadius` | was different: `δβ · recipOneSubUp δ` (the mirror used exact `δβ/(1−δ)`, which is more optimistic); fails closed unless `0 ≤ δ`, `0 ≤ β`, `δ < 1` |
| `torsionAvgCheck` Torsion/Average.lean:106, `avgDegOk` :87, `avgBoundsOk` :94 | `torsion_avg_check` | was different: a nonzero-degree entry FAILS (the mirror applied `toDeg 0`); `R` = zero-mode radius + model radius; final test `‖S‖ + σ δ_T ≤ σ` with `δ_T = a + ‖S‖ r` |
| `checkSmallness` :285, `isoC1Q`/`isoC2Q` Constants.lean:140/145 | `check_smallness` → `toy_constants.smallness` | aligned (ℚ, Nat powers, `<` and `≤`) |
| `Slp.compose` Expr/Compose.lean:180, `composeStep` :140 | `toy_check.compose` | was different: the WHOLE program in slot order (the mirror composed only the dependency closure of the wanted slots); `.add` = `CertModel.add a (toDeg a.deg b)`; `.mul` key `[0, slot]`; `.exp` takes `toDeg 0` of its argument (the mirror failed closed on nonzero degree); off-program slots are `zeroModel` |
| `charResolve` :105, `charEntry` :121, `normKey` ComposeModels.lean:107, `findKeyIdx` :118, `charPhaseModel` :89 | `charResolve`, `charEntry`, `normKey`, `charPhaseModel` | was different: witness keys matched by EXACT list equality (no padding); one check per normalized key (cache); `−k` with `reflectSorted`; phase = per-coordinate `toDeg 0` then `add` |
| `CertModel.mul` Model/Ops.lean:106, `polyProduct` :83, `crossUp` :98, `truncPoly` Terms:422 | `Mo.mul`, `polyProduct`, `crossUp` | was different: scalar route for an `isConst` factor (no lookup; `directItems(const, other)` order); missing key gives the crude `⟨deg, [], (|a|+r_a)(|b|+r_b)⟩`; literal cutoff |
| `directItems` Terms:411, `mergeErrTerms` :321 | `Mo.directItems`, `Mo.merge` | was different: literal merge (equal keys combine only where met); fast path only when both lists are strictly ascending with one key length (provably the same result) |
| `CertModel.toDeg` Ops:191, `twoPiZpowHi/Lo` :146/:150 | `Mo.toDeg` | was different: centre = UPPER bound `c` of `(2π)^e` from `max/min(Machin, piLo/UpQ)`, radius `c·rad + (c−lo)|P|_w` (the mirror used the midpoint and half-width: more optimistic) |
| `expWitnessRadius` Model/Exp.lean:108, `expWitnessRadiusOf` :91, `expResidualProduct` :69, `expm1Up` ExpBounds:205 | `Mo.expWitnessRadius*`, `expm1Up` | was different: `eB² (pinErr + (½+ρ) res) + eB·mη` with `eB = 1 + expm1Up(B)` (the mirror used `ratExpUp(2B)`, `ratExpUp(B)(ratExpUp(η)−1)`); residual = merge of `∂_jE` with the product, times `2·piUpQ`; missing advice gives the direct product |
| `invWitnessRadius` Model/Inv.lean:63, `oneSubSupUp` :42, `recipOneSubUp` :56 | `Mo.invWitnessRadius`, `oneSubSupUp`, `recipOneSubUp` | was different: `δ = oneSubSupUp(mul [2] ⟨0,Q,0⟩ ⟨0,b.poly,b.rad⟩)` (b's degree dropped, product truncated at the cutoff); radius `|Q|_w δ · recipOneSubUp δ` (the mirror used exact `1/(1−δ)`) |
| `ModelConfig.forWitness` ComposeModels:130 | `Cfg.forWitness`, `Cfg.full_key` | was different: sub-book of `s :: i :: rest` re-keyed `s :: rest` |
| `CertRealPoly.toSortedPoly` :66, `CertPoly.shift` | `Mo.toSortedPoly`, `Mo.shift` | was different: conjugates reversed, zero term at `padKey n []`, half terms; the mirror built a dict |
| `CertModel.ofDeriv2` Torsion/Frame.lean:295 | `Mo.ofDeriv2` | was different: `−k_j k_l c` at degree d+2 (the old mirror kept degree d+2 and never re-expressed it) |

### Advice key families (who looks up what)

| family | Lean site | looked up? | mirror |
|---|---|---|---|
| `[0, slot]` | `composeStep .mul` (cfgFull: invariance + energy; cfgLow: torsion) | yes, unless a factor is constant | was `[0, s]` over the dependency closure only; now every mul slot of the program |
| `[1, i, j]` | exp witness i, residual coordinate j (`forWitness 1 i`, key `[1, j]`) | yes, unless `∂_j g₀` or `E` is constant | was `[1, 0, i, j]` |
| `[1, |expWit|+c, j]` | character witness c (cached per normalized key) | same | was `[1, 1, slot, j]`, once per slot |
| `[2, i]` | `invWitnessRadius` (`forWitness 2 i`, key `[2]`) | unless Q or b is constant | aligned |
| `[3, 0, a, b, r]` | `gramEntryModel`, a ≤ b only | unless a factor is constant | was full `mat_mul` (`a > b` keys emitted but never read) |
| `[3, 1, i, j, k]` | `gramBGModel` | unless `B_ik` or `G_kj` is constant | aligned |
| `[4, t, i, j, k]`, t = 0..9 | `torsionModels` | unless a factor is constant | aligned layout; now emitted only when looked up |
| `[4, 10, i, j, l]`, `[5, a, l]` | `dkwModels`, `dkFreqModel` | **never** (`freqModel` is constant: scalar route) | no longer emitted |

## 2. What changed in the toys

The regenerated toys are in `certificates/so-toys/`, with hashes in `summary.json`. All four pass all eight
sub-checks, and TR is resonant as designed (it passes the checker; `IsDiophantine` fails, `verification.resonance`).

- **T2, T3, TR.** The data and every margin are identical. Only the advice books changed: every product of these
  toys has a constant factor, so Lean looks up no key. Both books are now empty; before, they listed every
  product as `direct`.
- **T2d.**
  1. **`cfgFull.cutoff` 532 → 10^6 (`SAFE_CUTOFF`).** Lean composes the whole jet program (the d2 and d3 slots
     too), whose products reach |k|₁ = 1064. The literal cutoff of 532 would therefore truncate the full stage,
     which the design forbids. The old mirror never saw those slots. `cfgLow` keeps 30 and still truncates, by
     design (max |k|₁ 530).
  2. **Advice books.** `cfgFull` went from 37 keys to 34 and `cfgLow` from 237 to 34. Each book is `[2, 0]` plus
     the 33 `[0, slot]` keys of non-constant mul slots. The character witness `[0, 0]` has a constant phase and
     `E = 1`, so there are no `[1, …]` keys. Gram and torsion products all have a constant factor, so there are no
     `[3, …]` or `[4, …]` keys.
  3. **Torsion radius.** `normR` rose from 1.4e-197 to 1.6e-12 and `δ_T` from 4.0e-197 to 4.5e-12. Lean
     re-expresses every `modelMatMul` entry at degree 0 by `toDeg`. That pays the Machin gap of the π enclosure
     (`k = j = 4`, relative width ~1e-12) times the weighted norm of jet slots with nonzero 2π-degree. The old
     mirror re-expressed once, at the end, about the midpoint. The margin is unaffected (`‖S‖/(1−δ_T)` = 2.93 ≤
     σT − μ = 1598.8). `torsInv` is recomputed from the new averaged centres.
- **Negative mutations** (`negative.json`): the 16 mutations are re-run in CHECK mode, using the base toy's
  emitted books as Lean would read them. All 16 fail their intended sub-check, with exactly the same
  failing sets as before.

## 3. Checks run

- `toy_gen.py` (all four toys): all pass (T2d ≈ 400 s). New SHA-256: T2 `229e05ce…`, T2d `ab4815d0…`, T3
  `ec5413d4…`, TR `73bb712e…`. A second run into a separate directory reproduces every `<toy>.json`
  byte for byte.
- `toy_keys.py`: §4.
- `toy_negative.py`: all as intended; no failing set changed. The Lean controls (`checkWeight`, `checkPiEnclosure`,
  smallness) do not read the mirror. They are kept from the previous run because this worktree has no Lean build.

## 4. Key-coverage test (`toy_keys.py`)

An independent, support-only transcription of the Lean lookup order. It reads only the emitted JSON and the jets,
and shares no code with the mirror. Whether `polyProduct` consults the book depends only on the key sets of its
factors, and no Lean operation of the direct route drops a term because of its coefficient value. Propagating key
sets through `Slp.compose` (×3), `gramCheck` (×2) and `torsionModels` therefore reproduces the lookups exactly.

For each toy and configuration, the emitted set equals the looked-up set: no unused key, no missing key, no
duplicate, all `direct`. Results are in `key_coverage.json`. The looked-up/emitted counts:

| toy | cfgFull | cfgLow |
|---|---|---|
| T2 | 0 / 0 | 0 / 0 |
| T2d | 34 / 34 | 34 / 34 |
| T3 | 0 / 0 | 0 / 0 |
| TR | 0 / 0 | 0 / 0 |

## 5. Not mirrored

- **Packed advice.** The packed route is covered by `sodata_packed.py`; this toy mirror covers the direct route
  only.
- **A rounded (CertFixed) backend.** There is none in the toy mirror. The balanced summation trees are transcribed
  structurally (`sumUp`, `modelSum`, `listSum`), so a rounded backend plugged into `toy_model` would inherit Lean's
  order.
- **`cfg.toMant`.** It is still emitted as the string `"none (direct route)"` and is not a data value.

## 6. Observations on the Lean (reported, not changed)

1. `[5, a, l]` and `[4, 10, i, j, l]` are documented as advice keys (SO-DEFS handoff), but they are never looked
   up, because `freqModel` is constant. SO-DATA must not emit them.
2. A missing `[0, slot]` key or a failed packed check silently gives the crude enclosure. That is sound, but it
   fails only later, through the margins. A generator must check coverage (§4) rather than rely on a failure.
3. Each `toDeg` pays `(twoPiZpowHi − twoPiZpowLo)·|P|_w`, and the torsion pays it per matrix product. At lunar
   `err` (~1e-80 and below), `piEnc.machinK/J` must be sized so that the Machin gap is below `err`; k = j = 4
   gives only ~1e-12. The invariance check also pays it on every jet slot of nonzero degree.
4. Character witnesses are found by exact key-list equality, with no padding. The generator must emit
   normalized keys of length exactly n.
5. `mergeErrTerms` combines equal keys only for ascending inputs. Unsorted, or mixed-length, half keys are sound
   but give larger norms. The generator must emit ascending half keys of length n.
6. Kernel cost: `checkInvariance` and `checkEnergy` each run the identical full `Slp.compose` at `cfgFull`, and
   `checkTorsion` reruns `gramCheck`. Sharing these is a design option for SO-SOUND/SO-DATA.
