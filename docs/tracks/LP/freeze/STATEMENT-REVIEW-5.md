# Independent LP statement review 5 (delta): §3d (LP2 under OD-11 (b)) after the R4.1 (A) fix

2026-11-01. Independent, refute-first reviewer. I did not write any of the reviewed declarations and used no
subagents. This is a paper-level delta review of review 4 (`freeze/STATEMENT-REVIEW-4.md`). Following the brief,
**Lean and Lake were not run**, so no elaboration, build, lint or `#print axioms` result below is my own (see
"Checks"). This report is the only file I wrote in the repository.

## Verdict

**PASS WITH NOTES.** Review 4's blocking finding R4.1 is **resolved** by resolution (A):

- Both theorem types in `inp-lp-spsrcb2:KAM/Planetary/Spatial/SpatialSafety/Source.lean` are **byte-identical** to
  the R4.1 (A) replacement text (the `_general` one differs only by its name and the absence of `hνmax`, `hνle`). The
  proposal §3d code block is also byte-identical to it.
- Neither type applies `spatialKeplerAxis`, `spatialKeplerAction`, `spatialKeplerEccVector`, `spatialStrongAMD`,
  `spatialKeplerPeri/Apo`, or any `spatialOsc*` element as a quantity. The only raw total helpers left are
  `spatialKeplerEnergy`, `spatialOscEnergy` and `spatialOscEcc`, and each occurs only as a sign condition inside a
  guarded predicate.
- The five-bin result is unchanged (SOURCE 8, STANDING 15, TYPING 7, RULED 0, EXCESS 0). No premise was added or
  removed. Every conclusion of the old §3d is recovered definitionally, and conversely.

One documentation CHANGE-RECOMMENDED (R5.1): the §4b spatial bullet's parenthetical about `spatialKeplerEnergy` is
inexact and omits `spatialOscEnergy/Ecc`, an imprecision inherited from review 4. Six NOTEs follow.

```text
LP2 (§3d, R4.1 (A) text)  DECLARATION_FIDELITY: PASS   (faithful restatement of §3c; old §3d recovered by rfl)
R4.1 (OD-11 (b) spatial freeze gate): RESOLVED at statement level
FREEZE_PACKAGE (LP2 under (b)): no open statement blocker; remaining = owner decisions OD-1…OD-11, R4.2 naming,
  orchestrator confirmation of build/axioms (not run by me)
```

| Id | Class | One line |
|---|---|---|
| — | — | No BLOCKING finding |
| R5.1 | CHANGE-RECOMMENDED | §4b spatial bullet: `spatialKeplerEnergy` is "used only inside the carrier predicate" is inexact; `spatialOscEnergy/Ecc` also occur raw in the `∃ ho` predicate. Exact replacement text below |
| R5.2 | NOTE | `SourceCarrier`:20–22 is now accurate for the three named helpers; its open-ended "…" could name the predicate-only exceptions (optional) |
| R5.3 | NOTE | Stale proposal prose: §1 LP2 row, §3c intro, the §3d "same shape as §3b" sentence, and the §3d header status |
| R5.4 | NOTE | §3b/§3d are no longer mechanical twins (supersedes R4.4); acceptable |
| R5.5 | NOTE | `h₀` now sits immediately after the physical premise, which it contains; harmless and well-founded |
| R5.6 | NOTE | Carry-overs: R4.2 (anchor naming under (b)), R4.5–R4.9 unchanged; R4.6 items at `Elements`:35 and `Model`:21 still open |
| R5.7 | NOTE | Handoff says the file has 247 lines; it has 248. Build/lint/axioms are the prover's claims, not verified here |

No suspected erratum in MAIN as amended.

## Identity

All relative paths are under `/root/code/KAM-inp-lp/`. Review HEAD (`inp-lp`) is
`ab2f9993b260c7447f225a3dd9363bc42dd56c2f`. The proved file is on branch `inp-lp-spsrcb2` at
`1f07852128289cfcaef53959ac7fbea1dc101cc5`. That branch descends from `inp-lp-spsrcb` (`6e84c27a`, the review-4
base); `git merge-base --is-ancestor` confirms this. `KAM/Planetary/Spatial/` is not yet on `inp-lp` HEAD, so all Lean
evidence is quoted from the `inp-lp-spsrcb2` blobs.

| Object | SHA-256 |
|---|---|
| `docs/tracks/LP/FREEZE-PROPOSAL.md` (draft 6) | `d1a3d3018da319e57ab3f14e927c4d04182951349f9ea3352be8c7188da552d0` |
| `freeze/STATEMENT-REVIEW-4.md` | `cce49c531cc02f7b40b50dbd408fda30ad45595efe730955f8b682f39b18abb3` |
| `inp-lp-spsrcb2:…/SpatialSafety/Source.lean` = `freeze/odb-Spatial-SpatialSafety-Source.lean.txt` | `c36eb7ac6ecc38f09967b4f2b2d83502026541e8d445bf158897cb6a4990bcc2` |
| `inp-lp-spsrcb2:…/Spatial/SourceCarrier.lean` = `freeze/odb-Spatial-SourceCarrier.lean.txt` | `efe897ea57837613d406fd3176ff0fd35fc32b403027440830d454dcf34b3fe6` |
| `inp-lp-spsrcb:…/SpatialSafety/Source.lean` (old §3d, review 4) | `19522c834648daea38edf9b9c9405fb51fabfa898000402b88872179194cbf6c` |
| `audits/LP-SP-SRCB2-handoff.md` | `254124b465fa77275758c04a9d1fdf613f7e0a86f039249eb32f62d1df740973` |
| `source/MAIN.md`, `source/AMENDMENTS.md` | `68e9167f…48c1b`, `c887d1e2…51881` (both unchanged since review 4) |

**Unchanged definitions.** The `SourceCarrier` hash equals review 4's (review 4:63). `git diff --stat inp-lp-spsrcb
inp-lp-spsrcb2` lists no change to `Elements.lean`, `Model.lean`, `Newton.lean`, `Osculating/Basic.lean`,
`SourceCarrier.lean` or `SpatialSafety/Main.lean`. `StrongAMD/Threshold/Defs.lean` is identical on `inp-lp` HEAD and
`inp-lp-spsrcb2`. Review 4's definition audit therefore carries over unchanged, and only the theorem types are new.

Below, `Source` means `odb-Spatial-SpatialSafety-Source.lean.txt`, `old` means
`inp-lp-spsrcb:…/SpatialSafety/Source.lean`, and `Carrier` means `odb-Spatial-SourceCarrier.lean.txt`. `Basic`,
`Elements` and `Main` mean the `inp-lp-spsrcb2` blobs of `Spatial/Osculating/Basic.lean`, `Spatial/Elements.lean`
and `Spatial/SpatialSafety/Main.lean`.

## 1. Verbatim check

I extracted review 4:335–415 (the R4.1 (A) code block), `Source`:145–225 (`_source` type), `Source`:42–122
(`_general` type) and proposal:384–464 (the §3d code block), then ran a byte-level `diff`:

- **R4.1 (A) vs `_source`:** one difference, the final line. `Source`:225 ends `… a.1) :=` where the review ends
  `… a.1)`. The ` :=` is declaration syntax, not part of the type. No other byte differs, including whitespace and
  line breaks.
- **R4.1 (A) vs `_general`:** lines 1–2 differ and nothing else (besides the same ` :=`):
  - name `lp2_spatial_strongAMD_safety_source_general` (`Source`:42);
  - `(hν : ∀ i, 0 < ν i)` without `(hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)` (`Source`:43).

  This is exactly the variant R4.1 prescribed (review 4:423–424).
- **R4.1 (A) vs proposal §3d:** byte-identical (empty `diff`).

The handoff's claim of "NO character-level changes" (`LP-SP-SRCB2-handoff`:9–11) is **confirmed**.

## 2. No unfrozen total helper applied to a physical state

I counted identifier occurrences in both types (`Source`:42–122 and :145–225; the counts are identical):

| Identifier | Count | Where |
|---|---|---|
| `spatialKeplerAxis`, `spatialKeplerAction`, `spatialKeplerEccVector` | **0** | — |
| `spatialStrongAMD`, `spatialStrongAMDOn`, `spatialKeplerPeri/Apo` | **0** | — |
| `spatialOscVelocity/Param/Axis/EccVector/Peri/Apo` | **0** | — |
| `spatialKeplerEnergy` | 3 | physical premise (:155), `h₀` (:156–157), `hs` (:175–176), each as `… < 0` |
| `spatialOscEnergy`, `spatialOscEcc` | 1 each | the `ho` binder type (:198–200), as `… < 0`, `… < 1` |
| `spatialSource{KeplerAxis,KeplerAction,KeplerEccVector,KeplerPeri,KeplerApo,StrongAMD}` | 4, 5, 1, 3, 2, 4 | every canonical element at `z₀` and `z t` |
| `spatialSourceOsc{Energy,Axis,Ecc,EccVector,Peri,Apo}` | 1, 2, 1, 1, 4, 3 | the osculating block |

The `ho`-binder occurrences are the inlined body of the frozen-listed carrier `SpatialOscPhase` (`Basic`:163–166). The
`h₀`/`hs` occurrences are the inlined body of `SpatialNegativeEnergy` (`Elements`:63–64). Both are allowed by
review 4 (review 4:316–319).

**Refutation attempt: are these predicates faithful on the whole phase space?** Yes:

- Off the guard `|q_i| > 0`, Lean's `x / 0 = 0` sends the junk values to `spatialKeplerEnergy = |p|²/(2ν) ≥ 0`
  (`Elements`:32–33) and `spatialOscEnergy = |V|²/2 ≥ 0` (`Basic`:52–54). So the conditions `E < 0` and `E^osc < 0`
  are **false** there even before the `0 < |q_i|` conjunct is read.
- On the guard (`ν > 0`, `μ > 0`, hence `k = 1 + μν > 0`), every formula is literal MAIN (42).

So no junk value can make any of these predicates true. The physical premise lacks the `0 < ν_i` conjunct, but `hν`
is a standing binder. The only defect is in the §4b wording (R5.1).

## 3. Five-bin binder delta vs review 4

| Input (new position) | Old §3d (`old`) | New (`Source`) | Bin | Change |
|---|---|---|---|---|
| standing binders `hn … hτ` | :142–146 | :145–149 | STANDING (15) | none |
| `μ`, `0 < μ`, `μ ≤ μ₀` | :150 | :153 | SOURCE (3) | none |
| `z₀ : Phase (n * 3)` | :151 | :154 | TYPING | none |
| physical premise `∀ i, 0 < |q_i| ∧ E_i < 0` | :152 | :155 | SOURCE (2) | identical text |
| `h₀ : ∀ i, 0 < ν i ∧ 0 < |q_i| ∧ E_i < 0` | :158–159 (after `hch`) | :156–157 (right after the physical premise) | TYPING (3) | **moved only**, identical text |
| axes ∈ `A` | :153, `spatialKeplerAxis ν z₀` | :158, `spatialSourceKeplerAxis ⟨z₀, h₀⟩` | SOURCE | defeq (`Carrier`:71–72, :100–101) |
| Diophantine (5) | :154–156, `spatialKeplerAction ν z₀` | :159–162, `spatialSourceKeplerAction ⟨z₀, h₀⟩` | SOURCE | defeq (`Carrier`:75–76) |
| `hch` (two TYPING components) | :157 | :163–164 | TYPING (2) | defeq type |
| AMD premise `≤ orderedStrongThreshold hn ⟨_, hch⟩ − δ` | :160–161 | :165–166 | SOURCE | identical text |

**Counts:** SOURCE 8, STANDING 15, TYPING 7, RULED 0, **EXCESS 0**. These are identical to review 4 (review 4:234–235,
418). No premise was added or removed: the premise multiset is the old one up to one reordering and three
definitional renamings.

**`h₀` placement (refutation attempt).** Can moving `h₀` earlier turn it into a hidden condition?

- `h₀` now precedes the axes, Diophantine and `hch` premises.
- Its type mentions only `ν` and `z₀`, and it follows from `hν` (an earlier standing binder) and the immediately
  preceding physical premise: `h₀ := fun i => ⟨hν i, phys i⟩`. The proof constructs the analogous `hs` the same way
  (`Source`:238–239).
- A consumer can therefore always supply it at that point. It depends on no later binder and asserts nothing about the
  conclusion. It stays TYPING.

**The `∃ hs` per-time block.** After `∀ t ∈ Set.Icc (-T) T,` (`Source`:174), the block opens with
`∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧ spatialKeplerEnergy ν (z t) i < 0,` (:175–176).

- Pointwise this is `0 < ν_i` together with exactly the former guard clause
  `0 < spaceLength (bodyVector3 (z t).1 i) ∧ spatialKeplerEnergy ν (z t) i < 0` (`old`:170).
- Nothing else is in the `hs` type.
- The former three separate `∃ hs` (`old`:172, :180, :194) and the raw guard conjunct (`old`:170) are all subsumed by
  this one binder.
- `∃` extends to the end of the per-time formula, so `hs` scopes every later conjunct, including `∃ ho` (:198).

**Dependent types: well-founded and proof-irrelevant.**

- The binder order is `h₀` (:156) → `hch : (fun i => spatialSourceKeplerAction ⟨z₀, h₀⟩ i) ∈ chamber ν` (:163–164)
  → `orderedStrongThreshold hn ⟨_, hch⟩` (:166). Each binder uses only earlier ones.
- `⟨_, hch⟩ : OrderedActions ν = {I // I ∈ chamber ν}` (`StrongAMD/Threshold/Defs`:74). The `_` is the action vector
  fixed by `hch`'s type.
- The same order holds in the conclusion: `hs` (:175) → `hcht` (:177–178) → `⟨_, hcht⟩` (:180).
- `spatialSourceKeplerAction ⟨z, h⟩ i` unfolds by δ and projection-ι to `spatialKeplerAction ν z i` for **every** `h`
  (`Carrier`:75–76). So the `hch`/`hcht` types, the `OrderedActions` element and the threshold value are independent
  of the particular `h₀`/`hs`, up to definitional equality and Lean's definitional proof irrelevance.
- The same holds for `spatialSourceStrongAMD ⟨z, h⟩` (`Carrier`:95–96, :132–133; `Elements`:70).
- The anonymous constructor into `SpatialElliptic` (a `def`, R4.7) elaborated per the handoff, as it did for the old
  §3d.

**Outputs, not inputs.** `hs`, `hcht` and `ho` occur only under `∃` in the conclusion. `ho`'s `0 < μ`,
`E^osc < 0` and `e^osc < 1` are proved outputs (`Source`:240–243).

## 4. Every conclusion of the old §3d is recovered (and conversely)

Fix `t ∈ [−T, T]`, and let `hs`, `hcht`, `ho` be the new witnesses. The `rfl` equations used are:

- `spatialSourceKeplerAxis/Action/EccVector ⟨z, h⟩ i ≡ spatialKepler{Axis,Action,EccVector} ν z i` (`Carrier`:71–80,
  :100–113);
- `spatialSourceStrongAMD ⟨z, h⟩ ≡ spatialStrongAMD ν z` (`Carrier`:95–96, :132–133; `Elements`:58–59, :70);
- `spatialSourceKeplerPeri/Apo ⟨z, h⟩ i ≡ spatialKeplerAxis ν z i * (1 ∓ spaceLength (spatialKeplerEccVector ν z i))`
  (`Basic`:200–206, :246–252).

| Old §3d conclusion (`old`) | Recovered from the new text (`Source`) |
|---|---|
| :170 raw guard `∀ i, 0 < |q_i(t)| ∧ E_i(t) < 0` | `fun i => (hs i).2` (:175–176) |
| :171–175 `∃ hcht` (raw action ∈ chamber), `∃ hs`, AMD margin `≤ B − δ/2` | `⟨hcht, hs, amd⟩`; `hcht`'s new type (:177–178) is defeq to the old one; :179–180 |
| :176–177 Λ drift (raw) | :181–183, defeq |
| :178–179 `a` drift (raw) | :184–186, defeq |
| :180–184 `∃ hs`, AMD drift | `⟨hs, :187–189⟩` |
| :185–186 `dStar ≤ a(1 − |𝐞|)` | :190–191 via `spatialSourceKeplerPeri_eq` |
| :187–190 adjacent canonical annulus gap | :192–194 via `spatialSourceKeplerPeri/Apo_eq`, with the same indices `a.upperIdx`, `a.1` |
| :191, :192–193 star and pair distances | :195, :196–197, identical text |
| :194–222 `∃ hs ho`, osculating block (incl. `A_elem` against raw `a`, `𝐞`) | `⟨hs, ho, …⟩` (:198–225); the `A_elem` clause at :208–213 is defeq to `old`:206–210 |
| constants, their positivity and the N10 ordering | :150–152 = `old`:147–149, identical |

**Converse.** Given the old conclusion and `hν`, set `hs := fun i => ⟨hν i, (raw guard) i⟩`. Take `hcht` from
:171, and get each `sourceStrongAMD ⟨z t, hs'⟩` clause for the new `hs` by proof irrelevance. The ellipticity of the
osculating carrier (`ho`) is carried over unchanged. So the new and old §3d are logically equivalent, and both are
equivalent to §3c. Nothing was weakened.

The proof script confirms this without being needed for the paper argument: both theorems are closed from the §3c
producers by `obtain`/`exact` repacking alone (`Source`:123–141, :226–244). The producers are
`lp2_spatial_strongAMD_safety` (`Main`:43) for `_general` and `…_normalized` (`Main`:153) for `_source`.

## 5. SourceCarrier docstring (`Carrier`:20–22)

The docstring reads: "the unrestricted total helpers `spatialKeplerAxis`, `spatialKeplerAction`, … stay internal and
are not frozen as physical quantities. Every physical quantity is exposed through a source subtype."

- For the three named helpers this is now **true** of the anchor: zero occurrences (§2).
- Every physical quantity in either type is a `spatialSource*` restriction. The exceptions are the literal frozen
  formulas `spaceLength (bodyVector3 …)`, the solution and Newton predicates, and the sign conditions inside guarded
  predicates.
- Review 4's R4.6 third item (review 4:503) is resolved. The handoff's decision not to edit the file
  (`LP-SP-SRCB2-handoff`:6) is accepted.
- The open-ended "…" would also cover `spatialKeplerEnergy` and `spatialOscEnergy/Ecc`. These do appear, but only as
  predicate content. See R5.2 (optional).

## 6. §4b spatial bullet vs the new text

Consistent on substance:

- Every `spatialSource*` identifier the anchor uses is in the "semantic unit" list (proposal:524–527).
- Both carriers are in the "literal" list as `SpatialElliptic (= SpatialSourceCanonicalPhase)` and
  `SpatialOscPhase (= SpatialSourceOsculatingPhase)` (proposal:519–520).
- Every other identifier in the type is in the literal list or in the threshold and frozen-planar inventory:
  `spaceLength`, `bodyVector3`, `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn`, `IsSpatialNewtonSolutionOn`,
  `spatialMasses`, the barycentric maps, `chamber`, `orderedStrongThreshold`, `AdjIdx`, `modeSize` and `Phase`.
- The bullet's own precondition "presupposes R4.1 (A)" (proposal:534) is now met.
- The listed internal helpers (`spatialKeplerAxis/Action/EccVector`, `spatialKeplerPeri/Apo`, `spatialStrongAMD`)
  enter only through the definition closure of the source restrictions, which is the intended reading.

One wording defect, R5.1.

## Findings

### R5.1 — CHANGE-RECOMMENDED: §4b's "used only inside the carrier predicate" is inexact and incomplete

**Evidence.**

- proposal:530 says `spatialKeplerEnergy` is "used only inside the carrier predicate". It also occurs in the
  **physical premise** `∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0` (`Source`:155;
  proposal:394). That is a SOURCE premise, not the carrier predicate (it has no `0 < ν_i` conjunct).
- proposal:531 lists `spatialOsc*` as internal with no qualification. Yet `spatialOscEnergy` and `spatialOscEcc` occur
  raw in the `∃ ho` binder type (`Source`:198–200; proposal:437–439), the inlined `SpatialOscPhase` predicate
  (`Basic`:163–166).
- Review 4 made the same incomplete claim: "The only remaining raw formula is `spatialKeplerEnergy`" (review 4:419).
  The prover's handoff states it correctly (`LP-SP-SRCB2-handoff`:22–24).

**Impact.** Not a fidelity or gate defect. Every such occurrence is a sign condition in a guarded predicate that is
faithful on the whole phase space (§2). But §4b is the freeze inventory, and a frozen-definition audit should not have
to rediscover these occurrences.

**Replacement** for proposal:529–531 (from "The total formulas stay" to "`spatialOsc*`."):

> The total formulas stay **internal implementation helpers in the definition closure** and are not certified as
> MAIN's objects off their carriers: `spatialKeplerEnergy`, `spatialKeplerAxis/Action/EccVector`, `spatialStrongAMD`,
> `spatialStrongAMDOn`, `spatialKeplerPeri/Apo` and `spatialOsc*`. In the anchor text, only `spatialKeplerEnergy`,
> `spatialOscEnergy` and `spatialOscEcc` occur directly. Each occurs only as a sign condition inside a guarded
> predicate:
>
> - `spatialKeplerEnergy` in the physical premise and the canonical carrier predicate (`h₀`, `hs`);
> - `spatialOscEnergy` and `spatialOscEcc` in the osculating carrier predicate (`ho`).
>
> These predicates are false whenever `|q_i| = 0` and literal otherwise.

### Notes

- **R5.2 — SourceCarrier docstring precision (optional).** `Carrier`:20–22 is accurate for the named helpers. To
  close the "…", one could append: "(`spatialKeplerEnergy`, `spatialOscEnergy` and `spatialOscEcc` enter only as
  sign conditions in the carrier predicates)". This is not required for the freeze.

- **R5.3 — Stale proposal prose.** None of these changes a code block.
  - §1 LP2 row (proposal:30) still says "text §3c, not yet statement-reviewed". Review 4 passed §3c, and under (b)
    the anchor surface is the §3d text (R4.2 tail, review 4:448–449).
  - §3c intro (proposal:308–309) still calls LP-SP-SRC "in progress".
  - §3d (proposal:380–381), "Same shape as §3b relative to §3: a typing binder `h₀`, the source AMD in the hypothesis,
    existential subtype proofs in the conclusion", no longer describes the difference. §3d now also restricts the
    canonical axis, action and eccentricity vector in the premises and conclusions, places `h₀` before the axes
    premise, and merges the per-time witnesses into one `∃ hs`.
  - The §3d header and italic note (proposal:368, :370–373) say "delta re-review pending"; update them after this
    review.

- **R5.4 — §3b/§3d twin asymmetry (supersedes R4.4).** The planar §3b (proposal:216–290) keeps raw
  `keplerAxis/Action/EccVector`, the `h₀`-after-`hch` order and three separate `∃ hs`. §3d no longer mirrors that.
  This is acceptable because the planar raw helpers are frozen repository conventions (review 4:421–422). Restating
  §3b the same way remains optional, for symmetry only.

- **R5.5 — Physical premise and `h₀` adjacency.** `h₀` (`Source`:156–157) contains the physical premise (:155)
  pointwise, plus `0 < ν_i`. Keeping both separates the SOURCE premise from the TYPING datum, as in §3b. Merging them
  would blur that distinction, so no change is recommended.

- **R5.6 — Carry-overs.**
  - R4.2: §3d still shows the implementation name `lp2_spatial_strongAMD_safety_source`. The frozen anchor name under
    (b) is still to be fixed, as for §3b.
  - R4.5 (geometric L16 scope), R4.7 (`SpatialElliptic` is a `def`), R4.8 (`spatialHamiltonian` totalized) and R4.9
    (no spatial LP0) are unchanged.
  - R4.6 is still open for `Elements`:35 ("Osculating semimajor axis" on the canonical `spatialKeplerAxis`) and
    `Model`:19–21 ("MAIN (1), literally; no totalization"). Both are unchanged on `inp-lp-spsrcb2`, and the handoff
    asks for them to be assigned (`LP-SP-SRCB2-handoff`:33–34).

- **R5.7 — Handoff details.**
  - The handoff says `Source.lean` has 247 lines (`LP-SP-SRCB2-handoff`:4). `wc -l` on the blob gives 248. This is
    trivial and far below the 1500-line cap.
  - The build ("Build completed successfully"), lint (exit 0), short-name check and `#print axioms`
    `[propext, Classical.choice, Quot.sound]` (`LP-SP-SRCB2-handoff`:17–21) are the prover's claims. I did not
    reproduce them (see "Checks").

## Checks performed

- `sha256sum` of every input in the Identity table. The odb attachments are byte-identical to the
  `inp-lp-spsrcb2` blobs.
- Byte-level `diff` of review 4:335–415 against `Source`:145–225, `Source`:42–122 and proposal:384–464, with exactly
  the differences reported in §1.
- Identifier-occurrence count over both theorem types (`grep -o | sort | uniq -c`), reported in §2.
- `git diff --stat inp-lp-spsrcb inp-lp-spsrcb2` for the definition files. `git merge-base --is-ancestor` for the
  branch relation. Threshold `Defs.lean` compared between HEAD and `inp-lp-spsrcb2`.
- Full reading of the old and new `SpatialSafety/Source.lean`, `SourceCarrier.lean`:1–150, `Elements.lean`:25–81,
  `Osculating/Basic.lean`:40–90 and 155–260, `Threshold/Defs.lean`:28–95, proposal §1, §3b–§3d and §4b, review 4,
  the handoff, `OWNER-DECISIONS.md` OD-11, and MAIN:597–603 (T19).

**Not performed: any Lean, Lake or lint run** (the brief forbids Lean/Lake; `scripts/lint_sources.sh` launches a Lean
subprocess). This is a deviation from AGENTS "Before handing off". Elaboration, the build and the axioms of
`lp2_spatial_strongAMD_safety_source{,_general}` are **unverified by me**. The orchestrator should confirm them (one
targeted capped build plus `#print axioms`) before recording the gate as closed.

## Handoff

- **Files:** `docs/tracks/LP/freeze/STATEMENT-REVIEW-5.md` only (not staged, not committed).
- **Approach:** delta review against review 4. Byte-level verbatim comparison; identifier census of both types;
  five-bin delta; dependent-binder well-foundedness; clause-by-clause recovery of the old §3d through the `rfl`
  equations, plus the converse; docstring and §4b consistency.
- **Uncertainties:** Lean not run (above). The anchor name under (b) (R4.2) and owner decisions OD-1…OD-11 are open.
- **Suspected errata in MAIN:** none.
- **Deviations:** no lint or build run (brief).

## Hard rules (verbatim)

1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.
