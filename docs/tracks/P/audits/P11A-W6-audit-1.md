# Independent audit: P11A-W6

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11aw6`.
Audited HEAD: `ea71d2a1f23fc965d151b97959e51453b555d176`.

## Verdict and scope

**PASS WITH NOTES for P11A-W6 (`bpP:p11a:sublevel`).** The implementation proves the audited design signature with the stated constant and no extra premises. The notes concern inherited branch differences, dependency warnings, the expected stale generated root, and signature-source location. No mathematical defect was found in the audited module.

This is an infrastructure package: it supplies `KAM.Planetary.sublevel`, not a frozen theorem/provider pair. There is no frozen anchor to seal in W6. Provider/frozen type equality and a frozen seal-body probe therefore do not apply. An independently elaborated copy of the exact design signature, with body `by exact sublevel H he he'`, and an `example : type_of% @auditExpectedSublevel := @sublevel` both pass instead. This verdict does not assert closure of P-G, P-PLANAR, P-FIXED, or the P11A campaign.

Read AGENTS.md, PLAN.md, DECISIONS.md, the supplied package-audit brief, the W6 handoff, P11A design (especially the W6 row at line 708 and the node map at lines 228–233), all three cited design-audit reports, the Track P statement and the sublevel blueprint at `blueprint-P/parts/p11a1-weak-measure.tex:119–141`. The frozen P-G anchor was inspected for context; it is not an input to W6. No frozen definitions occur in this module's project import closure.

The requested signature file `.drafts/design/P11ASignatures.lean` is absent in this worktree. Read the existing copy at `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean:137–142`, without importing or elaborating its draft proofs. Its SHA-256 at inspection was `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`.

Only `KAM/Planetary/WeakMeasure/Sublevel.lean` (444 lines) is audited as instructed by AUDIT FOCUS. Its SHA-256 is `a92a918ec294b12b7d59595e203c0785be8fbf43919877056f466a77af351094`.

## Branch comparison and protected paths

Ran `git diff inp...HEAD` (including its statistics and protected paths). Git reports:

```text
warning: inp...HEAD: multiple merge bases, using 026f93d5639c1243025532fea8acf097a82e1643
```

That comparison includes 40 files, 7314 insertions, one deletion: it includes inherited packages, reports, and 16 generated `KAM.lean` imports. Thus the brief's literal broad protected-path condition is **not empty** for `KAM.lean`; this exception is recorded, not silently treated as a clean broad diff. `KAM/Frozen`, `manifest`, and `README.md` have no changes in that comparison (quiet diff exit 0). Root history attributes generated updates to inherited commits `408ea7a` and `5991245`.

Also ran the handoff's narrower `git diff inp-p11aw5...HEAD`: four files, including inherited W1 Stability and its audit/handoff, plus the new 444-line Sublevel module. For this baseline, `git diff inp-p11aw5...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (quiet diff exit 0). W6 history for Sublevel consists of `f26df42`, `5ca83e6`, `c1dfe65`, `ea71d2a`.

`git diff --check inp-p11aw5...HEAD` exits 0. The broad `git diff --check inp...HEAD` reports only an inherited trailing space at `docs/tracks/P/audits/P23-12-handoff.md:28`; it is outside W6. The initial worktree already had untracked `docs/tracks/P/audits/P11A-W6-handoff.md`. The auditor did not change it or any production file.

## Declaration and node audit

All names below are in `KAM.Planetary`; line numbers refer to Sublevel.lean. Every new public theorem is listed.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Euclidean scaling helper | `p11euclid_smul` (35) | PASS | Exact absolute scalar homogeneity, including zero and negative scalars. |
| Euclidean separation helper | `p11euclid_eq_zero` (38) | PASS | Zero Euclidean length implies the actual vector is zero; no dimension premise needed. |
| `sl-lower`, multilinear bound | `p11_jet_cons_bound` (43) | PASS | Full operator gauge bounds one arbitrary slot and the repeated unit slots; zero arbitrary vector treated separately. Smoothness is used for the scalar/vector jet bridge. |
| `sl-lower`, mean value | `p11_jet_mvt` (80) | PASS | Differentiates the actual directional jet along the segment and integrates its derivative bound; all segment-membership and size inputs are explicit. These are the blueprint MVT inputs, discharged in `p11_sl_lower`. |
| `bpP:p11a:sublevel#kappa` | `p11_sl_kappa` (121) | PASS | Same natural ceiling, all three lower bounds and exact upper bound. Positivity and `M ≥ β` are source inputs. |
| Thickening geometry helper | `p11_mem_thick` (167) | PASS | A point of K belongs to its positive closed Euclidean thickening. |
| Thickening geometry helper | `p11_ball_mem_thick` (170) | PASS | Ball radius at most v gives membership using its center in K. Valid even for vacuous negative-radius cases. |
| `stepP:p11a:sl-lower` | `p11_sl_lower` (175) | PASS | Obtains attained order and unit direction from the finite-type amount; proves one fixed jet of gt is at least β/4 throughout the ball. No lower-bound conclusion is assumed. |
| `stepP:p11a:sl-ball`, exponent arithmetic | `p11_sl_ball_arith` (230) | PASS | For 1 ≤ ν ≤ μ, 0 < x < 1/4 and Q ≥ 0, proves the exact `2ν Q (4x)^(1/ν) ≤ 8μ Q x^(1/μ)`. The x bound specializes the source epsilon range. |
| `stepP:p11a:sl-ball` | `p11_sl_ball` (256) | PASS | ν=0 gives an empty sublevel set; ν≥1 uses the proved ball theorem with β/4 and the above arithmetic. |
| `stepP:p11a:sl-cover`, cell object | `p11cell` (289) | PASS | Actual closed coordinate cell for every index and side parameter; exposed body. |
| `stepP:p11a:sl-cover`, cell radius | `p11cell_euclid_le` (293) | PASS | Two points of a nonnegative-side cell have Euclidean separation at most sqrt(n) h. |
| `stepP:p11a:sl-cover`, finite cover | `p11_cube_cover` (310) | PASS | Coordinate minima of compact nonempty K give a max-norm cube of side diam K; clamped floor includes the right endpoint. Index type has exactly κ^n elements. No covering premise added. |
| `stepP:p11a:sl-sum`, arithmetic | `p11_sl_sum_arith` (362) | PASS | Cancels κ^m against r^m, keeps one factor κ, then substitutes its upper bound. The input κ ≤ ρ C is the proved ceiling estimate. |
| `bpP:p11a:sublevel`, cover/ball/sum assembly | `sublevel` (381) | PASS | Exact design signature; r positive, r ≤ v, Mr ≤ β/4 proved internally. Finite subadditivity yields the exact C_sub. |

The helper premises are typing, regularity, positivity, or intermediate mathematical inputs proved at their actual call sites. None exports a conditional replacement for an unpaid main theorem. `p11_sl_lower` consumes only the intended source bundle plus the constructed-radius bounds; its proof discharges the MVT hypothesis from H.size and thickening membership.

## Definition classification and statement fidelity

The sole new global definition is `p11cell`: a coordinatewise closed cell with lower endpoint `a0 i + j i * h` and upper endpoint `a0 i + (j i + 1) * h`. This is the intended object on its whole carrier. For κ=0 the index type has no inhabitants when n>0; the covering theorem assumes κ≥1. For h<0 a positive-dimensional cell is empty, as its coordinate inequalities dictate; the distance lemma requires h≥0 and the actual cover has h=d/κ>0. There are no fallback values or hidden choices in the definition. The file-level `@[expose] public noncomputable section` exposes it.

Local `set` objects are actual jets, a normalized nonzero vector, affine segment, scalar jet curve, ceiling argument, max diameter, radius, sublevel set and its numerical bound. The only normalization by a potentially zero length is guarded by a separate zero-vector case. Compact minimizers and the attained jet order/direction come from proved attainment lemmas; no arbitrary supremum value is used as an extremizer without proof.

Compared the theorem signature to the design source by removing whitespace: identical. `P11Patch`, `P11SublevelHyp`, and `p11Csub` in Basic.lean are byte-identical to their corresponding design blocks. The bundle contains exactly geometry, regularity, positivity, finite type (S1), full operator size (S2), and diagonal closeness (S3). In particular, no sublevel-measure conclusion is bundled as a field.

The ambient norm stays the max norm on `Fin n → ℝ`; only explicit lengths use the Euclidean gauge. Thus `Metric.diam P.K` is precisely d_infinity, whereas cell balls have radius sqrt(n)d/κ. There is no missing sqrt(n) or change of Lebesgue measure.

At the assembly step the proof selects a center only for cells intersecting the target sublevel set E (lines 412–420), instead of every cell meeting K. This is sufficient: such a center belongs to K, and every point of E in that cell is within r of it. The finite cover is still proved for all K. Shared closed-cell boundaries only overcount, which is valid for the upper estimate. N=1 is retained; the exponent n−1 becomes zero. The order-zero finite-type alternative is explicitly handled.

## Independent validation receipts

All Lean/Lake invocations below use `LEAN_NUM_THREADS=1` and `nice -n 5`, sequentially. No heartbeat, recursion-depth or synthesis override was added. The compile gate was allowed to wait for its slot. No library clean, dependency update or cache fetch was run.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw6 KAM.Planetary.WeakMeasure.Sublevel
```

Exit 0. Gate acquired slot 2 at 10:32:02 UTC. Final output:

```text
Build completed successfully (9055 jobs).
```

This is a targeted build using the existing worktree snapshot. Replayed dependency warnings: Stability.lean:302:29 (`hn`), :304:19 (`hK`), :403:27 (`hn`); DividedDifference.lean:96:59 (`hab`), all unused-variable warnings. No Sublevel.lean warning.

### Signature and axioms probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW6Audit.lean
```

Exit 0. The probe imports only the delivered Sublevel module, prints axioms of all 14 new public theorems, copies the design signature under `auditExpectedSublevel` with body `by exact sublevel H he he'`, and checks `example : type_of% @auditExpectedSublevel := @sublevel`. Neither signature test emitted an error or warning.

For every name below the exact output has the form `'KAM.Planetary.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`:

```text
p11euclid_smul
p11euclid_eq_zero
p11_jet_cons_bound
p11_jet_mvt
p11_sl_kappa
p11_mem_thick
p11_ball_mem_thick
p11_sl_lower
p11_sl_ball_arith
p11_sl_ball
p11cell_euclid_le
p11_cube_cover
p11_sl_sum_arith
sublevel
```

No sorryAx or other axiom occurs. The temporary probe is deleted after validation.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.Sublevel KAM.Planetary.WeakMeasure.Stability KAM.Planetary.WeakMeasure.BallSublevel KAM.Planetary.WeakMeasure.Basic
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.WeakMeasure.Basic
replaying KAM.Planetary.WeakMeasure.BallSublevel
replaying KAM.Planetary.WeakMeasure.Stability
replaying KAM.Planetary.WeakMeasure.Sublevel
```

### Source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the explicitly permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (530 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is PASS under the brief's stated lint exception, not an unqualified zero-exit lint receipt. No generated file was regenerated.

### Additional hygiene and imports

A recursive scan of the nine project modules reachable through KAM imports found no `KAM.Frozen.*` or `KAM.Provider.*` imports. Therefore no DRAFT_SORRY theorem or quarantined provider is transitively imported, and there is no imported frozen theorem whose manifest seal state needs an exception.

The audited source has 444 total lines and no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option` token. It has its copyright/authors header, `module`, public imports, module docstring and exposed public section. The targeted branch diff passes whitespace checks. Final workspace `git diff --check` exits 0; the only new audit artifact is this report, alongside the pre-existing untracked handoff. No state-changing git operation was used.

## Blueprint/source defects, deviations and limits

No new suspected blueprint or pinned-source defect was found in W6. The underlying source adaptations D1–D3 (one-variable constant, cube-based section bound, two tensor gauges and epsilon range) are already explicit in `blueprint-P/parts/p11a1-weak-measure.tex:119–145`; the implementation uses exactly that blueprint constant, rather than claiming literal Rus01 constants. This audit checks fidelity to those supplied statements and the delivered proof; it does not newly certify the historical source quotations against a PDF.

There is no implementation deviation requiring a statement change. The sublevel-centered cell selection and promotion of proof-local arithmetic to public helper lemmas preserve the full blueprint conclusion. The MVT, lower bound, covering and summation are proved, not assumed. Remaining limitations are outside the assigned module: subsequent P11A consumers, their proofs, and frozen headline/provider closure.

