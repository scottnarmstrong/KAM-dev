# Independent P11A-W0 package audit 1

Overall verdict: **FAIL — W0's retained N3 minimum-attainment gate is incomplete.** The implemented helper proofs pass mathematical inspection and compilation; the failure is missing required source-definition evidence, not a counterexample to a proved lemma. No frozen anchor is sealed by this infrastructure package.

## Scope and snapshot

Audited only `KAM/Planetary/WeakMeasure/Basic.lean` and its project import closure, under the package brief, handoff AUDIT FOCUS, AGENTS.md, PLAN/DECISIONS, track-P statement and Revision-3 design. User's explicit report location overrides the generic brief's main-worktree output instruction. No production edits, git mutations, source repairs or other package audits were performed.

- HEAD: `6c02f4e8a576f18aaa489085df7e2af397c57728`.
- `inp` at initial diff: `ef8fc426c638557035e6101216aad4ef8b8a570e`; it advanced concurrently to `4dad814dc58f7f254a380a342178c120e2d69be9` at final verification. Both comparisons have merge base `cba16d0704fe352828a08b2eff9cb691184b8208`; the final three-dot diff still contains only Basic.
- `git diff inp...HEAD --stat`: one added file, 285 insertions.
- Basic SHA-256: `9fd521308e38022803479924f24735c1f3007f130bd2966c0ccba36e77901aa7`.
- Design SHA-256: `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9`.
- `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` SHA-256: `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` (the scratch signature file is absent in this package checkout; the designated inp copy was read without changes).
- `blueprint-P/parts/p11a1-weak-measure.tex` SHA-256: `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5`.

Read design audits 1–3, particularly retained N3; previous design PASS is not implementation proof closure. The only project imports reachable from Basic are `KAM.Nekhoroshev.Interfaces.Norms` and `KAM.Fourier.Derivative`; neither introduces a frozen theorem or provider. No frozen statement occurs in the package interface. Frozen/provider exact-type and explicit-binder seal probes are therefore **N/A**, rather than silently counted as passed.

## Blocking finding W0-01: the source minimum has no attainment theorem

**Authority:** `docs/tracks/P/design/P11A-LEAN-DESIGN.md:38–41` says “Prove boundedness, continuity and attainment before using the infimum”; its retained N3 at **873–875** explicitly says “W0 must establish boundedness/attainment for each supremum/infimum on positive-dimensional unit spheres and nonempty compact patches”. This obligation remains after design audit 3 (its N3 row). W0 is assigned both `conv#data` and `index-def` in design rows 208–209.

**Source:** `blueprint-P/parts/p11a1-weak-measure.tex:44–46` defines beta as a **minimum**, then calls it “A minimum of a continuous function on a nonempty compact set”. Joint continuity in `(c,y)` and attainment are substantive parts of that definition's justification.

**Implementation:** Basic:51–54 defines `index_def` by `sInf`. Basic:239–268 proves nonemptiness, lower boundedness, nonnegativity and lower-bound/universal-bound rules. None proves joint continuity, compactness of the value set or an actual minimizing `(c,y)`. Basic:181–185 and 204–208 attain the direction suprema; 225–227 attains the finite maximum over orders. Those do not attain the outer infimum over coefficients and basepoints. The handoff expressly admits: “Not proved: attainment of the infimum in `index_def`”.

**Why blocking:** the current code makes a genuine infimum on the intended nonempty carrier, and its order lemmas are sound. This is weaker evidence than the source minimum and the mandatory W0 N3 delivery. Possible future consumers using only lower-bound rules do not waive the stated package gate. There is no identified false Lean theorem or exploitation of an empty infimum here.

**Required completion (not applied):** under source guards `1 ≤ n`, `1 ≤ m`, `IsOpen V`, `ContDiffOn ℝ mu w V`, nonempty compact `K ⊆ V`, prove enough joint continuity/compactness to export

```lean
∃ c : P11Vec m, p11euclid c = 1 ∧
  ∃ y ∈ K, index_def rho mu w K = p11maxJet mu (p11scalar rho w c) y
```

for the source conventions `rho = 1 ∨ rho = 2`, without assuming the minimizer or continuity of the desired maximum as a new source premise. A source-faithful proof may establish a stronger all-natural-rho version. Existing definitions and frozen files need no edits. Until this is delivered, mark `index-def`/N3 incomplete.

The least-positive-index wrappers are correctly conditional on existence; they do not prove `rank_compact`. Stability and rank-compact theorem bodies are outside this audit; no claim about their eventual proof requirements is certified.

## Declaration ledger

Names below are in `KAM.Planetary`. Each of the **24** abbreviations/definitions/structures has the same complete declaration text as the pinned signature after comment and whitespace removal. The ledger distinguishes formula identity from source-characterization completeness.

| Node / responsibility | Declaration (Basic line) | Verdict | Reason |
|---|---|---|---|
| conv#data | `P11Vec` (24) | PASS | Real Pi carrier; max norm retained. |
| conv#data | `P11CVec` (25) | PASS | Complex Pi carrier. |
| conv#data | `P11Phase` (26) | PASS | Product of two complex Pi carriers. |
| conv#data | `P11Family` (27) | PASS | Phase paired with complex parameters. |
| conv#data | `p11euclid` (29) | PASS | Existing explicit Euclidean length, no instance change. |
| conv#data | `p11dot` (30) | PASS | Literal real scalar product. |
| conv#data | `p11dotZ` (31) | PASS | Literal integer-mode real pairing. |
| conv#data | `p11dotC` (33) | PASS | Literal integer-mode complex pairing. |
| conv#data | `p11thick` (36) | PASS WITH NOTES | Existential closed Euclidean thickening; agrees with source distance thickening for nonempty compact K. |
| conv#data / N3 | `p11dg` (39) | PASS WITH NOTES | Diagonal unit-sphere gauge; maximum attained when n ≥ 1. |
| conv#data / N3 | `p11op` (42) | PASS | Closed-unit-ball multilinear gauge; compact and attained. |
| index-def | `p11scalar` (45) | PASS | Literal scalar family, output Fin 1 → ℝ, exponent rho. |
| index-def / N3 | `p11maxJet` (48) | PASS | Maximum over all orders 0 through mu; finite and attained. |
| index-def / N3 | `index_def` (51) | FAIL | Infimum formula matches; required source minimum attainment missing (W0-01). |
| conv#data | `p11JetBound` (55) | PASS | Pointwise universal jet bound; true=diagonal, false=operator; includes order zero. |
| stability convention | `p11eta` (58) | PASS WITH NOTES | rho=1 branch and squared-family branch exact; latter intended for rho=2. |
| S/D standing geometry | `P11Patch` (61) | PASS | Only source geometry, max-norm diameter, positive dimension/radius. |
| S1–S3 | `P11SublevelHyp` (73) | PASS | Source regularity, finite type, size and closeness; no sublevel result assumed. |
| sublevel constant | `p11Csub` (85) | PASS WITH NOTES | Literal explicit formula; positive radius supplied at theorem use. |
| rank-compact / p10:rnd-def | `p11RNondegenerate` (89) | PASS | No nonzero real functional annihilates all w(V). |
| diophantine-measure H | `p11Good` (92) | PASS | Original K and mode-dependent maps; correct ≥ divisor inequality. |
| D1–D3 | `P11DioHyp` (95) | PASS | Literal input bundle; profile positivity/D4 intentionally belong to later theorem binders. |
| index-def | `p11Index` (112) | PASS WITH NOTES | Nat infimum; least-positive specification proved only under candidate existence. |
| index-def | `p11Amount` (114) | PASS WITH NOTES | Amount at the least positive index; positivity conditional, not rank-compact closure. |
| N3 / order helper | `p11euclid_continuous` (120) | PASS | Continuous finite sum/square/square-root. |
| N3 / order helper | `p11euclid_nonneg` (124) | PASS | Square-root nonnegativity. |
| N3 / order helper | `p11euclid_zero` (126) | PASS | Literal zero evaluation. |
| N3 / order helper | `p11sphere_isCompact` (129) | PASS | Closed Euclidean level set bounded in the retained max norm. |
| N3 / order helper | `p11ball_isCompact` (136) | PASS | Closed Euclidean sublevel bounded in max norm. |
| N3 / order helper | `p11sphere_nonempty` (143) | PASS | One coordinate unit vector, requires n ≥ 1. |
| N3 / order helper | `p11tuple_isCompact` (149) | PASS | Finite product of compact closed balls. |
| N3 / order helper | `p11tuple_nonempty` (157) | PASS | All-zero tuple, including j=0. |
| N3 / order helper | `p11dg_nonneg` (173) | PASS | All values nonnegative; remains true on empty sphere. |
| N3 / order helper | `le_p11dg` (177) | PASS | Actual unit vector plus compact-image boundedness. |
| N3 / order helper | `p11dg_attained` (181) | PASS | Nonempty sphere and compact image; no smoothness premise. |
| N3 / order helper | `p11op_nonneg` (196) | PASS | Nonnegative image values. |
| N3 / order helper | `le_p11op` (200) | PASS | Actual admissible tuple and compact-image bound. |
| N3 / order helper | `p11op_attained` (204) | PASS | Zero tuple ensures nonemptiness; compact image. |
| N3 / order helper | `p11dg_le_p11op` (211) | PASS | Repeated attained unit direction is an admissible operator tuple. |
| N3 / order helper | `p11maxJet_set_finite` (216) | PASS | Image of finite natural interval Iic mu. |
| N3 / order helper | `le_p11maxJet` (222) | PASS | Finite-set supremum bound for j ≤ mu. |
| N3 / order helper | `p11maxJet_attained` (225) | PASS | Order-zero witness makes finite set nonempty. |
| N3 / order helper | `p11maxJet_nonneg` (229) | PASS | Attained value is a nonnegative diagonal gauge. |
| N3 / order helper | `index_def_set_nonempty` (239) | PASS | Unit coefficient exists for m ≥ 1; K supplies basepoint. |
| N3 / order helper | `index_def_set_bddBelow` (247) | PASS | Zero lower bound on every value. |
| N3 / order helper | `index_def_nonneg` (252) | PASS | Nonnegative real infimum, including totalized empty case. |
| N3 / order helper | `index_def_le` (257) | PASS | Infimum ≤ actual value, with proved lower boundedness. |
| N3 / order helper | `le_index_def` (263) | PASS | GLB rule with explicit m ≥ 1 and K nonempty. |
| N3 / order helper | `p11Index_spec` (270) | PASS | Nat.sInf_mem on nonempty positive-index candidates. |
| N3 / order helper | `p11Index_le` (275) | PASS | Nat.sInf_le for a supplied admissible index. |
| N3 / order helper | `p11Amount_pos` (279) | PASS | Extracts positivity from p11Index_spec; existence remains required. |

The two private compact-image lemmas `p11dg_set_compact` (163) and `p11op_set_compact` (187) also pass inspection: continuity is in the direction/tuple for a fixed continuous multilinear map. This does not require smoothness of the original function in y. No symmetry or joint continuity of the derivatives is smuggled into these proofs.

## Definition classification and whole-carrier check

Literal carrier aliases: P11Vec, P11CVec, P11Phase, P11Family, p11euclid. Literal algebra/set/predicate/formula definitions: p11dot, p11dotZ, p11dotC, p11thick, p11scalar, p11JetBound, p11eta, p11Csub, p11RNondegenerate, p11Good. Source-input structures: P11Patch, P11SublevelHyp, P11DioHyp. Extremum constructions: p11dg, p11op, p11maxJet, index_def, p11Index, p11Amount. No chosen physical output or theorem-shaped replacement object is defined.

For the literal and source-input groups: BODY_MATCH=OK; PUBLIC_CARRIER=OK as literal total formulas/input bundles; WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS. All fields of the structures are expanded below. The source smoothness and positivity restrictions remain caller obligations, not properties established by their raw constructors.

For p11dg/p11op/p11maxJet: BODY_MATCH=OK; PUBLIC_CARRIER=OK for the literal totalized gauge formulas; WELL_DEFINEDNESS=OK on the source n≥1 carrier; CHARACTERIZATION=OK for attained extrema on that carrier; CHOICE_INDEPENDENCE=N/A (no selection); DEFINITION_VERDICT=PASS on source carriers. At order zero the empty tuple evaluates f(y); with n≥1 the diagonal sphere is nonempty. The operator unit-ball supremum equals the source unit-sphere maximum by multilinear homogeneity when j>0 and n≥1; at j=0 the tuple is unique. This equivalence is mathematically valid, though no separately named sphere/ball equality theorem is exported here.

For index_def: BODY_MATCH=OK against the design's infimum formula; PUBLIC_CARRIER=OK as a real infimum with explicitly guarded intended uses; WELL_DEFINEDNESS=OK for a genuine infimum on nonempty coefficient sphere × K; CHARACTERIZATION=FAIL for the source's attained minimum; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=FAIL as complete index-def/N3 delivery (W0-01).

For p11Index/p11Amount: BODY_MATCH=OK; PUBLIC_CARRIER=OK as the design's guarded total formulas; WELL_DEFINEDNESS=OK under candidate existence; CHARACTERIZATION=OK for least positive index/amount under that guard; CHOICE_INDEPENDENCE=OK (least natural number unique); DEFINITION_VERDICT=PASS WITH NOTES. This conditional status does not close the source finite-type existence theorem or the missing index_def minimum characterization.

Whole-carrier edge cases were inspected rather than treated as source theorems: n=0 makes the diagonal sphere empty; m=0 or K=∅ makes the amount value set empty; no positive candidate makes the natural infimum default to zero; rho outside {1,2} takes the squared-form eta branch. For arbitrary noncompact K the existential p11thick is not asserted to be a distance sublevel; nonsmooth total functions' iterated derivatives are not asserted to represent source smooth jets. These are the design's existing total formulas. Their off-source values supply no source claim here. None of the inspected proofs uses a default to prove positivity, a false attainment or a physical conclusion. In particular the GLB rule explicitly requires nonemptiness.

## Hypothesis audit

These are internal extremum/order helpers, not replacements for rank_compact, stability, sublevel or a frozen theorem. Their extra guards are the premises of the corresponding elementary characterization, not assumed campaign results. All public theorem inputs were checked: dimensions, functions, orders, vectors, basepoints, sets and lower-bound numbers are TYPING; the following are the complete non-typing theorem binders. There are no instances carrying project assumptions.

| Declaration | Expanded logical binder | Bin | Source / reason |
|---|---|---|---|
| p11sphere_nonempty | hn : 1 ≤ n | SOURCE | Positive parameter dimension, p11a1:17, nonempty direction sphere |
| le_p11dg | ha : p11euclid a = 1 | SOURCE | Admissible direction, p11a1:22 |
| p11dg_attained | hn : 1 ≤ n | SOURCE | Nonempty sphere for maximum, p11a1:17,22 |
| le_p11op | ha : ∀ i, p11euclid (a i) ≤ 1 | SOURCE | Admissible tuple for literal supremum |
| p11dg_le_p11op | hn : 1 ≤ n | SOURCE | Source dimension and sphere maximum, p11a1:17,23 |
| le_p11maxJet | hj : j ≤ mu | SOURCE | Finite maximum includes chosen order, p11a1:45 |
| index_def_set_nonempty | hm : 1 ≤ m | SOURCE | Nonempty coefficient sphere, p11a1:42 |
| index_def_set_nonempty | hK : K.Nonempty | SOURCE | Nonempty patch, p11a1:44 |
| index_def_le | hc : p11euclid c = 1 | SOURCE | Coefficient in index-def domain, p11a1:43–45 |
| index_def_le | hy : y ∈ K | SOURCE | Basepoint in index-def domain, p11a1:45 |
| le_index_def | hm : 1 ≤ m | SOURCE | Nonempty coefficient sphere |
| le_index_def | hK : K.Nonempty | SOURCE | Nonempty infimum domain |
| le_index_def | hb : ∀ c, p11euclid c = 1 → ∀ y ∈ K, b ≤ p11maxJet ... | SOURCE | Exact lower-bound premise of GLB helper; no claim that this bound is independently established |
| p11Index_spec | h : ∃ mu, 1 ≤ mu ∧ 0 < index_def ... | SOURCE | Conditional least-positive-index definition, p11a1:46 |
| p11Index_le | h1 : 1 ≤ mu | SOURCE | Candidate positive order, p11a1:46 |
| p11Index_le | h : 0 < index_def ... | SOURCE | Candidate membership, p11a1:46 |
| p11Amount_pos | h : ∃ mu, 1 ≤ mu ∧ 0 < index_def ... | SOURCE | Conditional amount definition, p11a1:46 |

Logical-input counts: SOURCE=17, STANDING=0, RULED=0, EXCESS=0; remaining binders are typing data. The `p11Amount_pos` existence premise is not advertised as a proof of rank_compact: it is a distinct conditional order wrapper and only extracts the least candidate's positivity.

Expanded bundled fields (all SOURCE; TYPING parameters n/P/mu/g/gt/beta/M/rho/w/wt omitted from logical counts):

| Structure | Field | Source locator |
|---|---|---|
| `P11Patch` | `n_pos` | p11a1:17,120,150 |
| `P11Patch` | `nonempty` | p11a1:18,120,150 |
| `P11Patch` | `compact` | p11a1:18,120,150 |
| `P11Patch` | `openV` | p11a1:120,150 |
| `P11Patch` | `diameter_pos` | p11a1:120,150 |
| `P11Patch` | `v_pos` | p11a1:120,150 |
| `P11Patch` | `thick_sub` | p11a1:120,150 |
| `P11SublevelHyp` | `mu_pos` | p11a1:120 |
| `P11SublevelHyp` | `beta_pos` | p11a1:120 |
| `P11SublevelHyp` | `size_ge` | p11a1:120 |
| `P11SublevelHyp` | `g_smooth` | p11a1:120 |
| `P11SublevelHyp` | `gt_smooth` | p11a1:120 |
| `P11SublevelHyp` | `finite_type` | p11a1:122 (S1) |
| `P11SublevelHyp` | `size` | p11a1:123 (S2) |
| `P11SublevelHyp` | `close` | p11a1:124 (S3) |
| `P11DioHyp` | `m_pos` | p11a1:150 |
| `P11DioHyp` | `mu_pos` | p11a1:150 |
| `P11DioHyp` | `convention` | p11a1:150 |
| `P11DioHyp` | `beta_pos` | p11a1:150 |
| `P11DioHyp` | `size_ge` | p11a1:150 |
| `P11DioHyp` | `regular` | p11a1:150 |
| `P11DioHyp` | `perturbed_regular` | p11a1:155 |
| `P11DioHyp` | `amount` | p11a1:152 (D1) |
| `P11DioHyp` | `size` | p11a1:153 (D2) |
| `P11DioHyp` | `close` | p11a1:157 (D3) |

Bundle logical counts: SOURCE=25; EXCESS=0. P11Patch.K/V/v are typing data. Neither bundle includes the desired measure estimate, finite-type existence theorem, invariance, torus, selected solution or closure result. The source itself assumes S1/D1; these input fields do not prove those hypotheses.

## Verification receipts

All Lean/Lake invocations for this audit were sequential and used `LEAN_NUM_THREADS=1` and nice priority 5. No parallel agents or builds were started. Build used the required compile gate. Lint's ABI subprocess was run only after the other Lean checks completed.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw0 KAM.Planetary.WeakMeasure.Basic
[inp-gate] slot 1 acquired 08:06:21 for KAM.Planetary.WeakMeasure.Basic
Build completed successfully (9049 jobs).
exit 0
```

The job count is Lake's dependency accounting, not 9049 independently started Lean processes or a clean rebuild. No clean, update or cache-get command was used.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW0Audit.lean
exit 0
```

The scratch probe imports only Basic and prints axioms of all 27 public theorems. Exact output:

```text
'KAM.Planetary.p11euclid_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11sphere_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11ball_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11sphere_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11tuple_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11tuple_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dg_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.le_p11dg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dg_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11op_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.le_p11op' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11op_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dg_le_p11op' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11maxJet_set_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.le_p11maxJet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11maxJet_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11maxJet_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_set_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_set_bddBelow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.le_index_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Index_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Index_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Amount_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.Basic
replaying KAM.Planetary.WeakMeasure.Basic
exit 0
```

One invocation replayed the package module (there is no provider module).

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (464 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only failing line is the explicitly permitted stale generated `KAM.lean` check. Module checks, frozen-anchor guard and all 144 ABI hashes pass. No generated file was regenerated.

Static checks: `git diff inp...HEAD --check` exits 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0 with empty output. Basic has 285 physical lines, the copyright/module/public imports/module docstring/exposed public section, and no forbidden proof escape, resource override, EuclideanSpace use or new instance. Recursive project import inspection reports no provider/frozen module. All 24 complete definition/structure declarations match the signature text modulo comments/whitespace; no binder, field, constant, carrier, formula or Boolean selector changes were found.

## Errata, deviations and closeout

No new suspected defect in a pinned paper, frozen declaration or mathematical blueprint was found in this W0 scope. W0-01 is an implementation omission relative to the accepted source/design, not source errata. The handoff's “Uncertainties / errata / deviations: none” should not obscure its separately acknowledged, still-open attainment omission. No repair was applied.

The gauge maxima and conditional order facts are proved; the source minimum/N3 gate is not complete. No P-FIXED or other frozen theorem closure is certified. Only this report persists from the audit; disposable probes/logs were deleted after their output was incorporated.
