# Independent P11A-W0 package audit 2

Overall verdict: **PASS WITH NOTES** for W0 infrastructure. **W0-01 RESOLVED.** Joint continuity, the nonempty compact parameter domain, and an actual minimizing coefficient/basepoint pair are proved. The retained N3 extremum gate is satisfied within W0's scope. No frozen anchor is supplied or sealed; provider/type/seal probes are N/A. The only hygiene exception is the brief's expressly permitted stale generated `KAM.lean` check.

## Scope and immutable snapshot

Read audit 1 first, the package brief `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, AGENTS.md, PLAN/DECISIONS, the round-2 handoff and `.drafts/handoff-P11A-W0b.md`, track-P statements, source blueprint, Revision-3 design and design audit history. Audited only `KAM/Planetary/WeakMeasure/*` (one module, Basic) and its import closure. The user's exact absolute report path overrides the generic brief's main-worktree destination.

- HEAD: `26ed7acbbe356c7f4d2e11d44fc1c8b5be9593b9`.
- Initial `inp`: `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`; merge base: `cba16d0704fe352828a08b2eff9cb691184b8208`.
- `git diff inp...HEAD --stat`: Basic 465 additions; audit-1 247 additions; handoff 28 additions (3 files, 740 additions). Only Basic is production Lean in scope.
- Basic SHA-256: `a5173358149f5b8563ac5d0b1b50ae20f470af61b3f2ca4bb0207cdf1e0f2015`.
- Design SHA-256: `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9`.
- Pinned signatures read from `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`: `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`.

Independent textual comparison against round-1 commit `6c02f4e8a576f18aaa489085df7e2af397c57728` confirms the entire module prefix through `end Amount` is byte-identical. The only code delta is the appended Joint section. All 24 public definitions/structures were independently compared in full against pinned signatures after comment/whitespace removal: PASS. Previous passing statements, proof bodies, structure fields and imports are unchanged. Project import closure is exactly `KAM.Nekhoroshev.Interfaces.Norms` → `KAM.Fourier.Derivative` plus Mathlib; no provider, frozen module or DRAFT_SORRY theorem is imported. No direct frozen-object comparison is applicable.

## W0-01 and retained N3: resolved

Authority remains design lines 38–41 and 873–875: “W0 must establish boundedness/attainment for each supremum/infimum on positive-dimensional unit spheres and nonempty compact patches”. Blueprint `p11a1-weak-measure.tex:42–46` defines an actual minimum and explains “A minimum of a continuous function on a nonempty compact set”. The implementation now supplies that justification without changing the source object.

1. Basic:291–326 proves the y-slice derivative is the joint derivative precomposed with the continuous linear inclusion `a ↦ (0,a)`. Translation by `(c,0)` and open-domain unique differentiability justify the iterated chain rule, including j=0. No global regularity outside V is assumed.
2. Basic:331–365 proves the literal scalar family is jointly C^mu in `(c,y)` and its j-th y-derivative evaluated on repeated a is continuous in `(c,y,a)` for j≤mu. It uses finite sums/products and the natural power rho; no extra derivative order is needed.
3. Basic:367–425 takes the maximum over the compact direction sphere, then the finite maximum over orders 0..mu. The finite induction explicitly provides boundedness and a nonempty order set. Mathlib `Topology/Order/Compact.lean:477–502` handles an empty direction sphere by continuity of the constant empty supremum; therefore the stronger n=0 continuity statement is sound, without interpreting it as a source direction maximum.
4. Basic:428–434 proves compactness and nonemptiness of coefficient sphere × K. Basic:437–461 restricts the established continuity to that set, obtains an actual minimum with `exists_isMinOn`, and uses `IsLeast.csInf_eq` on the exact value set in `index_def`.

The exported conclusion is literally

```lean
∃ c : P11Vec m, p11euclid c = 1 ∧ ∃ y ∈ K,
  index_def rho mu w K = p11maxJet mu (p11scalar rho w c) y
```

Its premises are only `1 ≤ m`, `IsOpen V`, `ContDiffOn ℝ mu w V`, `IsCompact K`, `K ⊆ V`, `K.Nonempty`. It is stronger than the requested source theorem: all natural rho and no n≥1 restriction. In particular it covers rho=1,2 on positive-dimensional source carriers. It assumes neither continuity of the maximum nor existence of a minimizer.

For boundedness: the direction and tuple gauge value sets are compact (163,187), finite order values are finite (216), and the index set is bounded below by zero (247). An independent elaborating scratch probe also derived compactness of the complete index value image from the exported joint continuity and compact-domain theorem; hence both upper and lower bounds are available on source compact patches. Attainment is supplied respectively by 181,204,225,437. This closes W0's portion of N3. N3's later selected-stage-data choice specifications belong to other packages and are not certified here.

## Declaration ledger

All names are in `KAM.Planetary`; line numbers refer to current Basic. Each declaration has an individual row, including private helpers. Existing rows were rechecked against the unchanged code and source contracts.

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
| index-def / N3 | `index_def` (51) | PASS | Formula unchanged; source minimum now characterized by `index_def_attained` (437). |
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

| N3 / gauge image | `p11dg_set_compact` (163, private) | PASS | Compact continuous image of direction sphere. |
| N3 / gauge image | `p11op_set_compact` (187, private) | PASS | Compact continuous image of tuple ball. |
| N3 / slice calculus | `p11slice_iteratedFDeriv` (291, private) | PASS | Translate by (c,0), compose with inr; open sets justify within-to-global derivatives. |
| index-def / literal family | `p11jointFamily` (328, private def) | PASS | Literal uncurrying of p11scalar; no choice or fallback. |
| N3 / joint smoothness | `p11joint_contDiffOn` (331, private) | PASS | Finite bilinear pairing followed by natural power, all rho. |
| N3 / derivative continuity | `p11joint_term_continuousOn` (345, private) | PASS | Joint derivative continuity through mu, evaluated on repeated (0,a). |
| N3 / compact maximum | `p11sphere_sSup_continuousOn` (367, private) | PASS | Mathlib compact-maximum theorem on parameter subtype; empty sphere handled as constant. |
| N3 / diagonal gauge continuity | `p11joint_dg_continuousOn` (375, private) | PASS | Identifies literal gauge set with compact sphere image. |
| N3 / finite maximum continuity | `p11sSup_range_continuousOn` (388, private) | PASS | Induction, singleton base and finite nonempty csSup_insert; no unbounded sup rule. |
| index-def / N3 | `p11maxJet_joint_continuousOn` (418) | PASS | Joint continuity on univ × V from source C^mu regularity and openness. |
| index-def / N3 | `index_def_params_isCompact` (428) | PASS | Product of coefficient sphere and compact patch. |
| index-def / N3 | `index_def_params_nonempty` (432) | PASS | Positive frequency dimension and nonempty patch supply witnesses. |
| index-def / N3 | `index_def_attained` (437) | PASS | Actual minimizing c,y for the unchanged infimum; closes W0-01. |

## Definition classification and whole-carrier check

All 25 definition/abbreviation/structure declarations (24 public, one private) were inspected.

- Literal carriers: P11Vec, P11CVec, P11Phase, P11Family, p11euclid. Pi max-norm instances remain intact; Euclidean lengths are explicit.
- Literal algebra/set/predicate/formula objects: p11dot, p11dotZ, p11dotC, p11thick, p11scalar, p11JetBound, p11eta, p11Csub, p11RNondegenerate, p11Good, and private p11jointFamily. The latter is just `p11scalar rho w p.1 p.2` on its entire carrier. BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS/CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS.
- Source input structures: P11Patch, P11SublevelHyp, P11DioHyp. Exact fields are unchanged and signature-matched; no conclusion-shaped field is added. BODY_MATCH=OK, PUBLIC_CARRIER=OK, DEFINITION_VERDICT=PASS.
- Extremum objects p11dg, p11op, p11maxJet: compact/finite value sets and attainment characterize their intended maxima on source carriers. The operator closed-ball gauge equals the source sphere gauge by multilinear homogeneity for positive dimension (and the unique tuple for j=0); a separately named sphere/ball equality theorem remains unexported, as in round 1. BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS=OK, CHARACTERIZATION=OK on source carriers, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS.
- index_def: unchanged literal infimum now characterized as the source attained minimum under source regularity/geometry. BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS=OK, CHARACTERIZATION=OK, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS. The round-1 CHARACTERIZATION failure is resolved.
- p11Index/p11Amount: conditional least-positive-order wrappers. BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS/CHARACTERIZATION=OK under candidate existence, CHOICE_INDEPENDENCE=OK by uniqueness of the least natural number, DEFINITION_VERDICT=PASS WITH NOTES. Existence remains the later rank_compact theorem's task.

Off-source cases remain explicit: n=0 gives an empty direction sphere; m=0 or K=∅ gives an empty index value set; no positive candidate gives natural infimum zero; rho outside {1,2} takes p11eta's squared branch. The new attainment theorem excludes the latter empty parameter cases through m≥1 and K.Nonempty, and its n=0 case correctly attains the totalized gauge function on a nonempty coefficient domain. No proof uses a default value to establish source positivity or a physical result. Noncompact p11thick is not asserted to equal a distance sublevel, nor are derivatives of nonsmooth total functions asserted to be smooth source jets.

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


Round-2 public logical binders, expanded and classified (all dimensions, sets, orders and functions are TYPING):

| Declaration | Logical inputs | Bin and source |
|---|---|---|
| p11maxJet_joint_continuousOn | IsOpen V; ContDiffOn ℝ mu w V | SOURCE; blueprint 42–46 |
| index_def_params_isCompact | IsCompact K | SOURCE; blueprint 44 |
| index_def_params_nonempty | 1≤m; K.Nonempty | SOURCE; blueprint 42,44 |
| index_def_attained | 1≤m; IsOpen V; ContDiffOn ℝ mu w V; IsCompact K; K⊆V; K.Nonempty | SOURCE; blueprint 42–46 |

Added public logical input occurrences: SOURCE=11, STANDING=0, RULED=0, EXCESS=0. No added project instance or bundled input. Private calculus/maximum lemmas are distinct intermediate helpers: their generic C^j/continuity/order premises are established at their actual call sites by the preceding proofs. No helper assumes the missing source minimum. In a P11DioHyp application, `regular.of_le` supplies C^mu from C^(mu+1); patch inclusion K⊆V follows from zero-distance membership in p11thick and `thick_sub`. No strengthened source premise is required.

## Independent verification receipts

All audit-owned Lean/Lake invocations were sequential, `LEAN_NUM_THREADS=1`, nice priority 5; no subagents. Build went through the required gate, whose script runs `nice -n 5 lake build`. No clean/update/cache fetch, generated-root regeneration, production edit or state-changing git command was used.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw0 KAM.Planetary.WeakMeasure.Basic
[inp-gate] slot 2 acquired 08:42:29 for KAM.Planetary.WeakMeasure.Basic
Build completed successfully (9049 jobs).
exit 0
```

Lake's job count includes cached dependency accounting; no full-library rebuild was requested.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW0Audit2.lean
exit 0
```

The probe imports Basic only; checks the exact attainment conclusion without hidden additional premises, derives compactness of the complete index value image, and prints all 31 public theorem axioms. Exact axiom output:

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
'KAM.Planetary.p11maxJet_joint_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_params_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_params_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.Basic
replaying KAM.Planetary.WeakMeasure.Basic
exit 0
```

One invocation replays the whole package module; no provider exists in this package.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (464 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

Lint has exactly the permitted stale-generated-root exception; all other checks pass. The generated file was left untouched. No timeout or default-heartbeat failure occurred in these independent checks.

Static verification: `git diff inp...HEAD --check` exits 0 with empty output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0 with empty output. Basic has 465 physical lines and the required copyright, module command, public imports, module docstring and exposed public section. No forbidden proof escape, resource override, new instance or EuclideanSpace use occurs in code. The 64-row ledger accounts for every declaration (24 public definitions/structures, one private definition, 31 public theorems and eight private theorems).

## Errata, deviations, limitations and closeout

No new suspected pinned-source, frozen-statement or blueprint defect was found. W0-01 was an implementation omission, now resolved; no source repair or deviation was introduced. The all-natural-rho and n=0 extensions are valid stronger internal statements and do not redefine the source conventions. The original handoff's “Not proved: attainment” paragraph is historical and superseded by its round-2 addendum and Basic:437; it no longer describes current code.

`rank_compact`, finite-type candidate existence, stability and the later sublevel/measure/physical theorem packages remain outside this audit. W0's conditional least-index helpers certify no such closure. No frozen anchor is seal-ready merely because this infrastructure passes.

Final HEAD and inp identities are unchanged from the initial snapshot, and Basic's SHA-256 is unchanged. Only this report persists from the audit; all audit-created scratch probes and logs were removed after incorporation. Final git status contains only `?? docs/tracks/P/audits/P11A-W0-audit-2.md`. Report fence, trailing-whitespace and declaration-count checks pass. **W0: PASS WITH NOTES; W0-01: RESOLVED; zero open blocking findings in scope.**
