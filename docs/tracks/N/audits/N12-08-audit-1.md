# N12-08 independent audit 1

Overall verdict: **PASS WITH NOTES**.
The two Slab modules implement the specified nonlinear slab estimate without an added source premise.
No frozen anchor is sealed by N12-08. The downstream frozen `averaging_mean` and `averaging_most`
remain **FROZEN_UNPROVED**; this package verdict does not certify either root.

## Scope and inputs

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-n1208`.
HEAD: `4225b26e0b5b4feced799f07fded18c59d5c794d`.
Read AGENTS, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`,
the local N12-08 handoff, track N statement (especially averaging), design row N12-08,
its signature appendix and proof plan, design audits 1 and 2, and Part 12's standing data and
rank/slab proof. Used the lean-statement-audit method, adapted to an infrastructure package.
No delegation, production edits, git mutations, or external-source theorem claims.

The user's exact report destination overrides the generic brief's main-worktree destination.
The handoff's explicit AUDIT FOCUS restricts this audit to:

- `KAM/Nekhoroshev/Averaging/Slab.lean`, 320 lines, SHA-256
  `31164c9d67029ad09386cb4a117f2183e82edadc3520d798efcc06a09515fa6c`.
- `KAM/Nekhoroshev/Averaging/SlabBox.lean`, 147 lines, SHA-256
  `33a74fe04fd657831054fe18a6cff6be4c25f5009bd885eb974f75a37a0fcc05`.

Read their imported Setting/Rank definitions and proof interfaces and the literal `avgQ` definition.
`Coefficients.lean` is byte-identical to branch `inp-n1204`; this report does not independently
re-audit the coefficient package. The handoff's SlabBox line count of 145 is stale; actual count 147
is harmless and under the cap.

`git diff inp...HEAD` was inspected. Current `inp` is
`f11c90357967f666b1673409df890dbcec823dff`; Git warns of multiple merge bases and chooses
`4dad814dc58f7f254a380a342178c120e2d69be9`. This diff has six added averaging files:
Coefficients, Field, Rank, Setting, Slab, SlabBox. The protected-path diff is empty.
Also inspected `git diff inp-n1207...HEAD`; that reference currently resolves to
`16195236f679eadbbb6c56c97fdbd9b27f742956` and its full diff includes unrelated integrated work.
Restricting that comparison to the Slab files gives the two new modules; Rank and Setting have no delta.
The package implementation commits are `179eec3` (SlabBox) and `4225b26` (Slab).
The pre-existing untracked handoff was preserved.

## Declaration and node ledger

Names below are relative to `KAM.Nekhoroshev`. Source locators are in
`blueprint-N/parts/p12-averaging.tex` unless otherwise stated.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| sl-box, L154; SlabBox:31 | `AvgSlab.section_dist_le` | PASS | MVT on the full coordinate interval in the closed max-norm cube; derivative modulus suffices. No sign assumption needed. |
| sl-box, L154; SlabBox:71 | `AvgSlab.volume_box_le` | PASS | Genuine Lebesgue box volume; measurable coordinate splitting, section diameter, then Fubini. Arbitrary real v and r=0 are valid strengthenings. |
| slab notation, L150; Slab:37 | `AvgSlab.lineFun` | PASS | Literal real dot product with the frozen frequency map. |
| slab gradient, L150; Slab:41 | `AvgSlab.gradFun` | PASS | Column j of M paired with e, hence `(Mᵀ e)ⱼ`. |
| standing collar, L18–23; Slab:44 | `AvgSlab.closedBall_subset_domain` | PASS | 7R/8 collar lies inside the genuine real analytic domain. |
| sl-cover, L152; Slab:52 | `AvgSlab.unif_M` | PASS | Uniform entrywise continuity of M on the compact collar; r is chosen before I,I′,i,j and before any direction. |
| gradient identity, L150; Slab:85 | `AvgSlab.hasDerivAt_line` | PASS | Chain rule along coordinate update supplies the actual derivative, with the correct transposition. |
| large coordinate, L152; Slab:105 | `AvgSlab.exists_coord` | PASS | Finite averaging of squares; N>0 is typing/nonempty-dimension data, no assumed transversality. |
| sl-cover/sl-box/sl-sum; Slab:117 | `AvgSlab.slab_freq` | PASS | Constructs one C₁≥1 before every Euclidean unit direction and positive v. |
| slab L144–148, sl-k L158; Slab:264 | `slab` | PASS | Exact design and signature-file statement; same C₁ for direction and integer estimates, denominator is Euclidean length. |
| design numerical specification; Slab:308 | `AvgSlabBound` | PASS | Exact intended bound, derived rather than assumed in the source result. |
| convenience projection; Slab:314 | `exists_avgSlabBound` | PASS | Constructs the numerical specification from `slab d` under a distinct name. |

Both `slab`'s telescope/conclusion and `AvgSlabBound`'s entire body were compared mechanically
against `/root/code/KAM-inp/.drafts/design/N12Signatures.lean` and the local design appendix:
all exact textual comparisons returned True. There is no provider export in this package,
so provider-versus-frozen and seal-body probes are **not applicable**. Importing draft anchors
merely to simulate a provider audit would not establish any package obligation.

## Premises and constant scope

The source result has only `d : AveragingData n R s h f`. Its implicit n,R,s,h,f are typing/fixed
system data. Recursively expanded logical inputs are:

| Expanded binder / field | Bin | Authority / meaning |
|---|---|---|
| `d.hn : 1 ≤ n` | STANDING | Part 12 L18: n≥1; valid strengthening of frozen n≥2. |
| `d.hR : 0 < R` | STANDING | Part 12 L18. |
| `d.hs : 0 < s` | STANDING | Part 12 L18. |
| `d.hh.1` complex differentiability | STANDING | Literal frozen `IsAnalyticIntegrable`; source analytic standing data. |
| `d.hh.2.1` boundary continuity | STANDING | Same frozen predicate. |
| `d.hh.2.2.1` existential finite nonnegative bound for h | STANDING | Same predicate; not a chosen numerical estimate for this result. |
| `d.hh.2.2.2.1` real-valued restriction | STANDING | Same predicate. |
| `d.hh.2.2.2.2` real C³ restriction | STANDING | Same predicate; gives continuity of Dω. |
| `d.hf.1` nonnegative size one | STANDING | Literal frozen `IsAnalyticPerturbation R s 1 f`. |
| `d.hf.2.1` complex differentiability | STANDING | Same predicate. |
| `d.hf.2.2.1` boundary continuity | STANDING | Same predicate. |
| `d.hf.2.2.2.1` period-one periodicity | STANDING | Same predicate. |
| `d.hf.2.2.2.2.1` real-valued restriction | STANDING | Same predicate. |
| `d.hf.2.2.2.2.2` pointwise size-one bound | STANDING | Same predicate. |
| `d.hrank` global alternative | STANDING | Part 12 L18 and frozen rank predicate: everywhere-surjective Dω OR everywhere-nonzero ω and surjective `(v,c)↦Dωv+cω`. |

For this expanded logical-input table: SOURCE=0, STANDING=15, TYPING=0, RULED=0, EXCESS=0.
Fixed parameters n,R,s,h,f are five TYPING entries, separate from the 15 logical inputs.
The rank disjunction retains both global alternatives; it is not replaced with an arbitrary
pointwise branch or a globally nonzero frequency component. Its quantified membership and
surjectivity are precisely the literal rank predicate, not hidden slab conclusions.

Auxiliary lemmas are explicitly local/generic proof steps. Their extra arguments are not source
premises of `slab`; the slab proof supplies them. Each logical input is classified here:

| Lemma | Input binder | Bin | Source / construction |
|---|---|---|---|
| `section_dist_le` | hr | SOURCE | Nonnegative cube radius for sl-box. |
| same | hφd | SOURCE | Coordinate derivative on the cube, sl-box L154. |
| same | hg | SOURCE | Lower derivative modulus on the cube, sl-box L154. |
| same | hP₁ | SOURCE | First endpoint in cube. |
| same | hP₂ | SOURCE | Second endpoint in cube. |
| same | hv₁ | SOURCE | First endpoint in slab. |
| same | hv₂ | SOURCE | Second endpoint in slab. |
| same | hlt | SOURCE | Ordered distinct section points. |
| `volume_box_le` | hr | SOURCE | Cube radius. |
| same | hc₁ | SOURCE | Positive lower derivative bound. |
| same | hφc | SOURCE | Continuity from source C¹ function, constructed at Slab:212–214. |
| same | hφd | SOURCE | Actual coordinate derivative, supplied by `hasDerivAt_line`. |
| same | hg | SOURCE | Proved on entire cube at Slab:184–209. |
| `closedBall_subset_domain` | d | STANDING | Expanded above. |
| `unif_M` | d | STANDING | Expanded above. |
| same | hθ | SOURCE | Positive continuity tolerance. |
| `hasDerivAt_line` | d | STANDING | Expanded above. |
| same | hI | SOURCE | Analytic-domain guard. |
| `exists_coord` | hN | TYPING | Nonempty finite coordinate set. |
| same | hT | SOURCE | Square-sum bound; derived from lambda and slab membership at Slab:170–171. |
| `slab_freq` | d | STANDING | Expanded above. |
| `slab` | d | STANDING | Expanded above. |
| `exists_avgSlabBound` | d | STANDING | Expanded above. |

All remaining implicit/explicit auxiliary parameters (m,N,φ,g,j,c,r,c₁,v,P,t₁,t₂,θ,I,e,a,T
and the fixed system parameters) are TYPING. No instance binder encodes a mathematical result;
finite-coordinate and real/complex scalar instances are canonical library infrastructure.
No EXCESS or RULED premise occurs.

Witness scope is correct: r and the finite covering centers are chosen before e or v.
For a cube meeting the thin slab, the selected coordinate j may depend on e and a point of
intersection; the radius, cover cardinality and derivative threshold do not. With
`cc=λ/(4√n)`, the witness is
`C₁=max 1 (max (#t*(2r)^(n-1)*(2/cc)) (2*Vol(G)/λ))`.
It precedes e,v,k,u. This is an existential bound; no equality to the blueprint's particular
`max(1,2p/c₀,2Vol(G)/λ)` was specified. Retaining the cube side factor permits side lengths
above one without weakening the result. The formal statement uses the exact approved fixed-system
telescope; the construction uses frequency/rank data, not ε, a mode, or a direction.

## Definition classification

All three new definitions are literal formulas, exposed on their entire declared carriers:

| Definition | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | Verdict |
|---|---|---|---|---|---|---|
| `AvgSlab.lineFun` | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `AvgSlab.gradFun` | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `AvgSlabBound` | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

There are no new structures, abbrevs, chosen public objects, fallback branches or global instances.
The total derivative in gradFun is exactly the existing avgM formula; the derivative theorem is
guarded by the analytic domain. `AvgSlabBound` describes a numerical estimate for arbitrary h,R,C₁;
its name does not assert this predicate always holds. `exists_avgSlabBound` proves existence on
the intended source inputs. It is not a field of AveragingData or an assumed bound in `slab`.
The k≠0 guard ensures no total-division artifact enters the integer-mode assertion.

## Independent proof reconstruction

1. The C² frequency map makes Dω continuous. Compactness of the max-norm ball of radius 7R/8
   yields an entrywise modulus at tolerance cc/n; r is positive and at most R/8.
   Finitely many radius-r open balls centered in G cover G. Their closed cubes stay in that collar.
2. If such a cube meets the slab with v≤λ/2, rank transversality at an intersection point gives
   `|Mᵀe|₂²≥3λ²/4`. A coordinate has square at least `3λ²/(4n)`, hence modulus at least 2cc.
   The sum of n entrywise errors times |eᵢ|≤1 is at most cc. Thus the same coordinate derivative
   has modulus at least cc everywhere in the closed cube, including all segments used by MVT.
3. SlabBox explicitly proves the updated coordinate interval remains in the cube. It applies
   `exists_hasDerivAt_eq_slope` with endpoint continuity and interior derivatives, then absolute
   values give `cc*(t₂-t₁)≤2v`. This argument does not need a separately supplied constant sign.
4. The set is closed relative to a closed cube, hence measurable. `piFinSuccAbove` and its inverse
   preserve Lebesgue volume. Fubini/Tonelli writes volume as the integral of one-dimensional
   section volumes. Every section has diameter ≤2v/cc; sections outside the projected cube are
   empty. The projected cube has volume `(2r)^(n-1)`. No unstated Jacobian or normalization occurs.
5. Finite subadditivity sums these estimates. For v>λ/2 the total volume
   `Vol(G)=(3R/2)^n` gives the other term of C₁. All ENNReal conversions have nonnegativity guards.
6. For a nonzero integer mode, K=|k|₂ is proved strictly positive, e=k/K is Euclidean-unit,
   and the two slab sets are proved equal with threshold u/K. Substitution gives C₁u/|k|₂.

No failed inequality, source contradiction, conclusion-shaped hypothesis, or missing Fubini/MVT
premise was found in these steps.

## Hygiene and fresh verification

All commands ran in `/root/code/KAM-inp-n1208`. Final verification was serialized with
`LEAN_NUM_THREADS=1` and `nice -n 5`.

Targeted build:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1208 KAM.Nekhoroshev.Averaging.Slab
[inp-gate] slot 2 acquired 08:39:50 for KAM.Nekhoroshev.Averaging.Slab
Build completed successfully (3188 jobs).
exit 0
```

Exact-type / defining-equation / axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1208Audit.lean
exit 0; no warnings or errors
```

The probe imported only Slab. It copied `slab`'s exact signature from N12Signatures under
`audit_slab`, with body `by exact slab d`, then checked
`example : type_of% @slab := @audit_slab`. It also proved by rfl that `AvgSlabBound` equals
its complete signature-file numerical formula. It ran `#print axioms` on every new public
theorem; exact output:

```text
'KAM.Nekhoroshev.AvgSlab.section_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.volume_box_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.closedBall_subset_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.unif_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.hasDerivAt_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.exists_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.slab_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.slab' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.exists_avgSlabBound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation covering both modules:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Slab KAM.Nekhoroshev.Averaging.SlabBox
replaying KAM.Nekhoroshev.Averaging.SlabBox
replaying KAM.Nekhoroshev.Averaging.Slab
exit 0
```

Lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (484 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The exit-1 cause is exactly the stale generated root explicitly permitted by the audit brief.
No generated file was changed. Both files satisfy the module/header/docstring/public-section
conventions. Maximum line lengths are 99 (Slab) and 98 (SlabBox), respectively. No prohibited
tokens, resource overrides, EuclideanSpace, or files over 1500 lines occur in the audited files.

A recursive project-import walk is acyclic (53 local modules); its 18 imported frozen anchors
are all SEALED definitions. It contains no provider or frozen theorem, hence no DRAFT_SORRY import.
The two relevant downstream frozen theorem manifest entries remain DRAFT_SORRY and were read as
statements only, never imported into the proof probe.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
# no diff; Git emits the multiple-merge-base warning described above

git diff --check inp...HEAD
# no whitespace diagnostics; same merge-base warning; exit 0

git diff --no-index --check /dev/null docs/tracks/N/audits/N12-08-audit-1.md
# no whitespace diagnostics (exit 1 is normal for a nonempty added file)
```

Execution correction: the first lint command was launched without an explicit thread setting or
nice prefix. On inspecting that lint invokes Lean for ABI hashes, I stopped it and the waiting
build gate, then reran the final lint above before starting the final build. No audit-owned build
had acquired a slot during the initial lint. The final receipts above all use the requested settings;
the initial lint's incomplete output is not used as verification evidence.


## Notes, defects and scope limits

- **Integration note:** design dependency row N12-08 lists N12-07; the implemented public import
  also requires N12-04 Coefficients for avgQ (`Slab.lean:8`, definition in Coefficients:35).
  Record `Slab → Coefficients` alongside `Slab → Rank` and land the coefficient dependency first.
  This is a real omitted design edge, already disclosed in the handoff; the inspected import closure
  is acyclic and contains no provider or draft theorem. No code repair is needed for this audit.
- **Documented proof deviation:** blueprint L152 says “finitely many (Q_m,U_m,j_m) ... cover K₀”.
  The implementation instead covers G once, using uniform continuity in I and linearity in e;
  it chooses j when a box meets the slab. The independent reconstruction above verifies this
  equivalent argument. Blueprint L156's side≤1 simplification is replaced by retaining `(2r)^(n-1)`.
- The Slab:51 docstring says “a radius independent of everything else”. Literally r depends on
  the fixed system and tolerance θ; the theorem correctly quantifies that dependence. Interpret
  this prose as independence of the points and direction. This is a wording note, not a theorem defect.
- No new suspected pinned-source erratum or frozen-statement defect was found. The source theorem
  here is the project's own rank-to-volume lemma; no fresh audit of Nei76/AKN printed PDFs is claimed.
  The blueprint's constant-sign observation remains true; using only the modulus in MVT is valid.

Read-only limits: only this report is added. Temporary audit probes are removed after verification.
The frozen averaging roots remain DRAFT_SORRY. Provider equality/seal checks are N/A for N12-08,
and this report makes no claim about future shell/envelope consumers or campaign closure.

Closeout: all required package checks completed; **PASS WITH NOTES** for N12-08.
