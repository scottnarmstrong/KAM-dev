# W1-CUBIC independent audit 2 — tight delta

Date: 2026-10-30. Worktree: `/root/code/KAM-inp-wph`, branch `inp-wph`.

## Verdict and scope

**PASS WITH NOTES for the round-2 delta. F1 CLOSED; F2 CLOSED.** The missing symmetric continuous
four-linear form, defining pairing identity and exact C_* bound are now supplied. The two-sided
selection map has additivity, complex homogeneity and symmetry in all three arguments on the source domain.
The generic additivity API retains explicit summability premises; an auditor probe discharged these
from the existing selection estimate in every slot, without any additional source premise.

This is acceptance of these two repairs and the changed lines only. It does not re-audit the rest of
W1-CUBIC, certify the entire W1 subsection, or promote any frozen theorem. No provider or seal is supplied;
provider/frozen-type and seal-body checks are N/A. W-NLW2 remains outside this audit's closure claim.
Round-1 notes N1–N4 remain in force, without revalidation; N5 is fixed by the sole CubicDeriv docstring change.
The unexported general weighted-space Riesz-gradient remark remains outside the accepted repair scope.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external `inp-audit-package.md` brief,
round-1 report, handoff including its AUDIT FOCUS and Round 2 section, and the two relevant blueprint clauses.
Method: tier-2 correspondence audit, complete inspection of the changed Lean lines, separate adversarial
refutation pass on F1/F2, source-premise probes, then hygiene. Existing dependencies are accepted at the
round-1 boundary; only their specific interfaces used by the repairs were consulted.

Permission/decision record: the user specifies report-only work at this exact worktree path, ephemeral
probes under `.lake/abi-scratch/`, narrow checks, one Lean/Lake/checker invocation at a time and
`LEAN_NUM_THREADS=1`. These instructions override the generic brief's main-worktree output location.
The already regenerated root delta is authorized. No source, frozen file, manifest, root or git state was
changed by the auditor. No delegation or network access was needed.

## Frozen inputs

Snapshot R2: `7807261a1a352b711f6c4f2723247a57a6027e3c`.
Round-1 baseline: `448ac3f5f1ba4fd585668b8c0611229ac1f467b3`.
Current comparison ref `inp`: `434ba8f0d0cc3eb3f577db412edfa56aa017f6d1`.
Merge base for `git diff inp...HEAD`: `eb722cbc51ba0a6d84e3c8567fcba010df8eb6ab`.
The initial worktree was clean. The full `inp...HEAD` file inventory was compared with the round-1
boundary, then detailed review was restricted to `git diff 448ac3f5 HEAD -- KAM/Wave/Cubic`:
three new modules (554 lines) and one changed docstring line. The authorized generated root adds exactly
these three imports. No unchanged cubic proof was re-audited.

SHA256 manifest (all line locators below refer to snapshot R2):

| File | SHA256 |
|---|---|
| `KAM/Wave/Cubic/QPair.lean` | `d2a42d09f923b62653dec194e32b099e8caeec18ab8733772c0723a4735c9c17` |
| `KAM/Wave/Cubic/QSymm.lean` | `5b00fd18a51f951c72accccdb29202801388e7aaad4a289c4d3f91580f0c5e90` |
| `KAM/Wave/Cubic/SelectionTwoAlg.lean` | `c4fc263b9ac7d047dd3811e8df5cf72737111d5110ae7aa75391c45855aba419` |
| `KAM/Wave/Cubic/CubicDeriv.lean` | `0b18623193ac1f02d5090557ad1e731e7c4ebf2d20423a2631205f2c17a829a9` |
| `KAM/Root/Wave.lean` | `0982a5c58f56291a163b12c26bfffa99b9ed54b022307267e84796846e7f57e8` |
| `blueprint-W/parts/w1-sequences.tex` | `b27ab7134c188941198e547c4577e3263e0e5f618a41ebd6983ac48b8b07e796` |
| `docs/tracks/W/audits/W1-CUBIC-audit-1.md` | `fc33513f9db09b587f98ac45d604897a919b40b7a977499972923471bf765dd2` |
| `docs/tracks/W/audits/W1-CUBIC-handoff.md` | `2c8f1189b09f7fcfa5dfaea78674f2445381e82290436545e64e783d5634094f` |

## F1 — CLOSED: four-linear form, identity, symmetry, bound

Source: `blueprint-W/parts/w1-sequences.tex:526-527`, “symmetric continuous $4$-linear form”
with `Q(q1,q2,q3,q4) = <T(q1,q2,q3),q4>_0` and `|Q| ≤ C_* ∏ ‖qi‖`.

`QPair.lean:129` defines an actual `ContinuousMultilinearMap K (fun _ : Fin 4 => lp _ 2) K`.
It composes the already constructed trilinear map with a continuous bilinear unweighted pairing, then
uncurries the final slot. This proves multilinearity and continuity rather than taking them as premises.
`waveQuartForm_apply` at line 144 identifies the exact series, with three inputs decoded at `(a,p)`,
T's output decoded at `(a,p+1)`, and the fourth input decoded at `(a,p)`. There is no complex conjugation:
this is the source's bilinear pairing, and the RCLike version is a valid strengthening of the real claim.
The weighted lp realization is the existing isometric carrier representation, not a change of norm.

`wavePair_summable` and `wavePair_norm_le` prove absolute convergence and pairing norm ≤ 1 using
Cauchy–Schwarz and weights ≥ 1. Composition therefore gives `waveQuartForm_norm_le` and
`norm_waveQuartForm_le` with **exactly** `waveCubicConst p = K_(p+1/2)^2/π`. No extra factor or
mass/input dependence enters. The construction works for `a ≥ 0`, stronger than the source's `a > 0`;
the separate identification with integral G keeps `a > 0`.

Refutation pass: checked against the possibilities of only diagonal symmetry, only first-three-slot
symmetry, conditional Fubini, a sesquilinear pairing, or an incorrect weight in the last slot.
`QSymm.lean:51` proves absolute convergence of the full quadruple series from the real selection
estimate applied to coefficient/input moduli, then pairs the resulting weighted sequence with the
fourth input. `waveTri_pairing_eq_quad` legitimately groups this absolutely convergent sum.
The involution at lines 120–129 exchanges k and l using the actual coefficient symmetry, and
`waveQuartForm_swap34` supplies the previously missing last-slot exchange. `waveQuartForm_perm`
at line 147 combines all three adjacent transpositions via generation of `Perm (Fin 4)`; its
quantifier is every permutation, not a selected subgroup. No candidate defect survived.

The explicit equality `G(κy) = (1/4) Q(y,y,y,y)` is not separately named in the new modules.
An auditor probe **elaborated this exact equality** from `waveG_hasSum_pairing`, the existing
cubic/trilinear coordinate identification and `waveQuartForm_apply`. Thus the old diagonal identity
and the new form compose without a source gap; a dedicated wrapper would be optional API work.

## F2 — CLOSED: two-sided trilinearity and symmetry

Source: `blueprint-W/parts/w1-sequences.tex:411`, “In both cases $T_c$ is trilinear; it is symmetric
if $c$ is symmetric in its first three indices.”

`SelectionTwoAlg.lean:29` names precisely the existing guarded summand; line 33 is a reflexive
identity with the old sum. The three `waveSelSumZ_add_*` proofs use `Summable.tsum_add` and
pointwise distributivity. The three homogeneity proofs factor the scalar out of the infinite sum.
`waveSelTwo_*` transports these identities through the output guard: l=0 is proved directly,
and l≠0 uses the original sum. No convergence at output zero is assumed.

Refutation pass: attempted to retain round-1 F2 because the additivity exports are conditional.
For arbitrary source inputs w,v,w',w'', the scratch probe proved each of the three pointwise
`waveSelTwo_add_*` conclusions under only a≥0, p≥1/2, M≥0, the source coefficient bound and
`WaveTwoMem` membership of the four inputs. Each summability premise is discharged by
`((waveSel_twoSided ha hp hM hc ...).1 l hl).of_norm`. All three examples elaborate, including
l=0 through the implication guard. The premises are intermediate convergence facts with an
existing producer, not conclusion-shaped assumptions or unpaid source obligations. This is the
same acceptance criterion applied to the one-sided generic helpers in round 1.

The two generic adjacent-swap proofs reindex the guarded ℤ³ sum by genuine involutions,
correctly preserving all three nonzero guards. They use exactly the corresponding symmetry
of c and commutativity of multiplication. `waveSelTwo_swap_left_right` composes these swaps;
the adjacent transpositions generate all permutations of three arguments. A separately bundled
trilinear map or permutation theorem is not required for this source sentence. The swap helpers
state symmetry of the total ℤ-indexed extension of c; for source c on nonzero indices use its
zero extension. Coefficients at zero indices are never used by the guarded sum. No candidate
counterexample to source-domain trilinearity/symmetry survived.

API note retained: source-domain additivity is obtained by the demonstrated composition; the
production module does not export an additional wrapper that repeats all selection premises.

## Complete changed-declaration ledger

Names are in `KAM.Wave`. Every new public declaration is listed; 5 definitions, 14 lemmas,
25 theorems, 44 total. PASS for generic helpers denotes their stated conditional type;
source-domain discharge is established above.

| Node | Declaration | R2 locator | Verdict / reason |
|---|---|---|---|
| gradient-identity (i) | `norm_coeffW_le_norm` | `QPair.lean:31` | PASS; weights ≥ 1 give coordinate domination. |
| gradient-identity (i) | `wavePair_summable` | `QPair.lean:41` | PASS; absolute pairing convergence. |
| gradient-identity (i) | `wavePair` | `QPair.lean:53` | PASS; literal unweighted series. |
| gradient-identity (i) | `wavePair_norm_le` | `QPair.lean:57` | PASS; Cauchy–Schwarz, exact constant 1. |
| gradient-identity (i) | `wavePair_add_left` | `QPair.lean:76` | PASS; additivity with produced summability premises. |
| gradient-identity (i) | `wavePair_add_right` | `QPair.lean:84` | PASS; additivity with produced summability premises. |
| gradient-identity (i) | `wavePair_smul_left` | `QPair.lean:91` | PASS; homogeneity in this slot. |
| gradient-identity (i) | `wavePair_smul_right` | `QPair.lean:98` | PASS; homogeneity in this slot. |
| gradient-identity (i) | `wavePairCLM` | `QPair.lean:106` | PASS; actual continuous bilinear map. |
| gradient-identity (i) | `wavePairCLM_apply` | `QPair.lean:115` | PASS; literal evaluation. |
| gradient-identity (i) | `norm_wavePairCLM_le` | `QPair.lean:119` | PASS; operator norm ≤ 1. |
| gradient-identity (i) | `waveQuartForm` | `QPair.lean:129` | PASS; actual continuous 4-linear map on Fin 4. |
| gradient-identity (i) | `waveQuartForm_apply_vec` | `QPair.lean:135` | PASS; correct slot order and weight decoding. |
| gradient-identity (i) | `waveQuartForm_apply` | `QPair.lean:144` | PASS; exact defining pairing identity. |
| gradient-identity (i) | `waveQuartForm_norm_le` | `QPair.lean:154` | PASS; exact C_* operator bound. |
| gradient-identity (i) | `norm_waveQuartForm_le` | `QPair.lean:163` | PASS; exact C_* product bound. |
| gradient-identity (i) | `waveQuartic_comm34` | `QSymm.lean:32` | PASS; integral coefficient exchange. |
| gradient-identity (i) | `waveTriCoef_comm34` | `QSymm.lean:37` | PASS; normalized coefficient exchange. |
| gradient-identity (i) | `waveQuadTerm` | `QSymm.lean:43` | PASS; literal four-input summand. |
| gradient-identity (i) | `waveTri_quad_summable` | `QSymm.lean:51` | PASS; absolute quadruple convergence proved. |
| gradient-identity (i) | `waveTri_pairing_eq_quad` | `QSymm.lean:101` | PASS; justified grouping. |
| gradient-identity (i) | `waveTri_pairing_swap` | `QSymm.lean:114` | PASS; exchange of third and fourth inputs. |
| gradient-identity (i) | `waveQuartForm_swap34` | `QSymm.lean:131` | PASS; last-slot exchange of the actual form. |
| gradient-identity (i) | `waveQuartForm_vec4` | `QSymm.lean:139` | PASS; alternate evaluation interface. |
| gradient-identity (i) | `waveQuartForm_perm` | `QSymm.lean:147` | PASS; every permutation of Fin 4. |
| selection (b) algebra | `waveSelTermZ` | `SelectionTwoAlg.lean:29` | PASS; exact nonzero-input guard. |
| selection (b) algebra | `waveSelSumZ_eq_tsum` | `SelectionTwoAlg.lean:33` | PASS; definitional bridge. |
| selection (b) algebra | `waveSelSumZ_smul_left` | `SelectionTwoAlg.lean:38` | PASS; homogeneity in this slot. |
| selection (b) algebra | `waveSelSumZ_smul_mid` | `SelectionTwoAlg.lean:45` | PASS; homogeneity in this slot. |
| selection (b) algebra | `waveSelSumZ_smul_right` | `SelectionTwoAlg.lean:52` | PASS; homogeneity in this slot. |
| selection (b) algebra | `waveSelSumZ_add_left` | `SelectionTwoAlg.lean:59` | PASS; additivity with produced summability premises. |
| selection (b) algebra | `waveSelSumZ_add_mid` | `SelectionTwoAlg.lean:68` | PASS; additivity with produced summability premises. |
| selection (b) algebra | `waveSelSumZ_add_right` | `SelectionTwoAlg.lean:77` | PASS; additivity with produced summability premises. |
| selection (b) algebra | `waveSelSumZ_swap_left_mid` | `SelectionTwoAlg.lean:87` | PASS; coefficient symmetry and guarded reindexing. |
| selection (b) algebra | `waveSelSumZ_swap_mid_right` | `SelectionTwoAlg.lean:104` | PASS; coefficient symmetry and guarded reindexing. |
| selection (b) algebra | `waveSelTwo_smul_left` | `SelectionTwoAlg.lean:120` | PASS; homogeneity in this slot. |
| selection (b) algebra | `waveSelTwo_smul_mid` | `SelectionTwoAlg.lean:127` | PASS; homogeneity in this slot. |
| selection (b) algebra | `waveSelTwo_smul_right` | `SelectionTwoAlg.lean:134` | PASS; homogeneity in this slot. |
| selection (b) algebra | `waveSelTwo_add_left` | `SelectionTwoAlg.lean:141` | PASS; additivity with produced summability premises. |
| selection (b) algebra | `waveSelTwo_add_mid` | `SelectionTwoAlg.lean:151` | PASS; additivity with produced summability premises. |
| selection (b) algebra | `waveSelTwo_add_right` | `SelectionTwoAlg.lean:161` | PASS; additivity with produced summability premises. |
| selection (b) algebra | `waveSelTwo_swap_left_mid` | `SelectionTwoAlg.lean:171` | PASS; coefficient symmetry and guarded reindexing. |
| selection (b) algebra | `waveSelTwo_swap_mid_right` | `SelectionTwoAlg.lean:178` | PASS; coefficient symmetry and guarded reindexing. |
| selection (b) algebra | `waveSelTwo_swap_left_right` | `SelectionTwoAlg.lean:186` | PASS; coefficient symmetry and guarded reindexing. |

Additional changed line: `CubicDeriv.lean:17` removes the nonexistent
`waveCubicNL_hasFDerivAt_fderiv` reference and explicitly says “in directional form”. **N5 CLOSED**;
this makes no change to any declaration or to the retained N1 API distinction.

## Definition classification and binder check

| New definition | Whole-carrier classification |
|---|---|
| `wavePair` | Literal tsum of the unweighted products. Absolute convergence and bilinearity proved on the admissible a,p domain; no theorem relies on a totalized divergent sum outside that domain. |
| `wavePairCLM` | Continuous bilinear realization of that sum, with bound supplied during construction. |
| `waveQuartForm` | Uncurrying of pairing composed with the genuine trilinear map, for every lp input tuple. |
| `waveQuadTerm` | Literal coefficient times four input values, indexed (l,(i,j,k)); no fallback. |
| `waveSelTermZ` | Literal source summand on nonzero input indices, zero otherwise, exactly matching the existing sum. |

F1 binders: K/RCLike, m, a,p, tuple/permutation/input indices are typing data; hm is standing m>0;
ha and hp are source domain hypotheses (ha strengthened to allow zero); IsEll hypotheses are input
membership. No derivative, symmetry, continuity or convergence conclusion is assumed.
F2 binders: c and complex sequences/scalars/indices are typing data; coefficient-symmetry hypotheses
are precisely the algebraic source condition (on the chosen total extension); Summable hypotheses
are generic helper preconditions discharged from the old selection theorem on the source carrier.
There is no new instance or structure bundling an unpaid analytic conclusion.

## Verification evidence

All Lean-bearing checks below were sequential, with `LEAN_NUM_THREADS=1` and nice priority 5.
Other sessions on the host are outside this audit's process ownership. The build was first checked
with `--no-build` and all targets were current, so the warm targeted build scheduled no compilation
fan-out. No clean rebuild, package mutation or heartbeat/depth override was used.

1. Targeted gated build, exit **0**:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wph KAM.Wave.Cubic.QPair KAM.Wave.Cubic.QSymm KAM.Wave.Cubic.SelectionTwoAlg
```

Final output: `Build completed successfully (3308 jobs).`
Preflight with the same gate and `--no-build` exited 0: `All targets up-to-date (3308 jobs).`
Replayed warnings are deprecations and unused simp arguments, not errors.
An initial attempt to pass `-j1` exited 1 (`error: unknown short option '-j'`) before doing any work;
this toolchain has no such option. It was removed; the preflight confirmed that no rebuild was needed.

2. One kernel replay invocation, exit **0**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.Cubic.QPair KAM.Wave.Cubic.QSymm KAM.Wave.Cubic.SelectionTwoAlg
```

Complete output:

```text
replaying KAM.Wave.Cubic.SelectionTwoAlg
replaying KAM.Wave.Cubic.QSymm
replaying KAM.Wave.Cubic.QPair
```

3. Exhaustive axiom census and source-premise probes, exit **0**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/MaudWph2.lean
```

The probe imports QSymm and SelectionTwoAlg and runs `#print axioms KAM.Wave.<name>` for
all 44 names in the ledger, including definitions. Exactly 44 output lines, all in this format:

```text
'KAM.Wave.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No sorryAx or other axiom appears. The same invocation proves all three source-domain additivity
examples, checks the actual Fin 4 continuous-multilinear carrier, and proves the G/Q diagonal identity.
Initial scratch-only attempts needed `noncomputable section` on the data-valued example and an explicit
`(K := ℝ)` on Q in the diagonal example; after those probe corrections the complete file exits 0.
No production change was needed. The mathematical portion of the successful probe is reproduced below
(the 44 census commands are determined by the exhaustive ledger):

```lean
import KAM.Wave.Cubic.QSymm
import KAM.Wave.Cubic.SelectionTwoAlg
open KAM.Wave
noncomputable section

section SourceTwo
variable {a p M : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (hM : 0 ≤ M)
variable {c : ℤ → ℤ → ℤ → ℤ → ℂ}
variable (hc : ∀ i j k l : ℤ, i ≠ 0 → j ≠ 0 → k ≠ 0 → l ≠ 0 → ‖c i j k l‖ ≤
  M * ((|(i : ℝ)| * |(j : ℝ)| * |(k : ℝ)| * |(l : ℝ)|) ^ (-(1 / 2 : ℝ))) *
  waveSelCountZ l i j k)
variable {w v w' w'' : ℤ → ℂ} (hw : WaveTwoMem a p w) (hv : WaveTwoMem a p v)
variable (hw' : WaveTwoMem a p w') (hw'' : WaveTwoMem a p w'')
example (l : ℤ) : waveSelTwo c (fun j => w j + v j) w' w'' l = waveSelTwo c w w' w'' l + waveSelTwo c v w' w'' l := by
  apply waveSelTwo_add_left c w v w' w'' l
  · intro hl
    exact ((waveSel_twoSided ha hp hM hc hw hw' hw'').1 l hl).of_norm
  · intro hl
    exact ((waveSel_twoSided ha hp hM hc hv hw' hw'').1 l hl).of_norm
example (l : ℤ) : waveSelTwo c w (fun j => w' j + v j) w'' l = waveSelTwo c w w' w'' l + waveSelTwo c w v w'' l := by
  apply waveSelTwo_add_mid c w w' v w'' l
  · intro hl
    exact ((waveSel_twoSided ha hp hM hc hw hw' hw'').1 l hl).of_norm
  · intro hl
    exact ((waveSel_twoSided ha hp hM hc hw hv hw'').1 l hl).of_norm
example (l : ℤ) : waveSelTwo c w w' (fun j => w'' j + v j) l = waveSelTwo c w w' w'' l + waveSelTwo c w w' v l := by
  apply waveSelTwo_add_right c w w' w'' v l
  · intro hl
    exact ((waveSel_twoSided ha hp hM hc hw hw' hw'').1 l hl).of_norm
  · intro hl
    exact ((waveSel_twoSided ha hp hM hc hw hw' hv).1 l hl).of_norm
end SourceTwo

example {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m) {a p : ℝ}
    (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) :
    ContinuousMultilinearMap K (fun _ : Fin 4 => lp (fun _ : ℕ+ => K) 2) K :=
  waveQuartForm (K := K) m hm ha hp

example (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 < a) (hp : 1 / 2 ≤ p)
    (y : lp (fun _ : ℕ+ => ℝ) 2) :
    waveG m hm (coeffW a p y) = (1 / 4) * waveQuartForm (K := ℝ) m hm ha.le hp ![y,y,y,y] := by
  rw [waveQuartForm_apply]
  have h := waveG_hasSum_pairing m hm ha
    ((waveEll_iff_isEll a p _).2 (isEll_coeffW a p y))
  rw [← h.tsum_eq, ← tsum_mul_left]
  congr 1
  ext l
  have hN := waveCubic_coeffW_eq_coeffW_triML m hm (a := a) (p := p) hp ha y
  rw [hN, coeffW_waveTriML m hm ha.le hp]
  ring
```

4. Slim-worktree lint wrapper, exit **0**:

```sh
LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wph
```

This invokes `nice -n 5 sh scripts/lint_sources.sh` with the prescribed build overlay, including
the frozen ABI check. Complete output:

```text
check_lean_modules: PASS (1729 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

No stale-root exception was needed. Source escapes, module headers, line/file limits, generated roots,
errata rendering, frozen-file guard and ABI hashes all pass. New-file lengths: QPair 173,
QSymm 187, SelectionTwoAlg 194; changed CubicDeriv 126. All three new modules use the required
module/public-import/docstring/exposed-public-section form. No forbidden token or resource override
occurs in the changed modules.

5. Read-only diff checks, exit **0**, empty output:

```sh
git diff --check inp...HEAD
git diff --check 448ac3f5 HEAD -- KAM/Wave/Cubic
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

`KAM/Root/Wave.lean` has only the three authorized generated imports; source lint confirms root
consistency. Starting/final commit and all frozen snapshot hashes were checked again unchanged.
The final tracked-source status contains only this new report. Auditor-owned scratch probe/log files
were removed after recording their evidence; the report reproduces the successful probe.

## Errata, deviations, and closeout

No new suspected source/blueprint erratum, false theorem, constant discrepancy, unsupported premise,
or carrier defect was found within this delta. No implementation deviation was introduced.
The two inherited findings are closed against their original criteria; no reportable candidate or
UNREFUTED-TENTATIVE item remains for these repairs.

Closeout: 44/44 new declarations classified and axiom-checked; 5/5 definitions inspected; complete
changed proof lines reviewed; exact C_* and pairing checked; full four-slot symmetry checked;
all three source-domain additivity bridges and G/Q diagonal identity elaborated; targeted build,
three-module kernel replay and prescribed source lint passed. No provider/anchor closure is claimed.
Unchanged N1–N4 and the wider package/source campaign retain their round-1 scope and status.
