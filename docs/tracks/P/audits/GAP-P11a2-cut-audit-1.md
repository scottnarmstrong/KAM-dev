# GAP-P11a2-cut independent audit 1

Overall verdict: **PASS WITH NOTES**, for the seven-node package under its explicit package rulings. No failing node, proof escape, dependency-output premise, or unauthorized source strengthening was found. The scalar exceptions do not establish the unrestricted vector-valued source statements. No frozen theorem is sealed by this package.

## Scope, authority, and immutable inputs

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-g11cut`. Only implementation audited: `KAM/Planetary/MaximalStep/CutoffNodes.lean` (346 lines). The only repository file created by this audit is this report. Temporary probes were confined to `.lake/abi-scratch/` and deleted. No commits, source repairs, generated-file regeneration, package updates, or external communications.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the named handoff including AUDIT FOCUS, and the seven complete NODE records and their cited blueprint ranges. Also read the specific package brief `/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-P11a2-cut.md` and controlling `GAP-PLAN-P2.md` sections 2 and 6. The user's exact report destination overrides the generic audit brief's main-worktree destination. Applied the statement-audit five-bin method and a focused manuscript-audit correspondence/refutation pass; the existing instructions supply the permission envelope without another approval request.

Snapshot:

```text
HEAD       885fd3c2eefc995f8e9f4d4491d267eb19a2ec95
inp        02f1bcd96b3681d37a276e77c2ec795dbece6ae4
merge-base 2232899efa0b453dde9f8bd246c46bd5f90b1d30
```

The full `git diff inp...HEAD` adds only `CutoffNodes.lean` (346 insertions). The handoff was already untracked on entry. Protected-path diff `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. All implementation/source locators below refer to this snapshot; the handoff and external briefs are pinned by hash below.

| Input | SHA-256 |
|---|---|
| `KAM/Planetary/MaximalStep/CutoffNodes.lean` | `70954a00b5f249cc9b39188dd13678f0fa29199013376812770dc8d19bb56a65` |
| `blueprint-P/parts/p11a2-cutoff-step.tex` | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |
| `docs/graph/P/DEPGRAPH.md` | `b38752f1f9a41c2fc77511b6b5d7cee3b4bc9af1c6a1d4bdf92a960dbaddbbaa` |
| Package handoff | `7e54ca98f3d1b65ce8a1e9872b01b5aeac34949a0f65ee6f9450abfb8e71c9ae` |
| External `GAP-PLAN-P2.md` | `330c51f0559a2f998a4809baa16bd59359119309d393372d9ebb9355e8381cea` |
| External `GAP-P11a2-cut.md` | `a8b43516fa2f9c4b5a459e2e72a718e662ba82cb1115bc1a4b95c7126f785b90` |

All seven theorem exports are **UNSIGNED**. None occurs in the supplied P11A/P11B signature files; the package-specific graph-gap scope supersedes the original package brief's generic signature boilerplate. No new provider or frozen anchor exists, so provider=frozen-type and seal-copy probes are N/A. The downstream P-FIXED anchor remains `by sorry`; no theorem-closure claim is made here.

## Per-node verdicts

Every declaration below is in `KAM.Planetary`. DG means `docs/graph/P/DEPGRAPH.md`; BP means the pinned `blueprint-P/parts/p11a2-cutoff-step.tex`.

| Node; graph record | Declaration; Lean lines | Verdict | Literal conclusion, hypotheses, quantifiers |
|---|---|---|---|
| `bpP:p11a:c2-conv#data`; DG 22514–22538 | `p11_c2_conv_data`; 35–42 | PASS WITH NOTES | BP 22: thickening membership iff, openness, and every centered polydisc inclusion. Existing Pi carriers give max norms; `modeSize` is the literal sum of absolute coordinates; derivatives use induced CLM/multilinear norms. Package plan export 1 explicitly makes the matrix max-row-sum identity optional. The theorem strengthens the source by allowing all n,t, including nonpositive t. No new norm instance. |
| `stepP:p11a:fc-tail`; DG 22764–22792 | `p11_fc_tail`; 47–113 | PASS WITH NOTES | BP 43–45, 59–60: correct unestimated lattice tail with strict T<modeSize and exponent −2πd modeSize. M is a uniform sup-bound, the established design representation of the source norm. Applied on each action/parameter slice. Scalar form explicitly permitted by the 02:30 package ruling and flagged in handoff; no vector closure. It drops n≥1, T≥0, d<r and openness hypotheses, hence is stronger on those axes. |
| `stepP:p11a:tc-a`; DG 23082–23110 | `p11_tc_a`; 124–150 | PASS WITH NOTES | BP 98, 108: both the sharp pointwise M+M‖η‖/s estimate and every coordinate derivative bound M/s; actual action derivative at zero. Scalar exception as ruled. Dropped r>0 and B openness do not weaken the result. |
| `stepP:p11a:tc-b`; DG 23112–23140 | `p11_tc_b`; 154–191 | PASS WITH NOTES | BP 98, 110: both inequalities with a=‖η‖, a<qs, 0<q<1. The 02:30 ruling explicitly removes the proof-local coefficient identity from the export requirement. Scalar exception as ruled. No series expansion is assumed. |
| `stepP:p11a:cu-coeff`; DG 23176–23203 | `p11_cu_coeff`; 214–265 | PASS | BP 114–115, 126: both coefficient families holomorphic for every Fourier index; both actual cutoff families are finite character sums and holomorphic/periodic on **all** ℂⁿ×B. No bound on R, loss restriction, or output of another node is assumed. This is stronger than the parent's assumptions. |
| `stepP:p11a:cu-a`; DG 23205–23233 | `p11_cu_a`; 271–282 | PASS | BP 114, 118, 128: all three uniform bounds, including each coordinate of R_*1, with identical constants and radii. Nonnegative eps encodes a norm bound and is explicitly retained as typing data. q is eliminated by internally using q=1/2. |
| `bpP:p11a:cutoff`; DG 23141–23174 | `p11_cutoff_node`; 297–342; `p11TrigPolyAdm` 288–293 | PASS WITH NOTES | BP 114–122: coefficient identities, affine decomposition, entire-angle polynomial/admissible clauses, all (a),(b),(c), and the loss addendum. R is scalar already in this source proposition. Additional loss premises are precisely the allowed 0<alpha≤1, T≥1, d=p11Loss n T alpha, d≤1; they occur only inside the addendum. d≤1 is allowed but not mathematically necessary: see note below. |

The seven-node slice is complete under these rulings. `cu-b` is outside the assigned seven; its bound is also consumed internally through `p11_cutoff` clause 3. No graph file/status was edited. Independent universal data may be grouped differently by Lean's implicit binders; there are no existential constants with wider dependencies, no reordered dependent witnesses, and no restricted complex-point domain. In `cu-coeff`, all k are quantified before the parameter holomorphy assertion; every j is covered in the derivative-family and component bounds. The addendum quantifies alpha after fixed cutoff data and conditions d on that alpha, as specified by the plan.

## Expanded binder ledger

Notation: TYPING includes scalar parameters, carriers and nonnegative norm-bound representation; STANDING includes n≥1. SOURCE citations refer to BP. `hF`/`hR` are expanded into joint differentiability and period-one assertions. `hb` is expanded into its full universal pointwise bound; it is a source boundedness assumption, not a derived cutoff estimate. No instance or hidden hypothesis structure remains. Rows follow the Lean header order; each value in a grouped Lean binder is listed separately. Counts refer to these expanded rows, excluding variables introduced only inside the conclusion.

### `p11_c2_conv_data`

| Expanded binder | Bin | Source/ruling |
|---|---|---|
| `n` | TYPING | 22 |
| `E` | TYPING | 22 |
| `t` | TYPING | 22 |

Counts: SOURCE 0, STANDING 0, TYPING 3, RULED 0, EXCESS 0.

### `p11_fc_tail`

| Expanded binder | Bin | Source/ruling |
|---|---|---|
| `n` | TYPING | 22, 43–45 |
| `r` | TYPING | 22, 43–45 |
| `s` | TYPING | 22, 43–45 |
| `T` | TYPING | 22, 43–45 |
| `d` | TYPING | 22, 43–45 |
| `M` | TYPING | 22, 43–45 |
| `hr: 0<r` | SOURCE | 43 |
| `hd: 0<d` | SOURCE | 45 |
| `B` | TYPING | 26; package plan export 2 |
| `F` | TYPING | 26; package plan export 2 |
| `hF.1: DifferentiableOn ℂ F/R on domain_def` | SOURCE | 26, 45 |
| `hF.2: ∀ j z∈domain_def, shift by e_j preserves F/R` | SOURCE | 26, 45 |
| `hM: 0≤M` | TYPING | 26, 45; nonnegative norm representation |
| `hb: ∀ z∈domain_def, ‖F/R z‖≤M/eps` | SOURCE | 26, 45 |
| `θ` | TYPING | 26, 59 |
| `η` | TYPING | 26, 59 |
| `b` | TYPING | 26, 59 |
| `hθ: θ∈T_(r−d)` | SOURCE | 59 |
| `hη: ‖η‖<s` | SOURCE | 26; package plan export 2 |
| `hbB: b∈B` | SOURCE | 26; package plan export 2 |

Counts: SOURCE 8, STANDING 0, TYPING 12, RULED 0, EXCESS 0.

### `p11_tc_a`

| Expanded binder | Bin | Source/ruling |
|---|---|---|
| `n` | TYPING | 22, 98 |
| `r` | TYPING | 22, 98 |
| `s` | TYPING | 22, 98 |
| `M` | TYPING | 22, 98 |
| `hs: 0<s` | SOURCE | 98 |
| `B` | TYPING | 98 |
| `F` | TYPING | 98 |
| `hF.1: DifferentiableOn ℂ F/R on domain_def` | SOURCE | 26, 98 |
| `hF.2: ∀ j z∈domain_def, shift by e_j preserves F/R` | SOURCE | 26, 98 |
| `hb: ∀ z∈domain_def, ‖F/R z‖≤M/eps` | SOURCE | 98 |

Counts: SOURCE 4, STANDING 0, TYPING 6, RULED 0, EXCESS 0.

### `p11_tc_b`

| Expanded binder | Bin | Source/ruling |
|---|---|---|
| `n` | TYPING | 22, 98–101 |
| `r` | TYPING | 22, 98–101 |
| `s` | TYPING | 22, 98–101 |
| `M` | TYPING | 22, 98–101 |
| `q` | TYPING | 22, 98–101 |
| `hs: 0<s` | SOURCE | 98 |
| `hq: 0<q` | SOURCE | 101 |
| `hq1: q<1` | SOURCE | 101 |
| `B` | TYPING | 98 |
| `F` | TYPING | 98 |
| `hF.1: DifferentiableOn ℂ F/R on domain_def` | SOURCE | 26, 98 |
| `hF.2: ∀ j z∈domain_def, shift by e_j preserves F/R` | SOURCE | 26, 98 |
| `hb: ∀ z∈domain_def, ‖F/R z‖≤M/eps` | SOURCE | 98 |
| `θ` | TYPING | 98, 110 |
| `η` | TYPING | 98, 110 |
| `b` | TYPING | 98, 110 |
| `hθ: θ∈T_r` | SOURCE | 98 |
| `hbB: b∈B` | SOURCE | 98 |
| `hη: ‖η‖<qs` | SOURCE | 110 |

Counts: SOURCE 9, STANDING 0, TYPING 10, RULED 0, EXCESS 0.

### `p11_cu_coeff`

| Expanded binder | Bin | Source/ruling |
|---|---|---|
| `n` | TYPING | 22, 114 |
| `r` | TYPING | 22, 114 |
| `s` | TYPING | 22, 114 |
| `T` | TYPING | 22, 114 |
| `hr: 0<r` | SOURCE | 114 |
| `hs: 0<s` | SOURCE | 114 |
| `B` | TYPING | 114 |
| `hB: IsOpen B` | SOURCE | 114 |
| `R` | TYPING | 114 |
| `hR.1: DifferentiableOn ℂ F/R on domain_def` | SOURCE | 26, 114 |
| `hR.2: ∀ j z∈domain_def, shift by e_j preserves F/R` | SOURCE | 26, 114 |

Counts: SOURCE 5, STANDING 0, TYPING 6, RULED 0, EXCESS 0.

### `p11_cu_a`

| Expanded binder | Bin | Source/ruling |
|---|---|---|
| `n` | TYPING | 22 |
| `hn: 1≤n` | STANDING | 22 |
| `r` | TYPING | 114 |
| `s` | TYPING | 114 |
| `T` | TYPING | 114 |
| `d` | TYPING | 114 |
| `eps` | TYPING | 114 |
| `hr: 0<r` | SOURCE | 114: r>d>0 |
| `hs: 0<s` | SOURCE | 114 |
| `hT: 0≤T` | SOURCE | 114 |
| `hd: 0<d` | SOURCE | 114 |
| `hdr: d<r` | SOURCE | 114 |
| `he: 0≤eps` | TYPING | 114: eps is a norm |
| `B` | TYPING | 114 |
| `hB: IsOpen B` | SOURCE | 114 |
| `R` | TYPING | 114 |
| `hR.1: DifferentiableOn ℂ F/R on domain_def` | SOURCE | 26, 114 |
| `hR.2: ∀ j z∈domain_def, shift by e_j preserves F/R` | SOURCE | 26, 114 |
| `hb: ∀ z∈domain_def, ‖F/R z‖≤M/eps` | SOURCE | 114 |

Counts: SOURCE 9, STANDING 1, TYPING 9, RULED 0, EXCESS 0.

### `p11_cutoff_node`

| Expanded binder | Bin | Source/ruling |
|---|---|---|
| `n` | TYPING | 22 |
| `hn: 1≤n` | STANDING | 22 |
| `r` | TYPING | 114 |
| `s` | TYPING | 114 |
| `T` | TYPING | 114 |
| `d` | TYPING | 114 |
| `eps` | TYPING | 114 |
| `q` | TYPING | 114 |
| `hr: 0<r` | SOURCE | 114: r>d>0 |
| `hs: 0<s` | SOURCE | 114 |
| `hT: 0≤T` | SOURCE | 114 |
| `hd: 0<d` | SOURCE | 114 |
| `hdr: d<r` | SOURCE | 114 |
| `he: 0≤eps` | TYPING | 114: eps is a norm |
| `hq: 0<q` | SOURCE | 114 |
| `hq1: q<1` | SOURCE | 114 |
| `B` | TYPING | 114 |
| `hB: IsOpen B` | SOURCE | 114 |
| `R` | TYPING | 114 |
| `hR.1: DifferentiableOn ℂ F/R on domain_def` | SOURCE | 26, 114 |
| `hR.2: ∀ j z∈domain_def, shift by e_j preserves F/R` | SOURCE | 26, 114 |
| `hb: ∀ z∈domain_def, ‖F/R z‖≤M/eps` | SOURCE | 114 |

Counts: SOURCE 11, STANDING 1, TYPING 10, RULED 0, EXCESS 0.

The cutoff addendum's additional conditional inputs are audited separately because they are inside the conclusion:

| Input in order | Bin | Source/ruling |
|---|---|---|
| `alpha : ℝ` | TYPING | BP 71–73, 122 |
| `0<alpha` | SOURCE | BP 71; explicitly permitted in handoff |
| `alpha≤1` | SOURCE | BP 71; explicitly permitted in handoff |
| `1≤T` | RULED | 02:30 package ruling; BP 71 |
| `d=p11Loss n T alpha` | SOURCE | BP 72, 122; named loss choice |
| `d≤1` | RULED | 02:30 package ruling; BP 73 |

Counts for this conditional: SOURCE 3, STANDING 0, TYPING 1, RULED 2, EXCESS 0. `p11Real ... R` is the source conditional input to clause (c), BP 120; its body quantifies all real points in the source domain and requires imaginary part zero. It is not a premise for the other conclusions.

## Definition classification and proof review

The only new definition, `p11TrigPolyAdm`, is a **literal conjunction of two source predicates**: a finite Fourier polynomial supported at modeSize≤T, and holomorphy/periodicity on ℂⁿ×B. It contains no analytic estimate, dependence gate, choice of a constructed function, or hidden proof conclusion. The existential coefficient family is a witness to a polynomial representation, not a nonunique construction defining R_*; the actual function P remains an input. Coefficients outside B are irrelevant to this domain predicate. The explicit zero support condition removes the extra modes in `hmModes n T`, whose integer ceiling may otherwise include indices above the real threshold. For T<0 the support condition forces every coefficient zero, as the source truncation does. Empty B has the expected vacuous predicate. Finite-character orthogonality identifies this representation with P=cut_T P on B; the actual exported witnesses are the explicit Fourier coefficients, and `cu-coeff` exposes their formulas. A new public equivalence with the fixed-point formulation was not exported and is not claimed.

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK (functions on ℂⁿ×B represented by ambient functions restricted to that domain)
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A (existential predicate, no choice construction)
DEFINITION_VERDICT: PASS
```

Reviewed consumed meanings: `P11Vec`/`P11CVec` are Pi spaces with their max norm; `P11Family` is the stated product. `domain_def` is strip × action ball × B. `p11Admissible` expands to joint differentiability and period-one angle shifts. `p11Bound` is the design-selected pointwise norm bound, avoiding an unguarded sSup. `p11Taylor` is value plus action Fréchet derivative at zero; `p11Cutoff` is Fourier truncation of that Taylor part. `p11R0`/`p11R1` are the value/derivative of the actual cutoff, not unrelated substitutes. `p11Error` and `p11Loss` have the source constants, exponents and 2π convention. No off-domain derivative default supplies a source-domain claim: s>0 and openness are supplied wherever higher joint derivative regularity needs them.

Proof pass:

- `fc-tail` derives the slice's holomorphy, periodicity and bound internally; uses boundary-radius Fourier decay and actual reconstruction; proves summability of the full lattice majorant and restricted tail; subtracts the indicator sum using summability. It does not exploit a nonsummable tsum default or assume coefficient decay.
- `tc-a` derives the action operator bound from Cauchy and evaluates on η and the coordinate vectors of norm≤1. It retains M+Ma/s rather than the weaker 2M.
- `tc-b` proves the sharper endpoint by y↓‖η‖/s from the strict-radius remainder theorem, then proves monotonicity for nonnegative M. Its M≥0 is derived at the actual zero-action point. The right-neighborhood filter is nontrivial and the denominators are positive.
- `cu-coeff` derives `stepF0_diff`, `stepF1_diff` and parameter Fourier holomorphy inside the proof, rewrites to finite sums, and proves entire-angle joint differentiability and periodicity. Its R_*1 equalities keep the necessary b∈B guard.
- `cu-a` internally supplies q=1/2 to `p11_cutoff`, uses `p11_cutoff_coeff`, and projects the vector sup bound to each coordinate.
- `cutoff` builds every coefficient identity, polynomial witness, norm/realness clause and loss bound internally. All imports are landed modules. No proved dependency output occurs as a public premise.

## Refutation pass, source precision and deviations

No unresolved blocking finding. The following suspected mismatches were checked against contrary evidence before deciding the verdict:

1. **Scalar/vector scope — authorized deviation, not unrestricted source closure.** BP 45 and 98 quantify F with values in ℂ^q. The external package brief's 02:30 ruling says: “otherwise export the scalar form and flag it in the handoff.” The handoff does flag it, and the module docstring does too. Thus `fc-tail`, `tc-a`, `tc-b` pass the explicitly permitted scalar scope. Without this ruling these would be weaker exports. BP 114 itself takes scalar R, so `cu-a`, `cu-coeff`, `cutoff` have no vector-codomain mismatch. The ruling refutes treating these three scalar restrictions as unauthorized failures.

2. **Norm-data clause — optional proof clause, existing definitions checked.** DG 22523 includes induced matrix and multilinear norms. The controlling package plan explicitly makes the matrix max-row-sum theorem optional in export 1. Existing Pi norms, `modeSize`, and induced derivative norms supply the literal conventions; the new lemma supplies the missing openness/inclusion claims. It does not claim to prove the optional matrix identity. The explicit plan refutes an omission blocker.

3. **Loss addendum — allowed premises; correction to claimed necessity.** The handoff quotes the candidate omission as “E_T ≤ α” at BP 124; the actual text is at **BP 122**, while 124 ends the proposition. BP 122 says “With T=T_ν, d=d_ν, α=α_ν of Lemma … loss-choice: E_T≤α”. That reference may be read as importing the lemma's hypotheses; the source is imprecise rather than unconditionally refuted under that reading. The package exports exactly the ruled restrictions, solely in the addendum.

   The claim that **d≤1 is genuinely necessary is false** for the error estimate under n≥1, T≥1, 0<alpha≤1. Put u=πT and A=log(2c_n/alpha)+n log u. Then A>1, u>1, d=A/u and

   `E_T = alpha/2 * (u^(-n) + A^(-n)) ≤ alpha`.

   This has no d≤1 step. Contrary-evidence check: `MaximalStep/Loss.lean` 84–119 introduces `hd` but proves the estimate with separate bounds on precisely those two summands; `hd` is unused. Thus the package's extra condition is permitted and conservative, but should not be recorded as an unavoidable mathematical defect of the blueprint. No source repair was made.

   T≥1 and alpha≤1 cannot simply both be dropped from the uniform assertion: numerical diagnostics for n=1 give T=0.065, alpha=1, d≈0.3624166906≤1 and E≈9.20467672>1; T=1, alpha=15 gives d≈0.0316159935≤1 and E≈77.89733932>15. These diagnostics illustrate the needed restrictions; the algebraic identity above, not floating-point output, supports the d≤1 redundancy conclusion.

4. **tc-b equality — explicitly waived.** DG 23121 includes the identity with proof-local g_j. The 02:30 ruling explicitly requests the inequality chain only; the export contains both inequalities. The missing series identity is not silently promoted to a proved export.

These are recorded deviations/precision notes, not changes to the pinned source or errata ledger. No further suspected source defect was found in this slice.

## Mechanical verification

All Lean/Lake-bearing commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource overrides or clean rebuilds were used.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-g11cut KAM.Planetary.MaximalStep.CutoffNodes
   ```

   Exit **0**. Output: `[inp-gate] slot 1 acquired 02:48:06 for KAM.Planetary.MaximalStep.CutoffNodes`; `Build completed successfully (9125 jobs).` Replayed inherited modules emitted unused-variable/simp and deprecation warnings; no warning arose in `CutoffNodes.lean`. The job count includes cached/replayed prerequisites, not a clean library rebuild.

2. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.CutoffNodes
   ```

   Exit **0**. Output: `replaying KAM.Planetary.MaximalStep.CutoffNodes`.

3. Axiom/body and application probes:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/G11CutAudit.lean
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/G11CutApplications.lean
   ```

   Both exit **0**. First probe printed each complete elaborated type and checked all seven public theorems and the definition. Every `#print axioms` returned exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. It also checked the definition's complete exposed equation by `Iff.rfl` and consumed the thickening theorem's two property conjuncts. Second probe copied all seven inspected theorem headers to anonymous examples and supplied every explicit proof argument in order; all seven applications elaborated, with no output. This is a check of the audited unsigned exports, not a claim of byte equality to a nonexistent signed contract. Both temporary files were removed before lint.

4. Source/import hygiene:

   The recursive project import closure has **79** KAM modules, **12** frozen imports, all manifested **SEALED definitions**, zero providers and zero frozen theorem imports. Frozen definitions are ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, Planetary.Phase, Planetary.CircularPoint, Planetary.CircularTube. No DRAFT_SORRY anchor is imported. No forbidden tokens/overrides or EuclideanSpace occur in the new module. It has copyright, `module`, public imports, module docstring, public section and exposed definitions. Maximum line width **99**, line count **346**. None of the eight new public short names duplicates a declaration elsewhere in KAM; every public name is under `KAM.Planetary` with a p11 prefix, so no root declaration is shadowed.

5. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, exclusively for the brief-permitted generated-root notice. Exact substantive output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1214 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint failure. The generated root was not edited; this notice is explicitly not a package finding.

6. `git diff --check inp...HEAD`: exit **0**, no output. Protected-path diff: empty. Final `git status --short` contains only the pre-existing untracked handoff and this untracked report. `git diff --check` passes. Both temporary probes are absent; the report has no pending placeholders.

## Closeout

Seven node verdicts supplied; all new public declarations and the sole new definition classified. No excess binder or assumed dependency output. Fresh targeted elaboration, exact applications, standard-foundation axiom closure and kernel replay passed. Permitted scalar restrictions and conservative loss restriction remain explicit; broader vector closure, optional matrix identity, downstream frozen theorem closure, and an independent re-audit of unchanged imported mathematics are outside this report's claims. The generated root is the merge orchestrator's responsibility. No implementation edits requested or performed.
