# N6-2 independent package audit 1

**Verdict: PASS for N6-2's public definitions and theorems.** The parameter core, canonical direct
form, source-hypothesis form and three bridges match the v2 design signatures and implement the
homological blueprint contract. No material statement, proof or dependency defect was found.
This is infrastructure approval, not a frozen-anchor seal or closure of any track-I/N/P headline.

## Scope and immutable inputs

Audit date: 2026-10-28. Tier-2 refute-first review, following
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md` and the handoff's AUDIT FOCUS.
The user's explicit destination overrides the brief's generic main-worktree destination: this report
belongs to `/root/code/KAM-inp-n62/docs/tracks/N/audits/N6-2-audit-1.md`.
The authorized persistent change is this report only; no repairs, commits, generated-root updates,
source downloads or external messages were performed. Temporary checks live in `.lake/abi-scratch/`
and are removed after use. No subagents were used.

Snapshot v1:

| Input | Revision / SHA-256 |
|---|---|
| Audited HEAD | `2da9ccb5fc60b4cbd04df675d34edcdbdb614ecd` |
| `inp` at intake | `00cf49c93cbcea2fd371edf0865258fadd64a43d` |
| Merge base selected by requested three-dot diff | `f45c6617a5e134742856494cfee2a6f95ea2d1b6` |
| `KAM/Nekhoroshev/NormalForm/Homological.lean` | `57982c662bb285db748ac9d5d73733f6e9794ac6abfcf443461eaba211363df7` |
| Dependency `NormalForm/Setting.lean` | `c5b5cea712c16ed67bca33e0cad5ed7939c30905b4cb7c3ff6359b8f4c9ae841` |
| `docs/tracks/N/design/PART67-LEAN-DESIGN.md` | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| Supplied `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |
| `blueprint-N/parts/p6-normal-form.tex` | `1c9c5e640ba0825040f1a2ad1de3aac9b38df9dbfcc1b280245ed53c3f2533ac` |
| `blueprint-N/parts/p11b-partial-nf.tex` | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| Package audit brief | `316d17309e362cccf5ee0c182cfe3142c9fad9cd4b8c295332d751d4a334d37d` |
| `N6-2-handoff.md` | `2d438fac24df0809f2766a153c50c12cd35cfbab22dc8cc830dac561bb60634e` |

`git diff inp...HEAD` warns of multiple merge bases and selects the base above. Its complete scope is
515 added lines in `Homological.lean` and 179 added lines in inherited N6-1 `Setting.lean`.
Only `Homological.lean` is assigned a fresh package verdict. Setting, W4 coefficient/projection modules,
the canonical setting and relevant frozen definitions were inspected as dependencies. The initial
untracked handoff is prover-owned and was preserved.

Read authorities: AGENTS.md, PLAN.md, DECISIONS.md, track-N statement conventions, design v2 row N6-2
and Appendix A.2, design-audit-1 F3 and design-audit-2's F3/N6 discussion, blueprint
`bpN:p6:homological`, `bpN:p6:iterative-direct`, and `bpN:p11:hom`.
Acceptance criteria were exact public types/bodies, faithful expanded premises and constants,
sound finite-mode/projection/divisor/reality arguments, clean public axiom closure, targeted build,
kernel replay and source hygiene. Direct re-audit of Pöschel's PDF, N6-1 proof closure, the extended
Part-11 bracket implementation and headline frozen providers are outside scope.

## Public declaration ledger

All names below have namespace `KAM.NormalForm`; locators refer to snapshot v1.

| Blueprint/design node | Lean declaration (line) | Verdict | Evidence |
|---|---|---|---|
| p6 homological definition | `homGen` (40) | PASS | Literal selected Fourier quotient, divisor `2πi k·freq h`. |
| p6 homological definition | `homRes` (47) | PASS | Literal `projMode Λ (truncate K f)`. |
| F3 parameter core / p11 hom | `homGenParam` (52) | PASS | Independent `n,m`; frequency has the full parameter input. |
| F3 parameter core / p11 hom | `homResParam` (59) | PASS | Same Fourier lattice and projection, independent parameter carrier. |
| F3 rectangular reality | `RealOnParam` (64) | PASS | All real pairs whose inclusion belongs to the specified domain. |
| F3 bridge | `realOnParam_iff_realOn` (70) | PASS | Exact design type; `Iff.rfl`. |
| F3 bridge | `homGen_eq_homGenParam` (74) | PASS | Exact total-function specialization; `rfl`. |
| F3 bridge | `homRes_eq_homResParam` (78) | PASS | Exact total-function specialization; `rfl`. |
| F3 parameter core / p11 hom | `homological_param` (342) | PASS | Exact v2 statement, full support/equation/bounds/conditional reality. |
| p6 homological under N-dir | `homological_direct` (441) | PASS | Actual specialization of proved core and canonical bracket identity. |
| p6 homological under N1/N2 | `homological` (491) | PASS | Proved divisor bound is supplied inside the proof. |

Whitespace-normalized comparison reports `True` for all five public definition bodies. Comparison of
all six theorem headers also reports `True` after removing comments/whitespace and accounting for
the section-bound `{m : ℕ}` in `homological_param`. No other statement change is present.
An independently generated probe takes each theorem header from the supplied signatures and fills
it with the landed export applied to every explicit argument in signature order. All six elaborate.
There is no provider or frozen theorem export in this package; provider/frozen seal-copy checks are
therefore inapplicable, rather than omitted for an asserted seal.

## Binder and semantic audit

T = TYPING; S = SOURCE, including the explicitly specified v2 parameter generalization. These are
the complete outer binders; a dash denotes absence. No standing, ruled or excess premise is needed.
The design's literal types and the blueprint notation at p6 lines 10 and 30–41 fix the typing data.

| Binder | parameter | direct | source | Authority / meaning |
|---|---|---|---|---|
| `n` | T | T | T | Number of angles and Fourier indices; arbitrary natural number. |
| `m` | T | — | — | Independent parameter dimension, design F3. |
| `D` | T | T | T | Arbitrary complex base set. |
| `r` | T | T | T | Parameter neighbourhood radius. |
| `s` | T | T | T | Geometric strip width. |
| `K` | T | T | T | Real Fourier cutoff. |
| `α` | T | T | T | Divisor scale. |
| `q` | T | — | — | Independent core divisor ratio, v2 A.2. |
| `p` | — | T | T | Hölder parameter, p6 notation. |
| `L` | — | — | T | Frequency Lipschitz scale. |
| `δ` | T | T | T | Carried weighted-norm bound. |
| `Λ` | T | T | T | Arbitrary subset of the unchanged integer Fourier lattice. |
| `ω` | T | — | — | Holomorphic frequency field, v2 F3. |
| `h` | — | T | T | Integrable Hamiltonian. |
| `f` | T | T | T | Scalar perturbation on the specified product carrier. |
| `hq` | S | — | — | `1 ≤ q`, core signature (includes q=1). |
| `hp` | — | S | S | `1 < p`, p6 notation. |
| `hα` | S | S | S | `0 < α`, p6 setting. |
| `hs` | S | S | S | `0 < s`, homological proposition. |
| `hK` | S | S | S | `0 ≤ K`, cutoff convention. |
| `hL` | — | — | S | `0 ≤ L`, p6 setting. |
| `hω` | S | — | — | Holomorphic ω on `polyNbhd D r`, design F3. |
| `hh` | — | S | S | Holomorphic h on `polyNbhd D r`, p6 setting. |
| `hdir` | S | S | — | N-dir: every admissible I,k has divisor at least α/q. |
| `hnr` | — | — | S | N1: every I in D and selected k has divisor at least α. |
| `hlip` | — | — | S | N2: every indicated pair I₀,I satisfies the Lipschitz estimate. |
| `hrad` | — | — | S | `K*L*r ≤ α/p`, p6 homological proposition. |
| `hf.differentiableOn` | S | S | S | Holomorphy component of the source Fourier class. |
| `hf.periodic` | S | S | S | Every coordinate shift by one on the source domain. |
| `hδ` summability | S | S | S | For every parameter, weighted coefficient family is summable. |
| `hδ` upper bound | S | S | S | For every parameter, that sum is ≤ δ. |

Expanded counts (after replacing each `hf` and `hδ` by its two components): parameter
T=12, S=10; direct T=11, S=10; source T=12, S=13. In all three, STANDING=0, RULED=0,
EXCESS=0. `DivisorBound`, `IsNonresonant` and `FreqLipschitz` expand to the pointwise predicates
described in their rows; they contain no produced witness or hidden helper theorem.
`WBound` includes summability as well as the bound: no divergent `tsum` is used as a norm estimate.

The three additional premises *inside the conditional reality conclusion* are also SOURCE:
negation closure of Λ, reality of f at all real points in the domain, and reality of every frequency
component at all real parameter points. These are exactly p6(c) and the repaired p11 hom statement.
They are not silently assumed for the non-reality conclusions. Bridge binders are all typing data:
`realOnParam_iff_realOn` has n,U,u (3); the generator bridge has n,K,Λ,h,f (5); the resonant
bridge has n,K,Λ,f (4); no logical premise is present.

All bounds use the original `Dom n D r s`, with no loss of r or s. `modeWeight s k` is
`exp(2π*s*|k|₁)`; the generator bound is exactly `q*δ/(2π*α)`, and the wrappers use
`conjExp p = p/(p-1)`. The norms of ξ and T_K f are bounded by δ. The parameter theorem does
not choose a constant after extra data. Its support clauses preserve the cutoff and resonant
normalization. The blueprint's projection-normalization statements are recoverable from the
exported coefficient vanishing and ξ identity using `projections`; they are not extra assumptions.
The source's sharp norm δ is generalized to any carried upper bound. Omitting positivity of r
strengthens the design/source theorem harmlessly: the parameter domain is empty when r≤0.

### Definitions

| Definition | Classification and whole-carrier check |
|---|---|
| `homGen` | Literal explicit Fourier formula, not a chosen solution. |
| `homRes` | Literal composition of the two intended Fourier projections. |
| `homGenParam` | Literal rectangular version of the same quotient formula. |
| `homResParam` | Literal rectangular projection composition. |
| `RealOnParam` | Literal domain-relative reality predicate; not a theorem-shaped result package. |
| private `zFin` (91) | Finite-set representation of `zBall n K`; existence proved for every real K. |
| private `genCoeff` (103) | Literal Fourier quotient with the source mode indicator. |

For each of these seven definitions:
`BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL;
CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS`.
For private definitions, the carrier check refers to their declared internal carrier.
There is no arbitrary solution choice. The indicator zero is the intended off-support coefficient.
Complex division is total, as in the supplied literal design; whenever a denominator is used as a
divisor on the source domain, `divisor_ne_zero` proves it nonzero from α/q>0. No theorem draws a
conclusion from division-by-zero fallback semantics. The generator's selected sum is finite even
away from the analytic domain; arbitrary off-domain values of f remain arbitrary input data.

## Proof inspection and adversarial pass

The full new module was read. Private helper ledger:

| Declaration (line) | Verdict | Point checked |
|---|---|---|
| `finite_zBall` (85) | PASS | Embeds ℓ¹ cutoff in the finite natural-ceiling mode cutoff. |
| `zFin` (91) | PASS | Exact finite-set representation. |
| `mem_zFin` (93) | PASS | Membership equivalence. |
| `tsum_indicator_zBall` (97) | PASS | Terms vanish outside finite cutoff; no unjustified series interchange. |
| `genCoeff` (103) | PASS | Exact indicator-guarded quotient. |
| `homGenParam_eq_fourierSeries` (108) | PASS | Indicator multiplication identity. |
| `homGenParam_eq_sum` (117) | PASS | Actual finite-sum identity. |
| `divisor_ne_zero` (131) | PASS | α>0 and q≥1 imply positive divisor lower bound. |
| `differentiableOn_dotC` (144) | PASS | Finite linear combination of frequency coordinates. |
| `genCoeff_differentiableOn` (150) | PASS | Coefficient holomorphy times reciprocal, using proved nonvanishing. |
| `norm_genCoeff_le` (172) | PASS | Correct modulus `2π|k·ω|`; no missing factor or inequality reversal. |
| `zBall_neg` (202) | PASS | ℓ¹ cutoff is symmetric. |
| `truncate_eq_sum` (205) | PASS | Exact finite cutoff sum. |
| `projMode_inter_eq_sum` (214) | PASS | Finite intersection projection sum. |
| `homResParam_eq_projMode` (224) | PASS | Uses actual coefficients of the truncated function from W4 projections. |
| `hasFDerivAt_genTerm` (234) | PASS | Product rule with fst/snd derivatives at interior points. |
| `fderiv_homGenParam` (253) | PASS | Termwise derivative of a finite sum, evaluated on an angle basis vector. |
| `dotC_eq_sum` (271) | PASS | Finite scalar distributivity. |
| `directional_homGenParam` (278) | PASS | Cancels only a proved nonzero divisor and sums the complementary modes. |
| `im_tsum_indicator_eq_zero` (304) | PASS | Conjugation and negation equivalence reindexing, including total-tsum convention. |
| `conj_dotC` (322) | PASS | Uses real frequency components. |
| `dotC_neg` (327) | PASS | Integer mode negation. |
| `conj_coeff` (330) | PASS | Reality on every real-angle slice; hs puts that slice in the strip. |

For the main proof, `coefficients_series` is supplied with proved holomorphy and a proved summable
weighted majorant; `hδ` supplies the original summable family. Two applications of `projections`
give truncation and resonant class/norm bounds. The directional identity plus the resonant finite
sum partitions the cutoff, proving the equation pointwise. The canonical wrapper proves the
Poisson bracket identity by differentiating h∘snd, and obtains holomorphy of freq from N6-1's
`differentiableAt_freq`, which uses `holomorphic_regularity`. The source wrapper supplies the
proved `divisor` theorem's second conjunct, rather than adding that result as a source premise.

Adversarial attempts and dispositions:

| Attempted objection | Refutation / outcome |
|---|---|
| Part 11 still has square-only parameters | Refuted: core has independent m; only canonical wrappers identify m=n. The full parameter vector enters f̂ and ω. |
| Reality can hold without a real frequency | Refuted as an objection to this implementation: the exact real-frequency premise is retained and used in conjugating the divisor. |
| A `2π` or bracket-sign mismatch | Refuted: derivative of χ supplies `2πi kᵢ`; denominator and canonical bracket sign cancel to +f̂. |
| Infinite differentiation or coefficient-of-product gap | Refuted: cutoff finiteness is proved first; finite termwise differentiation replaces that proof-plan route. |
| Projection composition assumes its own conclusion | Refuted: the truncated coefficient identity comes from the already proved W4 `projections`, not a premise of the new theorem. |
| Hidden divergent norm or zero-divisor branch | Refuted: WBound contains summability; positivity supplies nonvanishing at every cancellation. |
| q=1, empty D, zero-dimensional vectors or nonsymmetric Λ break the core | Refuted: q=1 is admitted directly; empty domains are vacuous; finite sums and derivative formulas work in dimension zero; symmetry is required only for reality. |

No surviving material finding or unresolved tentative blocker remains. This refutation pass was
performed separately from discovery by the same independent auditor; no additional reviewer is claimed.

## Hygiene and independent verification

All auditor-started Lean/Lake commands were sequential, with `LEAN_NUM_THREADS=1` and nice level 5.
The lint command's ABI subprocess inherits these settings and ran after kernel replay completed.
Unrelated sessions were left untouched. No clean/cache/package mutation or broad build was requested.

Targeted build (exit 0):

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-n62 KAM.Nekhoroshev.NormalForm.Homological
[inp-gate] slot 2 acquired 06:25:23 for KAM.Nekhoroshev.NormalForm.Homological
Build completed successfully (3171 jobs).
```

Exact-signature and axiom probe (exit 0, no warnings/errors):

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N62Audit.lean
'KAM.NormalForm.realOnParam_iff_realOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.homGen_eq_homGenParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.homRes_eq_homResParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.homological_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.homological_direct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.homological' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Probe reproduction: for each of those six names, extract the header before `:=` from the pinned
supplied signature file, replace `theorem <name>` with `example`, and append `:= by exact <name>`
with respectively `U u`, `K Λ h f`, `K Λ f`, `hq hα hs hK hω hdir hf hδ`,
`hp hα hs hK hh hdir hf hδ`, and `hp hα hs hK hL hh hnr hlip hrad hf hδ`.
Import only `KAM.Nekhoroshev.NormalForm.Homological`; open `Set Metric KAM.Weighted KAM.Canonical`
and use namespace `KAM.NormalForm` with `variable {n : ℕ}`. Add the six `#print axioms` commands.
The probe does not import the draft signature module or any of its `sorry` bodies.

Kernel replay (one invocation, exit 0):

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.NormalForm.Homological
replaying KAM.Nekhoroshev.NormalForm.Homological
```

Source lint (raw exit 1 solely for the generated-root exception explicitly allowed by the brief):

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (419 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Thus lint is PASS under the brief's stated exception; the generated root was left untouched.
There are no line-length, proof-escape, size, module-system, frozen-guard or ABI findings.

Additional checks:

- `rg -n '\b(sorry|admit|axiom|unsafe|opaque|set_option)\b' KAM/Nekhoroshev/NormalForm/Homological.lean`:
  no matches (exit 1, the expected grep result).
- `rg -n '.{101}' KAM/Nekhoroshev/NormalForm/Homological.lean`: no matches (exit 1).
- `wc -l KAM/Nekhoroshev/NormalForm/Homological.lean`: 515, below 1500.
- Module header, copyright, public interface imports, module docstring, public exposed section: present.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, apart from the merge-base warning.
- `git diff --check inp...HEAD`: exit 0, only the same merge-base warning.
- Recursive inspection of project imports reaches 42 project modules, no provider, and eight frozen
  definitions, all manifest state SEALED: ActionNbhd, ComplexStrip, HamiltonianVectorField,
  HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero.
  No frozen theorem or DRAFT_SORRY anchor is imported.

## Errata, deviations and limits

No new suspected pinned-source erratum, blueprint contradiction or unauthorized deviation was found.
The existing design proof-plan citation at design line 278, “`DifferentiableOn.fderiv`”, remains the
known documentation issue identified as N6 in design-audit-2 (lines 60–69). Its proposed correction
is already respected by this implementation through `differentiableAt_freq` and
`holomorphic_regularity`; it is not a new N6-2 proof defect. No source or design file was repaired.

The implementation legitimately substitutes finite-sum differentiation for the design's
coefficient-of-product route. Rectangular reality and arbitrary q≥1 are explicit v2 design features.
Part 11 still owns its fast-coordinate frequency specialization and weighted-bracket identification;
this audit establishes the shared parameter solve, not those downstream implementations.

No frozen anchor is sealed here. No assertion of track-root proof closure follows from the build,
the kernel check or this PASS. All assigned declarations are classified, all six public theorem
exports have clean axiom receipts, and no material uncertainty remains within the stated scope.
Final source hash matches snapshot v1; auditor-created probes/logs were removed. Final
`git diff --check` is clean and repository status retains only this report and the pre-existing
untracked prover handoff. No implementation file was changed by the audit.
