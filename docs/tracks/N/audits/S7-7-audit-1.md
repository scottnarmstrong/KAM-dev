# S7-7 independent package audit 1

**Verdict: PASS WITH NOTES** for `bpN:p7:nonresonant`, implemented by
`KAM.Stability.nonresonant`. The statement and proof pass the package audit. This is an
infrastructure theorem, not a provider or a frozen-anchor seal. No frozen theorem is closed
by this verdict. The notes concern documented proof-route bypasses, an unused dimension
premise, and the expressly permitted stale generated root.

## Scope and snapshot

Audit date: 2026-10-28. Authority: the user's exact worktree/report-path instruction,
`AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and
`docs/tracks/N/audits/S7-7-handoff.md` (AUDIT FOCUS). The user's report destination overrides
the generic brief's main-worktree destination. Applied the `lean-statement-audit` workflow
to the helper contract; no delegation, production edits, or state-changing git operations.

| Input | Revision / SHA-256 |
|---|---|
| Worktree HEAD | `1e47a632cd281a4f91b03bb4ad422a93882e4473` |
| `inp` at comparison | `f11c90357967f666b1673409df890dbcec823dff` |
| `inp-n68b` | `71c948960935fe32cd69d6d17bf932b9d691b906` |
| `Nonresonant.lean` | `8f6f24f66d9ad6a28e27f230aeaffe35144152c6a43d0ea11660f0899fd765ce` |
| `NonresonantAux.lean` | `e659c845cc81e21148b12b03cafc4ba865e065f9dd9c75b42040d175b365ce2c` |
| `docs/tracks/N/design/PART67-LEAN-DESIGN.md` | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| `blueprint-N/parts/p7-stability.tex` | `f3d6e993abd74759469db1c9ae3c2c6d7cc65555a6d13167e8bfc7c38493e4bd` |
| `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |

Both `git diff inp...HEAD` and `git diff inp-n68b...HEAD` contain exactly the two new
`KAM/Nekhoroshev/Stability/Nonresonant*.lean` files (215 and 139 lines; 354 insertions).
The handoff's 212/138 line counts are slightly stale. The untracked handoff was present at
intake and is not an auditor-created change. N6-1 through N6-8 and S7-1 through S7-6 are
dependencies, not newly audited packages here.

Read the design's S7-7 row, §5 equivalences, §7 proof plan, Appendix B.5, both
`docs/tracks/N/design/DESIGN-N67-design-audit-{1,2}.md` reports, Part 7's setting,
derivative/gradient, preimage, transfer and nonresonant statements/proofs, and the track-N
statement/frozen interfaces. Design-audit-1 findings were closed at the design level in
audit 2; those earlier design approvals do not substitute for the present proof checks.

## Declaration ledger

All public names below are in namespace `KAM.Stability`. Private declarations are included
for a complete inventory of the changed files.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| `bpN:p7:nonresonant` | `nonresonant` (`Nonresonant:92`) | PASS WITH NOTES | Exact design signature; full stopped max-norm bound and original time window; valid alternate proof route below. |
| Real/complex derivative bridge | `thetaGradR_realH_re` (`NonresonantAux:32`) | PASS | Chain rule and restriction of scalars identify the genuine real derivative at an interior real point. No reality premise is needed for the real-part identity. |
| `bpN:p7:theta-derivative`, max-norm consequence | `norm_thetaGradR_le` (`NonresonantAux:49`) | PASS | Proves the required max-norm bound from the existing sum-of-complex-partials bound; no dimension factor or norm change. |
| Derivative linearity | `thetaGradR_realH_add` (`NonresonantAux:63`) | PASS | Analyticity and reality yield genuine differentiability before using `fderiv` additivity. |
| Action-only analytic inclusion | `inClass_snd` (`NonresonantAux:81`) | PASS | Holomorphic action function composed with second projection; angle periodicity is literal. |
| Action-only gradient | `thetaGradR_snd` (`NonresonantAux:87`) | PASS | Differentiable Hamiltonian is constant on each angle-coordinate line; derivative uniqueness proves zero. |
| Remove integrable part | `thetaGradR_h_add` (`NonresonantAux:113`) | PASS | Combines the preceding additivity and zero-gradient results. |
| `stepN:p7:nr-t3`, mean-value helper | `drift_bound` (`NonresonantAux:123`) | PASS | Generic conditional derivative estimate, with its gradient premise explicitly discharged at both uses in `nonresonant`; not a replacement for Proposition 1. |
| Analytic closure (private) | `inClass_add'` (`Nonresonant:34`) | PASS | Holomorphic sum and periodicity. |
| Analytic closure (private) | `inClass_sub'` (`Nonresonant:39`) | PASS | Holomorphic difference and periodicity. |
| Reality closure (private) | `realOn_add'` (`Nonresonant:44`) | PASS | Imaginary parts add. |
| Reality restriction (private) | `realOn_mono'` (`Nonresonant:49`) | PASS | Restricts to the smaller domain. |
| Small-κ arithmetic (private) | `arith_small` (`Nonresonant:53`) | PASS | Uses `exp(κ/6) ≤ exp 1`, positive denominator, and the multiplied time bound. |
| Large-κ arithmetic (private) | `arith_large` (`Nonresonant:66`) | PASS | Cancels positive exponential factors and proves the strict `15r/32` bound from `exp 1 > 2.56`. |

## Exact statement and expanded premises

The declaration text from `theorem nonresonant (` to `:=` is **byte-identical** to the
supplied signatures file, lines 659–674, and agrees with design Appendix B.5, lines
1117–1132. The temporary probe reconstructs this exact declaration under a fresh name,
applies all 17 explicit hypothesis binders in order, and checks the reverse `type_of%`
assignment. There is no provider/frozen type or seal body for this package; those two
brief checks are inapplicable rather than passing seals.

Blueprint authority for the following table is `blueprint-N/parts/p7-stability.tex:128–137`
(Proposition 1), its standing conventions at line 12, its setting at lines 26–31, and
Part 6's `(N2)` convention. `TYPING` rows are individual outer data binders. Predicate
fields are expanded so no bundled hard theorem is hidden.

| Binder / expanded field | Bin | Meaning and authority |
|---|---|---|
| `n` | TYPING | Coordinate dimension. |
| `D` | TYPING | Arbitrary real action set. |
| `r` | TYPING | Action width. |
| `s` | TYPING | Geometric angle width. |
| `K` | TYPING | Fourier cutoff. |
| `α` | TYPING | Nonresonance constant. |
| `L` | TYPING | Frequency Lipschitz bound. |
| `p` | TYPING | Hölder parameter; `q = p/(p-1)` is defined, not assumed. |
| `ε` | TYPING | Carried perturbation size bound. |
| `h` | TYPING | Complex integrable Hamiltonian on actions. |
| `f` | TYPING | Complex perturbation on angle/action pairs. |
| `hn` | STANDING | `1 ≤ n`, explicit Part 7 convention; unused in this stronger proof. |
| `hp` | SOURCE | `1 < p`. |
| `hr` | SOURCE | `0 < r`. |
| `hs` | SOURCE | `0 < s`. |
| `hK` | SOURCE | `0 < K`. |
| `hα` | SOURCE | `0 < α`. |
| `hL` | SOURCE | `0 ≤ L`. |
| `hh` | SOURCE | Holomorphic `h` on `polyNbhd (cpx D) r`. |
| `hhr` | SOURCE | `Im(h(I)) = 0` at real points of the complex domain; equivalent to reality on `U_r D` for `s > 0`. |
| `hf.differentiableOn` | SOURCE | Holomorphic `f` on `Dom n (cpx D) r s`. |
| `hf.periodic` | SOURCE | Period one in each angle coordinate. |
| `hfr` | SOURCE | `Im(f(x)) = 0` at the real points of that domain. |
| `hfb`, summability field | SOURCE | For every complex action in `V_r D`, summability of weighted Fourier coefficient norms. |
| `hfb`, bound field | SOURCE | Those sums are at most `ε`; weights are `exp(2π s |k|₁)`. |
| `hε0` | SOURCE | Nonnegative size bound; automatic for the source norm, explicit for the stronger carried-bound version. |
| `hnr` | SOURCE | For every `I ∈ cpx D`, `k ∈ Z_K ∖ {0}`, `α ≤ ‖Σ kᵢ freq(h,I)ᵢ‖`: exactly (i). |
| `hlip` | SOURCE | For `I₀ ∈ cpx D`, `I ∈ V_r D` with `‖I-I₀‖ < r`, `‖freq h I-freq h I₀‖ ≤ L‖I-I₀‖`: Part 6 (N2). |
| `hrad` | SOURCE | `K L r ≤ α/p`, clause (ii). |
| `hiii` | SOURCE | `ε ≤ α r/(2⁷ q K)`, clause (iii). |
| `J` | TYPING | Arbitrary set of times, quantified after all system hypotheses. |
| `J.OrdConnected` | SOURCE | Time domain is an interval. |
| `0 ∈ J` | SOURCE | Initial time belongs to the interval. |
| `z` | TYPING | Total real phase-space curve. |
| `IsOrbit`, membership field | SOURCE | At every time in `J`, `z t ∈ realStrip D r`. |
| `IsOrbit`, derivative field | SOURCE | At every such time, genuine two-sided `HasDerivAt z (X_(realH(h+f)) (z t)) t`. |
| `(z 0).2 ∈ D` | SOURCE | Initial action belongs to the base set. |
| `t` | TYPING | Arbitrary observation time. |
| `t ∈ J` | SOURCE | Observation lies in the stated orbit interval. |
| Time inequality | SOURCE | `|t| (5ε) ≤ sr exp(2πKs/6)`. |

Counts in this expanded outer-interface table: **TYPING 14, STANDING 1, SOURCE 25,
RULED 0, EXCESS 0**. The quantified actions, Fourier indices and times inside the three
expanded predicates are their literal domain quantifiers; they introduce no further
premises, instances or witness packages.

`WBound` includes summability, so the `tsum` convention outside the summable locus is
never used as a zero-norm escape. Passing a nonnegative upper bound in place of the exact
norm is the explicitly designed stronger statement (§5 item 4). The multiplied time
condition agrees with the printed time at `ε > 0`; at `ε = 0` it allows every real time,
without dividing by zero. No compactness, convexity, nonempty-D, normal form, confinement,
or existence result is an input premise. For empty `D` the initial-action premise is
impossible, exactly as intended. Constants do not gain any dependence on `z`, `J`, or `t`.

## Proof and dependency consumption

1. **Small κ**, `Nonresonant:108–114`: `thetaGradR_h_add` removes `h`,
   `norm_thetaGradR_le` bounds the gradient throughout `W_r`, and `drift_bound` applies on
   the entire segment between zero and `t`. `arith_small` completes the estimate using
   the original width `s`. No exponential remainder claim for the identity map is used.
2. **Large κ**, lines 115–127: `normal_form` is applied with `Λ = {0}` using the actual
   hypotheses; reality is obtained from its real branch and singleton symmetry.
   `preimage_nfl` supplies real preimages and `d = qKε/α ≤ r/128`, using the actual initial
   point to obtain the latter bound. This does not add `D.Nonempty` as a premise.
3. Lines 129–166 explicitly produce a finite weighted bound for `g`: the homological
   resonant projection bound, restriction to `(r/2,s/6)`, the normal-form correction
   bound, and `wbound_add`. Coefficients vanish outside `{0}` because they vanish outside
   `{0} ∩ Z_K`. `resonant_gradient` therefore places the real gradient in
   `resSpan {0} = ⊥`, proving it is zero. No θ-independence assertion is assumed.
4. Lines 167–195 supply all three transfer obligations: componentwise real-part
   estimates give (T1); the proved preimages give (T2); the globally bounded remainder
   gradient and `drift_bound` give (T3). The numerical lemma uses positive factors and
   exponential cancellation, proving `6r/(5e) < 15r/32` with slack.
5. Lines 196–209 instantiate `transfer` with `Nrm = ‖·‖`, `ϱ = 15r/32`, and the original
   multiplied admissibility predicate. Monotonicity follows from `ε ≥ 0`. Holomorphy,
   reality, mapping, symplecticity and Hamiltonian conjugacy all come from actual terms.
   `d + ϱ ≤ 61r/128 < r/2`; the final result is bounded by
   `ϱ + 2d ≤ 31r/64 ≤ r/2`.

`drift_bound` differentiates the action projection of the genuine orbit, restricts it to
the convex interval `uIcc 0 t ⊆ J`, and applies the mean-value inequality. This covers
negative times, endpoints and `t = 0`; no inferred dynamics from a junk derivative is
used. The analytic bridge lemmas establish differentiability on the open domains before
using derivatives of sums or action-only functions.

**Route notes:** `normal_form` (N6-8), `theta_derivative`/`resonant_gradient` (S7-2),
`preimage_nfl` (S7-3), and `transfer` (S7-4) are consumed directly. `homological` and
`wbound_add` additionally discharge the finite-norm premise for `g`. `nonresonant_case`
and `exit_ball` are not used. This differs from the design's procedural plan, but preserves
every theorem premise/conclusion: the gradient bounds are already uniform on the full
strip occupied by each orbit, making the local first-exit argument redundant. The small-κ
case can be estimated directly without manufacturing identity-map transfer data. This is
a justified bypass, not a claim that either bypassed theorem has been proved here.

## Definitions and import boundary

**New definitions/abbreviations/structures: none.** Both files contain only theorems.
For new objects: BODY_MATCH / PUBLIC_CARRIER / WELL_DEFINEDNESS / CHARACTERIZATION /
CHOICE_INDEPENDENCE are N/A; no new definition can hide a fallback or choice.

Checked the meaning-bearing existing definitions used by the statement and proof:
`polyNbhd` and `realNbhd` are existential strict max-norm tubes; `cpx` is the real
inclusion image; `Dom` uses the geometric strip; `realStrip` is the product with all real
angles; `realH` is the real part of the actual complex Hamiltonian; `thetaGradR` uses the
coordinate real derivative; `freq` uses the coordinate complex derivative; `conjExp` is
`p/(p-1)` with `p > 1`; `IsNonresonant`, `FreqLipschitz`, `InClass`, `RealOn`, `WBound`
and `IsOrbit` expand as recorded above. The source-to-frozen interface is compatible with
`realHamiltonian_eq_realH`; the frozen vector field has the actual Hamiltonian signs.

The import traversal reaches 114 project modules, **zero providers and zero frozen
theorem modules**. Its 19 frozen modules are definitions, each with a unique manifest
entry in state `SEALED` (ActionNbhd, ComplexStrip, DotC, FrequencyMap, GramMatrix,
HamiltonianVectorField, HamiltonianVectorFieldC, InvarianceError, IsDiophantine,
IsPrimaryOnStrip, IsRealOnReals, NormalFrame, OmegaZero, RealHamiltonian, Torsion,
TorsionAverage, Iso/IsHamiltonianSolutionOn, Nekhoroshev/IsSolutionOn,
Nekhoroshev/RealPart). No DRAFT_SORRY theorem or quarantined provider is imported.

## Validation receipts

Validation was serialized. All retained Lean/Lake receipts below use
`LEAN_NUM_THREADS=1` and `nice -n 5`. An initial unqualified lint invocation was stopped,
including its ABI child; only the fully qualified rerun below counts as a lint receipt.
The targeted build replayed existing artifacts; no library clean or cache operation was run.

### Targeted compile gate

```text
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-s77 KAM.Nekhoroshev.Stability.Nonresonant
[inp-gate] slot 1 acquired 08:27:45 for KAM.Nekhoroshev.Stability.Nonresonant
Build completed successfully (3269 jobs).
exit 0
```

The package warning is `Nonresonant.lean:92:21: Variable name hn is not explicitly
referenced`. Replayed upstream warnings concern the unused normed-space section variable
in `KAM.ODE.gen_exit`, `hgr` in `Gradient`, and `hϱ` in `Transfer`. No errors, sorry
warnings, heartbeat overrides or default-heartbeat failures occurred.

### Exact-type, explicit application and all-public-theorem axioms

The auditor-generated `.lake/abi-scratch/S77Audit.lean` imported only the package module,
opened its namespaces and reconstructed the supplied signature as `audit_nonresonant`.
Its proof was exactly:

```lean
by
  exact KAM.Stability.nonresonant hn hp hr hs hK hα hL hh hhr hf hfr hfb hε0 hnr hlip hrad hiii
```

It also contained:

```lean
example : type_of% @audit_nonresonant := @KAM.Stability.nonresonant
```

Then `#print axioms` was run for all eight new public theorems. Exact command/output:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S77Audit.lean
'KAM.Stability.nonresonant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.thetaGradR_realH_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.norm_thetaGradR_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.thetaGradR_realH_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.inClass_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.thetaGradR_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.thetaGradR_h_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.drift_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

### Source hygiene and protected paths

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (480 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The exit code reflects the one explicitly permitted generated-root exception. No other
lint failure was emitted. Both package files have copyright/license/author comments,
`module`, public interface imports, module docstrings and public sections. Their total
line counts are 215 and 139; neither has any line longer than 100 Unicode characters.
An additional comment/string-masked scan found no forbidden proof escape, resource
override or `EuclideanSpace` token in either file. No new definition needs `@[expose]`.

```text
git diff inp...HEAD --check
exit 0; no output
git diff inp-n68b...HEAD --check
exit 0; no output
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
```

### Kernel replay and final cleanup

One invocation replayed both audited modules:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Stability.Nonresonant KAM.Nekhoroshev.Stability.NonresonantAux
replaying KAM.Nekhoroshev.Stability.NonresonantAux
replaying KAM.Nekhoroshev.Stability.Nonresonant
exit 0
```

The complete two-line replay output was inspected. Auditor probe/log files were removed
from `.lake/abi-scratch/`. Final whitespace/report checks pass. The only persistent file
created by this audit is this report; the pre-existing untracked handoff remains untouched.
Neither production source nor frozen/manifest/generated files changed during the audit.

## Source/blueprint issues and limitations

No new suspected pinned-source mathematical erratum was found. No source PDF was
re-transcribed or independently re-audited; this is a package audit against the pinned
blueprint and approved design interfaces.

One **pre-existing totality wording mismatch** remains visible: Part 7's setting at
`blueprint-N/parts/p7-stability.tex:28` says “`G^R(x)=0 otherwise`”, whereas
`KAM/Nekhoroshev/Stability/Setting.lean:52–53` defines `realH` globally as `Re(G ∘ ι)`.
The revised design uses the latter real-part extension. The two agree on the open strip,
and all differentiation/orbit arguments here take place in that strip; no off-domain
zero value is used. This is a blueprint bookkeeping note, not a new package definition
or a pinned-source defect, and it does not change the verdict.

No other uncertainty or unauthorized deviation was found in the audited package.
The untouched frozen headline remains outside this package's proof claim.
