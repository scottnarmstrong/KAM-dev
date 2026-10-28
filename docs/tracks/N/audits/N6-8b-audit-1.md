# N6-8b independent package audit 1

Overall verdict: **PASS WITH NOTES**.
The three advertised infrastructure targets pass statement and proof review. There is no
frozen theorem or provider in this package, so no frozen seal-readiness or headline closure
is claimed. The expected stale generated root and an auditor scheduling deviation are notes.

## Scope and authority

Report destination is `/root/code/KAM-inp-n68b/docs/tracks/N/audits/N6-8b-audit-1.md`, as
explicitly required by the user; this overrides the brief's generic main-worktree destination.
Read repository rules, PLAN, DECISIONS, the package audit brief, the handoff/AUDIT FOCUS,
PART67 design v2 and N6-8 proof plan, both design audits, the original v2 signatures in
`/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean`, blueprint Part 6 and track-N
statement context. Applied the lean-statement-audit skill for statement/definition review.
No delegation, production edit, frozen edit, or state-changing git command.

Snapshot: HEAD `8d552de890c8d7885718eaf33b545b80a5f23663`; `inp` and comparison merge base
`ef8fc426c638557035e6101216aad4ef8b8a570e`. Required `git diff inp...HEAD` contains twelve
NormalForm files (2189 added lines), including inherited session-1 Arith/Steps work.
The actual session-2 delta `git diff c76bd4b^..HEAD` (parent
`482fa2bf0310e4163526dacd5b0c1c751bc91b06`) contains exactly the three files below.
The live `inp-n68a` reference has other differences and is not substituted for this commit
boundary. Arith/Steps are dependency interfaces, not re-audited deliverables.
The pre-existing untracked handoff is preserved.

| Scoped file under KAM/Nekhoroshev/NormalForm/ | Lines | SHA-256 |
|---|---:|---|
| NormalFormAux.lean | 177 | `4237625159cb717e9525147529723373d9491db90f59be512a447b437afbfaaa` |
| NormalFormCaseA.lean | 147 | `20336a8755122020f2a3d06e27faab4f59750dbaa125e1402dea756865d051ac` |
| NormalForm.lean | 155 | `8f5f8c2830d47b0349852e45b6d35925d80e1b8178b4b95c8c130ece366011f1` |

The supplied signature SHA-256 is
`c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f`, exactly the design v2 pin.
Python comparison found byte-identical declaration types for `normal_form` and
`nonresonant_case`, and byte-identical `nfSteps` definition. `NFConcl` is byte-identical to
the full conclusion of `normal_form`. Frozen-provider ABI and frozen-seal probes are N/A:
PART67 design opening explicitly says these parts have no frozen theorem/provider.
Instead, scratch probes reproduce each exact design type under a fresh name and apply the
implementation with all explicit proof binders in the original order.

## Per-node and declaration findings

Names below have prefix `KAM.NormalForm.`. All new public declarations are included.

| Blueprint node / role | Declaration (file:line) | Verdict | Evidence |
|---|---|---|---|
| normal-form#data / nf-N | `nfSteps` (CaseA:32) | PASS | Literal nonnegative floor of κ/(12 log 2); κ=2πKs. |
| normal-form | `normal_form` (NormalForm:96) | PASS WITH NOTES | Exact v2 type; all fifteen premises assembled into NFHyp; exhaustive carried-bound branch split. Root lint note only. |
| nonresonant-case / nr-triv | `nonresonant_case` (NormalForm:139) | PASS | Exact v2 type; identity/zero clauses literal, remainder bound retains factor exp(1). Stronger than source through omission of unused analytic premises. |
| normal-form conclusion packaging | `NFConcl` (CaseA:35) | PASS | Transparent literal conclusion, no assumed mathematical input. |
| nf-concl / translation | `chain_translate` (Aux:37) | PASS | Induction on compositions from per-step translation and maps-to premises; explicitly conditional helper. |
| nf-real | `chain_real` (Aux:59) | PASS | Real-point witnesses and maps-to give valid induction; explicitly conditional helper. |
| nf-concl / Fourier support | `coeff_homRes` (Aux:85) | PASS | Projections applied twice; intersection indicator, all action points in tube. |
| nf-concl / finite sums | `coeff_sum_eq_zero` (Aux:103) | PASS | Class and bound hypotheses justify coefficient additivity; induction gives support preservation. |
| domain restriction | `inClass_mono_nf` (Aux:124) | PASS | Restricts differentiability and period-one periodicity to smaller Dom. |
| zero correction | `wbound_zero_nf` (Aux:129) | PASS | Summability of zero coefficients and nonnegative bound, no junk tsum reliance. |
| nf-concl / constructed g | `nf_coeff_g` (Aux:142) | PASS | Conditional NFInv hypothesis supplies class/bounds; normal_form produces it through nf_inv_all. |
| nf-disp / angle seminorm | `fstSeminorm` (CaseA:74) | PASS | Norm composed with linear first projection. |
| nf-disp / action seminorm | `sndSeminorm` (CaseA:78) | PASS | Norm composed with linear second projection. |
| angle seminorm equation | `fstSeminorm_apply` (CaseA:81) | PASS | Definitional equality to ‖z.1‖. |
| action seminorm equation | `sndSeminorm_apply` (CaseA:83) | PASS | Definitional equality to ‖z.2‖. |
| nf-concl / nf-disp / nf-real | `nfConcl_caseA` (CaseA:86) | PASS | Constructs witnesses from audited Steps interface; no additional premise exported by normal_form. |
| nf-case B | `nfConcl_caseB` (NormalForm:38) | PASS | Single direct step with doubled losses; witness g=homRes K Λ f exactly. |

### Binder and semantic review

The following rows enumerate every outer binder of the main result. Logical bundles are
expanded into source properties rather than counted as unexplained assumptions.
S = SOURCE (including the design's explicit bound-predicate formulation); T = TYPING.
No EXCESS, STANDING, or RULED input is needed for these exact v2 declarations.

| normal_form binder / expanded property | Bin | Source / meaning |
|---|---|---|
| implicit n | T | Arbitrary finite dimension, p6 opening. |
| implicit D | T | Arbitrary complex action set, p6 opening/setting. |
| implicit r | T | Action radius. |
| implicit s | T | Geometric angle width. |
| implicit K | T | Real Fourier cutoff. |
| implicit α | T | Divisor parameter. |
| implicit L | T | Frequency Lipschitz parameter. |
| implicit p | T | Hölder exponent parameter, q=p/(p−1). |
| implicit ε | T | Carried perturbation bound. |
| implicit Λ | T | Arbitrary subset of integer modes; no hidden lattice premise. |
| implicit h | T | Total integrable Hamiltonian extension. |
| implicit f | T | Total perturbation extension, angles first. |
| hp | S | p>1, p6:normal-form L158. |
| hα | S | α>0, p6:setting L27. |
| hK | S | K>0, p6:normal-form L158. |
| hL | S | L≥0, p6:setting L27. |
| hr | S | r>0, p6:setting L27. |
| hs | S | s>0, p6:normal-form L158. |
| hh | S | Holomorphy on polyNbhd D r, p6:setting. |
| hnr expanded | S | ∀ I∈D, k∈Z_K\Λ, α≤‖k·freq h I‖; condition N1. |
| hlip expanded | S | ∀ I₀∈D, I∈polyNbhd D r, ‖I−I₀‖<r → ‖freq h I−freq h I₀‖≤L‖I−I₀‖; N2. |
| hrad | S | KLr≤α/p, p6:normal-form L158. |
| hf.differentiableOn | S | f holomorphic on Dom, p6:normal-form L158 / weighted class. |
| hf.periodic | S | ∀ j,z∈Dom, f(z.1+single j 1,z.2)=f z; period one. |
| hfb summability | S | ∀ I∈polyNbhd D r, summable weighted coefficient series. |
| hfb bound | S | ∀ I∈polyNbhd D r, Σ ‖f̂_k(I)‖exp(2πs|k|₁)≤ε. |
| hε0 | S | Nonnegative source norm, explicit guard in design's bound-predicate version. |
| hi | S | ε≤αr/(2^7 qK), p6:normal-form (i). |
| hii | S | 6≤κ, p6:normal-form (ii). |

Counts: T=12, S=17 after expanding InClass and WBound, EXCESS=0, STANDING=0, RULED=0.
There are no extra class-instance binders. NFHyp has exactly the fifteen corresponding
fields (StepsSeq:35–52); normal_form constructs every field from its own arguments.

| nonresonant_case binder / expanded property | Bin | Source / meaning |
|---|---|---|
| implicit n | T | Dimension. |
| implicit D | T | Complex action set. |
| implicit r | T | Action radius. |
| implicit s | T | Geometric angle width. |
| implicit K | T | Cutoff parameter. |
| implicit ε | T | Carried perturbation bound. |
| implicit h | T | Integrable Hamiltonian function. |
| implicit f | T | Perturbation function. |
| hfb summability | S | Finite weighted series at every action point. |
| hfb bound | S | Weighted sum≤ε at every action point. |
| hκ | S | κ<6, p6 L222. |

Counts: T=8, S=3, all other bins=0. The theorem requires neither nonresonance nor
convexity/smallness nor analyticity. This is the same stronger v2 design signature;
it does not assert the source equality of a sharp norm with an arbitrary upper bound.

For helpers, map/class/bound hypotheses are explicit premises of composition, projection,
restriction and finite-sum rules, not hidden prerequisites of the source theorem.
`nf_coeff_g` assumes NFInv (StepsSeq:131): class/bound for the current f and class/bounds
for previous projected summands. This is a conditional helper with its own name, not a
replacement source theorem; `nfConcl_caseA` supplies its input from `nf_inv_all H hN hA`.
The two case lemmas add only their named branch inequalities to the expanded NFHyp.
They are produced by `by_cases` inside normal_form. No conclusion-shaped hypothesis
survives in either public source-facing result.

All existential witnesses Ψ,g,fs occur after the full source data; no constant acquires
wider dependence. Dom uses open complex strips and max-norm action tubes; Fourier modes
are Fin n→ℤ and weights have 2πs. `IsNonresonant`, `FreqLipschitz`, `InClass`, `WBound`,
`Dom`, `polyNbhd`, `homRes` and the relevant frozen ActionNbhd/ComplexStrip definitions
retain these meanings. Fourier support is the design-approved coefficient condition on
Λ∩Z_K. The conclusion retains every map, normal-form, correction, remainder,
displacement and reality conjunct of blueprint p6 L157–172.

### Proof refutation attempts

Case A uses `N=nfSteps K s`, the proved all-step invariant, maps-to and open nested Dom
sets in `telescope`. The chain has N+1 maps, matching Φ₀ through Φ_N; g is nfG(N+1),
which is g_N under StepsSeq's indexing. Coefficient support follows the actual finite
sum, not an assumed spectral claim. Component seminorms transport the telescope bounds
with the action/angle ordering checked. The zero-step branch invokes nf_final_g_zero;
the incompatible strict Case B branch contradicts hA. Thus N=0 is not silently dropped.

Case B uses losses (r/4,s/3), restricts to (r/2,s/6), and supplies its exact g witness.
It proves the correction bound using the actual zero difference and proves the EqOn
clause by reflexivity for either side of its disjunction. The first-step case test is
literally `iterU α p ε (r/8) (s/6) < exp(-κ/6)`, as required by design audit 2 F2.
The direct step's identity, injectivity, symplectic and reality properties are consumed
with their domain inclusions. No new Arith/Steps interface premise was needed.

In nonresonant_case, ε≥0 is derived locally from the nonnegative weighted sum at the
current action point, so an empty tube is handled vacuously. The proof uses
1≤exp(1)exp(-κ/6), never the false bound exp(-κ/6) alone.

## Definition classification

There are exactly four new definitions; no abbrev, structure, instance or choice object.

| Definition | Classification and whole-carrier check |
|---|---|
| nfSteps | Literal real-expression nonnegative floor, correct for all real K,s; theorem uses K,s>0. No invented fallback. |
| NFConcl | Transparent internal proof-packaging predicate, exactly the theorem's existential conclusion. It is not a new source object or assumed result; both branches prove it and normal_form unfolds it. |
| fstSeminorm | Literal norm composed with linear first projection, valid on all complex phase space. |
| sndSeminorm | Literal norm composed with linear second projection, valid on all complex phase space. |

For each: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL;
CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.
The two seminorm evaluation theorems additionally expose their defining equations.
No junk value, conditional fallback or arbitrary witness is used by these definitions.

## Verification receipts

All final Lean commands below use `LEAN_NUM_THREADS=1` and `nice -n 5`.

Targeted build (exit 0):

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n68b KAM.Nekhoroshev.NormalForm.NormalForm
[inp-gate] slot 2 acquired 08:02:55 for KAM.Nekhoroshev.NormalForm.NormalForm
Build completed successfully (3241 jobs).
```

Exact-design application and axioms (exit 0):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N68bAudit.lean
'KAM.NormalForm.chain_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.chain_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.coeff_homRes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.coeff_sum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.inClass_mono_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.wbound_zero_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nf_coeff_g' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.fstSeminorm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.sndSeminorm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfConcl_caseA' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nfConcl_caseB' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.normal_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.nonresonant_case' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The probe imports only the built NormalForm module, reproduces the v2 signatures as
`audit_normal_form` and `audit_nonresonant_case`, and uses bodies respectively
`exact normal_form hp hα hK hL hr hs hh hnr hlip hrad hf hfb hε0 hi hii` and
`exact nonresonant_case hfb hκ`. This checks ordered explicit-binder assembly against
the independent exact signature text without importing any draft theorem.
The thirteen printed axioms sets contain only the three allowed axioms.

Kernel replay (one invocation, exit 0):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.NormalForm KAM.Nekhoroshev.NormalForm.NormalFormCaseA KAM.Nekhoroshev.NormalForm.NormalFormAux
replaying KAM.Nekhoroshev.NormalForm.NormalFormAux
replaying KAM.Nekhoroshev.NormalForm.NormalFormCaseA
replaying KAM.Nekhoroshev.NormalForm.NormalForm
```

These are independent auditor reruns, not the prover's handoff receipts.

Source lint rerun (exit 1, exactly the permitted generated-root exception):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (478 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Additional read-only checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0.
- Python full-file token scan of the three scoped files: no sorry/admit/axiom/unsafe/opaque,
  no set_option and no EuclideanSpace; no line over 100 characters. Sizes 177/147/155,
  all below 1500. Headers, module declarations, public imports, module docstrings,
  exposed public sections are present.
- Recursive project import walk from the three files visits 89 project modules and finds
  zero frozen theorem imports and zero provider imports. Consequently no DRAFT_SORRY
  anchor is imported, directly or transitively. Frozen definitions remain read-only.
- Only the report is added to the repository by this auditor. The pre-existing handoff
  is preserved; `.lake/abi-scratch/N68bAudit.lean` is deleted after successful elaboration.


## Errata, deviations and limits

No newly suspected mathematical blueprint/source defect was found. The existing p6 L173
sourcegap quotes Pöschel p194 “≤ e^{Ks/6} ε”; its preceding calculation requires the
negative exponent. The Lean statement uses the blueprint's recorded correction. This is
an existing blueprint-recorded issue, not a fresh verification of the pinned PDF.
The existing p6 deviations paragraph about derivative telescoping is not needed: this
package proves the requested component displacement estimates instead.

Auditor process deviation: the first lint command was started without explicitly setting
LEAN_NUM_THREADS=1 or nice. Its ABI subcommand briefly overlapped the first kernel replay.
The replay was terminated (exit 143); it is not a successful verification receipt.
Lint was then rerun with `LEAN_NUM_THREADS=1 nice -n 5`, and subsequent replay and probes
were serialized. This cannot be described as perfect compliance with the resource rule
throughout the turn. It does not change the audited Lean sources or theorem statements.

The expected generated-root lint exception is allowed by the audit brief; the root was
not regenerated. This package audit does not upgrade any frozen/root theorem or
independently re-audit the inherited Arith/Steps mathematics. Only this report is retained;
auditor scratch probes are removed after use.
