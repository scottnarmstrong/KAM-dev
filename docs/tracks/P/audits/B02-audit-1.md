# B02 independent package audit 1

**Overall verdict: PASS WITH NOTES for the scoped B02 infrastructure package.** Both public proof exports, `KAM.Planetary.schedule_ratios` and `KAM.Planetary.geom_recursion`, pass. N1 retains the design-required upstream formula reconciliation as an explicit consumer-release obligation. No frozen anchor or provider is part of B02, so no anchor is declared seal-ready and no P-G / planetary theorem closure is claimed.

2026-10-28. Only `KAM/Planetary/WeakKAM/Schedule.lean` is audited. The user’s exact worktree report destination overrides the generic brief’s main-worktree destination. No production sources, frozen files, manifest, generated root, README, or git state were edited.

## Authority and snapshot

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, B02-handoff.md, track-P statement, design row B02 and Appendix A, design audits 1–2, and source `blueprint-P/parts/p11a3-iteration-selection.tex` (especially L51–97, L156–165 and L233–237). Inspected the imported B01 carriers and the frozen action collar, strip, frequency and phase definitions. There is no applicable frozen theorem to match or seal.

- HEAD: `7868a90f39ddca7ed911278466a1e5cc91c0eff3`.
- Compared branch `inp`: `7ec42a1dd0f6154a1f6a357ba53d92080b367082`.
- `git diff inp...HEAD`: one new file, 248 insertions, Schedule.lean. B01 is already in the comparison base; it was inspected as a dependency, not re-audited as new work.
- Schedule SHA256: `1f95334a4cbb30208d6455a748e1f8313ae866109687d8f53c64f8779ff45dfd`.
- Live signature `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean`: `6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596`.
- Design SHA256: `8b3fd811a8c13414699fb79dc55e7b1b74e90cebf697f89e76a053ecb52c0bdd`; embedded Lean appendix equals the live signature text.

All **37 explicit declarations** have identical definition/structure bodies or theorem headers to the current signature, after removing comments and proof bodies. Separate Lean probes copy both theorem headers and apply the actual exports with the explicit binders in order. The added section variable `τ : ℝ` resolves the signature draft’s implicit-auto-binding oversight under autoImplicit=false; the elaborated schedule theorem has exactly `{n μ : ℕ} {τ : ℝ}`. No spurious τ binder appears on geom_recursion. This is the reported implementation deviation, not a stronger hypothesis.

Ownership is complete against design L228–234: B02 includes all schedule formulas, both proofs and raw chain/prefix/shell/retention data. `strip_budget`/`schedule_props` belong to B03; bump/cutoff constants and `smooth_cutoff` to B04; `finite_extension` to B05; `selectionInitial`/`initial` to B06; admissibility, adapted radius and lambdaMax definitions to B07; shell-index characterization and finite divisors to B08. Their absence here is not an incomplete B02 implementation.

## Findings and proof assessment

**N1 — upstream formula bridge remains unexported (release note).** Design L198 explicitly says: “Once P11A delivers its definitions, make these aliases or prove formula bridges against those exact definitions; never assume their equality.” Row B02 L228 lists “P11A fourier_cutoff formula.” Schedule L27–30 defines new scalar formulas and imports only Data; there is no named bridge to `p11C` / `p11Error` in `KAM/Planetary/MaximalStep/Constants.lean:L26–29`.

The formulas are mathematically and definitionally compatible. The auditor’s probe proves `selectionCN n = p11C n` by `rfl` and proves `selectionCutoffError n T d = p11Error n T d` by unfolding and `inv_pow`, for all n,T,d, without positivity hypotheses. Thus this is a missing exported identification, not a wrong constant or an unpaid analytic estimate. Before a P11A-consuming package is released, export these bridges or explicit aliases in the appropriate consumer/integration module (including B03 if it uses the upstream loss theorem). The scratch proofs are evidence only and are deleted; they do not supply a production bridge. The frozen real/complex frequency bridge also remains the separately acknowledged downstream analytic integration obligation; no B02 proof assumes it.

`schedule_ratios` derives E≥4τ+n+8 and E≥(τ+1)μ+7, writes varpi=u², q=u/4, varrho=4u for positive u=2^(-E), and bounds each growth exponent by -5. This is valid also at n=μ=1, τ=0. The source’s auxiliary α identity and immediate q/varrho corollaries are algebraic consequences, not extra assumed premises; the literal signature exports the advertised ratio bounds.

`geom_recursion` proves the geometric envelope by induction. The auxiliary product bound follows from (pv)^j≤1 and P*x0≥0; inserting c≤3v/8 gives the 7v/8 contraction, which implies the next envelope. All monotonicity uses have the necessary nonnegativity. The unused source premises v<1 and c≥0 are retained verbatim; the proof actually supports a stronger statement without them, but no signature change was made.

No new premise assumes a schedule inequality, construction, limiting torus, measure estimate or final proof step. SelectionExtensionChain and SelectionFiniteChain are explicitly conditional source-prefix predicates. The former does not demand retention, preserving the repair of design-audit F1; the latter adds exactly the source retention equation. Their eventual construction remains a later package’s theorem conclusion.

## Declaration ledger

All Lean names below are in `KAM.Planetary`; line locators refer to Schedule.lean. Source nodes have prefix `bpP:p11a:` (local steps `stepP:p11a:`).

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| `fourier-cutoff / schedule-consts` | `selectionCN` (L27) | PASS WITH NOTES | Literal P11A formula; missing named bridge, N1. |
| `fourier-cutoff / schedule` | `selectionCutoffError` (L29) | PASS WITH NOTES | Literal error formula; inverse-power bridge checked, N1. |
| `schedule-consts` | `selectionExponent` (L31) | PASS | E*=2(τ+1)(μ+1)+n+4. |
| `schedule-consts` | `selectionVarpi` (L32) | PASS | 2^(-2E*), real exponent. |
| `schedule-consts` | `selectionQ` (L33) | PASS | sqrt(varpi)/4. |
| `schedule-consts` | `selectionVarrho` (L34) | PASS | varpi/q. |
| `schedule-consts` | `selectionCQ` (L35) | PASS | 18n(4n+5). |
| `schedule-consts` | `selectionG` (L36) | PASS | Four growth factors; g4 simplifies to varrho*2^(2τ)*2^(n+1). |
| `schedule-consts` | `schedule_consts` (L40) | PASS | Formula tuple, no theorem claims hidden in fields. |
| `schedule-ratios; step:sr-exp` | `schedule_ratios` (L43) | PASS | Exact signature; positive q, four ratios, varrho bound; no extra premise. |
| `geom-recursion; step:gr-ind` | `geom_recursion` (L123) | PASS | Exact signature and all three conclusions; unused hv1/hc0 harmless. |
| `schedule` | `SelectionSchedule` (L157) | PASS | Eight raw scalar inputs; no proof fields. |
| `schedule` | `selectionT` (L167) | PASS | T0*2^j. |
| `schedule` | `selectionD` (L168) | PASS | γ*Tj^(-τ). |
| `schedule` | `selectiont` (L169) | PASS | t0*2^(-(τ+1)j). |
| `schedule` | `selectionε` (L171) | PASS | ε0*varpi^j. |
| `schedule` | `selections` (L173) | PASS | s0*q^j. |
| `schedule` | `selectionσ` (L174) | PASS | strip/24*2^(-j); δ=σ in source. |
| `schedule` | `selectiond` (L175) | PASS | Source log(2cN/α), with α=varpi/8. |
| `schedule` | `selectionr` (L178) | PASS | Finite strip-loss sum; r0=strip and recurrence recoverable. |
| `schedule` | `selectionell` (L180) | PASS | 2εj/sj. |
| `schedule` | `selectionTail` (L182) | PASS | Shifted natural-index tsum equals source tail under summability. |
| `schedule` | `selectionQsharp` (L183) | PASS | Source Qsharp with δ=σ. |
| `schedule` | `selectionQ₀` (L186) | PASS | Expanded stage-zero Qsharp. |
| `schedule` | `schedule` (L189) | PASS | Identity carrier alias; actual sequences supplied by preceding definitions. |
| `sec-retained#data` | `SelectionChain` (L192) | PASS | Raw sets and functions only; no existence or inequality fields. |
| `sec-retained#data` | `selectionFrequency` (L199) | PASS | Complex gradient plus prefix increments. |
| `sec-retained#data` | `selectionEnergy` (L202) | PASS | Prefix sum Δh; stage zero zero, as source h0=0. |
| `sec-retained#data` | `selectionCompose` (L204) | PASS | X0 ∘ ... ∘ X(j-1), correct composition order. |
| `schedule / sec-retained#data` | `selectionModeLength` (L209) | PASS | Explicit integer-mode l1 length, no ambient norm change. |
| `schedule / sec-retained#data` | `selectionShell` (L210) | PASS | 0<length≤Tj; strict previous cutoff when j>0; shell zero special case. |
| `schedule / sec-retained#data` | `selectionModeStage` (L214) | PASS | Natural ceiling of log2(length/T0); characterization belongs to B08. |
| `sec-retained#data / finite-extension` | `selectionExtendedFrequency` (L216) | PASS | Real frequency plus real cutoff-weighted finite increments. |
| `sec-retained#data / retained-def` | `selectionRetained` (L221) | PASS | Subset of Kj with all shell tests, margin 2γ and complex absolute value. |
| `sec-retained#data / finite-extension` | `SelectionExtensionChain` (L227) | PASS | Exactly initial, compact, nonempty, nested, holomorphic, real, bound; no resonance. |
| `sec-retained#data / retained-def` | `SelectionFiniteChain` (L242) | PASS | Analytic prefix plus literal shell retention; generated weaker-prefix projection. |
| `sec-retained#data` | `sec_retained_data` (L246) | PASS | Identity raw-chain alias; no concealed theorem. |

## Definition classification and totality

The 35 non-theorem declarations comprise 31 definitions and four structures. Scalar constants, error expressions and schedule sequences are literal numerical formulas; mode length is the l1 norm of the integer vector; shells and retention are literal set predicates; frequency/energy are finite prefix sums; composition is primitive recursion with the intended order. `schedule` and `sec_retained_data` are transparent identity aliases, not proofs. `SelectionSchedule` and `SelectionChain` store raw data; the two Prop structures store exactly the source analytic and retained-prefix premises.

All use existing Pi/Prod carriers with max norms; no EuclideanSpace or new norm instance occurs. Divisions, real logs/powers and fderiv are Lean’s standard total operations outside the source-admissible region. `selectionTail` is a standard tsum (no convergence claim is made here). `selectionModeStage` is total even for zero modes or invalid schedules; its source interpretation is restricted to nonzero modes with T0≥1, to be proved in B08. No B02 theorem exploits a zero denominator, divergent tsum, non-differentiable fallback or invalid shell. `selectionExtendedFrequency` is the intended globally defined product using total increments; B04/B05 must prove cutoff support so exterior arbitrary function values cannot affect the source extension. These obligations are not bundled as proof fields or silently claimed here.

## Independent validation

All Lean/Lake work was serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No unbounded/full-library build or cache regeneration was run. The targeted build reported replay of the requested module and its existing dependency snapshot.

1. Targeted compile gate:
   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b02 KAM.Planetary.WeakKAM.Schedule
   ```
   Exit **0**. Output: `[inp-gate] slot 2 acquired 15:31:25 for KAM.Planetary.WeakKAM.Schedule`; `⚠ [9080/9080] Replayed KAM.Planetary.WeakKAM.Schedule`; warnings at L123:51 (`hv1`) and L124:5 (`hc0`), both “Variable name ... is not explicitly referenced”; `Build completed successfully (9080 jobs).` The wrapper invokes `nice -n 5 lake build`.

2. Theorem-type, axiom and formula-identity probes:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B02Audit.lean
   ```
   Exit **0**. The initial probe included full `#print` proof output; a second run used `#check @...` to obtain concise, untruncated type/axiom evidence. Both passed. The final output includes:
   ```text
   'KAM.Planetary.schedule_ratios' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.geom_recursion' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
   The copied signature declarations apply `schedule_ratios hn hμ hτ` and `geom_recursion hv hv1 hc0 hc hP hp hpv x hx hzero hrec` successfully. The same probe checks these all-carrier identities:
   ```lean
   example (n : ℕ) : selectionCN n = p11C n := rfl
   example (n : ℕ) (T d : ℝ) : selectionCutoffError n T d = p11Error n T d := by
     simp only [selectionCutoffError, p11Error, selectionCN, p11C, inv_pow]
   ```
   These are the only two new explicit public theorems in B02. No provider/frozen seal probe applies because this package proves no frozen export. Auditor probe removed after validation.

3. One kernel replay invocation, covering the complete scoped lemma module:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Schedule
   ```
   Exit **0**; exact output: `replaying KAM.Planetary.WeakKAM.Schedule`.

4. Source lint, run serially after kernel replay:
   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```
   Exit **1**, solely the explicitly permitted stale generated-root exception. Exact substantive output:
   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (773 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```
   No generated file was regenerated. An earlier lint invocation was stopped before its ABI/Lean subprocess so all Lean work remained serial; the complete invocation above ran after kernel replay and supplied these final results.

5. Static/read-only checks: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty; `git diff --check` exits **0**, no output. Module header, public import, docstring, public noncomputable section and `@[expose]` are present. File length is **248**. Forbidden-token scan finds no sorry/admit/axiom/unsafe/opaque/resource override/EuclideanSpace. Recursive KAM import closure has **34 modules**, no provider and no frozen theorem, hence no imported DRAFT_SORRY anchor. Imported frozen definitions are unchanged and covered by the guard/ABI checks.

6. Name inventory: searched explicit declarations throughout KAM. No new fully qualified name is already declared elsewhere. `schedule` has an existing short-name homonym `KAM.Apost.schedule` in `KAM/Apost/Schedule.lean:L114`; the new name is `KAM.Planetary.schedule`, exactly the approved signature. This is not a namespace collision or an accidental replacement. All 37 declarations are accounted for in the table.

## Errata, deviations and remaining scope

No new suspected pinned-source defect or false blueprint statement was found. N1 is the design’s existing uncompleted integration requirement, with exact locations, quoted requirement and successful scalar-identity evidence above. The only implementation deviation is the explicitly declared implicit section variable τ. No heartbeat, recursion-depth or synthesis-heartbeat override was introduced; no default-heartbeat failure occurred.

This audit certifies B02’s definitions and two proofs, with the stated bridge-release note. It does not certify B03–B20, the construction of a valid schedule or infinite chain, P11A analytic suppliers, or any frozen planetary anchor.
