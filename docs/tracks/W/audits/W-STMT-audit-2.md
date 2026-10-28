# Independent delta statement audit W-STMT-2
PASS WITH NOTES

Audited `/root/code/KAM-w`, branch `w`, HEAD `29a21098dc22343d4954161106eedbfa495eefab`, on 2026-10-28 under `.drafts/briefs/W-STMT-delta2.md`. W-ST1 and W-ST2 are fixed; no new material carrier defect or headline mismatch was found. The remaining note is the already known repository ABI-lint failure W-ST4. This is statement approval evidence, not a theorem proof, owner approval, freeze, or full repository validation.

Only this report is a repository deliverable. No draft, source, frozen file, manifest, generated root, or ledger was edited; no commit was made. Transient oleans and probes were written outside the repository at `/tmp/w-stmt-audit2-h2z5ud5r`. Initial `git status --short` was empty.

## Findings and requested-item verdicts

Draft file paths below are relative to `.drafts/W/KAM/Wave/`.

| ID / item | Verdict | Exact evidence and disposition |
|---|---|---|
| W-ST1: positive actions | PASS, CLOSED | `Defs/LinearTorus.lean:28` requires `_hI : ∀ i, 0 < I i`. Negative and zero actions have no guard witness; no public unguarded alternative exists. `Theorems/Nlw2.lean:50–53` threads the guard in the conclusion. |
| W-ST2: positive mass | PASS, CLOSED | `Lam:25`, `ReconU:27`, `ReconV:27`, `CubicGrad:24`, `IsClassicalSolution:28` all carry `0 < m`. These are every definition using mass. The theorem still assumes just `hm : 0 < m`. |
| All 11 definitions / other fallbacks | PASS | Whole-carrier checks below cover weights, decoded coefficients, reconstruction, integrability, generic embedding predicate, and derivative totalization. No additional meaningless permitted input was found. |
| Headline / clauses (1)–(6) | PASS | Compared the current actual theorem to `blueprint-W/parts/w-headline.tex:13–70`, revision 1, and the documented diff `git diff a6ea781 HEAD -- docs/tracks/W/W-STATEMENTS.md`. Only guard threading and the equivalent clause-(3) quantifier change affect the mathematical text. |
| Independent elaboration / counterexamples | PASS | Frozen dependency, 11 definition files, and theorem each exit 0 in dependency order. Probe exits 0; old calls fail at the new proof slots and their missing positivity claims are disproved. |
| W-ST3: receipt count / axioms | PASS, CLOSED | Revision 1 explicitly corrects the historical receipt: 11 definition files + 1 theorem, 438 physical lines, maximum 79. Independent axiom output below confirms definitions have no `sorryAx`; theorem does. |
| Q1–Q5 | PASS | Actual revision brief's orchestrator rulings and `W-STATEMENTS.md:320–326` agree; these are recorded for owner review, not represented as exact-text owner approval. |
| W-ST4: global lint ABI | NOTE, OPEN | Independent lint rerun fails at missing built `KAM` modules, after module-system and frozen-anchor checks pass. The revision brief explicitly says to note this and not build the library. No global lint/ABI PASS is claimed. |

## Authority and snapshot

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` including D30, the delta brief, the full first audit, revision brief, original and revision handoff, current `W-STATEMENTS.md`, all 12 actual drafts, the three blueprint parts, and the reused frozen `KAM.IsDiophantine` definition. The first audit and designer receipts were treated as claims to verify. This delta checks the unchanged revision-1 blueprint; it does not reopen the earlier pinned-source normalization audit or certify the future PDE KAM proof.

| Artifact | SHA256 |
|---|---|
| `blueprint-W/parts/w-headline.tex` | `fdbd3af8aba7360e7c9e41f7adfe5b821f2983daf84a134ccefda7f6bf8de410` |
| `blueprint-W/parts/w0-conventions.tex` | `016d51ed338af4b0dd7192cf82bc2f29783bac56e1405d5bb8542f22b9d2330d` |
| `blueprint-W/parts/w0-normalization.tex` | `83719844737c92a00fc571cea8395ddb4431c063daf3dbefaf8462d5f96ab21a` |
| `docs/tracks/W/W-STATEMENTS.md` | `3e6e698a076606b9f79e2a48cced8a6c1728af818746e1f59e9b6f0bae00fc30` |
| `Theorems/Nlw2.lean` | `7a77905577cfa3e6b59b3deb7c06fce7c09b738ab3ccec8be20280f99f04c7b9` |

Independent Python extraction of each actual `namespace KAM.Wave ... end KAM.Wave` declaration block, compared with the Markdown Lean fences, returned `True` for all 12 files (outer whitespace stripped). Headers/imports/section wrappers were checked in the actual files. No drift between the reviewed declarations and the Markdown proposal was found.

## Every public definition: whole-carrier review

All constructions are explicit formulas or predicates: none chooses an object using a deferred existence/uniqueness characterization. Thus choice-independence obligations for characterized objects are inapplicable. Their ordinary classical implementation axioms are listed below.

| Definition | Carrier / body / well-definedness | Verdict |
|---|---|---|
| `lam` | Real `m` plus proof `0<m`, positive integer `j`; body `√(j²+m)`. Radicand strictly positive. Guard unused computationally but mandatory for application. | PASS |
| `sineMode` | `j:ℕ+`, `x:ℝ`; normalized `√(2/π) sin(jx)` is meaningful for all real x, including values outside the PDE interval needed for local analyticity. No zero mode, bad square root, or denominator. | PASS |
| `ellWeight` | Every real `a,p` and positive integer j gives the strictly positive finite weight `j^p exp(aj)`. The blueprint restricts weighted-space parameters to `a≥0`, but the standalone weight formula is meaningful also for negative a. It creates neither a sequence-space assertion nor a singularity there. | PASS |
| `WaveSpace` | Exactly two real `lp 2` spaces on positive integers, product max norm, representing `E_{1,1}` by weighted coordinates. Every point has precisely one decoded coefficient pair; no unrestricted raw sequence is mistaken for a summable one. | PASS |
| `coeff` | An actual ℓ² coordinate divided by `j exp(j)>0`. Weighting its output recovers the input point coordinatewise; its weighted squared sum is the input ℓ² sum. No division-by-zero branch or default coefficient. | PASS |
| `reconU` | Positive mass, ℓ² weighted coordinate, any real x; exponential coefficient decay and positive frequency imply absolute uniform convergence, including all fixed spatial derivatives. | PASS |
| `reconV` | Same carrier; multiplication by `√λ_j` only adds polynomial growth, absorbed by exponential decay. Absolute uniform convergence holds for every permitted input. | PASS |
| `cubicGrad` | Same positive mass and decoded sequence; reconstruction is continuous on `[0,π]`, so its cube times a sine mode is integrable. Division by `√λ_l>0`. The literal gradient of `¼∫U⁴` is exactly this formula, with positive cubic force and no extra factor. | PASS |
| `linearTorus` | Strictly positive two actions, all real angles; finite supported ℓ² sums store `w_j√(2I_i)cos(2πθ_i)` and `−w_j√(2I_i)sin(2πθ_i)` in modes 1 and 2. All square roots are positive; higher modes zero. | PASS |
| `IsAnalyticTorusEmbedding` | A predicate on maps to any real normed vector space: period one, local real power series, injectivity modulo integers, injective derivative. It remains meaningful without a completeness instance; its claimed holomorphic-extension equivalence is used only for complete Banach targets, in particular `WaveSpace`. | PASS |
| `IsClassicalSolution` | Positive mass guard now included as ruled; exact named derivative witnesses, five joint continuity requirements, equation `utt=uxx−m*u−u³`, and endpoint conditions. Arbitrary candidate u is a meaningful input to a predicate, which can be false. | PASS |

For the weighted-coordinate identification, set `w_j=j exp(j)`. The inverse maps are `q_j=y_j/w_j` and `y_j=w_j q_j`, with `Σ|q_j|²w_j²=Σ|y_j|²`; the norm and complete real Banach structure are preserved. `Prod` uses the max norm, also checked by `rfl` in Lean. This is mathematical verification of an explicit representation, not a claim that reusable transport lemmas have already been formalized.

For reconstruction, `j≤λ_j≤√(1+m)j`, and `|y_j|≤‖y‖₂`; hence decoded coefficients and every fixed spatial derivative are bounded by a constant times a polynomial in j times `exp(−j)`. These bounds are summable uniformly for all real x. Thus neither `tsum`'s nonsummability value nor the integral's nonintegrability value occurs on the permitted carriers. `cubicGrad` has a raw coordinate-sequence output, as needed in (4); smoothing membership is future infrastructure, not an omitted headline conjunct.

`fderiv` is a total operation in Mathlib. If a candidate K were nondifferentiable at θ, its `fderiv` there would be zero, which cannot be injective on the nontrivial domain `Fin 2 → ℝ`. Thus derivative totalization cannot falsely certify an immersion, including for an incomplete generic target. Local real analyticity and immersion are asserted, not supplied as hidden hypotheses. Off-interval arbitrary u or derivative-witness values do not affect the classical-solution predicate. No extra carrier restriction is needed for these candidate-map predicates.

The added guard arguments are proof-irrelevant. In particular, `linearTorus I h₁ θ = linearTorus I h₂ θ` and `lam m h₁ j = lam m h₂ j` were checked by `rfl`. A mandatory proof slot does not become optional because its body ignores the proof. Assuming false positivity externally would add an inconsistent premise; no such premise exists here.

## Headline premises, quantifiers and six clauses

The entire input surface is `{m : ℝ}` (TYPING) and `(hm : 0 < m)` (SOURCE, blueprint standing mass convention). Counts remain SOURCE 1, STANDING 0, TYPING 1, RULED 0, EXCESS 0 under the package's binder classification. There are no new input structures, typeclasses, or conclusion-shaped premises. The `hI` of clause (3) is bound inside the conclusion.

Existentials remain `r₀,C,τ,η,Γ,ν,K`, in that order, after m and before all family parameters/angles. Constants may depend on m. The Diophantine γ is chosen per I, while τ is common. Output witnesses η,ν,K are represented as total functions and constrained on the displayed sets; restricting/extending them preserves the blueprint's restricted-domain data.

| Part | Actual theorem lines | Blueprint lines | Comparison / verdict |
|---|---|---|---|
| Preamble | 36–42 | 42–45,69–70 | PASS: positive r₀,C, τ>1; nonnegative η locally and right limit zero; Borel Γ inside the positive small-action region; frequency continuity and joint-family continuity. |
| (1) | 44–45 | 47–48 | PASS: Lebesgue density one in sup-norm balls. For h>0 the positive-quadrant denominator is h², finite and positive. ENNReal division and convergence therefore have exactly the real-ratio meaning here. |
| (2) | 47–48 | 49–50 | PASS: frozen flow-Diophantine ℓ¹ convention, positive γ per torus, common τ>1, leading frequency limit `λ/(2π)` along Γ. |
| (3) | 50–53 | 51–52 | PASS: same embedding and both bounds, with the same C,η and `r=√(I₀+I₁)`. Only positivity data was added to use the corrected linear torus. |
| (4) | 55–59 | 53–55 | PASS: directional derivatives of all decoded coordinates, `λP` and `−λQ−G`, at every angle. Coordinate evaluation/decoding is bounded linear, and the asserted analytic embedding gives the differentiability needed to identify these with `DK·ν`. No sign, mode, or time-unit change. |
| (5) | 61–71 | 56–60 | PASS: joint local analyticity at every point of `ℝ×[0,π]`, global classical solution, exact reconstructed velocity, and the three-term uniform bound. Spatial derivatives within the interval agree with the classical witness, including endpoints by derivative uniqueness on this nondegenerate interval. |
| (6) | 73–74 | 61–63 | PASS: equality of any two family points implies equal actions and integer angle difference. Neither family disjointness nor embedding is lost. |

For clause (3), let `HΓ : Γ ⊆ {I | ∀i,0<I i}` be supplied by line 41. A guarded statement `∀ I hI, I∈Γ → F I hI` implies `∀ I (h:I∈Γ), F I (HΓ h)` by instantiation. Conversely the latter implies the former because proofs of positivity are propositionally irrelevant. This equivalence was independently proved in the probe with no `sorry`. It does not assume positivity of arbitrary actions or add positivity to the theorem's input premises.

Pointwise bounds for all angles/times are equivalent to the blueprint supremum bounds on their nonempty domains. Density one rules out an empty/null Γ or one avoiding a neighbourhood of zero, makes the frequency limit nonvacuous, and forces parameters arbitrarily close to zero. Diophantine positivity excludes rational dependence, embedding excludes constant K, and (6) excludes a family constant in I. η's right limit prevents a fixed nonvanishing relative error. No new vacuity loophole was found.

The source weakenings remain exactly those declared in blueprint lines 82–100: pure cubic, modes `{1,2}`, weights a=p=1, period-one angles, Borel density-one actions, little-o closeness, and deferral of linear stability, Whitney regularity and family Lipschitz regularity. These were not silently restored or further weakened.

## Independent elaboration and probes

No `lake build` was run: these are draft modules outside the library root, and the brief specifically prescribes scratch elaboration and prohibits rebuilding the library for W-ST4. Every Lean invocation below was serialized, single-threaded, at default heartbeat/recursion settings. The frozen dependency was read-only and its artifacts went to scratch.

Exact shell command template, run from `/root/code/KAM-w`, with `M` and `F` replaced by the two columns below:

```bash
LEAN_NUM_THREADS=1 nice -n 5 lake env bash -c \
  'export LEAN_PATH="$LEAN_PATH:$1"; exec lean -o "$1/$2.olean" -i "$1/$2.ilean" "$3"' \
  bash /tmp/w-stmt-audit2-h2z5ud5r M F
```

Parent output directories were created in scratch before each command. There was one Lean process at a time.

| M (dependency order) | F | Exit / output |
|---|---|---|
| `KAM/Frozen/Defs/IsDiophantine` | `KAM/Frozen/Defs/IsDiophantine.lean` | 0; no output |
| `KAM/Wave/Defs/Lam` | `.drafts/W/KAM/Wave/Defs/Lam.lean` | 0; no output |
| `KAM/Wave/Defs/SineMode` | `.drafts/W/KAM/Wave/Defs/SineMode.lean` | 0; no output |
| `KAM/Wave/Defs/EllWeight` | `.drafts/W/KAM/Wave/Defs/EllWeight.lean` | 0; no output |
| `KAM/Wave/Defs/WaveSpace` | `.drafts/W/KAM/Wave/Defs/WaveSpace.lean` | 0; no output |
| `KAM/Wave/Defs/Coeff` | `.drafts/W/KAM/Wave/Defs/Coeff.lean` | 0; no output |
| `KAM/Wave/Defs/ReconU` | `.drafts/W/KAM/Wave/Defs/ReconU.lean` | 0; no output |
| `KAM/Wave/Defs/ReconV` | `.drafts/W/KAM/Wave/Defs/ReconV.lean` | 0; no output |
| `KAM/Wave/Defs/CubicGrad` | `.drafts/W/KAM/Wave/Defs/CubicGrad.lean` | 0; no output |
| `KAM/Wave/Defs/LinearTorus` | `.drafts/W/KAM/Wave/Defs/LinearTorus.lean` | 0; no output |
| `KAM/Wave/Defs/IsAnalyticTorusEmbedding` | `.drafts/W/KAM/Wave/Defs/IsAnalyticTorusEmbedding.lean` | 0; no output |
| `KAM/Wave/Defs/IsClassicalSolution` | `.drafts/W/KAM/Wave/Defs/IsClassicalSolution.lean` | 0; no output |
| `KAM/Wave/Theorems/Nlw2` | `.drafts/W/KAM/Wave/Theorems/Nlw2.lean` | 0; warning at `Nlw2.lean:36:8`: declaration uses `sorry` |

The theorem warning is the allowed unfrozen draft body, not an elaboration failure. No heartbeat failure occurred. All files have copyright, `module`, public imports, module docstring and public section; definitions are exposed. No forbidden proof escape, resource override, provider import or `EuclideanSpace` occurs in draft code. The single theorem `sorry` is explicitly permitted for this audit's unfrozen draft; it is not permission to place it in the production library.

The exact independent probe follows; it also prints axioms for all twelve declarations.

```lean
import KAM.Wave.Theorems.Nlw2
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
open KAM.Wave
#check_failure (lam (-1) 1)
#check_failure (cubicGrad (-1) 0 1)
#check_failure (linearTorus (fun _ => -1) (fun _ => 0))
#check lam 1 one_pos 1
#check reconU 1 one_pos 0 0
#check reconV 1 one_pos 0 0
#check cubicGrad 1 one_pos 0 1
#check linearTorus (fun _ => 1) (fun _ => one_pos) (fun _ => 0)
#check IsClassicalSolution 1 one_pos (fun _ _ => 0)
example : ¬ (0:ℝ) < -1 := by norm_num
example : ¬ (0:ℝ) < -2 := by norm_num
example : ¬ (0:ℝ) < 0 := lt_irrefl _
example : ¬ ∀ i : Fin 2, (0:ℝ) < -1 := by norm_num
example : ¬ ∀ i : Fin 2, (0:ℝ) < 0 := by norm_num
example (m : ℝ) (hm : 0 < m) (j : ℕ+) : 0 < lam m hm j := by
  unfold lam
  apply Real.sqrt_pos.2
  positivity
example (a p : ℝ) (j : ℕ+) : 0 < ellWeight a p j := by
  unfold ellWeight
  positivity
example (I : Fin 2 → ℝ) (h₁ h₂ : ∀ i, 0 < I i) (θ : Fin 2 → ℝ) :
    linearTorus I h₁ θ = linearTorus I h₂ θ := rfl
example (m : ℝ) (h₁ h₂ : 0 < m) (j : ℕ+) : lam m h₁ j = lam m h₂ j := rfl
example (y z : lp (fun _ : ℕ+ => ℝ) 2) :
    ‖((y,z) : WaveSpace)‖ = max ‖y‖ ‖z‖ := rfl
example (Γ : Set (Fin 2 → ℝ)) (hΓ : Γ ⊆ {I | ∀ i, 0 < I i})
    (F : (I : Fin 2 → ℝ) → (∀ i, 0 < I i) → Prop) :
    (∀ I hI, I ∈ Γ → F I hI) ↔ (∀ I (h : I ∈ Γ), F I (hΓ h)) := by
  constructor
  · intro h I hmem
    exact h I (hΓ hmem) hmem
  · intro h I hI hmem
    exact h I hmem
#print axioms KAM.Wave.lam
#print axioms KAM.Wave.sineMode
#print axioms KAM.Wave.ellWeight
#print axioms KAM.Wave.WaveSpace
#print axioms KAM.Wave.coeff
#print axioms KAM.Wave.reconU
#print axioms KAM.Wave.reconV
#print axioms KAM.Wave.cubicGrad
#print axioms KAM.Wave.linearTorus
#print axioms KAM.Wave.IsAnalyticTorusEmbedding
#print axioms KAM.Wave.IsClassicalSolution
#print axioms KAM.Wave.nlw2
```

Exact invocation:

```bash
LEAN_NUM_THREADS=1 nice -n 5 lake env bash -c \
  'export LEAN_PATH="$LEAN_PATH:$1"; exec lean "$1/Probe.lean"' \
  bash /tmp/w-stmt-audit2-h2z5ud5r
```

Exit **0** on the first run. `#check_failure` deliberately prints the rejected-call diagnostics: the numeric/function argument cannot inhabit the required positivity proposition. The old cubic call additionally misaligns the remaining arguments, so that diagnostic alone would not establish carrier safety; the explicit negative/zero positivity refutations and actual signatures supply that evidence. The pretty-printer's recovered `sorry` inside rejected terms is error recovery, not an accepted definition body or theorem proof. Positive instances all typecheck. Two unused-bound-variable linter warnings occur only in the transient refutation examples. Positive frequencies, positive weights, proof-irrelevance equalities, the max norm identity, and the guarded-quantifier equivalence are all proved without `sorry` in this probe.

Axiom results, independently printed:

- `nlw2`: `[propext, sorryAx, Classical.choice, Quot.sound]`.
- Every one of `lam`, `sineMode`, `ellWeight`, `WaveSpace`, `coeff`, `reconU`, `reconV`, `cubicGrad`, `linearTorus`, `IsAnalyticTorusEmbedding`, `IsClassicalSolution`: `[propext, Classical.choice, Quot.sound]`.

Thus “definitions none” means no draft hole or added project axiom; it does **not** mean literally axiom-free. No theorem proof or kernel closure is claimed from this elaboration.

## Q1–Q5 and handoff

| Question | Recorded ruling | Check |
|---|---|---|
| Q1 | Weighted coordinates accepted; freeze `WaveSpace` and `coeff` together as separately versioned anchors. | PASS: exact representation and intended anchor granularity recorded. No actual freeze performed. |
| Q2 | Require strictly positive actions by proof argument or subtype. | PASS: proof argument selected, Γ remains a set in real two-space for volume. |
| Q3 | Total η with local constraints accepted. | PASS: unused extensions cannot affect the local limit or family bounds. |
| Q4 | `AnalyticOnNhd ℝ` / `AnalyticAt ℝ` for actual Banach targets; no uniform strip inferred. | PASS: actual headline target is complete. Generic predicate remains meaningful; documentation's Banach equivalence is qualified. |
| Q5 | Proposed frozen paths `KAM/Frozen/Wave/Defs/...` and `KAM/Frozen/Wave/Theorems/Nlw2.lean`, namespace `KAM.Wave`. | PASS: all actual draft header comments agree; current draft imports still intentionally use draft module paths. Final relocation/import rewriting needs the usual freeze validation. |

The original historical handoff paragraphs still contain the old count and “not applicable” axiom statement, but the appended Revision 1 explicitly corrects both, as the revision brief requested. The current statement document contains the corrected count and axiom receipt. W-ST3 is closed; these historical paragraphs must not be read as the current receipt.

No new suspected pinned-source erratum was discovered in this delta. Previously recorded normalization/sign issues remain outside this delta's reopening scope. No mathematical deviation was introduced by the auditor. Designer deviations remain the explicit weighted encoding, directional coordinate derivatives, velocity bound via reconstruction, and the now source-faithful carrier guards. Analytic transport, summability/smoothing lemmas and the full PDE KAM proof still need formal proof; they were not supplied by these literal definitions or by a successful draft elaboration.

`DECLARATION_FIDELITY: PASS`

`DRAFT_ALLOWLIST: PASS` under the explicit audit brief; no owner approval/freeze is inferred.

`PROOF_STATUS: DRAFT_UNFROZEN_UNPROVED`

## Repository gate and final validation

Exact gate command: `LEAN_NUM_THREADS=1 scripts/lint_sources.sh`, exit **1**. Output:

```text
check_lean_modules: PASS (417 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
/root/code/KAM-w/.lake/abi-scratch/tmpfnhmnrxp.lean:1:0: error: unknown module prefix 'KAM'

No directory 'KAM' or file 'KAM.olean' in the search path entries:
/root/code/KAM/.lake/packages/Cli/.lake/build/lib/lean
/root/code/KAM/.lake/packages/batteries/.lake/build/lib/lean
/root/code/KAM/.lake/packages/Qq/.lake/build/lib/lean
/root/code/KAM/.lake/packages/aesop/.lake/build/lib/lean
/root/code/KAM/.lake/packages/proofwidgets/.lake/build/lib/lean
/root/code/KAM/.lake/packages/importGraph/.lake/build/lib/lean
/root/code/KAM/.lake/packages/LeanSearchClient/.lake/build/lib/lean
/root/code/KAM/.lake/packages/plausible/.lake/build/lib/lean
/root/code/KAM/.lake/packages/mathlib/.lake/build/lib/lean
/root/code/KAM-w/.lake/build/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean
```

This gate excludes `.drafts`; its successful early stages do not substitute for the independent draft checks above. The only allowed library dependency was elaborated read-only into scratch. No full library build, clean, root regeneration or frozen-file mutation was attempted.

Final checks: `git diff --check` exits **0**, no output. `git diff --no-index --check /dev/null /root/code/KAM-w/docs/tracks/W/audits/W-STMT-audit-2.md` exits **1**, no output: the file is new, with no whitespace-error diagnostic. `git status --short` shows only `?? docs/tracks/W/audits/W-STMT-audit-2.md`. Branch and HEAD remain unchanged. The report title is immediately followed by `PASS WITH NOTES`. Scratch artifacts were retained outside the repository for reproducibility and are not deliverables.
