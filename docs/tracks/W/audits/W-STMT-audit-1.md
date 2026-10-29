# Independent statement audit W-STMT-1
FAIL

Audited `/root/code/KAM-w`, branch `w`, HEAD `926e73931cc35c3bdde55ead090c7fe8ce0928fe`, on 2026-10-28, under `.drafts/briefs/W-STMT-audit.md`. Only this report is a repository deliverable; no source, draft, frozen file, manifest, or approval record was edited, and no commit was made. Transient elaboration artifacts and probes were placed outside the repository in `/tmp/w-stmt-audit-dqbtx6j5` and removed after checking.

The theorem's premises, witness order and clauses (1)–(6) match blueprint revision 1 on the intended positive-mass, positive-action domains. **The draft package fails the required whole-carrier definition audit:** `linearTorus` silently clamps negative actions, and the mass-dependent definitions admit masses at which their source oscillator coordinates cease to exist. These are definition-domain defects, not counterexamples to the positive-mass PDE theorem. Passing elaboration does not waive them. Nothing here is owner-approved, manifested, frozen, or proved.

## Findings

Paths beginning `Defs/` and `Theorems/` in tables are relative to `.drafts/W/KAM/Wave/`.

| ID | Severity | File:line | Claim | Evidence | Required fix |
|---|---|---|---|---|---|
| W-ST1 | BLOCKER | `Defs/LinearTorus.lean:28–32`; `docs/tracks/W/W-STATEMENTS.md:302–303` | The public action carrier is broader than the source object, with a material zero fallback. | Blueprint `w-headline.tex:18–19` and `w0-conventions.tex:140–142` define the torus for positive actions. The draft accepts all real actions. At `I=(−1,−1)`, it returns zero for every angle, since `Real.sqrt (−2)=0`. Its docstring's nonnegative-action restriction is not a binder. A Lean probe verifies the zero output. | Restrict the source-facing action argument to positive actions, or supply positivity proof arguments. Nonnegative actions are an alternative only with an explicitly adopted extension of the blueprint to degenerate linear tori. Thread the existing `I∈Γ` positivity into the use in (3); do not add a new headline hypothesis. Re-audit the exact successor before approval. |
| W-ST2 | BLOCKER | `Defs/Lam.lean:24–25`, `Defs/ReconU.lean:27–28`, `Defs/ReconV.lean:27–28`, `Defs/CubicGrad.lean:24–25` | The positive-mass standing convention is absent from the public definition carriers. | `w0-conventions.tex:24–26,39–41,75–80,96–100` and `w0-normalization.tex:3` fix `m>0`. Nevertheless each definition accepts arbitrary real `m`. For `m=−1,j=1`, `lam=0`; the reciprocal square-root reconstruction and gradient use Lean's division-by-zero value. The probe proves `cubicGrad (−1) y 1=0` for every `y`. At `m=−2,j=1`, the nominal real frequency clamps a negative radicand to zero. The source's positive frequency and invertible symplectic rescaling do not exist on this carrier. | Carry a positive-mass subtype or an explicit `hm : 0<m` through these source-facing definitions. This is the existing source standing premise, not an extra conclusion-shaped assumption. Do not rely only on the eventual theorem's `hm` to certify the definitions on their whole carriers. |
| W-ST3 | NOTE | `.drafts/handoff-W-STMT.md`, Checks; `W-STATEMENTS.md:45–47` | The handoff's definition count and axiom-check dismissal need correction. | There are **11 definition files plus one theorem**, 436 physical lines total, not 12 definition files. `#print axioms` is applicable to a draft and independently reports `sorryAx` for `nlw2`; definitions have no `sorryAx`. | Correct the receipt count and record draft axiom status. Neither issue changes the mathematical type. |
| W-ST4 | NOTE | `scripts/lint_sources.sh` ABI stage | Full repository lint is not certified. | Independent run exits 1 after module and frozen-byte checks pass; ABI elaboration reports `unknown module prefix 'KAM'`. | Restore the normal built-artifact environment and rerun lint before landing/freezing. Do not rebuild the library from scratch for this audit. |

## Identity and source control

I read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (including D30), the brief and handoff, all three named blueprint parts, `W-STATEMENTS.md`, both W-BP0 audits, every actual draft, and the frozen `KAM.IsDiophantine` body. Earlier audit verdicts were context, not substitutes for checking the actual declarations and source formulas.

P96-W is the local pinned `/root/code/KAM/sources/pdf/poschel1996_wave_CMH_71_269.pdf`, SHA256 `77f083dc4f3d45802460c880a588ef227065810aa93cc963ff7684714d25d6a2`. I inspected its existing page images `.drafts/audit-img/w{5,6,10,11,13,22}.png`: printed pp. **272,273,277,278,280,289** (PDF page +267). These supply the family theorem/density/Diophantine claims, basis and reconstruction, physical Hamilton equations, gradient formula (7), quartic energy (9), and the family embedding with linearizing parametrization. No printed inconsistent action/twist normalization was substituted into the drafts. The current revision-1 blueprint is the exact statement comparison target, with its declared weakenings.

| Snapshot | SHA256 |
|---|---|
| `blueprint-W/parts/w-headline.tex` | `fdbd3af8aba7360e7c9e41f7adfe5b821f2983daf84a134ccefda7f6bf8de410` |
| `blueprint-W/parts/w0-conventions.tex` | `016d51ed338af4b0dd7192cf82bc2f29783bac56e1405d5bb8542f22b9d2330d` |
| `blueprint-W/parts/w0-normalization.tex` | `83719844737c92a00fc571cea8395ddb4431c063daf3dbefaf8462d5f96ab21a` |
| `docs/tracks/W/W-STATEMENTS.md` | `c2a0b27a57f435748a5f11bc8059a35890ddf351c9ea08b3cddebcd38c084f3f` |
| `Theorems/Nlw2.lean` | `cef049d6b549e4cb323267fc03be6bf0f89df8219cfdca5951fdbde11b87942a` |

All 12 actual declaration commands, including their complete bodies, occur verbatim in the corresponding Markdown Lean fences. The Markdown omits file headers/imports/section wrappers; the actual files, not those excerpts, were elaborated. The frozen dependency is manifest entry `kam.IsDiophantine.v1`, export `KAM.IsDiophantine`, definition, `SEALED`; actual whole-file SHA256 `45ac03a3d80f3be86018b756497d11e520e59e40beff85bc92e6bec6d873aea9` matches its manifest. Its stored ABI hash is `24a486c6ccc5648791465ec3577c2e37fd464ecaec8f0dab9c74a5588535e717`; the global ABI gate could not be rerun successfully in this worktree. The W drafts have no manifest identities yet, as the brief explicitly permits; none is being represented as a frozen anchor.

## Definition audit

These are literal formula/predicate definitions, not choices of characterized objects. In the following table, `N/A_LITERAL` means no existence/uniqueness-based construction is used. For failed carriers, `BODY_MATCH: OK` means the formula agrees on the source domain; it does not certify its invented off-domain interpretation.

| Definition (actual lines) | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | DEFINITION_VERDICT |
|---|---|---|---|---|---|---|
| `lam` (`Lam:24–25`) | OK | FAIL, W-ST2 | N/A_LITERAL | N/A_LITERAL | N/A | FAIL |
| `sineMode` (`SineMode:24–25`) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `ellWeight` (`EllWeight:24–25`) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `WaveSpace` (`WaveSpace:29–30`) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `coeff` (`Coeff:24–25`) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `reconU` (`ReconU:27–28`) | OK | FAIL, W-ST2 | N/A_LITERAL | N/A_LITERAL | N/A | FAIL |
| `reconV` (`ReconV:27–28`) | OK | FAIL, W-ST2 | N/A_LITERAL | N/A_LITERAL | N/A | FAIL |
| `cubicGrad` (`CubicGrad:24–25`) | OK | FAIL, W-ST2 | N/A_LITERAL | N/A_LITERAL | N/A | FAIL |
| `linearTorus` (`LinearTorus:28–32`) | OK | FAIL, W-ST1 | N/A_LITERAL | N/A_LITERAL | N/A | FAIL |
| `IsAnalyticTorusEmbedding` (`IsAnalyticTorusEmbedding:27–32`) | OK | OK for headline Banach target | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| `IsClassicalSolution` (`IsClassicalSolution:27–38`) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

**Basis, frequency, weight.** For positive mass, `lam m j=√(j²+m)>0` on every `j:ℕ+`, with no index-zero mode. `sineMode=√(2/π)sin(jx)` is the normalized real Dirichlet basis, defined by the same sine expression on the whole real line. The weight `j^p exp(aj)` is positive for every real `a,p` and every positive integer `j`; its formula makes sense beyond the nonnegative `a` used in the weighted-space convention and introduces no clamp or singularity. At `a=p=1`, it is exactly `j exp(j)`. The public mass issue is W-ST2, not a factor or sign error in the positive-mass formula.

**Weighted encoding, whole sequence carrier and norm.** Write `w_j=j exp(j)>0`. For any `y∈lp 2`, `q_j=y_j/w_j` satisfies

`Σ |q_j|² j² exp(2j) = Σ |y_j|² < ∞`.

Conversely, every source sequence of finite weighted norm gives `y_j=w_j q_j∈lp 2`. These maps are inverse on every coordinate, preserve addition and scalar multiplication, and preserve the norm exactly. This is an explicit coordinate representation, not a choice from mere existence or a deferred characterization of an unspecified object. The product norm is the required **max**, not a Hilbert product norm: Mathlib `Prod.norm_def`/`Prod.norm_mk` in `Analysis/Normed/Group/Constructions.lean:237–239` is definitionally `max`; `lp.norm_eq_tsum_rpow` in `Analysis/Normed/Lp/lpSpace.lean:458–462` gives the ℓ² norm. A transient Lean example also checks the max identity by `rfl`. Thus every `WaveSpace` point has exactly one source coefficient pair and vice versa. There is no default coefficient sequence and no missing sequence membership restriction. A formal reusable transport/isometry lemma would be useful proof infrastructure; this literal representation does not conceal an unproved choice-defined object.

**Reconstruction and gradient on their intended domains.** For `m>0`, `j≤λ_j≤√(1+m)j`. Dividing an ℓ² coordinate by `j exp(j)` supplies exponential decay; Cauchy–Schwarz against any fixed power of `j` times `exp(−j)` proves absolute uniform convergence of both reconstructions and all fixed-order spatial derivative series, for every phase point and all real `x`. The bounds on sine/cosine are uniform on the real line. Thus the `tsum` nonsummability default never activates on the positive-mass source carrier. The reconstructed function is continuous, so its cube times a sine mode is interval-integrable on `[0,π]`; the integral's nonintegrability default does not activate either. The gradient is exactly

`(1/√λ_l) ∫₀^π U_m(q)^3 φ_l dx`.

Differentiating `(1/4)∫U_m(q)^4` cancels the 4, giving this positive gradient with no extra factor. Hamilton's momentum equation subtracts it. This matches source p. 278 (7) and p. 280 (9), and blueprint `w0-conventions.tex:96–107`; no factor from the erroneous later complex/action normalization enters. `cubicGrad` returns a raw coordinate sequence, which suffices for the explicit coordinatewise conclusion; smoothing membership is not an omitted headline conjunct. W-ST2 still blocks the unrestricted-mass declarations.

**Linear torus.** The finite sum uses `i.succPNat`, so `Fin 2` really maps to modes 1 and 2 and every higher mode is zero. Stored coordinates include `w_j`, correctly undone by `coeff`. On positive actions, `Q=√(2I)cos(2πθ)` and `P=−√(2I)sin(2πθ)`. At `ν_j=λ_j/(2π)`, differentiation gives `Dν Q=λP`, `Dν P=−λQ`; neither momentum sign nor time units have changed. The positive-action comparison passes, while the whole-carrier verdict fails W-ST1.

**Embedding.** The four conjuncts are period-one periodicity, local real analyticity, injectivity modulo integer translates, and injectivity of the Fréchet derivative at every angle. For the actual complete real Banach target `WaveSpace`, local convergent real power series have local holomorphic extensions to its complexification, and conversely restriction of such an extension is real analytic. Thus `AnalyticOnNhd ℝ ... univ` captures the blueprint's wording here. No uniform analytic strip is smuggled into this local condition. The predicate is reusable on a generic real normed target; this audit's holomorphic-equivalence assertion is for the complete headline target, not a claim about arbitrary incomplete targets. Periodicity plus analytic continuity and injectivity on the compact quotient gives a topological torus embedding as well; immersion is stated separately.

**Classical solution.** The witness functions are `ut,ux,utt,uxx`. Continuity is required for exactly the five functions `u,ut,ux,utt,uxx`, jointly on `ℝ×[0,π]`. Two-sided `HasDerivAt` gives first and second time derivatives for every real time. `HasDerivWithinAt` gives the first and second spatial derivatives within `[0,π]`, one-sided at its endpoints. Since `π>0`, this interval has the uniqueness property for derivatives even at each endpoint. The PDE has exactly `utt=uxx−m*u−u³`, everywhere on that domain; both endpoint values vanish for every real time. No mixed derivative or continuity of an unlisted derivative is assumed by the blueprint. Off-interval values of the witness functions are immaterial to this predicate, rather than values assigned by a fallback branch. Unlike reciprocal oscillator coordinates, the literal classical PDE predicate is meaningful for every real mass.

## Theorem binder and clause audit

The complete expanded **input** binder table is:

| Binder | Information/type | Bin | Source |
|---|---|---|---|
| `m` | implicit `{m : ℝ}` | TYPING | `w-headline.tex:42`, fixed real mass |
| `hm` | explicit `(hm : 0 < m)` | SOURCE | `w0-conventions.tex:24–26`; D30; P96-W p. 273 |

Counts: SOURCE **1**, STANDING **0**, TYPING **1**, RULED **0**, EXCESS **0**. There are no input typeclass binders, assumption structures, or Prop aliases hiding additional premises. All constants/structures in the conclusion were expanded above, including the frozen Diophantine predicate. Its `∀k≠0` quantification belongs to the asserted conclusion, not to an extra theorem premise.

For clarity, all remaining binder groups are **outputs or variables within the conclusion**, not logical inputs:

| Group | Scope and source |
|---|---|
| `∃r₀,C,τ,η,Γ,ν,K` | In this exact order after `m,hm`, before any family parameter, `w-headline.tex:42–45,69–70`. |
| `∀r∈(0,r₀)` | Nonnegativity constraint on the existential error witness, same preamble. |
| `∀I∈Γ, ∃γ>0` | Torus-specific Diophantine constant, clause (2); the common exponent is already chosen. |
| `∀I∈Γ, ∀θ, ∀j:ℕ+` | Clauses (3)–(4), all angles and modes. |
| `∀I∈Γ, ∀θ₀, ∀t:ℝ, ∀x∈[0,π]` | Clause (5), with the four derivative witnesses inside its classical-solution conclusion. |
| `∀I∈Γ, ∀I'∈Γ, ∀θ,θ'`, equality implication, `∃k:Fin 2→ℤ` | Clause (6); equality of points is the trigger for the injectivity conclusion, not a source premise. |

| Item | Verdict on intended carriers | Exact comparison |
|---|---|---|
| Preamble (`Nlw2:36–42`) | PASS | Only positive mass is assumed. Constants may depend on it. `r₀,C>0`, `τ>1`, `η≥0` on `(0,r₀)`, right limit zero, Borel `Γ` in the positive action region of radius `r₀`, continuous frequency and joint family map are all present. |
| (1) (`44–45`) | PASS | `Metric.ball 0 h` for `Fin 2→ℝ` uses the sup norm, exactly `max_i |I_i|<h`. Standard `volume` is two-dimensional Lebesgue measure. For every `h>0`, the positive-quadrant denominator is finite and equals `ENNReal.ofReal(h²)>0`; the ratio in `ℝ≥0∞` is therefore the ordinary finite real ratio embedded in that space. Convergence there to 1 is equivalent to the displayed real convergence. No `0/0` or `∞/∞` loophole exists along `h↓0`. |
| (2) (`47–48`) | PASS | Frozen `IsDiophantine` asserts `γ/(Σ|k_i|)^τ≤|Σk_iν_i|` for each nonzero integer vector, exactly the ℓ¹ convention. `γ>0` per torus, a single `τ>1`, and the frequency limit along `𝓝[Γ]0` to `(λ₁,λ₂)/(2π)` all match. No map-Diophantine or uniform-γ replacement. |
| (3) (`50–53`) | PASS, subject to W-ST1/2 definition fixes | The full embedding predicate is retained. Both pointwise bounds for all angles are equivalent to the blueprint sup bounds, with the same `C` and `η(r(I))*r(I)`. `r(I)>0` and `r(I)<r₀` follow from the stated inclusion of `Γ`. |
| (4) (`55–59`) | PASS, subject to W-ST2 | Derivatives of decoded coordinates along `t↦θ+tν` at zero equal `λP` and `−λQ−cubicGrad`. The coordinate functional is bounded linear on `lp 2`; analyticity of `K` gives differentiability. Hence the directional `HasDerivAt` is the stated `DK(θ)ν`, not a weaker difference-quotient surrogate. Quantifying over all angles supplies the equation at all orbit times. |
| (5) (`61–71`) | PASS, subject to W-ST2 | Joint `AnalyticAt` at every point of `ℝ×[0,π]`, exact classical PDE and boundary values, the velocity identity via `HasDerivAt` at each time, and the three-term uniform smallness estimate all appear. `derivWithin` equals the classical `ux` witness, including endpoints, by uniqueness on the nondegenerate interval. The velocity identity makes use of `reconV` in the bound exactly equivalent to `|u_t|`. |
| (6) (`73–74`) | PASS | Both parameters, both angle representatives, equality implies parameter equality and integer angle difference. This is family disjointness plus torus injectivity, with no loss to separately embedded tori. |

Total-function representatives of the existential `η,ν,K` are equivalent to the blueprint's restricted-domain maps. Restricting gives the blueprint data; conversely arbitrary extensions exist because the codomains are inhabited, and all the constraints are local to the indicated sets. In particular the right-limit filter is eventually inside `(0,r₀)` because `r₀>0`. This freedom in **existential output witnesses** does not legitimize the fixed public object `linearTorus` assigning clamped amplitudes to negative actions.

The exact weakenings in `w-headline.tex:75–100` are reflected in `W-STATEMENTS.md:284–296`: stability, Whitney regularity, family Lipschitz regularity and off-family extension are not asserted; the family remains continuous and injective. A Borel density-one set replaces the Cantor requirement; little-o closeness replaces the stronger power estimate; only leading-order frequency asymptotics are asserted. Cubic nonlinearity, `{1,2}`, `a=p=1`, and period-one angles are explicit specializations/conventions. No extra weakening was found in clauses (1)–(6). W-ST1/2 are additional declaration-domain deviations and must not be dismissed as part of those adopted weakenings.

## Nonvacuity checks

**PASS: the intended theorem is nontrivial.** Taking `Γ=∅`, a null set, or a set missing a whole small neighbourhood of zero makes the density ratio zero, contradicting convergence to 1. Density also makes `0` an accumulation point of `Γ`, so the frequency limit is not a vacuous within-set limit. For every `I∈Γ`, positive `γ` and the nonzero-integer-vector condition exclude rational dependence and zero frequency. A constant `K` fails both injectivity modulo `ℤ²` and derivative injectivity (the domain has dimension two). A family independent of `I` fails (6). An arbitrarily large fixed `C` cannot replace the equations or embedding and still multiplies `r(I)→0`. The error witness cannot stay large on radii tending to zero: its right limit is zero, including the radii sampled by `Γ`. Free values of `η` outside `(0,r₀)` have no effect. Thus there is no trivial choice of witnesses satisfying the theorem as a whole. This nonvacuity result does not excuse the independent definition-carrier failures.

## Independent elaboration and checks

I followed the handoff's direct-file elaboration procedure, with **one draft/dependency elaboration at a time**, default heartbeats and `LEAN_NUM_THREADS=1`. No `lake build` target corresponds to these unregistered draft modules; the brief specifically prescribes scratch-output elaboration instead. I did not build a root/library or regenerate `KAM.lean`.

Scratch `S=/tmp/w-stmt-audit-dqbtx6j5`; for each module `M`, create its output parent directories, then run the following exact command pattern from `/root/code/KAM-w` (the scratch variable was passed in the environment):

```sh
LEAN_NUM_THREADS=1 W_STMT_AUDIT_SCRATCH="$S" nice -n 5 lake env bash -c \
  'export LEAN_PATH="$LEAN_PATH:$W_STMT_AUDIT_SCRATCH"; exec lean -o "$1" -i "$2" "$3"' \
  w-audit "$S/<M path>.olean" "$S/<M path>.ilean" "<absolute source path>"
```

`<absolute source path>` is the actual frozen path for the first row and `/root/code/KAM-w/.drafts/W/<M path>.lean` for each W module. Each draft file retained its original bytes. Dependency order and results:

| Module suffix | Exit | Output |
|---|---|---|
| `KAM.Frozen.Defs.IsDiophantine` | 0 | none |
| `KAM.Wave.Defs.Lam` | 0 | none |
| `KAM.Wave.Defs.SineMode` | 0 | none |
| `KAM.Wave.Defs.EllWeight` | 0 | none |
| `KAM.Wave.Defs.WaveSpace` | 0 | none |
| `KAM.Wave.Defs.Coeff` | 0 | none |
| `KAM.Wave.Defs.ReconU` | 0 | none |
| `KAM.Wave.Defs.ReconV` | 0 | none |
| `KAM.Wave.Defs.CubicGrad` | 0 | none |
| `KAM.Wave.Defs.LinearTorus` | 0 | none |
| `KAM.Wave.Defs.IsAnalyticTorusEmbedding` | 0 | none |
| `KAM.Wave.Defs.IsClassicalSolution` | 0 | none |
| `KAM.Wave.Theorems.Nlw2` | 0 | `Nlw2.lean:36:8: warning: declaration uses 'sorry'` |

A transient `Probe.lean` imported `KAM.Wave.Theorems.Nlw2` and `Mathlib.Tactic.NormNum`, printed axioms for all eleven definitions, `nlw2`, and `KAM.IsDiophantine`, and checked these concrete examples:

```lean
example : KAM.Wave.lam (-1) 1 = 0 := by norm_num [KAM.Wave.lam]
example : Real.sqrt (2 * (-1 : ℝ)) = 0 :=
  Real.sqrt_eq_zero_of_nonpos (by norm_num)
example (y : lp (fun _ : ℕ+ => ℝ) 2) : KAM.Wave.cubicGrad (-1) y 1 = 0 := by
  norm_num [KAM.Wave.cubicGrad, KAM.Wave.lam]
example : KAM.Wave.linearTorus (fun _ => -1) (fun _ => 0) = 0 := by
  have hs : Real.sqrt (-2 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
  norm_num [KAM.Wave.linearTorus, hs]
example (y z : lp (fun _ : ℕ+ => ℝ) 2) :
    ‖((y,z) : KAM.Wave.WaveSpace)‖ = max ‖y‖ ‖z‖ := rfl
```

It was run with the same single-threaded nice/Lake environment and scratch `LEAN_PATH`, replacing the final command with `exec lean "$W_STMT_AUDIT_SCRATCH/Probe.lean"`. The initial probe exited 1 because `norm_num` alone did not simplify the negative square root in two examples. The explicit `sqrt_eq_zero_of_nonpos` witnesses above repaired only that transient probe; the corrected rerun exited **0**, with no errors. This is not a draft elaboration failure or a heartbeat design signal.

A second transient `ExactType.lean` imported the theorem, opened the same namespaces, restated its complete explicit type as an `example` and supplied `KAM.Wave.nlw2 hm`. It was elaborated with the same command/environment, using `ExactType.lean` instead of `Probe.lean`: exit **0**, no output. This checks application to the complete type already compared clause by clause above; it does not prove the imported draft theorem.

Axiom output: `WaveSpace`, `lam`, `sineMode`, `ellWeight`, `coeff`, `reconU`, `reconV`, `cubicGrad`, `linearTorus`, `IsAnalyticTorusEmbedding`, `IsClassicalSolution`, and frozen `IsDiophantine` depend only on **`propext`, `Classical.choice`, `Quot.sound`**. `nlw2` additionally depends on **`sorryAx`**, as expected for this explicitly permitted draft. There is no project-specific axiom or hidden proof hole in a definition. The standard classical dependencies are not arbitrary selection of the represented source object.

`LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: exit **1**. Output:

```text
check_lean_modules: PASS (417 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
/root/code/KAM-w/.lake/abi-scratch/tmpdz00um81.lean:1:0: error: unknown module prefix 'KAM'
No directory 'KAM' or file 'KAM.olean' in the search path entries:
[dependency/toolchain paths and /root/code/KAM-w/.lake/build/lib/lean]
```

This gate excludes `.drafts`, so its early successes do not check the W draft semantics or layout. Direct inspection found the module header, public imports/section, docstring and exposed definitions in every draft; the maximum file length is 79, far below 1500. No resource override, `axiom`, `admit`, `unsafe`, `opaque`, `EuclideanSpace`, provider import, arbitrary project choice, or extra `sorry` was found in the draft code. The sole hole is `Nlw2.lean:75`, permitted by this brief. No global ABI PASS is claimed.

## Owner recommendations Q1–Q5

1. **Q1 — Accept weighted coordinates.** The explicit inverse decoding, exact ℓ²/weighted-norm identity and product max norm preserve the complete source space. Freeze the meaning of `WaveSpace` and `coeff` together. A hand-built weighted-space instance adds work without improving fidelity here.
2. **Q2 — Restrict the source-facing carrier; do not accept clamping.** Prefer `{I : Fin 2→ℝ // ∀i,0<I i}` or a positivity proof argument to match the blueprint literally. The existing `Γ` inclusion supplies this data. A nonnegative carrier avoids negative clamping but adds zero-action degeneracies beyond the literal blueprint and should be recorded if chosen. Apply the same discipline to the positive-mass carriers in W-ST2.
3. **Q3 — Accept total `η` with the stated local constraints.** It is an existential witness, restricted when consumed, and `r₀>0` makes its right-limit condition independent of the off-interval extension. No new subtype infrastructure is needed.
4. **Q4 — Accept Mathlib local real analyticity for the actual Banach targets.** It matches local holomorphic extension to the complexification; do not claim a uniform strip from it. Use `AnalyticOnNhd` for the torus and the existing pointwise `AnalyticAt` for the joint PDE reconstruction. If the reusable embedding predicate is later advertised on general targets via holomorphic extension, specify the required complete target there.
5. **Q5 — Use `KAM/Frozen/Wave/Defs/...` and `KAM/Frozen/Wave/Theorems/Nlw2.lean` after correction, independent re-audit and exact owner approval.** Keep namespace `KAM.Wave` if approved. Make `WaveSpace` and `coeff` individually versioned definition anchors, and bind their meaning-carrying dependencies to the manifest; leaving either mutable would change the theorem without changing its printed type. Retain one declaration per anchor and quarantine the draft theorem/provider. No move or freeze is authorized by this audit.

## Handoff and limits

Files delivered: this report only. Approach: reconstruct the blueprint/source definitions and complete theorem independently, expand semantic dependencies, challenge vacuity and carriers, inspect source page images, elaborate all actual files, print axioms and verify explicit carrier counterexamples.

No new suspected pinned-source erratum was found. The inspected p. 278 `u_tt` display again contains the already recorded N-4 sign typo: its inner term prints `+λ_j²q_j`, whereas differentiating p. 277 (6) requires `−λ_j²q_j`; the next printed line already has the negative linear operator. The draft retains the correct sign. The p. 280 norm-one claim is the already reviewed N-1, not used as a bound by these statements. Earlier normalization errata remain governed by D30 and the W-BP0 audits; this is not a fresh audit of every later normal-form constant. Draft deviations introduced and requiring correction are W-ST1/2; the three documented representation changes (weighted encoding, directional coordinate derivatives, velocity bound via reconstruction) are faithful on the source domains. This audit introduces no mathematical deviation and edits no ledger.

Uncertainties/limits: the theorem proof, analytic/smoothing infrastructure proofs, future shell compatibility and full PDE KAM construction are not certified. The local real/complex analytic equivalence and weighted encoding were checked mathematically, not supplied as new Lean transport theorems. Global manifest ABI validation remains blocked by missing built KAM artifacts. Exact successor carriers and final anchor placement still need the normal owner-approval pipeline.

`DECLARATION_FIDELITY: FAIL` (whole package; theorem clauses match on intended carriers).

`DRAFT_ALLOWLIST: PASS` under this audit brief's explicit unfrozen-draft exception; no manifest/freeze approval is inferred.

`PROOF_STATUS: DRAFT_UNFROZEN_UNPROVED` (not `FROZEN_UNPROVED`, since nothing W-related is frozen).

Final validation: `git diff --check` exited **0**, no output. `git diff --no-index --check /dev/null /root/code/KAM-w/docs/tracks/W/audits/W-STMT-audit-1.md` exited **1**, with no output (the new file differs from `/dev/null`; no whitespace-error diagnostic). `git status --short` showed only `?? docs/tracks/W/audits/W-STMT-audit-1.md`; the initial status was empty. The report begins with its title followed immediately by `FAIL`. Temporary probe sources and scratch oleans were deleted after the successful checks. Branch and HEAD were unchanged.
