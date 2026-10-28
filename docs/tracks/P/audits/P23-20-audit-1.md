# P23-20 independent audit 1

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p2320`.
HEAD: `1dbc40524f74e481c46caaa322ffe223a7f991db`.
Comparison ref `inp`: `71fdb6c99567fab5e7e6c71a0a86d42641d9c9ff`.

**Verdict: PASS WITH NOTES for P23-20's private implementation package.**
There is no signed declaration or frozen anchor assigned to this package; seal-readiness of
`two_scale_kam`, any frozen theorem, and campaign closure are **not claimed**.
The local estimates, immersion/Lagrangian property, invariance, and shared-witness applicability
pass. Minor notes are listed below. No missing hard mathematical obligation was found.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package-audit brief,
P23-20-handoff.md and its AUDIT FOCUS, the P23 design (N2, row 284, shared-witness contract,
upstream torus fixture and `two_scale_kam` command), track P statement, and the relevant
p3a/p3b blueprint statements and current producer interfaces. This is a code audit only of
`KAM/Planetary/TwoScale/Tori*.lean`; upstream code was consulted for interfaces and provenance,
not independently re-audited as a new package.

`git diff inp...HEAD` warns that there are multiple merge bases and selects
`003b1db80283ab9f885b58a8e415ba28053b37df`. The other merge base is
`0e8f8536a2f3557ed967edeb55956f9cf182484c`. The prescribed comparison was used,
without changing refs. Its 19 added Lean files include ten upstream LimitMap files outside
this audit's scope. All nine Tori files are additions. The pre-existing untracked handoff
was left untouched. The explicit report path in the user prompt overrides the brief's generic
main-worktree destination.

Files audited (line counts, including comments): Tori 75; ToriSetup 161; ToriEstimates 229;
ToriLagr 179; ToriInvLimit 68; ToriInvField 56; ToriInvStage 197;
ToriInvConj 164; ToriInvariance 222. No source edits were made.

## Findings and disposition

- N1, documentation only: `ToriInvConj.lean:16` says the derivative bound is
  `1 + κ₁κ₂/10`; the exported theorem at lines 118–121 actually proves
  `1 + κ₁κ₂`. The weaker bound is uniform in the stage and fully sufficient for
  invariance. The theorem's own docstring and handoff state the actual bound correctly.
  Align the module overview with the theorem; this does not affect mathematical acceptance.
- N2, whitespace only: `git diff --check inp...HEAD -- 'KAM/Planetary/TwoScale/Tori*.lean'`
  exits 2 and reports `ToriInvStage.lean:186: trailing whitespace` (`+  · `).
  No permission to edit implementation was exercised.
- N3, permitted generated-root exception: lint exits 1 solely because
  `KAM.lean is out of date; run scripts/gen_root_imports.py`. Root regeneration belongs to
  the orchestrator and was not performed.

## Declaration inventory

Names below are relative to `KAM.Planetary`. PASS denotes acceptance within the private-helper
contract, not a source theorem with independently assumed proof-step hypotheses.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Stage invariant interface | `StageSteps` | PASS | Four literal proved-output fields; assembled by `iterative_all`. |
| Limit invariant interface | `ToriLimit` | PASS | Thirteen proved-output fields on one stage family and one pair of limits. |
| Common stages | `iterative_all` | PASS | Destructures `iterative H` once, forms all three stage bundles. |
| Common limits | `tori_limit_of_iterative` | PASS | Sequentially constructs i, Φinf, strip extensions on those stages. |
| lg-lim / first derivative | `StripLimit.fderiv_tendsto` | PASS | Uses derivative order 1 on an inner closed strip containing the point. |
| estimates / complex extension | `tori_complex_ext` | PASS | Correct whole strip, exact real restriction, angle bound and same-stage derivative convergence. |
| estimates | `tori_estimates_of_limit` | PASS | Both block constants and strict realTube location match p3b:102–111. |
| lg-lim | `tendsto_symplFormC` | PASS | Continuity of the finite bilinear sum. |
| lg-lim / real transfer | `symplFormC_realInclusion₂` | PASS | Correct canonical order and sign. |
| lagr | `tori_lagr_of_limit` | PASS | Analyticity, stated derivative bound, injective derivative, zero pullback. |
| inv-lim | `curve_limit_field` | PASS | Compact thickening, local uniform convergence of derivatives, actual HasDerivAt. |
| inv-lim / continuity | `hvf_continuousOn` | PASS | Holomorphy gives continuous complex derivative; real restriction gives real field. |
| inv-err / frequency | `freq_lip` | PASS | MVT in a convex ball contained in the holomorphy domain; no convexity assumed of D. |
| inv-err / Cauchy | `fderiv_f_le` | PASS | Closed polydisc contained strictly in the source domain. |
| inv-err | `field_err` | PASS | Frequency difference plus both perturbation partials, max product norm. |
| inv-dphi / domain | `isOpen_phaseTube` | PASS | Open preimage and product. |
| inv-dphi / reality | `PsiSteps.psiR_hasFDerivAt` | PASS | Real projection of complex derivative at an interior point. |
| inv-conj / holomorphy | `kam_G_diff` | PASS | Composition with snd plus perturbation. |
| inv-conj / reality | `kam_G_real` | PASS | Direct sum of KamHyp reality fields. |
| inv-conj | `conj_field` | PASS | Real symplectic conjugation and equality on a neighborhood, not merely at a point. |
| inv-dphi / norm conversion | `limitmap_data_le_norm` | PASS | Correct fixed max-norm scaling factor. |
| inv-dphi | `PsiSteps.psiR_fderiv_bound` | PASS WITH NOTES | Uniform bound 1+κ₁κ₂ suffices; N1 affects overview only. |
| inv-err / scalar estimate | `stage_bound` | PASS | K≥1, M Rhat≤γ₁/3 and E≤Ehat Rhat γ₁/3 from source numerical bounds. |
| inv-err / scalar estimate | `stage_err_le` | PASS | Stage-independent coefficient after Rhat_j≤Rhat_0 and γ₁_j=γ₁. |
| inv-err / decay | `PsiSteps.eHat_tendsto` | PASS | Geometric domination by Ehat_0(1/160)^j. |
| invariance | `tori_invariance_of_limit` | PASS | Exact IsLatticeTorus L6, no extra frequency scaling. |
| Joint consumer | `tori_of_iterative` | PASS | H alone produces compatible stages, limits and all three applications. |

## Expanded input provenance and applicability

The five-bin test applies to the source-facing applicability theorem: its only logical input
is `H : KamHyp D sbar p h f` (STANDING/source hypothesis bundle); all dimensions, domains,
parameters and Hamiltonian functions are TYPING data. There are no RULED or EXCESS inputs.
The conditional helpers have additional **derived proof inputs**, explicitly permitted by the
P23 N2 shared-witness contract. They are not added premises of `two_scale_kam`.

Expansion of H (Setting.lean:42–75), each row STANDING, matches the P23 source interface:

| Field | Content |
|---|---|
| a_pos | Positive first block dimension. |
| b_pos | Positive second block dimension. |
| τ_gt | τ > a+b. |
| positive | Nine positive numerical parameters γ₂,s,ρ,E,M,Mhat,Mbar,Mbar₁,Mbar₂. |
| gamma_order | γ₂≤γ₁. |
| widths | 4s≤sbar<1. |
| normalized | Mhat≤M and both Mbar_i≤Mbar. |
| L_bound | initialL≤L. |
| holo | h holomorphic on the complex action neighborhood. |
| real_h | Integrable Hamiltonian real on reals in the source domain. |
| real_f | Perturbation real on reals there. |
| f_class | Perturbation analytic/Fourier class. |
| f_bound | Source perturbation bound E. |
| injective | Injective frequency map on the source complex action neighborhood. |
| hessian | Operator bound M, second block bound Mhat, actual invertible derivative with inverse block bounds. |
| small | kamConstant Ehat < 1. |

Counts at field granularity: STANDING 16; SOURCE 0 separately; RULED 0; EXCESS 0.
Logical contents of the conjunctions and inverse existence are stated above; none is a torus,
limit, convergence, field-error, or Lagrangian conclusion. The upstream public theorem also
has hL asserting equality with initialL; these helpers are stronger in not requiring it.

All conditional logical inputs and their producers:

| Input | Exact producer / application |
|---|---|
| `ActionSteps` (8 fields) | `iterative_all`, ToriSetup:109–112: hs_zero; stage KamHyp; action step frequency and block estimates; action Lipschitz; next-stage image; maps; Ehat recurrence; upper radius recurrence, all projections of the same `iterative H`. |
| `PsiSteps` (15 fields) | ToriSetup:113–116: stage KamHyp; Φ zero/composition; Φ differentiability/reality/periodicity; Ψ differentiability/reality/periodicity/maps/displacement; tube; Ehat and lower/upper radius recurrences, all projections of that same output. |
| `StageSteps.fs_zero` | iterative output fs 0=f. |
| `StageSteps.maps` | iterative output hPh, maps component. |
| `StageSteps.conj` | iterative output hPh, Hamiltonian conjugacy component. |
| `StageSteps.symp` | iterative output hPh, symplectic component. |
| `ToriLimit.stage_diff` | P.phi_diff composed with fixed-action inclusion; P.strip_mem supplies domain. |
| `ToriLimit.stage_lagr` | Q.symp applied to tangent vectors (u,0),(v,0); their symplectic pairing vanishes. |
| `ToriLimit.i_conv` | limit_actions_of_steps S: uniform convergence. |
| `ToriLimit.i_mem` | Same output: actionChain stage membership. |
| `ToriLimit.i_block` | Same output: first/second/total displacement bounds. |
| `ToriLimit.i_tail` | Same output: 20 Rhat_j Ehat_j tail. |
| `ToriLimit.i_tube` | Same output: membership in every half-radius stage tube. |
| `ToriLimit.i_freq` | Same output: frequency identity on that exact actionChain. |
| `ToriLimit.phi_conv` | P.limit_phi_real_of_steps hD with Dstar=i '' Ds 0. |
| `ToriLimit.phi_lip` | Same output: scaled defect constant 768n Ehat. |
| `ToriLimit.phi_block` | Same output: three 3/2 displacement estimates. |
| `ToriLimit.phi_per` | Same output: full integer lattice equivariance. |
| `ToriLimit.phi_strip` | P.limit_phi_strip_of_steps hD hU, using that same Φinf and convergence. |
| `hD0 : Ds 0 ⊆ D` | Ds 0=dioBase D h p, then Set.inter_subset_left (Tori:64). |
| `hI₀ : I₀ ∈ Ds 0` | Source torus index restriction; universally quantified in the joint conclusion. |
| Stage centers / proximity / scalar bounds | Instantiated inside invariance using i_mem, i_tube, i_tail, i_freq, P.hyp, P.rho_le_zero and seq_γ₁. |
| Curve continuity, limit-domain membership and field continuity | lagr analyticity; estimates plus 32 Ehat Rhat≤ρ; hvf_continuousOn using kam_G_diff/real. |

ToriSetup:130–155 selects i once, then Φinf once, then coordinatewise extensions;
Tori:63–68 applies the three helpers on precisely these witnesses. No identification of
independently selected limits is assumed. The final joint theorem omits the two block estimates
from its displayed conjunction, but retains ToriLimit, so `tori_estimates_of_limit H hD0 T hI₀`
recovers them immediately on the same witnesses. This is an interface observation, not an unpaid
estimate or a required source change.

## Definition classification

Only two new definition-like commands occur: `StageSteps` and `ToriLimit`, both literal Prop
structures recording derived data, not source definitions and not new fields of KamHyp.
Their complete fields are traced above. Bodies match their stated invariant-record purpose on
their entire typed carriers. No arbitrary chosen map, default branch, junk extension or
characterization-defined source object is introduced.

For both: BODY_MATCH OK; PUBLIC_CARRIER OK (internal invariant interface);
WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL;
CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS under N2.
The local `choose` in tori_complex_ext chooses genuine coordinate extensions satisfying
StripLimit, then proves all claimed properties of the assembled extension. No uniqueness of a
source-defined chosen map is asserted or needed.

## Mathematical checks and downstream boundary

Estimates use 3/2 for map displacement plus 20 for action displacement, giving total <22 Ehat Rhat
and hence <32 Ehat Rhat; the normalized ratios give the stated block constants.
The strip radius is the geometric width sbar/(2π), with angle displacement 3 Ehat s/(4π).
Cauchy's operator estimate actually gives ||Du||≤3 Ehat/4 before enlargement to
3(a+b)Ehat/4. This is stronger than the blueprint's coordinatewise row-sum bound.
Finite-stage first derivatives converge at the same complex point and direction; bilinearity
passes the zero symplectic form to the real limit. Pointwise first-derivative convergence
suffices for this conclusion.

For invariance, `field_err` bounds the two perturbation partial derivatives together by
||Df_j||≤E_j/min(ρ_j/2,sbar/(4π)); the max norm on Phase means no missing sum or dimension factor.
Its frequency term is controlled in a convex ball around the actual chain center in Ds j.
`stage_err_le` then gives the uniform error coefficient
`C0 = 20γ₁/3 + (γ₁/3)(2 + 4π Rhat_0/sbar)` and a fixed derivative bound κ, so the curve error is
at most κ C0 Ehat_j→0, uniformly in angle and time.

In `curve_limit_field` (ToriInvLimit:41–62), for each compact time set K the continuous limit
curve has compact range y''K. A positive closed thickening lies in the open real Hamiltonian
domain, and is compact because Phase is finite dimensional. Continuity of X gives uniform
continuity on this thickening. Uniform convergence eventually puts x_j(K) in it. Thus the
fields converge uniformly on each compact K, and the derivative-limit theorem applies locally.
There is no global uniform-continuity premise, global compactness assumption, or hidden bound
on a second derivative. Local uniform derivative convergence proves the exact global-in-time
pointwise HasDerivAt statement required.

The remaining P23-22 work is ordinary assembly, not hidden P23-20 analysis:

| IsLatticeTorus requirement | Available discharge |
|---|---|
| L1 analyticity | tori_lagr_of_limit, first component. |
| L1 Kθ∈O | estimates location and trivial angle membership in univ. |
| L1 DifferentiableAt Hr | kam_G_diff at the complex inclusion of Kθ, restrict scalars to ℝ, compose inclusion and Complex.reCLM; inclusion is interior since 32 Ehat Rhat≤ρ. |
| L2 periodicity | T.phi_per at (θ,i I₀), definition of angleShift. |
| L3 injectivity modulo lattice | Small defect T.phi_lip (768n Ehat<1/10) implies actual injectivity on univ×i''Ds 0. Equal torus values force θ=θ', so the literal L3 uses k=0. Shifted equality follows too by L2 and injectivity. |
| L4 injective derivative | tori_lagr_of_limit. |
| L5 Lagrangian | tori_lagr_of_limit. |
| L6 invariance | tori_invariance_of_limit at w=realFreq h I₀ and exactly Hr from the signed design. |

A scratch probe assembles the complete actual upstream `IsLatticeTorus` predicate from
H,P,Q,hD0,T,hI₀, including all four handoff leftovers. This also checks L6 literally against
the upstream predicate rather than a paraphrase. P23-22 still must select the frequency index
and assemble its other action, map, inverse-frequency and measure outputs; this audit does
not certify those unimplemented obligations.

## Validation receipts

All completed audit-owned Lean invocations were serialized, used `LEAN_NUM_THREADS=1` and `nice -n 5`,
and used default resource budgets. The first lint attempt was stopped during its Python-only
frozen-guard phase and rerun with the required environment/niceness before the subsequent Lean
checks. No project or package dependency sources were modified.

1. Targeted gate build (exit 0):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2320 KAM.Planetary.TwoScale.Tori
   ```

   Output: `[inp-gate] slot 2 acquired 16:25:00 for KAM.Planetary.TwoScale.Tori`;
   `Build completed successfully (9187 jobs).` The gate invokes `nice -n 5 lake build`.
   Replayed warnings concerned unused variables/simp arguments and deprecated tactics;
   no elaboration error or resource-budget failure occurred.

2. Lint (exit 1, the permitted root exception only):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (727 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

3. All-public-theorem axiom and full-consumer probe (exit 0):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2320Audit.lean
   ```

   Its output, one entry for each of the 25 theorem declarations, was:

   ```text
   'KAM.Planetary.tori_of_iterative' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StripLimit.fderiv_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.tori_complex_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.tori_estimates_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.isOpen_phaseTube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.PsiSteps.psiR_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kam_G_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kam_G_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.conj_field' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.limitmap_data_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.PsiSteps.psiR_fderiv_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.hvf_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.curve_limit_field' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.freq_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fderiv_f_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.field_err' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.stage_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.stage_err_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.PsiSteps.eHat_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.tori_invariance_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.tendsto_symplFormC' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.symplFormC_realInclusion₂' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.tori_lagr_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.iterative_all' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.tori_limit_of_iterative' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The same file's complete IsLatticeTorus assembly, reproduced below, elaborated with no
   further messages. Earlier scratch-only tactic attempts needed beta reduction and explicit
   simplification of the zero integer lattice vector; these were probe-writing errors, not
   implementation failures or added assumptions. The final probe exits 0.

4. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.ToriSetup KAM.Planetary.TwoScale.ToriEstimates KAM.Planetary.TwoScale.ToriLagr KAM.Planetary.TwoScale.ToriInvLimit KAM.Planetary.TwoScale.ToriInvField KAM.Planetary.TwoScale.ToriInvStage KAM.Planetary.TwoScale.ToriInvConj KAM.Planetary.TwoScale.ToriInvariance KAM.Planetary.TwoScale.Tori
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.TwoScale.Tori
   replaying KAM.Planetary.TwoScale.ToriInvariance
   replaying KAM.Planetary.TwoScale.ToriInvConj
   replaying KAM.Planetary.TwoScale.ToriInvStage
   replaying KAM.Planetary.TwoScale.ToriInvField
   replaying KAM.Planetary.TwoScale.ToriInvLimit
   replaying KAM.Planetary.TwoScale.ToriLagr
   replaying KAM.Planetary.TwoScale.ToriEstimates
   replaying KAM.Planetary.TwoScale.ToriSetup
   ```

5. Read-only hygiene and boundary checks:

   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty diff, exit 0;
     only the multiple-merge-base warning described above.
   - `git diff --check inp...HEAD -- 'KAM/Planetary/TwoScale/Tori*.lean'`: exit 2,
     exact diagnostic `KAM/Planetary/TwoScale/ToriInvStage.lean:186: trailing whitespace.`
   - `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option|_root_' KAM/Planetary/TwoScale/Tori*.lean`:
     no matches (exit 1). No escaped names or root-namespace declarations.
   - New declarations all reside in KAM.Planetary (nested StripLimit/PsiSteps names included).
     A scan of public theorem/lemma/def/abbrev/structure short names in every other KAM source
     found no public short-name collision. Other `freq_lip` occurrences are private.
     `eHat_pos` is used from StepConst:149, not redeclared here.
   - Module/size checks pass: copyright, module, public imports, module docstring,
     exposed public noncomputable section, nine files each at most 229 lines.
   - Source import-closure scan: 141 KAM modules, no provider and no frozen theorem imports.
     The twelve frozen modules in that closure are definitions, all currently SEALED in the
     manifest (including Phase, HamiltonianVectorField, SymplecticForm, ActionNbhd and
     ComplexStrip). No DRAFT_SORRY theorem or provider is available through the package.
   - Scratch probe and logs are removed after recording these receipts; only the requested
     report is added by the audit. No state-changing git command was used.


## Reproducible downstream probe

The successful scratch file imported the two modules below, printed axioms for all 25 theorem
rows in the inventory, and then elaborated this exact full torus assembly (default budgets):

```lean
import KAM.Planetary.TwoScale.Tori
import KAM.Planetary.Hamiltonian.Transport

open Set Metric Real Filter Topology
open KAM.Canonical KAM.NormalForm KAM.Weighted
namespace KAM.Planetary
variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}
  {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}
  {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φinf : Phase (a + b) → Phase (a + b)}
example (H : KamHyp D sbar p h f) (P : PsiSteps sbar p Ds hs fs Ψ Φ)
    (Q : StageSteps D sbar p h f Ds hs fs Φ) (hD0 : Ds 0 ⊆ D)
    (T : ToriLimit sbar p h Ds hs Φ is i Φinf) {I₀ : Fin (a + b) → ℝ} (hI₀ : I₀ ∈ Ds 0) :
    IsLatticeTorus KAM.ODE.angleShift
      (fun z : Phase (a + b) => (h (KAM.realInclusion (a + b) z.2) +
        f (KAM.realInclusion₂ (a + b) z)).re)
      (univ ×ˢ realTube D (32 * eHat p * rhoHat p))
      (realFreq h I₀) (fun θ => Φinf (θ, i I₀)) := by
  have hmem : i I₀ ∈ i '' Ds 0 := ⟨I₀, hI₀, rfl⟩
  have hloc := (tori_estimates_of_limit H hD0 T hI₀).2.2
  obtain ⟨hAn, _, hInjD, hLagr⟩ := tori_lagr_of_limit H T hI₀
  have hr : 32 * eHat p * rhoHat p ≤ p.ρ := by
    nlinarith [H.eHat_lt_small, H.R_le_ρ, H.R_pos, H.eHat_nonneg]
  have hWidth : 0 < sbar + p.s := by
    have := H.widths.1; have := H.positive.2.1; linarith
  have hW := isOpen_coefficientDom D p.ρ (sbar + p.s)
  have hz : ∀ θ, KAM.realInclusion₂ (a + b) (Φinf (θ, i I₀)) ∈
      coefficientDom D p.ρ (sbar + p.s) := by
    intro θ
    rw [(conv_data _ _ _).2]
    refine ⟨fun k => ?_, realTube_mono hr (hloc θ)⟩
    simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.ofReal_im, abs_zero]
    positivity
  refine ⟨⟨hAn, fun θ => ⟨⟨trivial, hloc θ⟩, ?_⟩⟩, ?_, ?_, hInjD, hLagr,
    tori_invariance_of_limit H P Q hD0 T hI₀⟩
  · have hd := (kam_G_diff H).differentiableAt (hW.mem_nhds (hz θ))
    exact Complex.reCLM.differentiableAt.comp _
      ((hd.restrictScalars ℝ).comp _ (KAM.realInclusion₂ (a + b)).differentiableAt)
  · intro θ k
    simpa [KAM.ODE.angleShift] using T.phi_per (θ, i I₀) ⟨trivial, hmem⟩ k
  · intro θ θ' heq
    change Φinf (θ, i I₀) = Φinf (θ', i I₀) at heq
    have hl := T.phi_lip (θ, i I₀) ⟨trivial, hmem⟩ (θ', i I₀) ⟨trivial, hmem⟩
    have h0 := H.R_pos
    have hs0 := H.positive.2.1
    have hn := limitmap_data_nonneg h0 hs0 ((θ, i I₀) - (θ', i I₀))
    have he : ((Φinf (θ, i I₀) - (θ, i I₀)) -
        (Φinf (θ', i I₀) - (θ', i I₀))) = -((θ, i I₀) - (θ', i I₀)) := by
      rw [heq]; abel
    rw [he] at hl
    simp only [limitmap_data, Prod.fst_neg, Prod.snd_neg, norm_neg] at hl
    change limitmap_data (rhoHat p) p.s ((θ, i I₀) - (θ', i I₀)) ≤
      768 * ((a + b : ℕ) : ℝ) * eHat p *
        limitmap_data (rhoHat p) p.s ((θ, i I₀) - (θ', i I₀)) at hl
    have hsmall : 768 * ((a + b : ℕ) : ℝ) * eHat p < 1 := by
      have := P.lam_small
      linarith
    have hzero : limitmap_data (rhoHat p) p.s ((θ, i I₀) - (θ', i I₀)) = 0 := by
      nlinarith
    have hθ : θ = θ' := congrArg Prod.fst (sub_eq_zero.1 (limitmap_data_eq_zero h0 hs0 hzero))
    refine ⟨fun _ => 0, ?_⟩
    rw [hθ]
    ext k
    simp
end KAM.Planetary
```

## Blueprint/source defects and deviations

No new pinned-source mathematical defect found. The handoff's description of a blueprint
“global bound” should be read precisely: p3b:143 says “There ||DX_H||≤B₀” on a stated common
inner domain for nearby pairs, not on the entire ambient space. That argument is not refuted
by this implementation; the compactness proof is a valid alternative that avoids its
quantitative second-derivative estimate. It proves only locally uniform derivative
convergence before invoking the local curve-limit theorem, which is sufficient for the same
HasDerivAt conclusion. This is a proof-method deviation, not a source erratum.
The joint Cauchy estimate merges p3b:138–140's three errors without dropping either partial.
The deliberately looser derivative constant and the stronger operator Cauchy bound above
change no source-facing theorem statement. N1 is a code-documentation mismatch, not a
pinned-source error. No heartbeat/design failure was encountered.
