# Independent design audit 1: N Parts 6–7

**Overall verdict: FAIL.** F1 is a false theorem caused by an incomplete norm structure. F2 weakens an explicit blueprint conclusion. F3 leaves an advertised consumer without an applicable homological signature. These are design findings; the scratch signatures elaborate successfully. Do not issue unchanged prover targets for the affected interfaces.

## Scope, authority and frozen snapshot

Tier-2 refute-first audit under `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`, the user's narrower write envelope, `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, and `.drafts/handoff-DESIGN-N67.md`. No proofs were audited or completed. No subagents were used. Only this report is retained as a change; the explicitly authorized signature copy and temporary probes are removed after checking. No state-changing git commands were used.

Snapshot v1 (2026-10-28):

| Input | Immutable revision / SHA-256 |
|---|---|
| Design worktree HEAD | `949524142150f68a0c11bb04d589d89ef83ac945` |
| `inp` when comparison began | `cf91d0eb53d4b0b03586d20e54b7fc8ede4b7150` |
| Merge base | `40237a3a44c50dbe4be9ae039cf809d0d520a175` |
| `docs/tracks/N/design/PART67-LEAN-DESIGN.md` | `0cefef0d0fb7d48f6932ec14c4fd5d55825917dd81671b878597e0fdca8348e6` |
| Original `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `f64cf1e3f37e241b39053123eb4f3cbf8e3bf66616418464165225d565b60b97` |
| `blueprint-N/parts/p6-normal-form.tex` | `1c9c5e640ba0825040f1a2ad1de3aac9b38df9dbfcc1b280245ed53c3f2533ac` |
| `blueprint-N/parts/p7-stability.tex` | `f3d6e993abd74759469db1c9ae3c2c6d7cc65555a6d13167e8bfc7c38493e4bd` |
| `docs/graph/N/packets/N-p6.nodes.md` | `9a926776db148740de214d7f8002aa774dad8771e97d884806b5d625f89d8c92` |
| `docs/graph/N/packets/N-p7.nodes.md` | `39819cc69681853349831656168f4fbb64ba8147af95707662d31769732ef034` |

`git diff inp...HEAD` at intake contains one new file: the 1,202-line design. Appendix A is byte-identical to the supplied 790-line signatures file. Signature inventory: **34 definitions, 5 structures, 39 theorem obligations**. Locators below refer to this snapshot; signature line numbers refer to the original file, with identical code in Appendix A. The neighboring `inp` branch can move during this audit; its intake hash above is the comparison authority.

Acceptance criteria were the brief's seven checks: exact blueprint/packet contracts, applicable consumer interfaces, frozen-object bridges, honest definitions, actual Mathlib names, executable package order and size, and a single elaboration of the unmodified signature copy. Successful elaboration is not approval of mathematical statements or proof closure.

## Numbered findings

### F1 — BLOCKING: `IsActionNorm` admits shifted norms; `exit_ball` is false

**Anchors.** Signatures L536–540 define the fields as only `continuous`, `add_le`, `neg`, `norm_le`. L585–590 promises an attained boundary radius for every such function. Blueprint `bpN:p7:exit-ball` (p7 L118–126; packet node at L970) says “a norm”; its proof uses “z(0) in V” (packet `stepN:p7:eb-exit`, L1004). This requires the value at zero to vanish.

**Counterexample.** Take `n=1`, `N(v)=‖v‖+1`, `J=Set.univ`, `z(t)=(0,0)`, `t₁=1`, and `ϱ=1/2`. The shifted norm satisfies every current structure field: continuity and symmetry are immediate, triangle follows from `norm_add_le` and `1≤2`, and it dominates the max norm. All curve/interval hypotheses hold. The exit premise is `1/2<1`, but the conclusion requires `1=1/2`. In particular no boundary time exists.

**Refutation pass: survived.** `norm_le` gives `0≤N(0)`, not `N(0)=0`; subadditivity gives no reverse bound. The structure has no homogeneity field. There is no hidden ambient norm instance on `N` and no hypothesis excluding constant curves or `t₁=0`. A separate Lean probe copied just these four fields and proved both admissibility of the shifted norm and impossibility of the boundary equality, without importing the draft's theorem obligations. Both probe theorems have only `[propext, Classical.choice, Quot.sound]`.

**Proposed fix.** At minimum add `map_zero`. To make the structure actually describe its documented object on the entire carrier, also require real absolute homogeneity. These are properties of the source norm, not new restrictions on the source theorem. The existing two examples satisfy them. Replace the structure with:

```lean
structure IsActionNorm (N : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous N
  map_zero : N 0 = 0
  add_le : ∀ a b, N (a + b) ≤ N a + N b
  neg : ∀ a, N (-a) = N a
  smul : ∀ (c : ℝ) a, N (c • a) = |c| * N a
  norm_le : ∀ a, ‖a‖ ≤ N a
```

The corrected first-exit signature, using that corrected structure, is:

```lean
theorem exit_ball {Nrm : (Fin n → ℝ) → ℝ} (hN : IsActionNorm Nrm)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : ContinuousOn z J)
    {ϱ : ℝ} (hϱ : 0 < ϱ) {t₁ : ℝ} (ht₁ : t₁ ∈ J)
    (hexit : ϱ < Nrm ((z t₁).2 - (z 0).2)) :
    ∃ tstar ∈ J, tstar ∈ uIcc 0 t₁ ∧
      Nrm ((z tstar).2 - (z 0).2) = ϱ ∧
      ∀ τ ∈ uIcc 0 tstar, Nrm ((z τ).2 - (z 0).2) ≤ ϱ
```

### F2 — MAJOR: `normal_form` omits the exact zero-correction cases

**Anchors.** Signatures L342–372 have only the estimate `WBound ... (g - homRes ...) (16 * ... * ε^2)`. Blueprint p6 L167 explicitly adds “g=g₀ if N=0 ... or in the second case”; packet `bpN:p6:normal-form`, L890, independently includes “(g=g_0 if N=0 or in case B)”. The design §4 says “hypotheses, carriers and conclusions may not” change and §3.1 assigns the whole result to `normal_form`.

**Refutation pass: survived.** The positive quadratic error bound does not imply equality when `ε>0`; `nfSteps K s=0` allows `6≤κ<12 log 2`, so it does not force `ε=0`. `g` is an existential witness, not definitionally tied to the constructed step sequence. A proof's private Case B equality would not be accessible through the proposed public signature. This is a contract omission, not a claim that the retained theorem is false. Current stability consumers use only the bound, so they do not repair the source-fidelity failure.

**Proposed fix.** Preserve the equality on the intended domain, without imposing equality of arbitrary off-domain values. Use the following complete replacement of `normal_form`; all existing conclusions remain, with the additional conditional equality before the remainder estimate. For the upper-bound formulation, the Case B test uses the carried bound `ε`, consistently with the step construction. At the sharp norm instance it is the literal blueprint case.

```lean
theorem normal_form {D : Set (Fin n → ℂ)} {r s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hp : 1 < p) (hα : 0 < α)
    (hK : 0 < K) (hL : 0 ≤ L) (hr : 0 < r) (hs : 0 < s) (hh : DifferentiableOn ℂ h (polyNbhd D r))
    (hnr : IsNonresonant D K α Λ h) (hlip : FreqLipschitz D r L h) (hrad : K * L * r ≤ α / p)
    (hf : InClass D r s f) (hfb : WBound D r s f ε) (hε0 : 0 ≤ ε)
    (hi : ε ≤ 1 / (2 ^ 7 * conjExp p) * (α * r / K)) (hii : 6 ≤ 2 * Real.pi * K * s) :
    ∃ (Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
      (g fs : (Fin n → ℂ) × (Fin n → ℂ) → ℂ),
      -- the map
      DifferentiableOn ℂ Ψ (Dom n D (r / 2) (s / 6)) ∧ InjOn Ψ (Dom n D (r / 2) (s / 6)) ∧
      MapsTo Ψ (Dom n D (r / 2) (s / 6)) (Dom n D r s) ∧
      (∀ z ∈ Dom n D (r / 2) (s / 6), ∀ v w,
        symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w) ∧
      (∀ k : Fin n → ℤ, ∀ z ∈ Dom n D (r / 2) (s / 6),
        Ψ (z.1 + (fun i => (k i : ℂ)), z.2) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      -- the normal form
      InClass D (r / 2) (s / 6) g ∧ InClass D (r / 2) (s / 6) fs ∧
      (∀ I ∈ polyNbhd D (r / 2), ∀ k, k ∉ Λ ∩ zBall n K → coeff g I k = 0) ∧
      (∀ z ∈ Dom n D (r / 2) (s / 6), (fun w => h w.2 + f w) (Ψ z) = h z.2 + g z + fs z) ∧
      -- (a)
      WBound D (r / 2) (s / 6) (fun z => g z - homRes K Λ f z)
        (16 * (2 * conjExp p * K / (α * r)) * ε ^ 2) ∧
      -- Exact correction in the zero-step or Case B branch.
      ((nfSteps K s = 0 ∨
          iterU α p ε (r / 8) (s / 6) < Real.exp (-(2 * Real.pi * K * s) / 6)) →
        EqOn g (homRes K Λ f) (Dom n D (r / 2) (s / 6))) ∧
      -- (b)
      WBound D (r / 2) (s / 6) fs (Real.exp (-(2 * Real.pi * K * s) / 6) * ε) ∧
      -- (c)
      (∀ z ∈ Dom n D (r / 2) (s / 6), ‖(Ψ z).2 - z.2‖ ≤ conjExp p * K * ε / α ∧
        ‖(Ψ z).1 - z.1‖ ≤ 10 * conjExp p * ε / (2 * Real.pi * α * r)) ∧
      -- (d)
      ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) (fun w => h w.2) → RealOn (Dom n D r s) f →
        RealOn (Dom n D (r / 2) (s / 6)) g ∧ RealOn (Dom n D (r / 2) (s / 6)) fs ∧
        ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n D (r / 2) (s / 6) →
          Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
```

### F3 — MAJOR: the advertised Part 11 homological reuse has no compatible carrier

**Anchors.** Design §0.5 says “Part 11 (`p11:hom`) consumes the direct forms”; §8 lists `homological_direct` for that consumer. Signatures L132–164 fix both angle and parameter dimensions to `n`, with `h : (Fin n → ℂ) → ℂ`. But `blueprint-N/parts/p11b-partial-nf.tex` L7–17 defines `n` angles and `n+2k` parameter coordinates (`k≥1`), and L117–123 states `bpN:p11:hom` for `f(θ,I,x̃)` and a divisor depending on fast `I` only. That proof explicitly uses Part 4's independent parameter dimension.

**Refutation pass: survived as a consumer/API finding.** Choosing the signature's `n` to match angles leaves too few parameter slots; choosing it to match the parameter slots changes the Fourier lattice and inserts nonexistent angles. The supplied API contains no dummy-angle extension/restriction bridge, norm-isometry theorem, or projection bridge making either route an application of this signature. Part 11's separate weighted-bracket iteration really is a new variant; this finding does not require the canonical Iterative Lemma to prove that variant unchanged. The defect is the specifically promised direct use of the homological solve and its omitted parameter bridge. The scalar Part 6 theorem itself has the right source contract.

**Proposed fix.** Add a shared homological core with independent angle and parameter dimensions, then retain the current canonical statement as a wrapper. A concrete replacement interface follows. `homGenParam` and `homResParam` have these real bodies; the theorem is the corrected consumer-capable core. Specialize `ω=freq h` for Part 6 and `ω(I,x̃)=freq h I` for Part 11; each caller proves its own bracket identity from the directional identity. Budget the fast-coordinate projection/holomorphy bridge in the Part 11 package. This adds no small-divisor, regularity, or conclusion-shaped premise beyond the consumer's source data.

```lean
def homGenParam {n m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ))
    (ω : (Fin m → ℂ) → Fin n → ℂ)
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (ω z.2)) *
      KAM.character k z.1) k

def homResParam {n m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ))
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  projMode Λ (truncate K f)

theorem homological_param {n m : ℕ} {D : Set (Fin m → ℂ)}
    {r s K α q δ : ℝ} {Λ : Set (Fin n → ℤ)}
    {ω : (Fin m → ℂ) → Fin n → ℂ}
    {f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hq : 1 ≤ q) (hα : 0 < α) (hs : 0 < s) (hK : 0 ≤ K)
    (hω : DifferentiableOn ℂ ω (polyNbhd D r))
    (hdir : ∀ I ∈ polyNbhd D r, ∀ k ∈ zBall n K \ Λ,
      α / q ≤ ‖dotC k (ω I)‖)
    (hf : InClass D r s f) (hδ : WBound D r s f δ) :
    InClass D r s (homGenParam K Λ ω f) ∧
    InClass D r s (homResParam K Λ f) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, k ∉ zBall n K \ Λ →
      coeff (homGenParam K Λ ω f) I k = 0) ∧
    (∀ z ∈ Dom n D r s,
      (∑ i, fderiv ℂ (homGenParam K Λ ω f) z (Pi.single i 1, 0) * ω z.2 i) +
        homResParam K Λ f z = truncate K f z) ∧
    (∀ I ∈ polyNbhd D r, ∀ k ∈ Λ,
      coeff (homGenParam K Λ ω f) I k = 0) ∧
    (∀ z ∈ Dom n D r s,
      homResParam K Λ f z = projMode (Λ ∩ zBall n K) f z) ∧
    WBound D r s (homResParam K Λ f) δ ∧
    WBound D r s (truncate K f) δ ∧
    WBound D r s (homGenParam K Λ ω f) (q * δ / (2 * Real.pi * α)) ∧
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) f →
      (∀ I : Fin m → ℝ, KAM.realInclusion m I ∈ polyNbhd D r →
        ∀ i, (ω (KAM.realInclusion m I) i).im = 0) →
      RealOn (Dom n D r s) (homGenParam K Λ ω f) ∧
      RealOn (Dom n D r s) (homResParam K Λ f))
```

Proposed fixes are review text, not proofs or landed changes; the supplied signature file was not modified to test these repairs.

### N1 — LOW: document the valid q=1 reparameterization for Track P

P Part 2 L40–54 explicitly allows `q=1`; `IterHyp` uses `p>1`, so its `conjExp p` is always strictly greater than one. This initially looks incompatible, but it is **refuted as a blocker**: for consumer data `(α,q₀)`, take design `p=2`, `α_design=2α/q₀`. Then `α_design / conjExp 2 = α/q₀`, and every estimate and smallness condition uses the unchanged ratio `conjExp 2 / α_design = q₀/α`. `homGen` and `iterMap` do not depend on α or p, so the constructed map is unchanged. For q₀=1 take α_design=2α. Add this wrapper calculation to §8; do not just set p to a nonexistent conjugate exponent. F3's parameter core can also expose q directly. P's split-displacement/oscillator/an-isotropic variants remain P's own explicitly stated variants, not consequences of the scalar displacement clause alone.

### N2 — MEDIUM: facade ownership must be postponed to make package builds executable

Design §7 says `Iterative` re-exports `IterativeMap`, `IterativeRemainder`, `IterativeReal`, while the wave-3 package N6-5 owns `Iterative` and waves 4 N6-6/7 create the latter two imports. N6-6 then depends on N6-5. The mathematical DAG can be acyclic, but the N6-5 deliverable cannot build as the declared complete facade at wave 3. Move `iterHyp_of_source` to `IterativeMap` (or a small independent source-wrapper module), and create the facade in N6-7 after its imports exist; N6-6 must import `IterativeMap`, not the eventual facade. Also list S7-3 explicitly among S7-6 prerequisites because `Resonant` imports `Transfer`. The size/wave summary says “5 waves” and “150–650 lines each”, while the table has wave 6 and a 950-line multi-module package: reconcile the summaries. No planned individual file exceeds 1500 lines.

### N3 — LOW: distinguish actual consumer uses from proposed reuse

The design and handoff advertise Track I use of `energy_core`, `no_exit`, Lemmas 1–2. Searching every `blueprint-I/parts/` file finds no references to these p7 labels. Current I confinement (`p5-confinement.tex`) uses the Part 3 torus/barrier/continuation route. Keep these interfaces reusable, but mark this as prospective reuse rather than a verified existing consumer. Likewise Part 12 has no direct p6/p7 result reference. Part 11 L89 explicitly says `energy-core` “is not applied”; only its argument is repeated. Correct §8's attribution rather than claiming a frozen-solution application that was not found.

### N4 — LOW: make the openness convention explicit for `telescope`

The signature asks `IsOpen (U (i+1))` for the holomorphic/symplectic conjunction; the literal blueprint says “subsets” and “holomorphic”. Interpreted as holomorphic on neighborhoods this is the usual harmless domain convention, and all advertised normal-form Uᵢ are open `Dom` sets. There is no application failure here. State that convention in the blueprint/design, or use neighborhood holomorphy if arbitrary nonopen sets are intended. This is not being treated as an extra geometric assumption on the actual consumers.

### N5 — MEDIUM: two Mathlib proof-plan citations need correction

Design §7.1 N6-4 names `map_sum_le` for the seminorm triangle inequality. A supplementary probe in the seminorm environment found no such unqualified identifier. Replace that citation with a local finite-sum induction using `map_add_le_add`, whose type was checked, or name and prove the intended finite-sum helper. This does not refute the `telescope` statement. The same probe checked `fderiv_sum`, `fderiv_comp`, `DifferentiableOn.differentiableAt`, `DifferentiableOn.div`, `ContDiffOn.restrict_scalars`, `HasFDerivAt.restrictScalars`, `Complex.reCLM`, `Set.InjOn.comp`, `le_of_tendsto`, `Summable.add` and `DifferentiableOn.comp`; the actual checked type of `DifferentiableOn.div` from `Mathlib.Analysis.Calculus.Deriv.Inv` has a scalar domain `s : Set 𝕜`, so it does not directly apply to the vector-parameter coefficient quotients in N6-2. Replace that proof-plan application by `DifferentiableOn.mul` and `DifferentiableOn.inv` after rewriting division as multiplication by inverse. Those general Fréchet versions work on the required parameter carrier and require only the already proved nonvanishing divisor. No new hypothesis is needed.

## Complete signature ledger

PASS means the mathematical statement/definition at the specified source interface is acceptable, possibly through the explicit bridges below. It does not mean its body is proved. F1 affects the dependency readiness of downstream stability proofs without making all their target statements false. Names in the first section are `KAM.NormalForm.*`, in the second `KAM.Stability.*`; the first two stubs are `KAM.Weighted.*`.

| Lean name (original line) | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `projMode` (L51) | `bpN:p4:projections` | PASS | Verbatim generalized upstream stubs; remove on landing. |
| `truncate` (L56) | `bpN:p4:projections` | PASS | Verbatim generalized upstream stubs; remove on landing. |
| `zBall` (L72) | `bpN:p6#data` | PASS | Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `freq` (L75) | `bpN:p6#data` | PASS | Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `dotC` (L78) | `bpN:p6#data` | PASS | Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `conjExp` (L81) | `bpN:p6#data` | PASS | Literal cutoff, gradient, pairing, conjugate exponent; positive-parameter guards at use. |
| `IsNonresonant` (L84) | `bpN:p6:setting / iterative-direct` | PASS | Correct point sets, max norms and divisor threshold. |
| `FreqLipschitz` (L88) | `bpN:p6:setting / iterative-direct` | PASS | Correct point sets, max norms and divisor threshold. |
| `DivisorBound` (L92) | `bpN:p6:setting / iterative-direct` | PASS | Correct point sets, max norms and divisor threshold. |
| `IsDecomp` (L98) | `bpN:p6:setting` | PASS | Finite decomposition and explicit weighted bound; no hidden proof field. |
| `starNorm` (L107) | `bpN:p6:setting` | PASS | Finite decomposition and explicit weighted bound; no hidden proof field. |
| `lipschitz` (L111) | `bpN:p6:lipschitz` | PASS | Holomorphy of h supplies regularity of freq; operator/entry constants preserved. |
| `lipschitz_entries` (L116) | `bpN:p6:lipschitz` | PASS | Holomorphy of h supplies regularity of freq; operator/entry constants preserved. |
| `divisor` (L123) | `bpN:p6:divisor` | PASS | Both thresholds retained; nonnegative K,L and p>1 are source data. |
| `homGen` (L132) | `bpN:p6:homological` | PASS | Explicit finite-mode constructions on the guarded locus; 2π and sign correct. |
| `homRes` (L138) | `bpN:p6:homological` | PASS | Explicit finite-mode constructions on the guarded locus; 2π and sign correct. |
| `homological_direct` (L143) | `bpN:p6:homological / iterative-direct` | FAIL | Source statement passes for equal dimensions; advertised Part 11 application has incompatible carrier (F3). |
| `homological` (L143) | `bpN:p6:homological` | PASS | Source-form divisor premises, support, identity, estimates and conditional reality retained. |
| `bracket_g` (L187) | `bpN:p6:bracket-g` | PASS | Correct 2/e factor and decomposition weights; monotone replacement by bounds is valid. |
| `iterMap` (L201) | `bpN:p6:iterative` | PASS | Same upstream flow/domain; concrete update and residual, guarded against junk flow. |
| `iterG` (L206) | `bpN:p6:iterative` | PASS | Same upstream flow/domain; concrete update and residual, guarded against junk flow. |
| `iterF` (L211) | `bpN:p6:iterative` | PASS | Same upstream flow/domain; concrete update and residual, guarded against junk flow. |
| `IterHyp` (L218) | `bpN:p6:iterative-direct` | PASS | Source divisor premise and smallness only; correct dimensionless ratio. |
| `iterU` (L238) | `bpN:p6:iterative-direct` | PASS | Source divisor premise and smallness only; correct dimensionless ratio. |
| `iterative_direct_a` (L248) | `bpN:p6:iterative / iterative-direct (a)` | PASS | Widths, symplecticity, integer translations, injectivity and left inverse match. |
| `iterative_direct_b` (L264) | `bpN:p6:iterative / iterative-direct (b)` | PASS | Both displacements, scaled bound and derivative estimate match. |
| `iterative_direct_c` (L276) | `bpN:p6:iterative / iterative-direct (c)` | PASS | Identity is definitional; resonant increment and remainder class retained. |
| `iterative_direct_d` (L284) | `bpN:p6:iterative / iterative-direct (d)` | PASS | Denominator, 2/e, tail exponential and all parameter dependences match. |
| `iterative_direct_e` (L291) | `bpN:p6:iterative / iterative-direct (e)` | PASS | Reality on the correct domains; symmetry of Λ required conditionally. |
| `iterHyp_of_source` (L303) | `bpN:p6:iterative` | PASS | Derives direct premises from N1,N2; not a conclusion-shaped assumption. |
| `chain` (L316) | `bpN:p6:telescope` | PASS | Correct composition order, any-bound displacement, chain rule and injectivity; see N4 for open sets. |
| `telescope` (L320) | `bpN:p6:telescope` | PASS | Correct composition order, any-bound displacement, chain rule and injectivity; see N4 for open sets. |
| `nfSteps` (L339) | `bpN:p6:normal-form#data` | PASS | Correct nonnegative floor; step states deliberately private future proof obligations. |
| `normal_form` (L342) | `bpN:p6:normal-form` | FAIL | Omitted g=g₀ in zero-step and Case B branches (F2); other clauses match. |
| `nonresonant_case` (L376) | `bpN:p6:nonresonant-case` | PASS | True stronger bound-predicate statement; id/zero clauses follow definitionally. |
| `cpx` (L394) | `bpN:p7:setting` | PASS | Correct real and complex neighborhoods, including empty/nonpositive-radius cases. |
| `realNbhd` (L397) | `bpN:p7:setting` | PASS | Correct real and complex neighborhoods, including empty/nonpositive-radius cases. |
| `realStrip` (L400) | `bpN:p7:setting` | PASS | Correct real and complex neighborhoods, including empty/nonpositive-radius cases. |
| `realH` (L404) | `bpN:p7:setting` | PASS | Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `IsOrbit` (L408) | `bpN:p7:setting` | PASS | Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `reMap` (L413) | `bpN:p7:setting` | PASS | Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `thetaGradR` (L418) | `bpN:p7:setting` | PASS | Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `hessR` (L422) | `bpN:p7:setting` | PASS | Uses frozen fields/real restriction; correct derivative slots; local totality bridge documented. |
| `isOpen_realNbhd` (L424) | `bpN:p7:setting` | PASS | Elementary neighborhood facts; positive strip required exactly where needed. |
| `realNbhd_mono` (L426) | `bpN:p7:setting` | PASS | Elementary neighborhood facts; positive strip required exactly where needed. |
| `realInclusion₂_mem_Dom_iff` (L430) | `bpN:p7:setting` | PASS | Elementary neighborhood facts; positive strip required exactly where needed. |
| `realHamiltonian_eq_realH` (L435) | `bpN:p7:setting / p10:hypotheses-check` | PASS | Explicit bridges to frozen objects; no parallel frequency or Hamiltonian assumed equal. |
| `freq_realInclusion` (L439) | `bpN:p7:setting / p10:hypotheses-check` | PASS | Explicit bridges to frozen objects; no parallel frequency or Hamiltonian assumed equal. |
| `real_system` (L447) | `bpN:p7:real-system` | PASS | Smoothness, field identification, periodicity and energy retained; Part 3 supplies existence/uniqueness. |
| `theta_derivative` (L467) | `bpN:p7:theta-derivative` | PASS | Pointwise-in-action sum, Euclidean consequence and value bound correct. |
| `resSpan` (L476) | `bpN:p7:resonant-gradient` | PASS | Arbitrary Λ; coefficient support gives membership in real span. |
| `resonant_gradient` (L481) | `bpN:p7:resonant-gradient` | PASS | Arbitrary Λ; coefficient support gives membership in real span. |
| `conjugation` (L491) | `bpN:p7:conjugation` | PASS | Holomorphic real symplectic map, mapping and conjugacy; genuine orbit conclusion. |
| `preimage` (L506) | `bpN:p7:preimage` | PASS | All displacement, reality and contraction-radius premises retained; positive r′,s′ implied. |
| `preimage_nfl` (L522) | `bpN:p7:preimage-nfl` | PASS | Correct witness-level form; action displacement and r/128 conclusion retained. |
| `IsActionNorm` (L536) | `bpN:p7:transfer / exit-ball` | FAIL | Does not require N(0)=0 or homogeneity; false exit theorem follows (F1). |
| `isActionNorm_norm` (L542) | `bpN:p7:transfer / exit-ball` | PASS | Both intended examples satisfy current fields and the proposed corrected fields. |
| `isActionNorm_euclid` (L544) | `bpN:p7:transfer / exit-ball` | PASS | Both intended examples satisfy current fields and the proposed corrected fields. |
| `transfer` (L548) | `bpN:p7:transfer` | PASS | T1–T3 explicit; arbitrary monotone admissibility predicate valid; generalized gauge sufficient here. |
| `stopped_extension` (L573) | `bpN:p7:stopped-extension` | PASS | True stronger local statement: no global regularity needed beyond curve and confinement premise. |
| `exit_ball` (L585) | `bpN:p7:exit-ball` | FAIL | False for allowed shifted norm and constant curve (F1). |
| `nonresonant` (L376) | `bpN:p7:nonresonant` | PASS | Source N1,N2, smallness, stopped orbit and sr exp(κ/6)/(5ε) preserved. |
| `IsOrthProj` (L615) | `bpN:p7:ext-linalg / resonance-data` | PASS | Idempotent self-adjoint linear projection; existence onto prescribed subspace. |
| `exists_orthProj` (L621) | `bpN:p7:ext-linalg / resonance-data` | PASS | Idempotent self-adjoint linear projection; existence onto prescribed subspace. |
| `resSpace` (L625) | `bpN:p7:resonance-data` | PASS | Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `IsCloseToRes` (L628) | `bpN:p7:resonance-data` | PASS | Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `IsMConvex` (L632) | `bpN:p7:resonance-data` | PASS | Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `IsQuasiConvex` (L636) | `bpN:p7:resonance-data` | PASS | Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `HessBound` (L641) | `bpN:p7:resonance-data` | PASS | Correct real pairing, attained distance and Euclidean curvature/bilinear bounds. |
| `energy_core` (L646) | `bpN:p7:energy-core` | PASS | All four conclusions, C²/C¹ local regularity, projection condition and segment preserved. |
| `ResSetting` (L679) | `bpN:p7:s-energy#rs` | PASS | Source RS only; finite-norm bounds, δ/4M and strict admissibility unchanged. |
| `resRho` (L704) | `bpN:p7:s-energy#rs` | PASS | Source RS only; finite-norm bounds, δ/4M and strict admissibility unchanged. |
| `IsAdmissible` (L707) | `bpN:p7:s-energy#rs` | PASS | Source RS only; finite-norm bounds, δ/4M and strict admissibility unchanged. |
| `admissible` (L716) | `bpN:p7:admissible` | PASS | Ball inclusion, 5δ/4+M distance bound and initial bound retained. |
| `no_exit` (L726) | `bpN:p7:no-exit` | PASS | All three exit/curvature/time premises retained literally. |
| `resonant_lemma1` (L739) | `bpN:p7:resonant-lemma1 (off graph)` | PASS | Convex stopped estimate and zero-denominator infinite-time case retained. |
| `resonant_lemma2` (L747) | `bpN:p7:resonant-lemma2` | PASS | Both R conditions retained; any Ω bound legitimately replaces maximum. |
| `resonant_prop2` (L763) | `bpN:p7:resonant-prop2` | PASS | Complex Euclidean Hessian, √n, added Mr bound, r/2 and all-time Λ=univ preserved. |

## Consumer verdicts

| Consumer | Verdict | Applicability evidence / remaining obligation |
|---|---|---|
| N Part 7 from Part 6 | FAIL readiness; retained targets otherwise match | Correct normal-form domains, real witnesses and quantitative displacements are available; F2 removes an explicit source clause and F1 blocks the stated exit API used in the proof. |
| N Parts 8–9 | PASS statement interface | `zBall` is the ℓ¹ cutoff, `IsNonresonant` uses the complex frequency on the real base, and `freq_realInclusion` bridges the frozen real frequency. Callers must supply Euclidean-to-ℓ¹ cutoff inclusion, real-tube containment, and √n radius conversion. Proposition 2 retains the complex Hessian and Mr≤ℓ/2; neither is silently dropped. |
| N Part 10 / frozen N solution | PASS bridge design | `realHamiltonian_eq_realH` identifies the actual frozen Hamiltonian globally; `real_system` gives local differentiability. Existing `KAM.ODE.ham_reduction` (Hamiltonian.lean L154–172) bridges the frozen predicate to `IsSolutionIn`; then `stopped_extension` handles arbitrary total field extensions. No new premise of the frozen theorem is introduced. |
| N Part 11 | FAIL advertised direct homological reuse | F3. The weighted slow-pair bracket, composition, conjugation and energy arguments require their own Part 11 variants. `p11c` L89 expressly disclaims applying canonical `energy_core`. The first-exit lemma can be used on the projected fast curve once F1 is fixed. |
| N Part 12 | PASS, no direct consumer found | Search found no direct p6/p7 result use. Existing source references/arguments in this part do not establish a new application of the canonical signatures. |
| P Part 2 | PASS with explicit wrapper N1 | Direct divisor form avoids any unjustified Lipschitz premise; q=1 can be obtained by rescaling α, with the same generator and map. P proves its two-scale displacement, loss-offset iteration, oscillator and anisotropic variants separately; the scalar N statement is not sufficient for those stronger conclusions by itself. |
| I | PASS for available canonical interface; consumer attribution needs N3 | Frozen I and N solution predicates have identical derivative/domain clauses and existing `ham_reduction` bridges both. No current blueprint-I use of the advertised energy/resonant results was found. No claim that these lemmas prove I confinement is made. |

The brief's p3 consumer search was also performed in I/P. Its results concern the already existing ODE layer (including Newton/restricted reductions), not a new p6/p7 signature obligation. No Newton or restricted solution predicate is redefined or changed here.

## Frozen objects, definitions and package verdicts

**Frozen objects: PASS.** Read the actual `KAM/Frozen/Defs/{ActionNbhd,FrequencyMap,HamiltonianVectorField,HamiltonianVectorFieldC,RealHamiltonian}.lean`, `KAM/Frozen/Nekhoroshev/Defs/{RealPart,IsSolutionOn}.lean` and `KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean`. `IsOrbit` uses the existing generic ODE predicate with the actual frozen vector field. The total `realH` is the real part of complex restriction, not an assumed copy of the frozen Hamiltonian: an explicit equality theorem is a package obligation. `freq_realInclusion` similarly carries holomorphy and reality and identifies the frozen gradient. The difference from the blueprint's off-domain zero extension is harmless on the open real domain, where derivatives are local. `realNbhd` and `cpx` match `actionNbhd` by the documented existing domain bridge.

**Definitions and structures: FAIL (F1).** The other definitions use ordinary total-function conventions with appropriate domain guards. In particular `homGen` divides only under a positive divisor hypothesis when used; its selected modes are finite for K≥0. `iterMap` uses the same `flow` and domain as `CanonData.omega` and the prescribed `ComposeData.omega`; existence/uniqueness comes from the small-field package, so the identity fallback in the total definition is not being used as a proof. Negative/zero radius neighborhoods are empty and cause no junk-norm inference. `starNorm` is explicitly decomposition dependent and the norm bounds are summable predicates, not uncontrolled tsums. All structure fields other than the incomplete norm fields are source premises or typing data; no global instance on bare functions/matrices is proposed. `IsOrthProj` describes an actual self-adjoint idempotent linear map; no conclusion is hidden as an existence assumption.

**Packages: PASS mathematical ordering, WITH N2 scheduling correction.** No mathematical import cycle or planned >1500-line individual Lean file was found. All external unfinished W4-7/C5-8/9/10 inputs are declared as unfinished, not counted as proved. Reviewed their referenced signature domains against the proposed `iterMap`; the literal omega choices agree. The N6-5 facade cannot be delivered before N6-6/7 as written; move facade ownership before briefs are dispatched. F3's generalized coefficient core/bridge must also receive explicit ownership. Approximate line counts are estimates, not elaboration guarantees.

**Constants and dropped premises:** no other changed normalization or wider dependence of a constant was found. The 2π factors use geometric strip widths; the bracket gain is 2/e; the normal-form remainder is exp(−κ/6); the time factors 5, 12, 288 and the Euclidean/max √n conversion remain explicit. Bound predicates are monotone replacements for finite norms, with the sharp norm as an instance; Ω/B are quantified bounds. The multiplied time inequalities correctly include all times when their nonnegative denominator vanishes. Allowing n=0 where the target remains true, omitting positive radius when membership makes it automatic/vacuous, dropping class assumptions in the purely algebraic `nonresonant_case`, and omitting Hamiltonian regularity from the topological `stopped_extension` are true strengthenings. The arbitrary monotone `adm` generalization does not require that 0 be admissible: if any queried time is admissible, monotonicity supplies all intermediate times. N1 was checked and rejected as a failure; F1 survived refutation.

## Mathlib and validation receipts

The named Mathlib inputs in §§2/7.1 were checked in temporary probes; N5 records the unavailable sum-helper spelling and the scalar-domain restriction of the division lemma. The main probe checked:

- `ContractingWith.exists_fixedPoint`, with `CompleteSpace`, an initial point and finite edistance; restriction to the complete closed subtype is the planned use.
- `taylor_mean_remainder_lagrange`, with `ContDiffOn` on `uIcc` and differentiability of the iterated derivative on `uIoo`; the C² segment supplies these for order one.
- `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, `Convex.norm_image_sub_le_of_norm_fderiv_le`, `norm_image_sub_le_of_norm_deriv_le_segment'`.
- `LinearMap.BilinForm.orthogonal`, `.isCompl_orthogonal_of_restrict_nondegenerate`, `Submodule.orthogonalBilin`, `Submodule.linearProjOfIsCompl`, `Matrix.toBilin'`.
- `Real.add_one_le_exp`, `Real.exp_one_gt_d9`, `Real.log_two_gt_d9`, `tsum_geometric_of_lt_one`, `HasFDerivAt.comp`, `ContinuousLinearMap.opNorm_le_bound`, `Finset.sum_le_card_nsmul`.

The bilinear-form complement theorem requires reflexivity and nondegeneracy of the restricted dot form, supplied by positivity in the proposed proof. `Submodule.linearProjOfIsCompl` returns a map into the subspace subtype: compose with `V.subtype` for the advertised ambient endomorphism. It exists as a deprecated alias; `projectionOnto` is the current name. No fictitious projection API is required.

Exact fresh checks:

```text
# One run of the unmodified signature copy, under both I/N/P compile slots and the worker lock:
flock /tmp/gp-worker-build.lock flock /tmp/inp-lean-slot-1.lock \
  flock /tmp/inp-lean-slot-2.lock env LEAN_NUM_THREADS=1 nice -n 5 \
  lake env lean .drafts/scratch/NPart67Signatures.lean
exit 0; exactly 39 warnings, each: declaration uses `sorry`; no errors.

# Temporary Mathlib-name and counterexample probe, serialized with the same locks/environment:
... lake env lean .lake/abi-scratch/N67AuditProbe.lean
final run: exit 0; every #check resolved; no warnings/errors.
'badN_allowed' depends on axioms: [propext, Classical.choice, Quot.sound]
'exit_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]

# Source lint, including its own Lean ABI subprocess, serialized after the probe:
flock /tmp/gp-worker-build.lock flock /tmp/inp-lean-slot-1.lock \
  flock /tmp/inp-lean-slot-2.lock env LEAN_NUM_THREADS=1 nice -n 5 \
  sh scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (401 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The first probe missed the `Mathlib.LinearAlgebra.Matrix.BilinearForm` import for `Matrix.toBilin'`; after adding that import, the name and type checked. This was a probe import omission, not a design defect. An initial lint run was stopped before its ABI stage to ensure its Lean subprocess ran serially after the probe; the complete serialized rerun above is the lint receipt. A supplementary helper-name probe initially reported the unavailable `map_sum_le` spelling (N5) and a missing division import. Subsequent checks resolved the division name, exposed its scalar-domain restriction, and verified the replacement `map_add_le_add`, general `DifferentiableOn.inv`/`.mul` and the remaining helper names (final auxiliary probe exit 0). All auditor-started Lean work used one thread and nice 5, without heartbeat, recursion-depth or synthesis-budget overrides. Other sessions' work was neither terminated nor modified. No `lake build` target exists for this Markdown-only audit: the exact requested signature elaboration is the targeted Lean check, with no library rebuild or cache operation.

The draft's 39 theorem bodies are `sorry`; their axiom sets cannot certify mathematical results. The counterexample probes above, unlike the draft theorem obligations, contain no `sorry`. Proposed replacement statements in this report have not been compiled as repairs.

## Closeout and limits

All 78 declarations have a row; four rows fail (the norm structure, first-exit theorem, missing normal-form clause, and advertised consumer-capable homological interface). Findings were checked again against their own possible defenses: F1 survives a formal counterexample, F2 survives definitional/equality and zero-step checks, F3 survives dimension-reparameterization and missing-bridge checks. The P q=1 concern was refuted and downgraded to N1. The facade issue remains a concrete scheduling correction N2.

No new suspected defect in the pinned Pöschel source is asserted by this audit. F1–F3 are design errors/omissions; N2–N5 are design bookkeeping/API notes. Existing source errata/deviations are preserved, including the negative exponential correction and added resonance-radius hypotheses. This audit checks blueprint/packet-to-design fidelity; it does not independently re-audit the pinned PDFs or implementation proofs, certify the unfinished upstream providers, freeze new declarations, or claim any track/root closure. No frozen file, source, manifest, original signature file, handoff, generated root, or README was edited.

**Closeout:** FAIL pending corrected norm/exit contract, restored exact normal-form cases, and an explicit parameter-capable homological interface or proved consumer bridge. Re-audit those changes before releasing the affected targets. Only the designated report is retained.
