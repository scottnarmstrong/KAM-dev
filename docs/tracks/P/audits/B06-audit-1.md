# B06 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the B06 infrastructure package. No frozen anchor or provider is assigned to B06, so frozen-provider type equality and seal-body tests are not applicable; this is not a seal of a campaign theorem.

Audited checkout: `/root/code/KAM-inp-p11b-b06`, HEAD `e1e6b1847619f0b4bd1a1d0d5a13e342d6301442`; comparison `git diff inp...HEAD`, with `inp` at `0c4b228c40c18845100d2ce1ebc27d8727a509ad`. The diff adds only `KAM/Planetary/WeakKAM/Initial.lean` (250 lines). The pre-existing untracked `B06-handoff.md` was read and left unchanged. This report is written in the package worktree as explicitly requested, overriding the generic brief's main-worktree destination.

## Contract and completeness

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief, B06 handoff, track-P statement, P11B design and both design audits. Checked the design's B06 row (line 232), graph mapping (lines 68–70), and the entire “Proof plans and release gates” section (lines 276–300). That section assigns no additional B06 export. Checked the live signature file `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean:271–288` and the corresponding embedded design signature at lines 619–636.

The assigned slice is complete: `selectionInitial`, `initial`, domain step `stepP:p11a:in-dom`, and Taylor step `stepP:p11a:in-taylor`. The blueprint contract is `blueprint-P/parts/p11a3-iteration-selection.tex:183–195`; its standing data and max-norm convention are at lines 30–41. No B07 admissibility or B10 iteration obligation is being counted as B06 work. The blueprint's parenthetical symplectic translation observation is not a separate B06 export in the approved signature/design.

All names in the table are under `KAM.Planetary`.

| Node / role | Declaration and source line | Verdict | Reason |
|---|---|---|---|
| initial object | `selectionInitial` :26 | PASS | Body exactly matches the signature and H₀ formula on its whole carrier. |
| in-dom | `selectionInitial_segment_mem` :31 | PASS | A witness in K and triangle inequality place every b+sη, 0≤s≤1, in K+(t₀+s₀). No convexity of K is assumed. |
| collar inclusion | `selectionInitial_actionNbhd_mono` :44 | PASS | Radius monotonicity, with no added positivity restriction. |
| coordinate derivative | `selectionInitial_fderiv_apply` :48 | PASS | Linear decomposition in the coordinate basis; valid even when the default fderiv is zero. |
| holomorphic gradient | `selectionInitial_gradient_differentiableOn` :57 | PASS | Finite-dimensional holomorphic regularity on the open collar, then evaluation on coordinate vectors. |
| in-taylor | `selectionInitial_taylor` :66 | PASS | Pointwise n C₁ ‖η‖²/2 bound; uses precisely the standing Hessian bound and collar constraints. |
| bpP:p11a:initial | `initial` :158 | PASS | Exact signature, binder order, constants, carriers and all four conjunction clauses. `_hs` versus `hs` is only an alpha-renaming. No extra premise. |

## Definitions and proof review

The only new definition is `selectionInitial`. It is H₀(θ,η,b) = h(b+η)+f(θ,b+η)−h(b), rather than R₀ itself. The first two clauses explicitly subtract the complex coordinate-gradient pairing N₀. There is no branch, inverse, selected witness, fallback, or domain-dependent substitution. The total functions h and f are evaluated literally everywhere; the theorem's domain guarantees their analytic premises at every point used. The surrounding exposed public section makes the definition body available.

The domain proof uses t₀≤ϑ, s₀≤ϑ and strict membership to keep the whole segment inside the open collar K+2ϑ, including the endpoints. Openness upgrades differentiability within the collar to differentiability at the relevant points. Holomorphy in all three variables follows by composing h, f and the gradient with the linear projections and translation, then taking products and finite sums (lines 186–209).

For Taylor, the convex set used in the mean-value argument is the segment itself, not K or its collar. The Hessian operator bound gives each coordinate gradient increment at b+sη at most C₁s‖η‖. Therefore the directional remainder derivative has norm at most n C₁s‖η‖². The fencing boundary B(s)=n C₁‖η‖²s²/2 has exactly that derivative and starts at zero. Evaluation at s=1 gives n C₁‖η‖²/2; adding the perturbation bound and using ‖η‖<s₀ gives ε+n C₁s₀²/2. This matches the blueprint's max-norm factor n and factor 1/2 without an unproved integral identity.

Periodicity is inherited from `hf.periodic` at the translated domain point (lines 224–226). Reality is inherited from `d.real` at b and b+η and `hf.real` at the translated real phase (lines 227–248). These last two exported clauses are for H₀ exactly as in the approved signature; the angle-independent N₀ automatically preserves periodicity. This audit does not claim a separate exported theorem about the reality of the complex gradient or a frozen physical torus.

The helpers have only source/typing premises. `SelectionData` supplies the source Hessian/holomorphy/reality assumptions; `SelectionPerturbation` supplies the source perturbation assumptions. No construction output or desired Taylor estimate is assumed. Stronger helper generality: the segment and radius lemmas do not require `SelectionData`, and the Taylor lemma omits the positive-radius premises, since nonempty membership supplies what its proof needs.

## Independent validation

All Lean/Lake commands were run serially, with `LEAN_NUM_THREADS=1` and niceness 5. No library clean, update, cache fetch, resource override, or frozen/generated edit was performed.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b06 KAM.Planetary.WeakKAM.Initial
   [inp-gate] slot 2 acquired 16:18:46 for KAM.Planetary.WeakKAM.Initial
   Build completed successfully (9084 jobs).
   exit 0
   ```

   The wrapper runs `nice -n 5 lake build`; this was a targeted build using the existing overlay.

2. Fresh signature/body and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B06Audit.lean
   exit 0
   ```

   The probe imported `KAM.Planetary.WeakKAM.Initial`, copied the literal signature-file definition as `b06ExpectedSelectionInitial`, and copied the literal theorem as `b06ExpectedInitial`. Its body was `by exact KAM.Planetary.initial d f ε t₀ s₀ hf ht ht' hs hs'`, applying every explicit binder in order. It also checked:

   ```lean
   example : b06ExpectedSelectionInitial = @selectionInitial n := rfl
   example : type_of% @b06ExpectedInitial := @initial
   example : type_of% @initial := @b06ExpectedInitial
   ```

   `#print axioms` was run for every new declaration, including the definition. Exact output:

   ```text
   'KAM.Planetary.selectionInitial' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionInitial_segment_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionInitial_actionNbhd_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionInitial_fderiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionInitial_gradient_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionInitial_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.initial' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Initial
   replaying KAM.Planetary.WeakKAM.Initial
   exit 0
   ```

   This package has one module and no separate provider/lemma module, so the single invocation covers the complete new proof module.

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (784 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failure is the explicitly permitted stale generated-root exception. No generated file was changed. All remaining lint gates passed.

5. Static hygiene and boundary checks:

   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   - `git diff --check inp...HEAD`: empty, exit 0.
   - New file: 250 lines, copyright, `module`, both `public import` declarations, module docstring, exposed public section. No forbidden proof escape, resource override or `EuclideanSpace` token.
   - Recursive local import inspection: 91 visited import names, 12 frozen definition modules, no provider and no DRAFT_SORRY import. Frozen theorem/provider seal checks are inapplicable because none are imported or introduced.
   - Declaration-name scan throughout KAM: no other declaration has any of the seven new short names. Every new declaration is inside `KAM.Planetary`. An additional fresh environment probe checked `getEnv.contains (Name.mkSimple s)` for each of the seven names and rejected any root declaration collision:

     ```text
     LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B06RootNames.lean
     B06 ROOT NAMES OK
     exit 0
     ```

   - Both audit probes were deleted after successful elaboration. Final `git status --short` shows only this new report and the pre-existing untracked handoff. `git diff --check` exits 0; the tracked source is unchanged by the audit.

## Notes, errata and limitations

No suspected mathematical blueprint or pinned-source defect was found in this B06 slice. Source comparison was against the pinned blueprint and approved design/signature, not a fresh independent transcription of the Rus01 PDF.

The proof uses the fencing/mean-value route in place of the blueprint's integral Taylor formula. This is a proof-method deviation only; the literal statement, coefficient and premises agree. `KAM.Head.DerivativeBounds` is an additional existing external API import for collar openness, with no provider or draft-anchor dependency.

Minor cleanup only: lines 231–234 repeat the same local `have e`; the second shadows an identical proof. It has no semantic effect and is not a public name collision. `_hs` is unused, preserving the approved theorem type.

The package verdict does not close P-FIXED or any other frozen anchor. The confirmed generated-root lint exception is left to the orchestrator; this audit did not regenerate `KAM.lean`.
