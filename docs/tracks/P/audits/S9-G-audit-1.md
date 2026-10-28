# Independent S9-G audit 1

Verdict: **PASS WITH NOTES** for the scoped infrastructure package. No frozen anchor is proved or sealed by this package; provider/frozen-type equality and seal-body probes are not applicable.

Audited only `KAM/Planetary/SecularSpectrum/GoodPolynomial.lean`, 287 lines, at HEAD `8d5767d684b5cf6041cf3e8a54e43818be0c67c9`, compared with `inp` at `0d0459067371b06163dac863ebbc269c47b67987` using `git diff inp...HEAD`. The complete branch diff also includes five oscillator modules changed by the inherited `58f454a` rename; those modules are outside the explicit AUDIT FOCUS. The handoff's “No other file touched” describes this package's implementation, not the full branch diff. No verdict is issued on those inherited changes.

Read the governing brief, AGENTS.md, PLAN.md, DECISIONS.md, S9-G handoff, P statement, P810 design including S9-G and the gs-c analytic-route note, both design audits, p9 blueprint good/good-set and external-fact statements, upstream carrier/data/spectrum/analytic-zero interfaces, and the relevant frozen P-G/P-PLANAR/P-FIXED context. The signature file is absent from this package worktree; the controlling original was read at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2.

## Declaration and node review

All names below are relative to `KAM.Planetary.SecularSpectrum`. PASS rows describe static mathematical/contract review; final independent check receipts follow below. Each new public declaration is inventoried.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| bpP:p9:good | `k4` | PASS | Exact signature body: integer vectors with positive l1 size at most four. |
| bpP:p9:good | `nr4` | PASS | Exact signature body: injectivity and all literal k4 relations nonzero. |
| bpP:p9:good | `discriminant` | PASS | Exact signature body: squared differences over j < l. |
| bpP:p9:good | `k4_finite` | PASS | Exact signature type; embeds in the finite pointwise interval [-4,4]. |
| bpP:p9:good | `good` | PASS | Exact signature body; proved finite k4, all permutations, no assumed finiteness. |
| good-locus definition | `goodAxes` | PASS | Exact signature body; restricted to positive increasing axes. |
| simple-locus definition | `simpleAxes` | PASS | Exact signature body; discriminant nonzero on axes. |
| symmetry helper | `discrGen` | PASS | Literal discriminant formula over a commutative ring. |
| symmetry helper | `upperProd` | PASS | Product of upper-triangular differences; other factors are one. |
| symmetry helper | `pairProd` | PASS | Product over all distinct ordered pairs; diagonal factors are one. |
| symmetry helper | `pairSign` | PASS | Product of -1 for each upper-triangular pair. |
| stepP:p9:gs-a helper | `discrGen_eq_sq` | PASS | Discriminant equals square of upper product. |
| stepP:p9:gs-a helper | `pairSign_mul_self` | PASS | Square of the finite sign product equals one in any commutative ring. |
| stepP:p9:gs-a helper | `pairProd_eq` | PASS | Correct sign relating ordered-pair and squared upper products. |
| stepP:p9:gs-a helper | `discrGen_eq` | PASS | Sign cancels using its square; no division or domain assumption. |
| stepP:p9:gs-a helper | `pairProd_comp` | PASS | Reindexes pairs by prodCongr; preserves distinctness. |
| stepP:p9:gs-a helper | `discrGen_comp` | PASS | Permutation invariance from ordered pairs and sign identity. |
| stepP:p9:gs-a helper | `permFac_comp` | PASS | Left multiplication permutes the entire permutation group. |
| bpP:p9:good-set(a) | `good_comp` | PASS | Unconditional invariance for every real vector. |
| stepP:p9:gs-b helper | `discriminant_ne_zero_iff` | PASS | Over the reals, product nonzero iff every pair differs. |
| stepP:p9:gs-b helper | `perm_sum_eq` | PASS | Reindexes coefficients by inverse permutation. |
| bpP:p9:good-set(b) | `good_ne_zero_iff` | PASS | Stronger than axes-only equivalence; rearrangement preserves k4 l1 size. |
| stepP:p9:gs-a helper | `goodPoly` | PASS | Universal multivariate polynomial with literal integer coefficients and finite factors. |
| stepP:p9:gs-a helper | `eval_goodPoly` | PASS | Evaluation gives the actual good function on its whole carrier. |
| stepP:p9:gs-a helper | `goodPoly_isSymmetric` | PASS | Polynomial-level permutation invariance, not just an assertion about eigenvalues. |
| bpP:p9:good-set(a), e-fts | `good_characteristic` | PASS | Exact signature; polynomial chosen before M and hM, only coefficients 0 through n-1. |
| analytic helper | `charpoly_coeff_eq_aeval` | PASS | Universal charpoly coefficient evaluated at actual matrix entries. |
| analytic helper | `analyticAt_charpoly_coeff` | PASS | Derives coefficient analyticity from analytic matrix family in any real normed source. |
| bpP:p9:good-set(a,b), gs-a/gs-b | `good_set` | PASS | Exact signature, including analytic-on-neighbourhood and permutation conjuncts. |
| bpP:p9:good-set(c), gs-c#analytic-route | `good_set_dichotomy` | PASS | Exact signature; open connected subset of axes, relative density, actual Lebesgue-null bad set. |

The four principal theorem types and six principal definition bodies match the signature text exactly after whitespace normalization. There is no new premise, altered binder order, wider constant dependence, changed carrier, or weakened requested conclusion. The additional lemmas are algebraic/analytic proof cuts with ordinary source or typing hypotheses, not assumed package conclusions.

## Definition classification and proof review

The six contract definitions (`k4`, `nr4`, `discriminant`, `good`, `goodAxes`, `simpleAxes`) are direct source objects/predicates on `Fin n → ℤ` or `Fin n → ℝ`, or literal restricted loci. The four generic ring helpers (`discrGen`, `upperProd`, `pairProd`, `pairSign`) are finite algebraic products; their conditional one factors are the multiplicative identities for omitted pairs, not junk values. `goodPoly` is the universal polynomial whose evaluation is proved equal to `good` everywhere. There are eleven definitions, no new abbrevs, structures or hidden instance assumptions. The exposed public noncomputable section permits unfolding.

The sign in the discriminant symmetry argument is retained correctly: `pairProd = pairSign * upperProd^2` and `pairSign^2 = 1`. Nonzero characterization reindexes k by the inverse permutation and uses invariance of both l1 inequalities. The symmetric-polynomial equivalence produces a polynomial independent of the matrix. Vieta uses index `i.rev`, corresponding to coefficient n-1-i, and the factor `(-1)^(i+1)` twice, so signs cancel. The leading coefficient is fixed to one and needs no extra variable. The n=0 case has empty products and an empty coefficient vector; no nonempty-spectrum hypothesis is introduced.

Analyticity is established through universal characteristic coefficients and `coeffs_analytic`, not by claiming globally analytic sorted eigenvalues. The identity expressing `good ∘ sigma` as that polynomial holds even at collisions. The dichotomy handles the identically-zero branch first; otherwise it supplies an actual nonzero point to `Nondegeneracy.generic` at r=1 and `analytic_zero_null`. Openness is ambient and the closure inclusion is density relative to B, exactly as signed off in the design. Local eigenframes and compact quantitative nonresonance estimates are separate cooperating interfaces, not new conclusions claimed here. The module imports S9-S but its composite-analytic argument does not require local eigenframe construction or root continuity.

## Hygiene and independent validation

All auditor-controlled Lean/Lake invocations are serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`. Only the report is a repository edit. Probe/log artifacts are under `.lake/abi-scratch/` and are removed after validation.

1. Targeted build (after the compile gate acquired slot 2):

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9g KAM.Planetary.SecularSpectrum.GoodPolynomial
   [inp-gate] slot 2 acquired 13:43:36 for KAM.Planetary.SecularSpectrum.GoodPolynomial
   Build completed successfully (9125 jobs).
   exit 0
   ```

   The wrapper runs `nice -n 5 lake build` for the targeted module. Its job count includes dependency replay. No warning in GoodPolynomial; replayed upstream warnings concern unused variables in Energy, Chart, Mass and LocalAnalytic.Unique, and deprecated `ite_cond_eq_false` in Coefficients.

2. Fresh signature/body/axiom probe, run after the build finished:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9GAuditProbe.lean
   exit 0
   ```

   The probe reuses the four literal signature theorem statements under anonymous `example` declarations, with direct applications of the package exports as bodies. Six further examples check definition-body equality by `rfl`. This verifies actual elaborated applicability in addition to the normalized text comparison. It does not import the draft signature file or its sorry bodies. All 19 public theorem axiom outputs, verbatim:

```text
'KAM.Planetary.SecularSpectrum.k4_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.discrGen_eq_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.pairSign_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.pairProd_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.discrGen_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.pairProd_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.discrGen_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.permFac_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.discriminant_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.perm_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eval_goodPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.goodPoly_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_characteristic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.charpoly_coeff_eq_aeval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_charpoly_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_set_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. One kernel replay invocation for the only in-scope lemma module (there is no provider):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.GoodPolynomial
   replaying KAM.Planetary.SecularSpectrum.GoodPolynomial
   exit 0
   ```

4. Source lint, after kernel replay completed:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (697 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failing condition is the explicitly permitted stale generated root. No other lint failure was emitted; no root regeneration was attempted.

Static checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
- `git diff --check inp...HEAD`: exit 0, empty output.
- `wc -l KAM/Planetary/SecularSpectrum/GoodPolynomial.lean`: `287`.
- `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/SecularSpectrum/GoodPolynomial.lean`: exit 1, no matches.
- Module header contains copyright/authors, `module`, public imports, module docstring, exposed public section. Ambient carriers are Pi types; matrix types are literal real matrices.
- Recursive local import review visited 79 KAM modules: no `KAM.Provider.*` and no `KAM.Frozen.*.Theorems.*` module. Hence there is no imported DRAFT_SORRY theorem or provider to quarantine; frozen definitions are permitted. No provider export or seal body belongs to this package.

## Findings, uncertainties, errata and scope

No mathematical or signature defect found in the audited module. No suspected pinned-source erratum or introduced mathematical deviation. This audit compares the pinned blueprint/design contracts and local implementations; it is not a fresh paper-wide source audit. Design audit 1's S9-G missing-edge finding is resolved by the explicit S10-Z import, as required in design audit 2.

The only qualification is the brief's allowed stale generated-root lint notice. No generated root regeneration, frozen/manifest edit, source repair, git state change, or unrelated-module audit was performed. Passing this infrastructure package does not prove nonidentity of good on all axes, produce a good point, or close any planetary KAM frozen theorem.

Final artifact validation: all 30 new public declarations are inventoried (11 definitions, 19 theorems/lemmas), all 19 theorem axiom outputs are recorded, no pending-check placeholders or trailing whitespace remain. The scratch probe and three scratch logs were deleted. `git diff --check` passes. Final `git status --short` lists only the new audit report and the pre-existing untracked handoff; no tracked repository file was edited.
