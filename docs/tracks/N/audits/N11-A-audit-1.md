# N11-A independent package audit 1

Overall verdict: **PASS WITH NOTES** for the assigned infrastructure slice. No provider or frozen anchor is proved by this package; seal readiness of N-PARTIAL-CONVEX is **not established**. The exact signed `orbit` theorem and its proof pass. Notes concern the already disclosed signed short name, accepted `Ext` warning, harmless tactic lint, and the permitted generated-root exception.

## Scope and evidence

Audited HEAD `9d16b3127c8a9fe9af335c5b64874bd29f32ebd8`; comparison `inp` observed at `a81e8d4215d2f99f8c148dd4ca24915a17ca95b5`. `git diff inp...HEAD` adds exactly Setting (177 lines) and Coordinates (298 lines), under `KAM/Nekhoroshev/Partial/`. Read AGENTS.md, PLAN, DECISIONS, the external package brief, current N11-A handoff/AUDIT FOCUS, N11-LEAN-DESIGN and both design audits, the track statement's partial-convex section, relevant p11a/b/c blueprint statements, the frozen partial-convex anchor and the actual frozen field/coordinate/solution definitions.

Signed authority: `/root/code/KAM-inp/.drafts/design/N11Signatures.lean`, SHA-256 `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4`. Setting SHA-256 `c0dce6491abdc47663398fdb97db57fd069d7d0b3bafe04b512a4bfe6ba23037`; Coordinates SHA-256 `61ebaaaebb2f7002638e44ac1af3fb3cb9b7cd0867b5f4f3271e6a5808f68491`.

All 33 signed object declarations have the literal signed bodies (whitespace ignored); `orbit` has the exact signed binder order, hypotheses and conclusion. Additional helpers implement coordinate algebra and derivative transport rather than replacing signed contracts. No signature stub from the upstream owner namespaces was duplicated. A scratch `example` repeats the signed `orbit` type and applies `KAM.Nekhoroshev.orbit H z t hh`.

Only this report is a persistent auditor edit. Scratch lives under this worktree's `.lake/abi-scratch/` and is removed. The user's exact worktree report path overrides the generic brief's main-worktree destination. No git mutation, frozen/manifest edit or generated-file regeneration was performed.

## Declaration ledger and definition classification

Every declaration below is in `KAM.Nekhoroshev`; lam/c/base/realDom/SL are in its `PartialBlock` namespace. Setting and Coordinates locators are local file line numbers. PASS on a definition means intended literal object on its carrier, with source positivity used where its geometric interpretation requires it; it does not assert positivity for arbitrary raw data.

| Node / role | Declaration (file:line) | Verdict | Classification / reason |
|---|---|---|---|
| `bpN:p11:ext-class` | `Ext` (Setting:41) | PASS | abbrev: Literal θ × (I,q,p) carrier; accepted root-name warning discussed below. |
| `bpN:p11:ext-class` | `EC` (Setting:42) | PASS | abbrev: Complex specialization of Ext. |
| `bpN:p11:ext-class` | `ER` (Setting:43) | PASS | abbrev: Real specialization of Ext. |
| `bpN:p11:ext-class` | `fastAction` (Setting:45) | PASS | def: Literal first n base coordinates. |
| `bpN:p11:ext-class` | `slowPair` (Setting:46) | PASS | def: Literal following q and p blocks. |
| `bpN:p11:ext-class` | `extCx` (Setting:49) | PASS | def: Coordinatewise real inclusion. |
| `bpN:p11:ext-class` | `extRe` (Setting:50) | PASS | def: Coordinatewise real part. |
| `bpN:p11:ext-class` | `extReal` (Setting:51) | PASS | abbrev: Exact existing RealOnParam predicate. |
| `bpN:p11:wfield` | `wfield` (Setting:54) | PASS | def: Fast weight 1, slow weight c; signs +,-,+,-. |
| `bpN:p11:wfield` | `realWfield` (Setting:60) | PASS | def: Real counterpart with the same coordinate order and signs. |
| `bpN:p11:wfield` | `extBracket` (Setting:66) | PASS | def: Literal Du applied to X_v; no altered Poisson sign. |
| `bpN:p11:adjoint (definition only)` | `extAd` (Setting:68) | PASS | def: Finite recursive iterated bracket in source order. |
| `bpN:p11:s-ext-class#data` | `PartialBlock` (Setting:73) | PASS | structure: Four raw geometry data fields Ic,S,rB,w; no theorem assumed. |
| `bpN:p11:s-ext-class#data` | `lam` (Setting:79) | PASS | def: Fixed w/rB, independent of iteration radius. |
| `bpN:p11:s-ext-class#data` | `c` (Setting:80) | PASS | def: Fixed 2π/λ². |
| `bpN:p11:s-ext-class#data` | `base` (Setting:81) | PASS | def: Witnessed singleton Ic × scaled slow set, including empty S. |
| `bpN:p11:s-real#data` | `realDom` (Setting:84) | PASS | def: Actual preimage of complex Dom at positive angle width 1. |
| `bpN:p11:ext-class` | `SL` (Setting:86) | PASS | def: Literal 64πksrB ≤ w². |
| `bpN:p11:ext-class` | `ext_class` (Setting:89) | PASS | def: Existing InClass and real-locus condition. |
| `bpN:p11:ext-class` | `slowLoss` (Setting:91) | PASS | def: Literal 16kcσ ≤ ρ. |
| `bpN:p11:s-nf#data` | `liftFast` (Setting:92) | PASS | def: h composed with the fast-action projection. |
| `bpN:p11:s-real#data` | `realHamiltonianExt` (Setting:93) | PASS | def: Source-mandated real restriction, zero off-domain. |
| `bpN:p11:s-real#data` | `ExtOrbit` (Setting:95) | PASS | def: Existing IsSolutionIn with actual real field and real domain. |
| `bpN:p11:symplectic (data only)` | `ExtCanonical` (Setting:100) | PASS | def: All linear functionals test DΨ Ω DΨᵀ=Ω. |
| `bpN:p11:s-nf#data` | `ExtNFHyp` (Setting:106) | PASS | structure: Only positive sizes, symmetry, holomorphy, reality, divisors, Lipschitz, SL, perturbation norm and cutoff. |
| `bpN:p11:conj (data only)` | `reExtMap` (Setting:130) | PASS | def: Actual complex map followed by real part, without a fallback. |
| `bpN:p11:conj (data only)` | `ExtConjHyp` (Setting:132) | PASS | structure: Source map assumptions, including holomorphy, image, reality, canonicality and Ht=H∘Ψ. |
| `energy-free / resonant (data only)` | `RealFastConvex` (Setting:149) | PASS | structure: Real-slice lower quadratic Hessian bound and real upper Hessian bound; no energy conclusion. |
| `energy-free / resonant (data only)` | `FastConvex` (Setting:161) | PASS | structure: Same convexity with upper Hessian bound on the complex tube; no frequency upper bound. |
| `energy-free / resonant (data only)` | `NearResonance` (Setting:172) | PASS | def: All real span pairings bounded by δ times Euclidean size. |
| `bpN:p11:orbit` | `theta` (Coordinates:31) | PASS | def: Fast angles divided by 2π; all other coordinates retained. |
| `bpN:p11:orbit` | `thetaInv` (Coordinates:35) | PASS | def: Literal inverse regrouping, fast angles multiplied by 2π. |
| `bpN:p11:orbit` | `converted` (Coordinates:38) | PASS | def: H∘thetaInv divided by 2π; time unchanged. |
| `orbit helper; or-chain / or-eq` | `theta_fst` (Coordinates:45) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `theta_fast` (Coordinates:47) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `theta_slowq` (Coordinates:50) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `theta_slowp` (Coordinates:54) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_q_fast` (Coordinates:58) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_q_slow` (Coordinates:62) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_p_fast` (Coordinates:66) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_p_slow` (Coordinates:70) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_theta` (Coordinates:76) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `ext_cases` (Coordinates:90) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `theta_thetaInv` (Coordinates:96) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `bpN:p11:orbit` | `thetaCLM` (Coordinates:108) | PASS | def: The actual theta bundled as a continuous linear map. |
| `bpN:p11:orbit` | `thetaInvCLM` (Coordinates:130) | PASS | def: The actual thetaInv bundled as a continuous linear map. |
| `orbit helper; or-chain / or-eq` | `thetaCLM_apply` (Coordinates:155) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInvCLM_apply` (Coordinates:157) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_single_fast` (Coordinates:164) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_single_angle` (Coordinates:182) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_single_slowp` (Coordinates:200) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `thetaInv_single_slowq` (Coordinates:219) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `fderiv_converted` (Coordinates:240) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `orbit helper; or-chain / or-eq` | `realWfield_converted` (Coordinates:253) | PASS | theorem: Literal coordinate evaluation, inverse/basis identity or derivative transport; no additional source premise. |
| `bpN:p11:orbit` | `orbit` (Coordinates:281) | PASS | theorem: Exact signed iff with differentiability guard and frozen Hamiltonian vector field. |

## Slice completeness and adversarial checks

The design's N11-A row (line 348) is complete: extended carriers/projections, fields/bracket, both Hessian bundles, fixed block geometry, class/reality, canonical/map/source predicates, resonance predicate, and θ/θ-inverse/orbit all exist. The literal definition rows at design lines 174–177, 182, 225–226 and 291 are discharged by the named definitions/proof. `stepN:p11:or-chain` is realized by `fderiv_converted` plus the continuous linear maps; `stepN:p11:or-eq` by `realWfield_converted` and transport through both maps. These internal steps need no separately exported graph theorem. No exported lemma merely borrows a graph name for a weaker conclusion. The Hessian extraction theorem belongs to N11-E3; scaled/vf to N11-C; flow and conjugation theorems to later packages. Their absence here is not missing N11-A work.

The forward orbit proof composes the actual curve derivative with thetaCLM. The reverse composes with thetaInvCLM and uses thetaInv_theta. It preserves two-sided HasDerivAt, all dimensions (including zero dimensions for this algebraic lemma), original time, actions and slow coordinates. The differentiability premise is exactly the frozen IsSolutionOn guard, not an extra source condition. Coordinate basis lemmas give the 2π cancellation separately in each block. No norm estimate or hidden constant dependence is involved.

Source bundles do not contain normal-form existence, confinement, orbit transfer or energy conclusions. ExtConjHyp's identity/canonical/map fields are precisely the assumed source conjugation-map contract. NearResonance is the dual all-pairings statement, not a silently changed norm. RealFastConvex retains the real-only bound required by design audit 1 F1 and its audit-2 repair; no complex bound was smuggled into it.

Whole-carrier check: all projections, regroupings, bracket iterates and CLMs are literal. Empty slow sets give empty witnessed base/domain, not an arbitrary selected centre. Division in λ and c is ordinary field division at degenerate raw data, without case-selected substitutes; relevant source bundles explicitly supply positive rB and w. `fderiv` is Mathlib's total derivative and is used under differentiability in orbit. `realHamiltonianExt` has an indicator: p11c lines 4–5 explicitly say the real Hamiltonian is the restriction “and 0 off it”. This is the intended total object, not a junk fallback used to bypass a source claim. `extRe` and `reExtMap` mean real projection on every input; ExtConjHyp separately asserts actual reality where consumed.

## Naming, imports and remaining notes

- Coordinates:281 exports the signed `orbit`; `KAM/Planetary/PlanarTorsion/OrbitJet.lean:67` already exports `KAM.Planetary.orbit`. Fully qualified names differ. No **additional public helper** short name is reused in KAM. Thus the literal helper restriction passes, but the handoff's request for an owner ruling remains if the campaign intends uniqueness for signed source exports too. Do not silently rename the exact signed interface; a broader all-export uniqueness policy would make this a naming failure until an explicit exception or coordinated signature revision.
- Setting:41 defines namespaced `KAM.Nekhoroshev.Ext`, not root `_root_.Ext`. The handoff explicitly accepts its short-name overlap with Mathlib Ext as a warning. Search of the delivered Nekhoroshev implementation finds no other Ext use requiring the root homological-algebra object; the N11 signatures also use Ext only for the new phase carrier. No global shadowing declaration is introduced. This does not certify unlanded future modules.
- The local KAM import closure has 71 modules and contains **no Provider module and no frozen Theorems module**. Consequently no DRAFT_SORRY or sealed-theorem assumption enters this slice; imported frozen objects are definitions. Heavy Gradient/Homological dependencies are acyclic under the successful targeted build.
- The first design audit's open-ball endpoint and adjoint source-locator notes concern later packages, not a defect found here. N11-G's Part-8 reconciliation gate remains outside this audit. No new suspected pinned-source erratum or mathematical deviation was found; no pinned-PDF re-audit is claimed.

## Independent verification

All audit Lean/Lake invocations are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no heartbeat, recursion-depth or synthesis override. The build uses the required compile gate. Other sessions' independent processes are outside this auditor's control.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11a KAM.Nekhoroshev.Partial.Setting KAM.Nekhoroshev.Partial.Coordinates
   ```

   Exit **0**. Gate output: `[inp-gate] slot 2 acquired 18:40:31 for KAM.Nekhoroshev.Partial.Setting KAM.Nekhoroshev.Partial.Coordinates`; final output: `Build completed successfully (3225 jobs).` Replayed warnings include upstream Gradient:168 unused variable and Coordinates unused simp arguments, redundant `<;>` and never-executed tactics (118,127 and 171–236). These are proof-style warnings, not failures or resource overrides.

2. Exact signed theorem application and all public theorem axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11AAudit.lean
   ```

   Exit **0**, no errors/warnings; the signed-type example elaborates. Provider=frozen-type and seal-copy probes are **not applicable**: neither assigned module defines a provider and neither is meant to seal an anchor. The scratch only imports Coordinates, so it does not introduce a draft anchor into the audited proof closure.

   Exact `#print axioms` output (all 20 new public theorems):

   ```text
'KAM.Nekhoroshev.theta_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.theta_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.theta_slowq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.theta_slowp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_q_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_q_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_p_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_p_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_cases' depends on axioms: [propext, Quot.sound]
'KAM.Nekhoroshev.theta_thetaInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInvCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_single_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_single_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_single_slowp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.thetaInv_single_slowq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.fderiv_converted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.realWfield_converted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.Setting KAM.Nekhoroshev.Partial.Coordinates
   ```

   Exit **0**. Exact output:

   ```text
replaying KAM.Nekhoroshev.Partial.Coordinates
replaying KAM.Nekhoroshev.Partial.Setting
   ```

   Both assigned modules were independently kernel-replayed in one invocation.

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the explicitly permitted generated-root exception. Exact output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (881 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   Module, frozen-anchor and elaborated ABI checks all pass. No root regeneration is authorized for this report-only audit.

5. Static checks: no prohibited tokens, EuclideanSpace or options in either audited file. All required module headers, public imports, docstrings, public sections and expose annotations are present. Setting has 177 lines, maximum width 96; Coordinates 298 lines, maximum width 99. Both satisfy 1500-line and 100-character limits. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has empty output. `git diff --check` exits 0.

Final disposition: the assigned N11-A objects and proof are complete and mathematically sound under the signed interface, with the naming/style/generated-root notes above. No new frozen theorem is sealed and no later Part-11 source gap is discharged. All verification results here were independently rerun; earlier design/prover receipts are contextual evidence only. Scratch probe and its logs were removed after their output was incorporated. Final report whitespace validation and unchanged production-file hashes passed.
