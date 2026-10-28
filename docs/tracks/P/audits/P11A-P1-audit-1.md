# P11A-P1 independent package audit 1

Overall verdict: **FAIL at the repository-wide lint gate**. The five-file P11A-P1 infrastructure slice passes its signature, proof, coverage, build and kernel checks, but lint also rejects an inherited 101-character line in a frozen file; the brief permits only the stale generated-root exception. This is not a defect introduced by P11A-P1. No frozen anchor is implemented or seal-ready in this package; P-FIXED remains outside the proof-closure claim.

Read-only audit of HEAD `9a2d476a62964f40e17fda514f6e67c2ac24c074` against `inp` using `git diff inp...HEAD`. At the initial comparison, `inp` was `7c254d1ada904dce883560fd988ff208b2edcb35`; the merge base was `d1a02150c8e815febce9e0fade2dd194d5ee7795`. The complete diff adds exactly the five scoped modules (807 lines). No changes occur in `KAM/Frozen`, `manifest`, `KAM.lean` or `README.md`.

Authority: AGENTS.md, PLAN, DECISIONS, the supplied package-audit brief, the current AUDIT FOCUS in the handoff, P11A design Revision 3 and its node registry, both historical P11A design audits, Part 11 blueprint lines 10–12 and 40–60, and track P statements. The user's exact report destination overrides the generic brief's main-worktree destination. No sub-agents were used. All Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; no source or git state was changed.

The signature authority is `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA-256 `627ab032a68be7aca3f547d898c1e82fe8146c18a363a5dd63163916b8d3beee`. The handoff's original blocker is obsolete: Patch, PatchHessian and BasePoint are present and audited.

## Declaration and graph coverage

All names below are in `KAM.Planetary`. PASS denotes the actual scoped statement, not a whole-campaign theorem.

| Node / responsibility | Declaration and locator | Verdict | Evidence |
|---|---|---|---|
| `bpP:p11:sec-conv#data` | `Preparation/Basic.lean:8–29` | PASS | Import facade reuses existing weighted domains, Pi carriers and frozen objects; no substitute definitions. |
| `bpP:p11:sec-A#data`, physical inputs | `P11Physical`, `Working.lean:30` | PASS | Signed fields exactly match; dimension, positive masses/axes and strict ordering are source premises. |
| Tube radius | `p11Zeta`, `Working.lean:44` | PASS | Signed finite minimum formula, including minimum axis and pairwise separation. |
| Radius positivity | `p11_zeta_pos`, `Working.lean:47` | PASS | Finite nonempty set attains its infimum; every member is positive. |
| Deferred forward-tube wrapper | `forward_tube`, `Working.lean:69` | PASS | Exact signed statement; body is the single application `forward_tube_core D.G_pos D.m0_pos D.m_pos D.a_pos hzeta`. Core belongs to the separate ForwardTube package. |
| Deferred margin selector | `p11PhysicalDelta`, `Working.lean:80` | PASS | Exact signed choice from the preceding proved existential at `p11Zeta D`. |
| Literal secular matrix | `p11SecularMatrix`, `Working.lean:84` | PASS | Exact signed half-Hessian of frozen secularAverage of the actual fixed perturbation in the product chart. |
| Patch output carrier | `P11PatchData`, `Working.lean:91` | PASS | Signed data-only output; no theorem assumes its desired properties. |
| Patch specification | `P11PatchSpec`, `Working.lean:99` | PASS | Signed spectral/frequency identities, open connected patch, compact positive-volume core, null boundary, finite-type amount and physical margin all retained. |
| Physical-data adapter | `p11PhysicalData`, `PatchHessian.lean:29` | PASS | Literal reuse of physical inputs as SecularForm.Data; positive dimension follows from n≥2. |
| Part 8 / Part 10 Hessian bridge | `p11SecularMatrix_eq`, `PatchHessian.lean:104` | PASS | Literal equality with `coeffs` at actual actions, with the source axes premise; no abstract matrix substituted. |
| Part 10 patch port / `sec-A#data` | `p11_patch`, `Patch.lean:42` | PASS | Good axes near prescribed physical axes; frequency analyticity/RND from Part 10; compact action core and amount from rank_compact; literal spectrum supplied by the Hessian bridge. |
| Selected physical patch | `p11PatchData`, `Patch.lean:138` | PASS | Exact signed unconditional choice backed by proved existence. |
| Selected patch properties | `p11PatchData_spec`, `Patch.lean:140` | PASS | Exports precisely the specification of that same selected patch. |
| `bpP:p11:norm-dict` | `norm_dict`, `Working.lean:176` | PASS | Exact signed analytic/RND/amount statement with factor `(2π)^(-(2+μ))`; no added premise. |
| `stepP:p11:nd` | `nd_scalar_eq`, `nd_p11dg_smul`, `nd_rnd`; norm_dict proof at `Working.lean:117–255` | PASS | Squared scalar contributes r², diagonal input derivative contributes rʲ; r≤1 and j≤μ give the required lower bound. RND follows from positive amount on nonempty K. |
| `bpP:p11:select` | `select`, `BasePoint.lean:107` | PASS | Exact signed interior point, common positive γ≤1, τ=max(nμ,2n), joint and both frozen block Diophantine conclusions. |
| `stepP:p11:sel-hyp` | `BasePoint.lean:119–160`, private `bp_jet_bound`, `bp_jet_bound_all` | PASS | Compact collar yields full jet bound; M_bound supplies scalar D2; D1 is patch amount; constant family makes diagonal D3 zero. No measure/rank premise is assumed. |
| `stepP:p11:sel-gam` | `BasePoint.lean:161–216` | PASS | Checks τ>nμ−1, strict smallness, ε=vol(K)/2, C≥0 and both C=0/C>0 cases. Chooses a sufficiently small positive γ; no zero/default division is used. |
| `stepP:p11:sel-int` | `BasePoint.lean:217–228`, private `bp_dio_of_good`, `bp_dio_fast`, `bp_dio_slow` | PASS | Positive-volume good set cannot lie in the null boundary. Integer embeddings (k,0)/(0,k) preserve l1 size and give both block conclusions. |

This covers every node assigned by the design table to Basic, Working and BasePoint; Patch and PatchHessian discharge the subsequently split patch port. The local step obligations are actual proof arguments, rather than additional hypotheses or unsigned weakened replacements. There are 15 new public named declarations: eight definitions/structures and seven theorems.

## Fidelity, definitions and consumer limits

All 12 signed declarations match the supplied signature after whitespace normalization: both structures, all five signed definition bodies, and all five signed theorem types, including complete let-bound conclusions. A fresh Lean probe copied the five theorem signatures under anonymous examples and applied the actual exports with their explicit arguments. Five copied definition bodies were checked against the actual definitions by `rfl`. The three unsigned public additions are the literal physical-data adapter, the exact Hessian equality and the selected-patch specification; none weakens a named graph conclusion.

Definition classification:

- `P11Physical`: source input structure; no spectral, analytic or KAM conclusion field.
- `p11Zeta`: literal geometric minimum on a finite nonempty positive set, not an empty-infimum fallback.
- `p11PhysicalDelta`: existence-backed positive forward-tube choice. Its positivity and bounds are obtained from choose_spec in Patch.
- `p11SecularMatrix`: total half-Hessian operator on the signed carrier. The theorem identifying it with coeffs supplies axes/analyticity before differentiation; off-domain derivative defaults are not used.
- `P11PatchData`: raw output data; `P11PatchSpec`: output proposition about the literal matrix, frequency map and measure objects. These are never extra physical input assumptions.
- `p11PhysicalData`: literal adapter, valid on every P11Physical input.
- `p11PatchData`: existence-backed choice satisfying the exported specification. No fallback or junk witness is used.

The signed patch interface intentionally exports the properties consumed here rather than every detail of the source's Part 10 construction. It supplies a positive finite-type order and amount, not a least-index identity or the original named axis cube. Patch chooses a max-norm closed ball in action space; its rescaling is again a closed ball, hence a rectangle with positive volume and null boundary. Selection uses exactly those properties. Its γ is conservatively capped further than the source's displayed `min{1,γ*}` to ensure strict smallness; all promised estimates remain valid.

The signature consumers inspected in P11SecularSpec/P11SecularFullSpec use the same chosen patch's frequency, spectrum, μ, physical margin and the selected interior Diophantine point. The exact `(2π)⁻¹` fast/slow factors and half-Hessian convention are maintained. Those future holomorphic-chart/lift/negativity/analytic-radius obligations are not proved merely by this package: P11PatchSpec does not independently export an SO diagonalizer, negative spectrum, or the blueprint's additional rho_* margin. No downstream implementation using these five modules exists elsewhere in the current KAM sources. This report approves the P1 interface and local consumers; it does not certify those future packages or frozen P-FIXED closure.

No ambient instance changes or root declarations occur. A repository-wide declaration search found only the already documented short-name overlap `forward_tube` with `KAM.Planetary.PlanarAssembly.forward_tube` (`PlanarAssembly/Geometry.lean:209`). This is the mandated signed export in a different namespace, not a newly reused public helper name. No other added public short name collides with a KAM declaration.

## Independent validation receipt

All commands ran from `/root/code/KAM-inp-p11ap1`.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap1 KAM.Planetary.Preparation.Basic KAM.Planetary.Preparation.Working KAM.Planetary.Preparation.PatchHessian KAM.Planetary.Preparation.Patch KAM.Planetary.Preparation.BasePoint
   ```

   Exit 0. Output includes `[inp-gate] slot 2 acquired 19:43:03` and `Build completed successfully (9246 jobs).` Replayed warnings include unused simp arguments in PatchHessian lines 84/88 and deprecated if_neg in BasePoint line 73; no elaboration error or resource override.

2. Signature/body/axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP1Audit.lean
   ```

   Final corrected probe exit 0, no warnings/errors. An initial auditor-generated probe failed because its extractor split a let-bound type at the first `:=`, and copied definitions lacked a noncomputable section. Only the scratch probe was corrected; no package code was changed. The complete theorem headers were then checked, including both let-bound types, and the successful probe above is the validation receipt.

   Exact axiom output:

   ```text
   'KAM.Planetary.p11_zeta_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.forward_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.norm_dict' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11SecularMatrix_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_patch' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PatchData_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.select' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   No provider-to-anchor or seal-body probe applies: no provider/frozen theorem is delivered. The corresponding exact-signature application probes were performed for the infrastructure exports instead.

3. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.Basic KAM.Planetary.Preparation.Working KAM.Planetary.Preparation.PatchHessian KAM.Planetary.Preparation.Patch KAM.Planetary.Preparation.BasePoint
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.Preparation.BasePoint
   replaying KAM.Planetary.Preparation.Patch
   replaying KAM.Planetary.Preparation.PatchHessian
   replaying KAM.Planetary.Preparation.Working
   replaying KAM.Planetary.Preparation.Basic
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1. Exact output:

   ```text
   Lean lines over 100 characters:
   /root/code/KAM-inp-p11ap1/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (892 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated-root line is the brief's permitted exception. The frozen 101-character line is an additional inherited failure, so the literal full-lint acceptance gate fails. All scoped module, frozen-anchor and ABI checks pass. Neither protected file was edited.

5. Static hygiene and protected paths: no forbidden token, EuclideanSpace, resource override or new instance in the scoped files; all use copyright/module/public imports/docstring/exposed public section. File lengths / maximum Unicode line lengths: Basic 29/97; Working 261/100; Patch 147/98; PatchHessian 136/99; BasePoint 234/100. No file exceeds 1500 lines. Transitive KAM import scan: 200 modules, no provider imports, no frozen theorem imports; all 58 imported frozen declarations are manifest-SEALED definitions. Thus no DRAFT_SORRY dependency is hidden in the proof chain.

   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. `git diff --check inp...HEAD`: empty, exit 0. Final report/scratch cleanup checks are recorded below.

## Notes, suspected defects and deviations

No new suspected pinned-source defect, false frozen statement, conclusion-shaped physical premise or unpaid local proof step was found. The inherited frozen-file line-length violation is a hygiene gate failure, not a mathematical erratum. Exact location: `KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77` (101 Unicode characters):

```lean
  by exact KAM.Provider.Planetary.amdConfinement hn B hB mu T delta hmu hT hdelta hmargin hAMD z0 hz0
```

The same line is present at merge base `d1a02150c8e815febce9e0fade2dd194d5ee7795`; `git blame` attributes it to inherited commit `913505490`. The protected-path three-dot diff is empty. The live `inp` branch moved during the audit and later contains a shorter version of that line, but this report evaluates the requested package worktree as it stands and does not import upstream changes. Earlier design-audit findings F1–F4 concern other interfaces; F5-R2 concerns chart_scaling_closeness and is addressed in design Revision 3. This package uses chart_scaling_jets' diagonal identity, with no full/diagonal gauge substitution.

The blueprint/source's stronger construction details and future consumer gates remain distinguished from this signed P1 result, as explained above. The obsolete handoff blocker and conservative interior/gamma construction are documentation/implementation notes, not proof holes. The remaining acceptance issue is the unrelated full-repository lint failure; it cannot be silently waived under the supplied brief or repaired in this read-only audit. No source repair, signature change, frozen edit or auditor-introduced mathematical deviation was made.

Final validation: `git diff --check` and `git diff --check inp...HEAD` exit 0 with no output. The report has no trailing whitespace, balanced code fences and no pending receipts. The temporary signature probe and the two audit logs were removed from `.lake/abi-scratch/`. Final git status contains only this new report and the pre-existing untracked P11A-P1 handoff. Tracked files remain unchanged; no state-changing git command was run.
