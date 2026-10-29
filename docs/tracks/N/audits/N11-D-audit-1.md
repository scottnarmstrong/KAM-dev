# N11-D independent package audit 1

Overall verdict: **PASS WITH NOTES** for the N11-D helper package. All four signed exports match the delivered interfaces and establish the entire assigned slice. No frozen anchor is supplied by this package: N-PARTIAL-CONVEX remains outside this verdict, and its frozen declaration remains `DRAFT_SORRY`. Provider/frozen-type and seal-body probes are therefore not applicable here. This is not a theorem-sealing receipt.

## Scope and inputs

Audited only `KAM/Nekhoroshev/Partial/RealSystem.lean` and `Continuation.lean`, at HEAD `ca5b8ed55a4e550447c36b2ad3a71b0f6eada37d`. Read the repository rules, PLAN, DECISIONS, external package-audit brief, N11-D handoff/AUDIT FOCUS, N11 design row and complete node inventory, both N11 design audits, Part-11c source statements/proofs, track-N partial statement, frozen partial-convex anchor and relevant carrier/solution definitions.

The exact user-specified report destination overrides the generic brief's main-worktree destination. Only this report is a persistent audit edit. Temporary Lean probes use this worktree's `.lake/abi-scratch/` and are removed after checking. No git state-changing operations or source repairs.

`git diff inp...HEAD` initially compared against `inp = 7c254d1ada904dce883560fd988ff208b2edcb35`. Git warned `multiple merge bases, using ea47150c9881c2fda67e782c455eafeb2f6c0d95`. The full diff contains four additions: Continuation (110 lines), RealSystem (444), Coordinates (298), Setting (177). The latter two are N11-A prerequisites; they were inspected as carriers/import dependencies, not assigned a new package verdict. The initial status contained only the untracked handoff. The shared `inp` reference moved during this audit; HEAD and the audited module contents stayed fixed.

Pins:

- Delivered `/root/code/KAM-inp/.drafts/design/N11Signatures.lean`: `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4`.
- `docs/tracks/N/design/N11-LEAN-DESIGN.md`: `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609`.
- `blueprint-N/parts/p11c-partial-stability.tex`: `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea`.
- RealSystem: `2bf47434447882d624ec2f6c04cb1ce8625671aa759ad83c8c06e2898a40d76a`.
- Continuation: `f3a52bccdbc8a3d1c72296c3b58059e52f7d49b60f14fab86f3d71efcae63408`.

## Signed declarations and complete node coverage

Unqualified declarations below are in `KAM.Nekhoroshev`; C denotes `blueprint-N/parts/p11c-partial-stability.tex`.

| Node / declaration | Implementation | Verdict | Reason |
|---|---|---|---|
| `bpN:p11:real-system` (C:7–18) | `real_system` (RealSystem:290), `real_system_bounds` (:325), `real_system_resonant` (:422) | PASS | The three exports together establish all clauses (a)–(d), with the literal unequal carrier. |
| `stepN:p11:rs-a` (C:15) | `real_system`; private `fderiv_ext_real` (:89), regularity and periodicity helpers (:160–251) | PASS | Smooth real restriction, C1 field, exact complex-field restriction and both scalar/field integer-angle periodicity. No replacement-field equality premise. |
| `stepN:p11:rs-b` (C:16) | `real_system`; private `realH_energy` (:253) | PASS | Energy is constant for all pairs of times in any order-connected interval. The smaller-radius orbit field and outer-radius field agree by local equality on an open neighborhood. |
| `stepN:p11:rs-cd` (C:17), clause (c) | `real_system_bounds` | PASS | Value bound U and sum of angular derivative norms bounded by U/(exp(1)*s). No reality assumption on u; fixed-base weighted estimates and the limit of positive strip losses retain the exact constant. |
| `stepN:p11:rs-cd` (C:17), clause (d) | `real_system_resonant` | PASS | Arbitrary set of frequencies; coefficient support plus InClass/WBound implies both real and imaginary derivative vectors lie in the literal real `resSpan`. No reality or symmetry assumption. |
| `bpN:p11:continuation` (C:35–41) | `continuation` (Continuation:93) | PASS | Independent angle/transverse dimensions n,N; actual maximal-solution predicate, compact transverse tail from t0≥0, and Tp=top. |
| `stepN:p11:ct-data` (C:39) | private `uniform_data_periodic` (Continuation:33) | PASS | Compact thickening, δ=min(δ0,1)>0, floor reduction into [-1,2]^n, translated closed-ball containment and uniform bounds/Lipschitz constants. Empty K needs no arbitrary witness selection. |
| `stepN:p11:ct-concl` (C:40) | `continuation` body (:104–106) | PASS | Supplies precisely the compact-tail membership required by `KAM.ODE.gen_continuation`. |

These are every node assigned to N11-D by design lines 227–236 and row 351. No additional unsigned public export claims a graph node; the four public theorem names are exactly the signed names.

The three RealSystem command types are token-identical to the delivered signatures modulo whitespace. Continuation is also token-identical after expanding the section variable `{N : ℕ}` into its theorem header. The fresh probe copies all four exact delivered signatures under fresh names, proves them by applying the implementation to every explicit binder in order, and checks the reverse `type_of% @implementation` assignment to the copied declaration. Thus section-variable generalization, binder order, inferred parameters, norms, constants, carriers and quantifier order are checked by elaboration, not merely visual resemblance.

## Definitions, proof soundness and consumers

The only new definition in the audited files is private `extCxCLM` (RealSystem:44): the product of the existing coordinatewise real inclusions as a continuous real-linear map. It is the intended inclusion on the whole carrier, including zero dimensions. Its application is proved equal to the existing `extCx`; there is no junk branch, arbitrary extension or replacement of a frozen object. Continuation introduces no def/abbrev/structure. Local `set` bindings are proof abbreviations, not public definitions or instances.

All other helpers are private: coordinate/domain transport, real derivative transport, symplectic cancellation, real regularity/field identification, periodicity, local energy conservation, width restriction, fixed-base Fourier representation and annihilator-to-span separation. No public helper short name is reused; no root namespace declaration or instance is introduced.

The existing `realHamiltonianExt` is explicitly zero off the real domain. Every derivative used in the proof is taken inside that open domain, where it agrees locally with Re(H∘extCx); energy transport checks this for both radii. The unequal-carrier derivative lemma proves the transport from holomorphy and reality directly. The weighted-field cancellation splits the fast and slow coordinate sums with the correct c and -c weights. No conclusion is assumed as a premise.

The bounds/resonance proofs instantiate the existing independent-base-dimensional weighted infrastructure, carrying summability via WBound. They do not exploit a junk tsum on the nonsummable locus or a supremum on an empty domain. Resonance follows from annihilation of every real functional vanishing on the lattice span, applied separately to real and imaginary parts.

Design audit 1 F2/F3 and N2 are discharged here at proof level: `real_system` exports field periodicity for the continuation/transfer consumer; `real_system_resonant` has no reality premise and includes both spans (energy can consume its first conjunct); and derivative transport works on EC n k without a surrogate equality premise. Bounds and energy have arbitrary working radius, supplying the smaller normal-form-radius consumers. No signed export is deliberately narrowed relative to its delivered type. No completed downstream transfer/provider proof is certified by this audit.

The recursive KAM import closure contains no provider and no frozen theorem module. Its 23 frozen imports are definitions, each `SEALED` in the local manifest. Hence no DRAFT_SORRY theorem enters this package. Frozen `IsSolutionOn` uses two-sided derivatives; the existing `ExtOrbit`/`IsSolutionIn` preserves the intended endpoint interpretation. Ordinary max-norm Fin-function carriers are retained throughout.

## Validation receipts

All Lean-related commands are serialized and run with `LEAN_NUM_THREADS=1`; the build uses the prescribed gate, which invokes `nice -n 5 lake build`. No heartbeat/recursion overrides, clean, dependency refresh, generated-root regeneration or protected-file edits.

1. **Targeted build — exit 0.**

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11d KAM.Nekhoroshev.Partial.RealSystem KAM.Nekhoroshev.Partial.Continuation
   ```

   Exact relevant output (dependency warning text omitted):

   ```text
   [inp-gate] slot 3 acquired 19:45:59 for KAM.Nekhoroshev.Partial.RealSystem KAM.Nekhoroshev.Partial.Continuation
   ⚠ [3230/3230] Replayed KAM.Nekhoroshev.Partial.RealSystem
   warning: KAM/Nekhoroshev/Partial/RealSystem.lean:291:5: Variable name `hR` is not explicitly referenced.
   Build completed successfully (3230 jobs).
   ```

   Other replayed warnings come from the prerequisite Coordinates and Stability.Gradient. No warning in Continuation. The unused hR is harmless and retained to match the signed type; no default-heartbeat failure occurred. The handoff's 443-line count for RealSystem is stale: the actual file has 444 lines, still below the cap.

2. **Fresh exact-interface/binder-body probes and axiom inspection — exit 0.**

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11DAudit.lean
   ```

   The probe was generated from the pinned delivered signature command text, not the implementation header. It contains no placeholder proof. All copied-signature applications and reverse `type_of%` examples elaborated; the only output was:

   ```text
   'KAM.Nekhoroshev.real_system' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.real_system_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.real_system_resonant' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.continuation' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Single-invocation kernel replay — exit 0.**

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.RealSystem KAM.Nekhoroshev.Partial.Continuation
   ```

   Complete output:

   ```text
   replaying KAM.Nekhoroshev.Partial.Continuation
   replaying KAM.Nekhoroshev.Partial.RealSystem
   ```

4. **Source hygiene.** Static scan found no sorry/admit/axiom/unsafe/opaque, resource option or EuclideanSpace in either audited file. Both have the copyright/module/public-import/docstring/public-section structure. RealSystem: 444 lines, maximum 100 Unicode characters; Continuation: 110 lines, maximum 99. No new public definitions, root shadow or reused public helper short names.

5. **Protected paths and whitespace.** `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (exit 0; only the multiple-merge-base warning). `git diff --check inp...HEAD` and `git diff --check` exit 0 with no whitespace findings. The repeated live comparison retains the same four files/1029 additions and the same merge base.

6. **Full source lint — exit 1 solely for the permitted generated-root exception.**

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (899 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, overlong-line, size, module, frozen-anchor or ABI failure. The brief expressly permits the stale root; it was not regenerated.

The audit scratch probe was deleted. Final persistent audit change: this report only; the pre-existing untracked handoff remains untouched. Validation logs were captured in `/tmp/n11d-audit-{build,probe,kernel,lint}.log`; the decisive outputs and exit statuses are reproduced above.

## Uncertainties, errata and deviations

No new suspected source/blueprint defect or implementation deviation was found in N11-D. The earlier design-audit F2/F3 repairs are present in proved exports, and the N2 unequal-carrier proof obligation is paid here. No claim is made about the remaining Part-11 packages, the frozen provider, or independent verification of the primary PDFs.

For continuity with both design audits, retain their two previously disclosed, out-of-slice notes: C:31's “complex nu-ball of radius 1/2” must be read as an open ball at the endpoint strip width (a closed ball can touch the excluded boundary); the adjoint graph proof locator “B L69–86” overreaches the proof ending at B:73 into the Taylor lemma. Neither affects the real-system/continuation statements audited here, and no source or graph repair was made. The N11-G Part-8 reconciliation gate remains outside this package verdict.

The only local notes are the unused signed hR binder, inherited dependency warnings, the stale generated root explicitly permitted by the brief, and the handoff's one-line count discrepancy. None is a proof or interface blocker. **All assigned N11-D nodes and all four signed declarations PASS; package PASS WITH NOTES.**
