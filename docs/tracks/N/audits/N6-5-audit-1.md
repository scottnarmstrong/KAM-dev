# Independent package audit 1 — N6-5

**Overall verdict: PASS WITH NOTES.** The scoped implementation of Iterative Lemma (a), (b), and its source-hypothesis wrapper passes statement, definition, proof, axiom, and kernel checks. No material mathematical defect was found. Global lint remains red for an inherited long line outside scope, in addition to the expected stale generated root. These are recorded below rather than silently treated as a clean lint run.

## Scope and authority

Audited on 2026-10-28 in `/root/code/KAM-inp-n65` under the package audit brief, `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, and the explicit AUDIT FOCUS in `docs/tracks/N/audits/N6-5-handoff.md`. The user's exact report destination overrides the generic brief's main-worktree destination. Only `KAM/Nekhoroshev/NormalForm/IterativeMap.lean` is a package target; upstream implementations were inspected where needed to verify its uses, without extending the package verdict to them.

Authority: `docs/tracks/N/design/PART67-LEAN-DESIGN.md` v2, §0 items 3–5, §7 N6-5 (lines 300–302), package row N6-5 (line 258), Appendix A.4 (lines 712–834); both `DESIGN-N67-design-audit-{1,2}.md` in that design directory; `blueprint-N/parts/p6-normal-form.tex` lines 10–14, 29–43, 93–136; and the track-N statement conventions. These Parts 6–7 results are infrastructure, with **no frozen theorem anchor and no provider**. Thus provider/frozen `type_of%` and seal-copy tests are inapplicable. Instead, independently elaborated fresh-name copies of the three exact Appendix A.4 theorem signatures applied the implemented declarations to their explicit binders in order. This is interface verification, not a seal of N-HEAD-C or any other frozen theorem.

Snapshot:

- HEAD: `52bb0ed4ce49b92207006eefe6f9be6b7be90ac5`.
- `inp` at intake: `f1451bf24a5bccd5dace39c45a9687c724360d0e`.
- Module SHA-256: `4dc5ca509ade3c4dcfae2678f8228c704ac1a26a0d4f57220a2c9ca74d8674fc`.
- Requested `git diff inp...HEAD` warns of multiple merge bases and selects `219d4b439621deb2f26e4e5bbd5278598230f79a`; the other base is `741f26a1d15d160fa8e00f43c0445e117a327b47`. The selected diff contains 43 files, including inherited packages. `git diff HEAD^ HEAD --name-only` contains only the scoped module. Its actual size is 205 lines, rather than the handoff's approximate 165.

## Declaration-by-declaration verdicts

All names below are in `KAM.NormalForm`. All eight design declarations have exactly matching bodies (definitions/structure) or signatures (theorems), after removing comments and normalizing whitespace. The three theorem signatures were also checked by Lean against independently copied design text.

| Blueprint node / obligation | Declaration (module line) | Verdict | Reason |
|---|---|---|---|
| iterative, concrete map | `iterMap` (35) | PASS | Literal time-one flow of the prescribed generator on `Dom n D (r-ρ) (s-σ)`; same domain as `CanonData.omega`. |
| iterative, resonant update | `iterG` (40) | PASS | Exactly `g + homRes K Λ f`. |
| iterative, remainder construction | `iterF` (45) | PASS | Exactly `(h∘snd+g+f)∘iterMap - h∘snd - iterG`. No remainder estimate is claimed here. |
| iterative-direct, source premises | `IterHyp` (52) | PASS | All 15 fields are source premises, the finite decomposition, or nonnegative bound data; the divisor field is the explicitly stated direct-form premise. |
| iterative, dimensionless bound | `iterU` (72) | PASS | Exactly `qδ/(2παρσ)`, with `q = p/(p-1)`. |
| auxiliary positivity | `IterHyp.conjExp_pos` (83) | PASS | Derives positivity from `p>1`; no iterative conclusion assumed. |
| iterative smallness | `IterHyp.iterU_le` (88) | PASS | Derives `u≤1/4` by multiplying the source smallness inequality by positive denominators. |
| it-gen / it-map bridge | `IterHyp.canon` (104) | PASS | Builds all `CanonData` fields from the first and ninth conjuncts of `homological_direct`, positive widths/bounds, and `u≤1/4≤1/2`. |
| auxiliary ratio identity | `IterHyp.phi_div` (122) | PASS | Algebraic identity `Φ/(ρσ)=u`. Its unused `IterHyp` binder is convenient specialization data; the identity in fact holds without it. |
| iterative / iterative-direct (a), it-map | `iterative_direct_a` (131) | PASS | Preserves holomorphy, target domain, symplectic form, all integer translations, injectivity and the specified left inverse on the exact design domains. |
| iterative / iterative-direct (b), it-map | `iterative_direct_b` (159) | PASS | Preserves scaled displacement `≤u`, angle displacement `qδ/(2παρ)`, action displacement `qδ/(e·2πα·σ)`, and derivative bound `2u` on the prescribed smaller domain. |
| iterative, source wrapper | `iterHyp_of_source` (191) | PASS | Constructs `IterHyp` directly, deriving its only nontrivial missing field with `(divisor hp hα hK hL hnr hlip hrad).2`; no new premise beyond the v2 signature. |

Per frozen anchor: **not applicable**. Per delivered obligation: (a) PASS, (b) PASS, source wrapper PASS. Items (c)–(e) remain outside N6-5 and are not certified by this report.

## Definition and premise classification

- `iterMap`: genuine chosen ODE flow, with the inherited total-flow convention. `KAM/Canonical/Flow.lean:54–55` returns the starting point if no solution exists. This fallback is not used to establish the claimed map properties: `H.canon` supplies `SmallField`; `canonical_map_a` supplies the appropriate gauge interior; `flow_a` (line 244) proves actual solution existence/dynamics there and its proof constructs the existence witness before unfolding `flow`. Off-domain values have no flow interpretation asserted by N6-5. No new fallback was introduced.
- `iterG`, `iterF`: ordinary total arithmetic/composition constructions, equal to their intended formulas on the entire carrier. `iterF`'s identity alone proves neither holomorphic class membership nor a small remainder; those are separate N6-6 obligations.
- `iterU`: ordinary total real quotient. Under `IterHyp`, `p>1`, `α>0`, `ρ>0`, `σ>0` ensure all denominators used for estimates are positive. No argument uses Lean's value for division by zero.
- `IterHyp`: a proposition structure bundling precisely source data. `decomp` is the explicit finite decomposition allowed by the blueprint, not an estimated remainder. `WBound` includes coefficient summability as well as a sum bound (`KAM/Weighted/Norm.lean:62`), so no junk nonsummable `tsum` is used. Replacing norm equality by a carried nonnegative upper bound is the explicit design §0.3 convention, and yields the sharp blueprint instance by taking the actual norm. The nonnegative bound also handles empty domains without an invalid inference from a vacuous `WBound`.

The direct divisor assumption is legitimate for `iterative-direct`; it is not asserted as an additional input to the source-form Iterative Lemma. `iterHyp_of_source` discharges it from (N1), (N2), and `KLr≤α/p`. Positivity of `r` follows from `0<ρ` and `2ρ<r`. There is no restriction on dimension or on the arbitrary complex base set beyond the design; norms remain Pi maximum norms, Fourier indices `Fin n → ℤ`, angles first, and the denominator uses the correct period-one `2π`.

The proof of (a) applies `canonical_map_a`, `_d`, `_b.1`, and `_e.1`; injectivity follows by applying the same time-minus-one flow to an equality of images. The proof of (b) applies `_a` and `_c`, rewrites `Φ/(ρσ)=iterU`, and simplifies the two component denominators. No inverse existence, small displacement, or canonical property is smuggled into a hypothesis.

## Independent verification

Checks were sequential, with no overlapping auditor-started Lean/lake invocations. Build, signature/axiom probe, kernel replay, and the final lint run used `LEAN_NUM_THREADS=1`. No heartbeat, recursion, or synthesis-budget override was used. An initial lint invocation omitted the explicit thread/nice prefixes; because lint invokes Lean for ABI hashes, it was rerun with both prefixes. This execution deviation is recorded rather than claiming the initial invocation complied.

### Targeted build

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n65 KAM.Nekhoroshev.NormalForm.IterativeMap
[inp-gate] slot 2 acquired 06:47:16 for KAM.Nekhoroshev.NormalForm.IterativeMap
Build completed successfully (3210 jobs).
exit 0
```

The gate executes `nice -n 5 lake build`; this was a targeted build using the existing worktree build overlay, not a clean library rebuild. No module warnings were printed.

### Design signatures and all theorem axioms

Temporary probe: `.lake/abi-scratch/N65Audit1.lean`. It imported only the scoped module, restated `iterative_direct_a`, `iterative_direct_b`, and `iterHyp_of_source` from Appendix A.4 under fresh names, supplied the corresponding implemented proof with all explicit binders, and printed axioms of every new public theorem. The scratch was removed after checking.

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N65Audit1.lean
'KAM.NormalForm.IterHyp.conjExp_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.iterU_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.canon' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.IterHyp.phi_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterative_direct_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterative_direct_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.iterHyp_of_source' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

### Kernel replay

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.NormalForm.IterativeMap
replaying KAM.Nekhoroshev.NormalForm.IterativeMap
exit 0
```

There is no provider or additional N6-5 lemma module to include in this invocation.

### Lint and static checks

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-n65/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (430 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The initial `sh scripts/lint_sources.sh` produced the same diagnostics and exit 1. The stale root is the brief's allowed exception; the Liouville line is an additional inherited failure, outside the explicit audit scope. The auditor did not edit either file.

Scoped static inspection: 205 lines; zero lines over 100 characters; no forbidden proof escape, resource option, or `EuclideanSpace`; copyright, `module`, interface `public import`s, docstring and exposed public noncomputable section present. `git diff --check inp...HEAD -- KAM/Nekhoroshev/NormalForm/IterativeMap.lean` exits 0, printing only the multiple-merge-base warning.

A recursive source-import scan found 59 reachable KAM modules including the target, **zero provider modules and zero frozen theorem modules**. Reachable frozen definitions were read: `ActionNbhd`, `ComplexStrip`, `HamiltonianVectorField`, `HamiltonianVectorFieldC`, `IsDiophantine`, `IsPrimaryOnStrip`, `IsRealOnReals`, `OmegaZero`. The package uses the literal frozen complex Hamiltonian vector field. There is no imported theorem whose manifest state would need an exception for SEALED use.

```text
git diff inp...HEAD -- KAM/Frozen manifest README.md
```

Empty apart from the merge-base warning. The generic combined protected-path check including `KAM.lean` is **not empty**: the inherited root diff adds 11 imports. Its last touching commit is `741f26a Regenerate KAM.lean (Canonical/CanonicalMap)`, before N6-5. The N6-5 commit changes only `IterativeMap.lean`; thus this is a comparison-scope note, not an N6-5 unauthorized edit. No generated or frozen file was changed during the audit.

## Defects, uncertainty, and handoff

No new suspected blueprint/source defect or mathematical deviation was found in the scoped implementation. The blueprint's already declared strengthening to `u≤1/4`, and the design's bound-predicate and total-flow conventions, are preserved. P's split-scale/oscillator variants and the remainder/reality items remain separate obligations. No pinned-PDF proof audit beyond the requested blueprint/design comparison is claimed.

Nonblocking notes: inherited global lint failure, inherited generated-root diff and multiple merge bases, approximate handoff line count, and the corrected initial lint execution prefixes described above. These do not invalidate the independently checked N6-5 proof bodies. No default-heartbeat design signal occurred.

Retained audit artifact: only `/root/code/KAM-inp-n65/docs/tracks/N/audits/N6-5-audit-1.md`. The pre-existing untracked handoff was preserved; no state-changing git command, source repair, frozen change, or generated-file edit was made.
