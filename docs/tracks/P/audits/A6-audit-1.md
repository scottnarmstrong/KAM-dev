# A6 independent seal-key audit 1

Verdict: **PASS WITH NOTES** for `planetary.d25.amdConfinement.v1`, The provider is seal-ready; the unchanged frozen export remains **FROZEN_UNPROVED** (`DRAFT_SORRY`). This audit does not modify or seal the anchor.

## Scope and frozen inputs

Audit date: 2026-10-28. Tier-2, refute-first package audit. Authorization: read-only audit plus this exact report and temporary `.lake/abi-scratch/` probes; no production edits, git mutations, root regeneration, or frozen edits. The user's explicit worktree-local report path overrides the brief's main-worktree output default. No delegation. Read AGENTS.md, PLAN.md, DECISIONS.md, the supplied package brief, A6 handoff, P14 design and both design audits, blueprint P14a, track-P statement, frozen theorem and relevant definitions.

Snapshot: HEAD `0ac29a11c889fff8012a829511ed69072270f70e`; observed `inp` `d9183adae208ecf2e726620694b69c8168e33006`. `git diff inp...HEAD` warns of multiple merge bases and selects `700477228205080ba6e81c21cb4f1d05acafe970`; the other base is `8d0d536bd0482e17f75f90c7243986bad65e9e98`. The requested diff was reviewed as emitted. It contains the three A6 files plus A5 AngularMomentum, excluded from fresh proof review by the handoff. The handoff was already untracked on entry.

SHA-256 frozen-v1:

| File | SHA-256 |
|---|---|
| KAM/Planetary/AMD/ConfinementExit.lean | `15a12a55564141b59e0066765619441d1f2e9805c157c51e63f6b60ba7b9d429` |
| KAM/Planetary/AMD/Confinement.lean | `c83ed8c15d3ecca11071a17a551821b08aba0c97ad3731fccadcd4a5a748d8d4` |
| KAM/Provider/Planetary/AmdConfinement.lean | `3303e03c34a218089e79afaf130c5790cf1c93d066e8b24e8fce4a6031a15357` |
| KAM/Frozen/Planetary/Theorems/AmdConfinement.lean | `9178a6ef739497349dbeb1acde187fe8446de0f7a7231b5428782bb61ebaac72` |
| manifest/frozen-anchors.json | `603b72b70fd185e5a033aca7b9bc371fd5bedd5a7125e8ad5de02f762b2cbc32` |
| docs/tracks/P/design/P14-LEAN-DESIGN.md | `04c358878699851e0e45adcccbfd06048e2474b6cffe015821df5e072f36fca3` |
| /root/code/KAM-inp/.drafts/design/P14Signatures.lean | `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88` |
| blueprint-P/parts/p14a-amd-expsafe.tex | `a2735bd6fbc36dc765bafccac43af4e3742b101a7e0f2d97725e70ac37ff8452` |
| docs/tracks/P/statement.md | `06d876320d40f7ae0cb5cdbe7e5b08a00b431125630079a2b3d3abcaac2e0b66` |

Manifest identity: theorem, version 1, export `KAM.Planetary.amdConfinement`, path above, provider `KAM.Provider.Planetary.amdConfinement`, owner ruling D25; source KAM-dev@4475a0a, Additions v0.4 (approved draft SHA `bf4b9d474e4c3fa32844af887f90851cb5bd026c101f2b5fc882b9169d5e72f0`), statement §P-AMD-CONFINEMENT, round 2 §2 lemmas 1,2,5,6 with round-3 stopped correction. ABI SHA `a06de42f8f9b1500dacb7d6458a771df2ac692e555eb951cd1b7f779ec077122`. Every listed definition-closure file hash independently matches the manifest.

## Declaration and proof ledger

Names without a namespace below are in `KAM.Planetary`. Locators refer to frozen-v1.

| Node / proof step | Declaration | Verdict | Evidence |
|---|---|---|---|
| amd-fwd, amd-close | `amd_exit_forward` (Exit:30) | PASS | Abstract continuity/relative sequential closure specialization of blueprint 137–144; `gen_exit`, explicit sequence `ts-ts/(k+2)`, and closure force the alleged exit back inside V. |
| amd-bwd | `amd_exit_backward` (Exit:68) | PASS | Pull back J and curve by negation; reverses order explicitly and invokes forward continuity lemma. No reversed dynamical equation is assumed. |
| restriction in amd-fwd/bwd | `isMovingSolutionOn_mono_of_subset` (Confinement:42) | PASS | Restricts both Hamiltonian predicate and collision-free clause. |
| initial collar | `amd_inner_mem_collar` (:48) | PASS | Inner-region inequalities plus positive delta and source margins imply collar membership; no admissibility premise needed. |
| amd-margin | `amd_collar_at` (:66) | PASS | Stopped input on actual [a,b] already in outer region; `ang_mom` gives constant J; sums action differences to obtain AMD bound. |
| amd-fwd/bwd/close | `amd_collar_of_solution` (:101) | PASS | Supplies every abstract exit premise from `amd_closure`, solution continuity and NoCollision. Positive/negative cases use only [0,s]/[s,0]; s=0 uses the initial collar. |
| bpP:p14:amd, amd-max/cont/a/b/c/d | `amd` (:144) | PASS | Exact signed telescope and conclusion; constructs hconf, then uses maximal/continuation machinery and reconstructs every frozen conjunct. |
| planetary.d25.amdConfinement.v1 provider | `KAM.Provider.Planetary.amdConfinement` (provider:25) | PASS | Literal frozen telescope; sole import Confinement; body applies `amd` to all 14 explicit binders in order. |
| frozen export | `amdConfinement` (frozen:53) | PASS WITH NOTES | Declaration fidelity and draft allowlist pass; frozen proof is still `by sorry`; no proof-closure promotion. |

The six auxiliary statements are explicit conditional helper contracts, not alternative source theorems. The exit helpers generalize the blueprint to a normed real space and relative closure in N; their closure and local-collar premises are produced at Confinement:111–137, not retained in `amd`. The restriction helper is generic. The inner/collar helpers isolate source proof steps; none weakens the final conclusion or introduces a new source premise. No extra public short-name declaration collides elsewhere in KAM; all new declarations are namespace-qualified, with no root shadow. The approved `amd_closure` rename is respected; no `closure` alias is introduced.

At Confinement:167–185, `moving_ode`, `amd_compact`, `gen_uniform_compact`, and `geometry` produce the field/domain and uniform compact data. hconf is **proved locally**, by restricting an arbitrary open-interval solution to `J ∩ [-T,T]` and invoking the collar theorem. At :186, `gen_confinement` consumes hconf. Its proof (ODE/Continuation:155–175) calls `gen_maximal` and `gen_continuation` in both directions, producing strict endpoint margins `Tm < -T` and `T < Tp`; no endpoint derivative is replaced by a one-sided derivative. At :193–200, uniqueness uses `gen_uniqueness_inter` and convex⇒OrdConnected, Newton reconstruction uses the literal moving solution with positive masses and mu≥0, and geometry/momentum/stopped drift are packed in frozen order.

## Expanded binder audit

Authority S: P14Signatures:522–547, identical frozen telescope; G: frozen AMDBoxAdmissible:37–48 and statement:472–487; I: frozen LowAMDRegion:38–40, ProgradeElliptic and statement:489–529. Every logical field below is SOURCE, not a new produced-result hypothesis. Universally quantified indices remain internal to the indicated field.

| Binder / expanded input | Bin | Authority |
|---|---|---|
| implicit n : ℕ | TYPING | S |
| hn : 2≤n | SOURCE | S, retained even though unused |
| B : AMDBox n | TYPING | S, fixed geometry carrier |
| hB: ∀i, mass i>0 | SOURCE | G |
| hB: ∀i, lower i>0 | SOURCE | G |
| hB: ∀i, lower i<innerLower i | SOURCE | G |
| hB: ∀i, innerLower i<innerUpper i | SOURCE | G |
| hB: ∀i, innerUpper i<upper i | SOURCE | G |
| hB: ecc>0 | SOURCE | G |
| hB: ecc<1 | SOURCE | G |
| hB: initialAMD>0 | SOURCE | G |
| hB: initialAMD<outerAMD | SOURCE | G |
| hB: ∀i, outerAMD<lower i*(1-sqrt(1-ecc²)) | SOURCE | G |
| hB: distance>0 | SOURCE | G |
| hB: radius>0 | SOURCE | G |
| hB: ∀i, distance≤(lower i/mass i)²*(1-ecc) | SOURCE | G |
| hB: ∀i, (upper i/mass i)²*(1+ecc)≤radius | SOURCE | G |
| hB: ∀i j, i<j ⇒ separated-annulus inequality | SOURCE | G |
| mu : ℝ | TYPING | S |
| T : ℝ | TYPING | S |
| delta : ℝ | TYPING | S |
| hmu : 0<mu | SOURCE | S |
| hT : 0<T | SOURCE | S |
| hdelta : 0<delta | SOURCE | S |
| hmargin: ∀i, lower i+2*delta<innerLower i | SOURCE | S |
| hmargin: ∀i, innerUpper i+2*delta<upper i | SOURCE | S |
| hAMD: initialAMD+2*n*delta<outerAMD | SOURCE | S |
| z0 : Phase (n*2) | TYPING | S |
| hz0: ∀i, mass i>0 | SOURCE | I, ProgradeElliptic |
| hz0: ∀i, body radius>0 | SOURCE | I, ProgradeElliptic |
| hz0: ∀i, Kepler energy<0 | SOURCE | I, ProgradeElliptic |
| hz0: ∀i, angular momentum>0 | SOURCE | I, ProgradeElliptic |
| hz0: ∀i, innerLower i<action i | SOURCE | I |
| hz0: ∀i, action i<innerUpper i | SOURCE | I |
| hz0: physicalAMD<initialAMD | SOURCE | I |
| hstop: universal stopped action estimate | SOURCE | S; StoppedActionBound:40–48 |

Counts of expanded outer inputs: SOURCE 30; STANDING 0; TYPING 6; RULED 0; EXCESS 0. No instance binders on the provider. The hstop body universally quantifies l,r and an actual curve, requires l≤0≤r, l<r, initial equality, literal IsMovingSolutionOn and outer-region membership on that segment; it concludes action drift only on the segment intersected with [-T,T]. Expanding IsMovingSolutionOn gives the differentiability-guarded Hamiltonian ODE plus NoCollision. This is precisely the explicitly approved conditional input, not assumed full-horizon confinement. B is fixed before all physical parameters; the existential solution follows all hypotheses. No constants have widened dependence.

## Definition classification and adversarial checks

New `def`/`abbrev`/`structure`: **none**. The `set x` in Exit:46 is a local explicit approximating sequence, not an exported definition or a fallback.

Existing semantic dependencies remain the manifested definitions. `physicalAMD = sum keplerAction - totalMomentum`; LowAMDRegion is literal prograde ellipticity, strict action bounds and strict AMD bound. The existing collar is outer membership plus closed delta action margins and AMD≤initialAMD+n*delta. MovingUniqueOn quantifies over every open convex local solution through the same initial point. IsNewtonSolutionOn keeps collision-freedom and two-sided HasDerivAt at every queried time. Body/carrier checks at these use sites pass; definition well-definedness/characterization/choice-independence gates are N/A for these literal predicates and formulas. No new choice construction, junk branch, default-value carrier, or theorem-shaped assumption bundle was introduced.

Refutation pass tested: (1) using hstop at an unknown exit endpoint—refuted, it is used only on earlier closed subsegments already inside V; (2) global closure at collision—refuted, hN comes from the actual solution's NoCollision at the exit; (3) negative-time sign/interval gap—refuted by explicit pullback and [s,0] restriction; (4) closed-endpoint continuation gap—refuted by strict margins from gen_confinement; (5) hidden angular-momentum premise—refuted by the explicit `ang_mom` invocation and physicalAMD identity. These are rejected candidate findings, not unresolved defects. No suspected new pinned-source or blueprint defect, and no introduced mathematical deviation. Original PDFs and the A5 proof were not independently re-audited.

## Exact verification

All Lean/Lake/checker invocations in this audit were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5` (including the ABI subprocess inherited from lint). No heartbeat or other resource override, cache repair, library clean, or generated-file edit.

Targeted build:

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a6 KAM.Planetary.AMD.ConfinementExit KAM.Planetary.AMD.Confinement KAM.Provider.Planetary.AmdConfinement
[inp-gate] slot 1 acquired 17:11:04
Build completed successfully (9127 jobs).
exit 0
```

Only replayed upstream warnings: unused NormedSpace in ODE.Exit, hmargin in AMD.Closure, hm/hκ in Kepler.Energy; no A6 warning or error.

Exact-type probe `.lake/abi-scratch/A6Audit1.lean` imported the frozen anchor and provider, then checked:

```lean
example : type_of% @KAM.Planetary.amdConfinement := @KAM.Provider.Planetary.amdConfinement
example : type_of% @KAM.Planetary.amdConfinement := @KAM.Planetary.amd
```

It also copied the entire actual frozen declaration under fresh name `KAM.Planetary.a6_audit_seal`, replacing only its name/body with:

```lean
by exact KAM.Provider.Planetary.amdConfinement hn B hB mu T delta hmu hT hdelta hmargin hAMD z0 hz0 hstop
```

Command `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A6Audit1.lean`: **exit 0**, both type probes and the prospective seal elaborate. Separately, direct text extraction before `:=` returned True for literal frozen/provider telescope equality and True for signed/library telescope equality, preserving every binder and conjunction.

The same probe ran `#print axioms` for all eight new public theorems listed in the ledger. Every one returned `[propext, Classical.choice, Quot.sound]`. The actual frozen `KAM.Planetary.amdConfinement` returned `[propext, sorryAx, Classical.choice, Quot.sound]`, exactly the remaining draft proof hole.

Provider import closure: 81 project modules, **zero DRAFT_SORRY imports**, no other provider; provider's only direct import is Confinement. Its only repository importer is the actual frozen anchor, line 31. No quarantine bypass.

Mechanical scans of the three files: no forbidden proof escapes, resource overrides, or EuclideanSpace; lengths respectively 90, 204, 52, all below 1500. All carry copyright, module command, public imports, docstring, public section. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty (apart from the multiple-base warning). `git diff --check inp...HEAD`: exit 0.

Kernel replay:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Planetary.AmdConfinement KAM.Planetary.AMD.Confinement KAM.Planetary.AMD.ConfinementExit
replaying KAM.Planetary.AMD.ConfinementExit
replaying KAM.Planetary.AMD.Confinement
replaying KAM.Provider.Planetary.AmdConfinement
exit 0
```

Full lint (allowed generated-root exception):

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (803 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the explicitly allowed stale generated root. Module, frozen-anchor guard, and elaborated ABI checks complete successfully; no timeout was used.

## Findings, notes, and closeout

No blocking finding survives the separate refutation pass. N1: generated `KAM.lean` is stale, the explicit permitted lint exception; leave regeneration to the integrator. N2: A6's provider proof and exact seal body are verified, but the actual frozen anchor remains DRAFT_SORRY with sorryAx until the orchestrator performs its separately authorized seal. The unused hn is preserved verbatim as a signature premise, not removed. The full requested diff also carries A5; that separately audited predecessor is not recertified here.

DECLARATION_FIDELITY: PASS
DRAFT_ALLOWLIST: PASS
PROOF_STATUS: FROZEN_UNPROVED (actual frozen export)
PROVIDER_PROOF: PASS / seal-ready

All eight new public declarations classified; no new definitions; direct predecessor applications checked; exact-type and prospective seal probes passed; targeted build and kernel replay passed. Audited file hashes remained unchanged. Probe and temporary verification logs were removed after recording results. Only this report was created as a persistent audit artifact; the pre-existing handoff was left untouched. No suspected errata or introduced deviations.
