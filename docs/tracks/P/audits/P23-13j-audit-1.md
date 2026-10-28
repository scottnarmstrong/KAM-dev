# P23-13j independent package audit 1

Audit date: 2026-10-28. Audited HEAD `1fdb2e87e5ff70ec4742914c2e5c8cfec723f578`; comparison branch `inp` was `31f0bfbf70c07b1eefd006237f331c00e003a0e5`.

## Scope and verdict

**PASS WITH NOTES** for P23-13j, node `bpP:p2:osc-iter`, export `KAM.Planetary.osc_iter`. No blocking or mathematical defect found in the scoped assembly. This supplies the complete signed oscillator step. No frozen anchor is proved or sealed by this package, so provider/frozen-type and frozen-seal probes are not applicable. The exact signed-type replacement probe below supplies the corresponding interface check.

Audited only `KAM/Planetary/Averaging/OscillatorStepComplete.lean`, as required by the handoff's AUDIT FOCUS. `git diff inp...HEAD` contains three new files: `OscillatorCompositionIntegral.lean` (349 lines), `OscillatorRemainder.lean` (122 lines), and the scoped module (99 lines). The first two are inherited prerequisite changes, not additional declarations audited under this verdict. Dependencies' mathematical implementations remain under their separate audits; the complete scoped export's axiom closure and kernel replay are independently checked here.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff, Revision 3 and Appendix A.3 of the design, the shared signed signature file, the P23-13 incomplete handoff, Track P statement, P blueprint lines 183–196 and inherited N Part 6 lines 93–105. The design audit named in the handoff resides at `/root/code/KAM-inp/docs/tracks/P/design/P23-design-audit-1.md`, rather than under `audits/`; that actual report was read. Frozen definitions used by the imported closure were inspected. The user's explicit report destination overrides the generic brief's main-worktree destination.

## Declaration review

| Node / declaration | Verdict | Reason |
|---|---|---|
| `bpP:p2:osc-iter` / `KAM.Planetary.osc_iter` (`OscillatorStepComplete.lean:33`) | PASS | Exact signed hypotheses, lets, carriers, constants, domains and conclusion order; proof combines the four required results without additional premises or witnesses. |

This is the only new public declaration. No new definitions, abbreviations, structures or instances occur in the scoped module.

### Literal statement fidelity

A Python comparison extracted each string from `theorem osc_iter {` through the text immediately before its proof delimiter (` := sorry` in the signature, ` := by` in production), from `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` and the production file. Result: `FULL literal statement equality: True UTF8 bytes: 3663`; unified diff empty. This compares the actual text, including binder order, every let and every conjunction, without normalization or substitutions. Both current files use `exp`, resolved by `open Real`; no `rexp` substitution is needed.

Shared signature file SHA256: `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`.
Scoped production file SHA256: `3e4f6770db25b1a54bb1f63275160c5ed569ca5553511c758628f3ef6e5b8e36`.

The source premises remain dimension positivity, divisor/analytic/weighted bounds, nonnegative delta, the stated smallness and finite source decomposition. In particular there is no new nonempty-domain assumption, nonnegative-Mj premise, assumed remainder estimate, realness premise on the output, or assumed map. Zero delta, K=0, J=0 and empty D remain admitted exactly as signed. Conditional reality remains a conclusion under realness of h, g and f.

### Splice and identical arguments

At lines 91–97, the eleven lets are introduced without replacing their values. `osc_iter_core`, `osc_remainder_bound` and `osc_iter_reality` receive exactly

```lean
hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
```

`osc_fp_class` receives its actual narrower explicit argument list, omitting hn/hm. All inferred dimensions, functions, outer widths and majorants match the target. Its explicit remainder expression is definitionally the signed fp.

Core conjuncts a1–a13 end with symplecticity; a14 is the four component displacements. The final constructor is exactly

```lean
⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, b1, b2, a14, b3⟩
```

Thus class and bound of fp follow symplecticity, before displacements and conditional reality. Commit `1fdb2e8` fixes precisely this destructuring/splice order; the audited HEAD contains the fix. No new map, choice, existential witness or analytic estimate is introduced by the proof.

Generator and increment class/bounds use the original domain; holomorphy, maps-to O, lattice, symplecticity and displacements use U; inverse, injectivity, derivative, identity and remainder use V. The bound retains `d=min(rho*sigma,rhop*rhoq)`, all four Rsum ratios, the inverse denominator `1-2*exp(1)*(1+m)*delta/(2*pi*alpha*d)` and the exponential tail. This matches Revision 3's final assembly contract and the oscillator blueprint's quantitative replacement.

## Definition classification and imports

There are no new global definition bodies to classify. All eleven local lets are literal signed objects: the existing total time-one map Ψ; finite sum g; coefficient-defined gp; explicit transformed residual fp; scalar d and Rsum; existing generator φ; domains O/U/V; scalar u. They introduce no fallback or junk object. Ψ uses the existing Hamiltonian field and actual flow on O, with source hypotheses furnishing the imported flow guarantees on U and V. The phase remains `((theta,q),(I,p))` in `Fin (n+m)` coordinates, with only n Fourier directions and the existing weighted summability predicate.

A recursive source-import inspection found 87 KAM modules, no provider imports and no frozen theorem imports. The twelve imported frozen definition files are all manifest `SEALED`: ComplexStrip, OmegaZero, IsRealOnReals, IsPrimaryOnStrip, ActionNbhd, HamiltonianVectorFieldC, HamiltonianVectorField, SymplecticForm, IsDiophantine, and Planetary Phase/Fast/Slow. No DRAFT_SORRY anchor is imported. A code-masked scan across this KAM closure found no sorry/admit/axiom/unsafe/opaque or prohibited resource override.

## Independent validation

All Lean/Lake invocations were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`. No root build, clean, update, cache command or resource-budget override was used.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313j KAM.Planetary.Averaging.OscillatorStepComplete
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 12:45:36 for KAM.Planetary.Averaging.OscillatorStepComplete
Build completed successfully (9133 jobs).
```

2. Exact signed-type probe and axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313jAudit.lean
```

The probe imports only the production complete module, copies the **entire** signed theorem under the fresh name `audit_signed_osc_iter`, and replaces its body by:

```lean
by
  exact osc_iter hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
```

It then checks both directions:

```lean
example : type_of% @audit_signed_osc_iter := @osc_iter
example : type_of% @osc_iter := @audit_signed_osc_iter
#print axioms KAM.Planetary.osc_iter
```

Final exit 0, with the sole output:

```text
'KAM.Planetary.osc_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An initial auditor-generated probe incorrectly stopped extraction at the first let-assignment delimiter and failed to parse; this was a scratch-generator error. Extraction was corrected to the proof delimiter, full statement equality was rerun (3663 UTF-8 bytes), and the corrected probe passed. No production change was made. The axiom result covers the theorem's transitive proof dependencies and rules out `sorryAx` in its proof closure.

3. Kernel replay of the sole new module (no provider or separate new lemma module in scope):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorStepComplete
```

Exit 0. Output:

```text
replaying KAM.Planetary.Averaging.OscillatorStepComplete
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted generated-root discrepancy. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (657 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is a nonzero full lint with passing module, frozen-anchor and ABI checks, accepted under the brief's exact exception. The generated root was not regenerated.

5. Scope/style checks: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output. `git diff --check` exited 0. The sole scoped module has 99 lines, copyright, `module`, public imports, module docstring, and `@[expose] public noncomputable section`. No forbidden proof tokens, ambient type substitution or resource override occurs. Only the new report and the preexisting handoff appear in `git status --short`.

## Notes, uncertainties and errata

No new mathematical uncertainty in the scoped splice was found. The earlier incomplete P23-13 core alone lacked remainder class/bound and conditional reality; this theorem now includes them all, using the separately implemented results rather than treating them as hypotheses. This verdict concerns completion of this signed step, not P23-15's iteration or any planetary headline/frozen seal.

The design's existing blueprint warning remains contextual: `blueprint-P/parts/p2-averaging.tex:177` writes the angular derivative denominator `e(S_0-S)` under a margin permitting only `S-sigma<S_0`; that denominator can be nonpositive. Revision 3 explicitly directs use of the target-width repair `S_0-S+sigma`. This assembly adds no derivative argument and relies on the existing landed estimates. This is an inherited blueprint discrepancy, not a new pinned-paper erratum or a new finding against 13j. No fresh PDF/source-paper erratum was verified in this narrow audit.

No implementation deviation was introduced by the auditor. The stale generated-root lint exception is expressly authorized by the audit brief; root regeneration remains the orchestrator's task. Only this report is a persistent audit edit; the preexisting untracked handoff was preserved. No frozen, manifest, production Lean, README or generated root file was edited.
