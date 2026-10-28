# P23-13e independent audit 1

Audit date: 2026-10-28. Audited HEAD `3ef2b02a0ff5101143bd70bf5e1ddde63397da51` against `inp` (`722ad4a37de68b025a0c690051afff665dcb1176`) and the requested immediate predecessor `inp-p2313d` (`4f031a0ad64f96233e10ba1c9f36ba667c476b6f`). Both comparisons isolate the same new 337-line file, `KAM/Planetary/Averaging/OscillatorComposition.lean`.

## Scope and verdict

**Overall: PASS WITH NOTES.** The three signed results `osc_trajectory_hat`, `osc_series_eq`, and `osc_composition_t` each PASS their exact interface and proof checks. All nine new public theorems pass axiom review and kernel replay. Notes are the permitted generated-root lint exception and the verified alternate Taylor proof route. No blocking or major finding; no signature repair required. No frozen anchor is claimed seal-ready by this helper-only package.

This is an infrastructure package: no provider or frozen theorem is supplied or sealed. Provider/frozen-type and frozen seal-body checks are therefore inapplicable. The three requested public interfaces are instead checked against the literal Appendix A.3 declarations, including fresh-name copies with direct application bodies and bidirectional `type_of%` checks. This verdict does not close the full `osc_iter` node, its remainder/reality clauses, P23-15, or a physical frozen headline.

Authority read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the named package audit brief and handoff, Track P statement, design Revision 3 and Appendix A.3, design audit 1, `blueprint-P/parts/p2-averaging.tex:165–196`, and the corresponding composition/adjoint statements in `blueprint-N/parts/p5-canonical-maps.tex:141–180`. The shared signature file `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` has SHA256 `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`. Its three relevant signature texts match Appendix A.3, and those match production literally before the proof bodies.

## Declaration review

All names below have prefix `KAM.Planetary`; line numbers are in the audited file. Each helper is distinctly named and proved from source data; none adds a premise to the three signed interfaces.

| Node / obligation | Declaration / line | Verdict | Reason |
|---|---|---|---|
| oi-transfer: flow inputs | `OscComposeData.toFlowHyp`, 45 | PASS | Constructs existing flow hypotheses at exactly E=Phi; positivity and smallness follow from source widths and numerical bound. No flow conclusion assumed. |
| oi-range: displacement | `OscComposeData.displacement`, 53 | PASS | Derives Phi/d <= 1/4 without extra assumptions. |
| oi-range | `osc_trajectory_hat`, 60 | PASS | Exact Appendix A.3 type. Starts in V, uses the literal O-flow and its gauge displacement, reaches original-minus-7/4-loss. |
| oi-ratio: hatted ratio | `osc_hat_ratio`, 90 | PASS | All four losses are multiplied by 3/4, hence d changes by 9/16 and q by 16/9; proves nonnegativity, hatted q < 1, q <= theta and theta < 1. |
| oi-transfer / oi-ratio: series terms | `osc_term_bound`, 111 | PASS | Adjoint at middle widths O, original generator widths, full losses; factorial-normalized terms have class and q^j A bound on V. |
| oi-range: trajectory adjoints | `osc_traj_bound`, 133 | PASS | Applies general adjoint with 3/4-loss and original generator margin; evaluation on the hatted domain gives N! (16q/9)^N A. |
| oi-transfer / oi-range: Taylor identification | `osc_taylor_t`, 171 | PASS | Direct Taylor along s -> X^(st) on fixed O; remainder is bounded by (abs(t)16q/9)^(M+1) A and tends to zero. |
| oi-transfer / oi-range | `osc_series_eq`, 264 | PASS | Exact Appendix A.3 type. Sets t=1 and identifies the limit with `osc_lie_series` using uniqueness of limits. |
| oi-transfer / oi-ratio | `osc_composition_t`, 278 | PASS | Exact Appendix A.3 type, same O-flow, oscillator class and weighted bound (1-abs(t)theta)^(-1) A on V. |

## Proof and carrier checks

Write d=min(rho*sigma,rhop*rhoq), q=`oscLieRatio m Phi d`, theta=`oscTheta m Phi d`. `OscComposeData` is inherited unchanged from P23-13d: positive dimensions, twice-loss margins, generator class/bound, Phi>=0 and Phi<=d/(16(1+m)). It has no conclusion-shaped field.

`toFlowHyp` uses E=Phi, not an unrelated perturbation size. V is contained in the full-unit gauge interior of O, hence the half-unit interior required by `flow_a`. The displacement is bounded by abs(t)Phi/d<=1/4. `oscDom_of_gauge_le` therefore places every trajectory in original-minus-7/4-loss. The field, initial point and total flow domain stay identical throughout.

For `osc_traj_bound`, middle widths are original-minus-one-loss and additional losses are 3/4 of each original loss. Their sum is below the original generator widths, and the twice-loss margins imply strictly positive residual widths. The product minimum is 9d/16; the evaluated adjoint bound is N! (16q/9)^N A. The factorial is positive even at N=0.

The alternate time argument is sound. Define G_j(s)=t^j ad_phi^j u(X^(st) z). For s in [0,1], st is in [-1,1], even for negative t. `hasDerivAt_adPow_flow` on Omega=Omega1=O and the real chain rule give G_j'=G_(j+1); no Hamiltonian-field rescaling identity or flow uniqueness premise enters. `taylor_integral_aux` gives the remainder; the nonnegative Taylor weight integrates to 1/(M+1)!, which cancels the adjoint factorial. Since abs(t)16q/9<1, the remainder tends to zero. There is no division by t, Phi or A; t=0, negative t, Phi=0 and A=0 are retained. Empty D is vacuous without adding nonemptiness.

For the weighted conclusion, each t^j-normalized term has bound (abs(t)q)^j A. `osc_bound_tsum` supplies oscillator class and weighted bound directly, without a sup-to-Fourier norm conversion. Pointwise Taylor identification transfers both using the existing local congruence lemmas. The geometric sum is (1-abs(t)q)^(-1)A. The proof establishes 1-abs(t)theta>0 before reciprocal monotonicity, giving the signed coarser bound. This sharper intermediate q estimate does not alter the public conclusion.

## Definitions and imports

New `def`/`abbrev`/`structure`: **none**. Local `set`/`let` expressions G, C, v, q, theta, B and R denote their literal displayed curves, series terms, constants or integral; no fallback or junk value is used. Total flow is used only where `flow_a` proves its solution and initial value; total tsum is used only where summability is established.

The production file imports `Mathlib`, `KAM.Canonical.Lie`, `OscillatorCompositionSeries`, `OscillatorFlowProps` and two Mathlib tactics. Recursive inspection of its 78 KAM modules finds **no provider and no frozen theorem import**. The 12 reachable frozen modules are definitions only (`HamiltonianVectorFieldC`, `ComplexStrip`, `OmegaZero`, `HamiltonianVectorField`, `IsPrimaryOnStrip`, `IsRealOnReals`, `ActionNbhd`, planetary `Phase`, `IsDiophantine`, `SymplecticForm`, planetary `Fast`, `Slow`); all are manifest `SEALED`. The canonical field is literally the frozen complex Hamiltonian field. Existing oscillator packing preserves ((theta,q),(I,p)), Fourier dimension n and phase dimension n+m. No equal-dimension N weighted composition theorem is substituted.

## Independent verification

Commands run from `/root/code/KAM-inp-p2313e`. All final Lean/Lake checks use `LEAN_NUM_THREADS=1` and `nice -n 5`; the compile gate is paused while standalone probes/replay or lint's ABI subprocess run, so these do not overlap.

1. `git diff --stat inp...HEAD` and `git diff inp-p2313d...HEAD -- KAM/Planetary/Averaging/OscillatorComposition.lean`: one file, 337 insertions. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `git diff --check inp...HEAD`: exit 0, no output.
2. Targeted compile gate: `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313e KAM.Planetary.Averaging.OscillatorComposition`: **exit 0**, no warnings. Exact output:

```text
[inp-gate] slot 1 acquired 12:11:40 for KAM.Planetary.Averaging.OscillatorComposition
Build completed successfully (9124 jobs).
```
3. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313eAudit.lean`: **exit 0**. The probe copies the three Appendix A.3 statements under fresh names with bodies `exact osc_trajectory_hat H`, `exact osc_series_eq H hu hb hA`, `exact osc_composition_t H hu hb hA ht`; it also checks each complete polymorphic type in both directions with `type_of%`. All six type checks and all three application bodies pass without diagnostics.

Exact axiom output:

```text
'KAM.Planetary.OscComposeData.toFlowHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OscComposeData.displacement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_trajectory_hat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_hat_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_term_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_traj_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_taylor_t' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_series_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_composition_t' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Kernel replay: `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorComposition`: **exit 0**. One invocation covers the sole new module containing all nine lemmas. Exact output: `replaying KAM.Planetary.Averaging.OscillatorComposition`.
5. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: **exit 1 solely for the permitted generated-root exception**. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (555 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

An earlier lint attempt was stopped during its ABI Lean subprocess after noticing that the invocation lacked the thread environment setting; the gate had not acquired a slot and was paused, so it did not overlap a build. The complete lint above was rerun with the required environment/priority. The interrupted attempt is not used as validation evidence.

6. Static hygiene: no forbidden tokens, heartbeat/recursion/synthesis overrides, or `EuclideanSpace` in the new file. Copyright, `module`, public interface imports, module docstring and public exposed section are present. 337 lines total, below 1500. All nine new public declarations were included in the axiom probe.
7. Final report whitespace/protected-path check and scratch cleanup: `git diff --check inp...HEAD`: exit 0, no output. `git diff --no-index --check /dev/null docs/tracks/P/audits/P23-13e-audit-1.md`: exit 1 for a new file, no whitespace diagnostics. Protected-path branch and working diffs are empty. Removed `.lake/abi-scratch/P2313eAudit.lean` and `P2313eKernel.log` after recording results. The only new repository artifact from this audit is this report.

## Findings, deviations and limitations

No suspected mathematical defect in the audited blueprint statements, design signatures or pinned-source claims was exposed by this package audit. No fresh external-source claim is needed beyond the local blueprint/design transfer under audit.

The intentional proof-route deviation is at `OscillatorComposition.lean:171–262`: design R3.3 (`P23-LEAN-DESIGN.md:1296`, paragraph beginning “For general t”) says “rescale the generator to `tphi`” and prove flow equality by uniqueness; the package row at line 1346 likewise says “uniqueness for tphi.” Production proves the same signed statement by Taylor along the fixed O-flow and explicit time rescaling instead. The proof above verifies the replacement and finds no missing uniqueness/scaling lemma. This is a documented method change, not a statement change or source erratum.

The generated-root warning is the audit brief's explicit exception; the generated file must be regenerated by the orchestrator at integration. No production file, frozen anchor, manifest, generated root, or README was edited by this audit. The pre-existing untracked handoff was retained.
