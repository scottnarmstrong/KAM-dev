# P23-13i independent package audit 1

Overall verdict: **PASS WITH NOTES** for P23-13i's reality interfaces. Both signed exports pass statement and proof checks. This package has no frozen theorem/provider to seal; it supplies the reality branch for P23-13j. It does not close the full `bpP:p2:osc-iter`, its remainder bound, or release P23-15.

## Scope and snapshot

Audited HEAD: `cdb8f643edb5d6d6f4e4a414978b3fef8ba90587` on `inp-p2313i`.
`inp` resolved to `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`;
`inp-design-p23r3` resolved to `a20e538c5ef2b4a2f5adee25654132ed4ba6b97c`.
The user-specified report destination in this worktree overrides the generic brief's main-worktree destination.

Read local `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the shared
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local
`docs/tracks/P/audits/P23-13i-handoff.md`. The handoff's AUDIT FOCUS controls scope:
only `KAM/Planetary/Averaging/OscillatorReality*.lean`, against the Revision 3 design.
There is exactly one such module, `OscillatorReality.lean` (337 lines).
Read Revision 3 and Appendix A.3 of `docs/tracks/P/design/P23-LEAN-DESIGN.md`,
`P23-design-audit-1.md`, the shared `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`,
`blueprint-P/parts/p2-averaging.tex:167–196`, the inherited reality clause in
`blueprint-N/parts/p6-normal-form.tex:105`, and track P's statement conventions.
Read the generator, oscillator setting/flow/step, homological interface and relevant frozen coordinate,
domain and Hamiltonian-field definitions to check actual applicability.

Both requested comparisons were performed:

```sh
git diff inp...HEAD
git diff inp-design-p23r3...HEAD
```

The first emits `warning: inp...HEAD: multiple merge bases, using a20e538c5ef2b4a2f5adee25654132ed4ba6b97c`.
Both broad comparisons include 81 files, 12,781 insertions and one deletion, reflecting inherited merged
work. Within the scoped `OscillatorReality*.lean` glob both contain only the new 337-line module.
`git diff HEAD^ HEAD --stat` independently shows exactly that module, 337 insertions.

**N1 — inherited protected-path difference.** The literal brief check
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
`KAM.lean` has 34 inherited added imports. The design-base comparison has the same root difference.
Frozen files, manifest and README have no differences in either comparison.
`git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty;
the ancestor root change is recorded by `git log -1 HEAD^ -- KAM.lean` as commit `5991245`
(`Regenerate KAM.lean ...`). Thus this is disclosed checkout history, not a P23-13i production edit.
The literal broad protected-path gate is not reported as passing. No generated file was regenerated.

## Per-declaration results

All declarations below have namespace `KAM.Planetary`; line numbers are in
`KAM/Planetary/Averaging/OscillatorReality.lean`.

| Node / obligation | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `stepP:p2:oi-transfer`, real parameter bridge | `oscRealFlat`, line 36 | PASS | Literal real `(I,p,q)` append, on the whole phase carrier. |
| Same bridge | `oscPack_real`, line 40 | PASS | Exact pack of the real inclusion; correct angle and all three parameter blocks, no hypotheses. |
| Same bridge | `oscRealUnpack`, line 54 | PASS | Literal real `((θ,q),(I,p))` reconstruction on every input. |
| Same bridge | `oscUnpack_real`, line 58 | PASS | Unpacking real flat data is the actual real phase inclusion. |
| Real frequency | `freq_real`, line 77 | PASS | Proves reality of each complex derivative from the real restriction on an open set; no frequency-reality assumption. Generic open-set version is stronger than the needed action-tube specialization. |
| Extract real integrable Hamiltonian | `h_real_of_realOn`, line 117 | PASS | Tests the supplied real phase Hamiltonian at real θ=p=q=0 and arbitrary real action in the tube. Positive oscillator/angle widths place that point in the domain. |
| Local homological reality | `osc_real_local`, line 145 | PASS | Builds the parameter ball and discharges all hypotheses of homological conclusion 10; conclusion 6 identifies the resonant part with the actual zero mode. Allows any complex center in `oscParams`, stronger than the real centers needed below. |
| Signed generator reality, Appendix A.3 | `osc_generator_real`, line 223 | PASS | Verbatim signed type, including both generator and literal coefficient-zero reality on the original domain; local conclusions pulled back by the actual pack/unpack identities. |
| `bpP:p2:osc-iter`, conditional reality only | `osc_iter_reality`, line 262 | PASS | Verbatim signed type, same Ψ/gp/fp and lets; reality of the sum g suffices; fp is real on V and the map preserves real points on U. |

There are no other new public declarations, instances or premise structures. The table covers both
definitions and all seven theorems. No helper assumes the main hard step or a conclusion-shaped premise.
The hypotheses of the two signed exports were neither added to nor weakened.
Unused source binders/lets are retained to preserve the signed interface. Line 260 suppresses only
`linter.unusedVariables`; it changes no resource budget or theorem semantics.

## Definition and proof audit

**Definition classification:** `oscRealFlat` and `oscRealUnpack` are total coordinate rearrangements made
from `Fin.append`, `firstBlock`, and `lastBlock`. They implement the intended real objects on their
entire carriers, including zero-size blocks. Neither uses choice, default derivatives, divergent sums,
conditionals or junk fallback values. No new norm, Fourier representation, flow or field is defined.

**Derivative step (77–107).** At a real action I, the curve is `γ(t)=ι(I+t e_i)`. Openness and continuity
keep it in U near zero. The complex derivative is restricted to real scalars, composed with γ, then
with imaginary part. Reality makes this scalar function locally zero, so uniqueness of derivatives
forces the imaginary part of `fderiv ℂ h (ι I) (e_i)` to vanish. Differentiability on the open domain
justifies the derivative; the proof does not exploit `fderiv` outside its meaningful domain.

**Homological step (145–217).** Openness of `oscParams` supplies a positive-radius ball contained in the
parameter set. `hf.flat.inClass` and the literal weighted bound restrict to that ball. Holomorphy of
`oscFreq` follows from `hh`, and the divisor premise restricts with `q=1`, Λ={0}. The unpack-real
identity proves `RealOnParam` of `oscFunction f` at every real parameter in that ball. Frequency reality
comes from `freq_real` and `h_real_of_realOn`, not an additional input. In
`KAM/Nekhoroshev/NormalForm/Homological.lean:342–361`, conclusion 10 requires symmetry of Λ, real f,
and real ω; all three are supplied. Conclusion 6 gives
`homResParam = projMode ({0} ∩ zBall n K) f`; `K≥0` proves the intersection is exactly {0}, including
K=0. `modeAverage_eq_projMode` then yields precisely coefficient zero. No arbitrary-ball reality is
assumed merely from reality at its center.

**Global generator (223–258).** At every real phase point of the original domain the pack-real identity
provides a real parameter in `oscParams`. Applying the local result at that parameter's own ball and
using `oscFunction_oscGen` plus `oscUnpack(oscPack z)=z` returns the same global generator and zero mode.
There is no domain substitution or generator redefinition.

**Step reality (262–333).** The generator result proves φ real and the coefficient zero real.
Thus `gp=g+ξ` is real using reality of the sum g alone. `osc_flowHyp` is constructed from the original
analytic/smallness premises, rather than assumed; its `real_flow` proves reality of the very flow
used by `oscStepMap` on U. For x in V, positive losses imply V⊆U. `mapsTo_flow` places Ψx in O,
and O⊆original domain allows evaluation of real h, g and f there. Both x and Ψx are actual real
inclusions, so the explicit subtraction defining fp is real. No Lie-series or remainder bound is
needed. Empty D gives vacuous domain assertions; no nonemptiness, positivity of each Mj, δ>0, K>0,
or nonempty finite g-family was introduced.

## Exact interface and hygiene verification

Every Lean/Lake invocation below was sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The compile gate itself invokes the targeted build with `nice -n 5`. No clean, update, cache download,
root build, resource override or state-changing git command was run.

1. **Targeted build** (exit 0):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313i KAM.Planetary.Averaging.OscillatorReality
   ```

   Literal output:

   ```text
   [inp-gate] slot 1 acquired 10:16:09 for KAM.Planetary.Averaging.OscillatorReality
   Build completed successfully (9119 jobs).
   ```

2. **Verbatim statements and independent application probe** (exit 0): a Python comparison extracted each
   theorem command through its type, excluding its body, from production, Appendix A.3 and the shared
   signature file. Both text equalities were `True` for both exports, including binder names/order,
   all lets, constants, domains and conditional guards. Shared file SHA256:
   `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`.
   The shared file is outside this worktree; no missing local fixture was fabricated.

   `.lake/abi-scratch/P2313iAudit.lean` imported only the production module. It copied each complete
   shared-signature statement under `audit_osc_generator_real` / `audit_osc_iter_reality` and used:

   ```lean
   exact osc_generator_real hwidths hK hα hh hdiv hf hb hrh hrf
   exact osc_iter_reality hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg
   ```

   Each command belongs to its respective copied declaration. These supply all and only explicit
   binders in order; both copied types also passed:

   ```lean
   example : type_of% @audit_osc_generator_real := @osc_generator_real
   example : type_of% @audit_osc_iter_reality := @osc_iter_reality
   ```

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313iAudit.lean
   ```

   No warnings/errors. This is the infrastructure analogue of the brief's provider/type and seal-body
   probes; there is no frozen anchor for these helpers and no seal was performed.
   The same invocation printed axioms of every new theorem, literally:

   ```text
   'KAM.Planetary.oscPack_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.oscUnpack_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.freq_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.h_real_of_realOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_real_local' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_generator_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_iter_reality' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Kernel replay** (exit 0), one invocation for the sole package module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorReality
   ```

   Literal output: `replaying KAM.Planetary.Averaging.OscillatorReality`.

4. **Source lint** (exit 1):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Literal output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (530 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   **N2 — permitted stale root only.** This is a nonzero full lint result with successful component
   checks, accepted under the brief's explicit stale-root exception. No other lint diagnostic appeared,
   including the 100-character-line check. The file has 337 lines, maximum line length 98 characters;
   an independent Python line scan found no line over 100 characters. Copyright, `module`, public
   interface imports, module docstring and `@[expose] public noncomputable section` are present.
   A forbidden-token/resource-override scan found no matches. The local unused-variable linter switch
   is the sole option setting.

5. **Import quarantine and protected objects.** Recursively enumerating local KAM imports from the
   scoped module found 73 modules, no provider and no frozen theorem module. All 12 reachable frozen
   modules are definitions with manifest state `SEALED`; no `DRAFT_SORRY` import is reachable:

   ```text
   KAM.Frozen.Defs.ActionNbhd
   KAM.Frozen.Defs.ComplexStrip
   KAM.Frozen.Defs.HamiltonianVectorField
   KAM.Frozen.Defs.HamiltonianVectorFieldC
   KAM.Frozen.Defs.IsDiophantine
   KAM.Frozen.Defs.IsPrimaryOnStrip
   KAM.Frozen.Defs.IsRealOnReals
   KAM.Frozen.Defs.OmegaZero
   KAM.Frozen.Defs.SymplecticForm
   KAM.Frozen.Planetary.Defs.Fast
   KAM.Frozen.Planetary.Defs.Phase
   KAM.Frozen.Planetary.Defs.Slow
   ```

   Thus there is no provider/frozen-anchor type to compare or seal. The exact signed helper-type
   probes above check the applicable contract instead. The broad protected-path discrepancy is
   explicitly recorded as N1, not silently omitted.

6. **Whitespace and audit edit scope.** `git diff --check` exited 0. The new report was also checked
   directly for trailing whitespace (none). The scratch probe was deleted after successful elaboration;
   the lint's temporary ABI probe was removed by its own script. No tracked production file was
   modified by this audit. Final status shows only the preexisting untracked handoff and the new report.

## Blueprint/source defects, uncertainties and deviations

No new suspected blueprint or pinned-source defect was found in the reality proof. No fresh pinned PDF
verification was needed or performed for this narrowly scoped implementation audit. The already
reported neighboring issue is `blueprint-P/parts/p2-averaging.tex:177`, quoted as
`1/(e(S_0-S))` under the stated margin `S-σ<S_0`: the denominator can be zero or negative.
Revision 3 section R3.4 explicitly preserves that inherited report and calls for the target-width
`S_0-S+σ` estimate. This package's reality arguments do not use the problematic printed estimate;
its existing flow input is not re-audited as a whole here. This is a carried blueprint issue, not a
newly verified CP10 erratum.

The design audit's module-path note is satisfied by the production import chain:
`OscillatorGen` imports `KAM.Nekhoroshev.NormalForm.Homological`, whose declarations live in
`KAM.NormalForm`. There is no import of a design signature fixture.

No mathematical deviation from the two signed statements was introduced. The two notes concern
inherited root history and the explicitly permitted stale generated-root lint failure. Remaining
P23-13b–h/j proof obligations and the quantitative full-step audit remain separate; this report certifies
only P23-13i's completed generator/zero-mode and step-reality branch. Persistent audit output is solely
`/root/code/KAM-inp-p2313i/docs/tracks/P/audits/P23-13i-audit-1.md`.
