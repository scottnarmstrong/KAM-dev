# P23-13f independent package audit 1

Audited revision: `ad0494a` (`inp-p2313f`), 2026-10-28. Worktree:
`/root/code/KAM-inp-p2313f`. Scope is exactly
`KAM/Planetary/Averaging/OscillatorCompositionIntegral.lean`, as directed by
the handoff's AUDIT FOCUS. The user's explicit report destination overrides
the generic brief's main-worktree destination.

## Verdict

**PASS WITH NOTES** for this infrastructure package. All independent checks
are complete as recorded below. The mathematical export
`KAM.Planetary.osc_composition_integral` satisfies the exact Appendix A.3
contract. There is no provider or frozen theorem anchor in P23-13f, so a
provider/frozen-type comparison and frozen seal-body test are not applicable.
This audit does not seal a physical theorem, prove the complete `osc_iter`,
close the whole transfer node, or release P23-15.

The notes concern the inherited comparison history and generated root, not an
extra mathematical premise or a missing integral estimate. No blocking
mathematical defect was found in the scoped file.

## Authority and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the requested
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local handoff.
Checked `docs/tracks/P/statement.md`, Revision 3 and Appendix A.3 of
`docs/tracks/P/design/P23-LEAN-DESIGN.md`, its design audit, and
`blueprint-P/parts/p2-averaging.tex:167–196`. The inherited integral contract
and proof are at `blueprint-N/parts/p5-canonical-maps.tex:203–212`.

The shared signatures are absent at this worktree's `.drafts/design/` path.
Read the actual shared file
`/root/code/KAM-inp/.drafts/design/P23Signatures.lean`, whose SHA256 is
`d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`,
matching the design receipt. Its main declaration starts at line 988.
Python extraction of the complete declaration text before `:=` established
byte-for-byte type equality between that signature, Appendix A.3 at line
1512, and the implementation at line 277. This includes implicit binder
order `{v} {B}`, `hB`, both continuity premises, the literal one-loss flow
domain, all four two-loss widths, the let-bound integral, and the exact
`(1 - oscTheta ...)⁻¹ * B` majorant.

Ran the requested `git diff inp...HEAD`. Git reports:

```text
warning: inp...HEAD: multiple merge bases, using 3ef2b02a0ff5101143bd70bf5e1ddde63397da51
```

The comparison contains 142 files / 23091 insertions, including unrelated
newer-base work. The named module is a new 349-line file. `git show --stat
--oneline HEAD` confirms `ad0494a` adds only this module. The exact protected
comparison `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
is **not empty**: `KAM.lean` has 81 added imports. Frozen files, manifest and
README have no differences. `git diff HEAD^ HEAD -- KAM/Frozen manifest
KAM.lean README.md` is empty. Thus the package commit itself preserves all
protected paths; the raw branch comparison does not satisfy the generic
empty-root-diff condition. This is disclosed under the handoff's explicit
instruction to ignore unrelated files. No generated file was edited here.

## Declaration and node review

All names below have prefix `KAM.Planetary`. Locators refer to the scoped
Lean file. Helpers refine the integral proof obligations in Revision 3;
they do not replace source conclusions with assumptions.

| Node / obligation | Declaration and line | Verdict | Reason |
|---|---|---|---|
| Real integration carrier | `oscCube`, 47 | PASS | Literal unit cube; independent of flat parameter dimension. |
| `oi-transfer`, coefficient interchange | `coeff_integral_flat`, 54 | PASS | Arbitrary `n,N`; joint continuity on the compact time/cube product implies product integrability, Fubini equality and time integrability of each coefficient. No integrability premise is added to the main result. |
| `oi-transfer`, domain geometry | `OscComposeData.sub_gaugeInterior`, 111 | PASS | Derives containment of the two-loss domain in the half-gauge interior using the existing one-gauge containment. |
| `oi-transfer`, flow carrier | `OscComposeData.flow_mem`, 117 | PASS | Existing `flow_b` supplies membership in the literal one-loss flow domain for all times in `[-1,1]`. |
| `oi-transfer`, joint derivative regularity | `osc_paramHyp_integrand`, 127 | PASS | Constructs all three `ParamHyp` fields, including the chain-rule derivative and its joint continuity. Only the signed generic family regularity is assumed. |
| `oi-transfer`, analytic and periodic class | `osc_integral_class`, 191 | PASS | Parametric integration on the open two-loss domain; exact unclamping on `[0,1]`; periodicity from flow equivariance and slice periodicity. |
| `oi-transfer`, real-cube regularity | `osc_continuousOn_integrand`, 245 | PASS | Real angles enter the positive-width strip; the fixed flat parameter enters the two-loss parameter domain; continuity follows by composition with `flow_b`. |
| `oi-transfer` / `oi-ratio`, Appendix A.3 integral bound | `osc_composition_integral`, 277 | PASS | Exact signed statement. Bounds each slice by `osc_composition_t`, proves denominator positivity, then controls every finite Fourier partial sum and obtains summability and the full weighted bound. |
| Private continuity helper | `continuous_realPt''`, 49 | PASS | Coordinatewise real inclusion is continuous. |
| Private summability helper | `wsummable_of_finset_le'`, 95 | PASS | Nonnegative coefficient weights and uniform finite-sum bounds give summability and the tsum bound. |

The coefficient helper is stronger than a fixed oscillator-dimension version:
it works for every independent parameter dimension `N`, without dimension
positivity assumptions. The domain helper gives times in `[-1,1]`, covering
the needed `[0,1]`. Neither strengthening alters the main theorem.

## Proof and definitions

The only new definition/abbreviation/structure is `oscCube` (line 47), a
transparent abbreviation for `Set.pi Set.univ (fun _ => Icc 0 1)` on
`Fin n → ℝ`. It has the intended meaning on its whole carrier, including
dimension zero. No fallback, choice or partial definition is introduced.
There are no new instances or premise bundles.

Expanded the inherited `OscComposeData` fields: positive dimensions,
twice-loss width margins, generator class and weighted bound, nonnegative
generator majorant and the numerical smallness inequality. None asserts a
flow conclusion, convergence, composition bound or integral conclusion.
Expanded `oscPack`, `oscUnpack`, `oscFunction`, `oscParams`, `oscDom`,
`oscClass` and `oscBound`: the Fourier dimension is `n`, parameter dimension
is `n+(m+m)`, and canonical phase dimension is `n+m`. The bound retains
`WSummable` and the weighted coefficient tsum at every flat parameter.
Only fast angles are Fourier expanded, with period one. There is no
supremum-norm replacement or conversion loss.

The total inherited `flow` has an identity fallback when no solution exists.
The proof does not exploit it: `H.toFlowHyp.smallField`, gauge-interior
containment and `flow_b` establish the actual regular flow and its domain
membership at every point/time used. All calls use the same literal
one-loss domain and the frozen `KAM.hamiltonianVectorFieldℂ`.

Specific analytic checks:

- Lines 138–188 derive joint composition continuity and differentiability.
  Differentiability at the flow image follows from the open domain and
  `hv`; flow differentiability follows from the open gauge interior.
  `fderiv_comp` identifies the true derivative before continuity of
  continuous-linear-map composition is used. Clamping extends the family
  to `[-1,1]` without requiring data outside `[0,1]`.
- Lines 203–242 remove clamping exactly on the integration interval and
  prove periodicity via `flow_d`, translation invariance of the one-loss
  domain, generator-field periodicity and `(hv t ht).periodic_int`.
- Lines 60–92 multiply the continuous integrand by the continuous Fourier
  character on a compact product. `integrableOn_compact`, restriction to
  `Ioc 0 1`, product-measure identification, `integral_integral_swap` and
  `hint.integral_prod_left` pay the measurability and integrability debts.
  No zero-default integral is used to evade an obligation.
- Lines 293–307 obtain `0 ≤ θ < 1` from `osc_hat_ratio`. Since `0 ≤ t ≤ 1`,
  the reciprocal comparison has a proved positive denominator and uses the
  signed `0 ≤ B`. This input is already present in Appendix A.3.
- Lines 308–343 work at a fixed flat parameter. Coefficient Fubini supplies
  interval integrability; norms and constant weights preserve it, and finite
  sums remain integrable. The integral triangle inequality, finite-sum
  interchange and integral monotonicity bound every partial sum by
  `(1-θ)⁻¹ B`. Nonnegative-series summability then gives the actual `wsum`
  bound. No infinite-sum/time interchange is assumed.

Empty parameter domains give the intended vacuous bound. `B=0` and zero
generator majorant remain allowed; no division by either is introduced.

## Imports and frozen objects

Recursively scanned the local `KAM` import closure (82 modules). There are
no provider imports and no frozen theorem imports. Its 12 frozen modules
are all definition anchors, each recorded `SEALED` in the local manifest:

```text
KAM/Frozen/Defs/ActionNbhd.lean
KAM/Frozen/Defs/ComplexStrip.lean
KAM/Frozen/Defs/HamiltonianVectorField.lean
KAM/Frozen/Defs/HamiltonianVectorFieldC.lean
KAM/Frozen/Defs/IsDiophantine.lean
KAM/Frozen/Defs/IsPrimaryOnStrip.lean
KAM/Frozen/Defs/IsRealOnReals.lean
KAM/Frozen/Defs/OmegaZero.lean
KAM/Frozen/Defs/SymplecticForm.lean
KAM/Frozen/Planetary/Defs/Fast.lean
KAM/Frozen/Planetary/Defs/Phase.lean
KAM/Frozen/Planetary/Defs/Slow.lean
```

Read these definitions, in particular the literal complex Hamiltonian
field, sup-norm action neighborhood/strip, phase and block conventions.
The paired-dimension N weighted composition theorem is not applied to the
oscillator carrier: `CompositionIntegralClass` supplies analytic integration
infrastructure and clamping; the new Fourier interchange helper explicitly
allows the independent parameter dimension.

## Independent verification

All Lean/Lake checks were sequential, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; no heartbeat, recursion or synthesis overrides were used.

1. Targeted gated build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313f KAM.Planetary.Averaging.OscillatorCompositionIntegral
   ```

   Exit 0, after the expected gate wait:

   ```text
   [inp-gate] slot 1 acquired 12:25:28 for KAM.Planetary.Averaging.OscillatorCompositionIntegral
   Build completed successfully (9128 jobs).
   ```

2. Exact-signature application and every new public theorem's axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313fAudit.lean
   ```

   Exit 0, no warnings. The probe imports only the production module,
   copies the complete Appendix A.3 declaration under `audit_exact_A3`, and
   proves it with `exact osc_composition_integral H hB hv hc hDc`.
   This checks application in the exact explicit-binder order without
   importing a signature fixture or adding any unproved declaration.
   Literal axiom output:

   ```text
   'KAM.Planetary.coeff_integral_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.OscComposeData.sub_gaugeInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.OscComposeData.flow_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_paramHyp_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_integral_class' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_continuousOn_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_composition_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation for the single new lemma module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorCompositionIntegral
   ```

   Exit 0. Literal output:

   ```text
   replaying KAM.Planetary.Averaging.OscillatorCompositionIntegral
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the explicitly permitted stale-root exception; all other
   components pass. Literal output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (634 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Kernel and lint output were captured under `.lake/abi-scratch/` during
   execution. No wrapper, root regeneration or source repair was used.

5. Scoped source scan finds no forbidden proof escape, `EuclideanSpace`
   or `set_option`. The file has 349 lines and maximum Unicode line length
   98. Copyright, `module`, public interface imports, module docstring and
   `@[expose] public noncomputable section` are present. `git diff --check`
   exits 0. After removing this audit's probe and captured logs, final
   `git status --short` lists only this untracked report and the preexisting
   untracked `P23-13f-handoff.md`; no tracked file is modified. A direct
   whitespace check of the new report also passes. No state-changing git
   command was run.

## Errata, deviations and limits

No new source or blueprint defect was found in the integral argument.
No pinned PDF was independently re-audited; this is an implementation audit
against the exact design and blueprint contracts.

The inherited blueprint issue remains at
`blueprint-P/parts/p2-averaging.tex:177`, which writes the angular derivative
denominator `e(S_0-S)` under only `S-σ<S_0`. That margin does not force
`S_0-S>0`. The target-width denominator is `e(S_0-S+σ)`, as already
acknowledged in Revision 3's source-limitations paragraph. P23-13f does not
use the incorrect displayed estimate; its slice estimate is the landed
`osc_composition_t`. This is a carried blueprint issue, not a newly verified
pinned-paper erratum.

Using finite partial sums instead of an explicit infinite Tonelli exchange
proves the same required conclusion and establishes summability at the
same time. No mathematical statement deviation was introduced. The
inherited generated-root differences and missing local signature copy are
disclosed above. The audit edits only this report and temporary scratch
artifacts; no production, frozen, manifest or generated file is repaired.
