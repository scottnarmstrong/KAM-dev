# S4 independent package audit 1

**Overall verdict: PASS WITH NOTES.** The complete S4 slice passes exact-signature, proof, axiom and kernel checks. No blocking finding. The sole validation note is the explicitly permitted stale generated `KAM.lean`; lint exits 1 for that reason. No frozen theorem anchor is assigned to or sealed by S4.

Scope: only `KAM/Planetary/SecularBox/ParametricIntegral.lean`, branch `inp-p14-s4`, HEAD `0d8cd7a7aaaec3f00b01ff1aad622c578f7e348f`. Comparison: `git diff inp...HEAD`, with current `inp` at `a341f3aebaad7052378f3fd4846d8619bf8da9d9`. The diff adds exactly this 157-line module. The pre-existing untracked S4 handoff is untouched.

The user's exact report destination inside `/root/code/KAM-inp-p14-s4` overrides the generic brief's main-worktree destination. Read AGENTS.md, PLAN, DECISIONS, the package brief, S4 handoff, P14 design and its two audits, the authoritative `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, track P statement, relevant blueprint nodes, frozen Phase and its three project definition dependencies. No external source result is needed for this elementary analytic helper.

## Scope and declaration ledger

There is no provider or frozen theorem anchor assigned to S4. Provider/frozen-type and seal-body tests are therefore inapplicable. S4 is the analytic feasibility gate at design lines 38, 349, 390, not a seal of secularBoxSafety or any planetary headline.

All names below are in `KAM.Planetary`.

| Node / role | Declaration and module line | Verdict | Reason |
|---|---|---|---|
| p14:sb-sm-3; required local p8:e-diff instance / S4 | `secular_parametric_integral`, 150 | PASS | Exactly the signed finite-order compact-parameter smoothness statement; all dimensions, binders, premises and conclusion retained. |
| S4 continuity supplier | `sb_param_integral_continuousOn`, 40 | PASS | Genuine continuity under compact integration for general real normed spaces and a measure finite on compact sets. No conclusion premise. |
| S4 derivative supplier | `sb_param_integral_hasFDerivAt`, 72 | PASS | Actual first Fréchet derivative equals the integral of the first-parameter derivative. Domination and integrability are proved. |
| S4 induction supplier | `sb_param_integral_contDiffOn`, 118 | PASS | All finite orders and complete normed codomains in universe u; sufficient generality for the derivative-valued induction. |

The S4 package row has one assigned declaration, and it is delivered. Other smooth-integrand, integral-identity, integrability and secular regularity work belongs to S3/S5 and is not claimed here. Blueprint p14b line 203 and Part 8 line 27 motivate the helper. Part 8 also states arbitrary higher derivative identities, Fubini and periodic translation; S4's deliberately scoped signature supplies smoothness, with a separate first-derivative formula. This audit does not certify those broader Part 8 claims as completed by S4.

## Signature, universes and section variables

Python extraction from `theorem secular_parametric_integral` to the following `:=` gives:

```text
PRODUCTION = SIGNATURE statement bytes: True
PRODUCTION = DESIGN APPENDIX statement bytes: True
```

Authoritative signatures SHA-256 at audit time: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.
Production module SHA-256: `a944ff96fd311df773fdbc7510f41f44644ffcfaf5a84a26c44b853e4c541b63`.

The signed statement is monomorphic in its finite real phase and integration spaces; the helper's `universe u` does not introduce a universe parameter or typeclass premise on the public assigned theorem. The General section ends at line 147. The theorem has only `{d q}`, `{U}`, `hU`, `{Q}`, `hQ`, `{g}`, `k`, `hg`. A fresh signed-copy probe and both directions of `type_of%` assignment check the complete elaborated telescope; no admitted signature module is imported.

The file-level `set_option linter.unusedSectionVars false` (line 30) is a linter setting, not a resource override. There is no `include`. In the induction theorem H is deliberately rebound after k so the induction hypothesis may be instantiated with `E →L[ℝ] H`; the outer section H and its instances do not become extraneous theorem premises. The checked public telescopes are recorded below.

## Proof and definition review

There are no new `def`, `abbrev`, `structure`, instances or object-valued public declarations. All four new declarations are theorems. The existing frozen `Phase d` is literally `(Fin d → ℝ) × (Fin d → ℝ)` with Pi max norms. No carrier substitution or junk object is introduced. Local witnesses and finite-measure instances are proved from compactness and the standing measure premise.

Continuity (lines 44–69): openness supplies epsilon>0 with a ball in U. Its closed half-radius ball is compact by ProperSpace, and its product with Q is compact. Joint continuity bounds the norm there by a real constant C. Q is closed and measurable; the restricted measure is finite because Q is compact. Continuity of each F-section gives restricted strong measurability. The constant bound is integrable and valid simultaneously on the parameter neighborhood and Q. Pointwise parameter continuity then discharges `continuousAt_of_dominated`. No positivity of C is needed separately; the norm-bound witness and finite-measure integrability suffice, including empty Q.

Differentiation (lines 76–115): openness converts C1 to the actual ambient derivative on U×univ. The map `p ↦ (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E P)` is continuous. Compactness gives a bound uniform over the same parameter neighborhood and all F in Q. The proof supplies all six hypotheses of Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`: nearby measurability, integrability at the base point, derivative measurability, uniform almost-everywhere derivative bound, integrable bound, and actual derivatives throughout that neighborhood. Composition with `(x,F)` produces the correct first-parameter derivative. The restricted measure and Bochner integral are literal; total integral fallback values are not used to evade integrability.

Induction (lines 125–145): order zero is continuity. For k+1, differentiating jointly yields Ck of the partial derivative integrand. The induction hypothesis is generalized over H and is instantiated at the complete continuous-linear-map space `E →L[ℝ] H`. The first-derivative theorem gives differentiability and identifies `fderiv` with that integral on U. `contDiffOn_succ_iff_fderiv_of_isOpen` concludes C(k+1); the analytic side condition at order omega is vacuous for finite k. `this.congr` uses the pointwise derivative identity in the correct direction. No bound, regularity conclusion or hard analytic step is assumed as an extra premise.

The assigned real theorem specializes the genuine general theorem at Lebesgue measure. Finite real phase spaces provide ProperSpace and the other standard instances. Empty U/Q and zero dimensions require no added hypotheses.

## Hygiene and validation

All validation commands ran serially with `LEAN_NUM_THREADS=1`; no simultaneous audit Lean/Lake process was started. Commands ran in `/root/code/KAM-inp-p14-s4`.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s4 KAM.Planetary.SecularBox.ParametricIntegral
```

The wrapper runs `nice -n 5 lake build` after acquiring a gate slot. Output, exit 0:

```text
[inp-gate] slot 1 acquired 17:53:35 for KAM.Planetary.SecularBox.ParametricIntegral
Build completed successfully (2764 jobs).
```

2. Fresh signed-copy/type/axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S4Audit.lean > .lake/abi-scratch/S4Audit.out 2>&1
```

Exit 0, no errors or warnings. The probe imported only the audited module, copied the literal signed telescope under `s4_audit_signed_copy`, proved it by `secular_parametric_integral hU hQ k hg`, and checked:

```lean
example : type_of% @s4_audit_signed_copy := @secular_parametric_integral
example : type_of% @secular_parametric_integral := @s4_audit_signed_copy
```

It printed all four public declarations and their axioms. Exact axiom output:

```text
'KAM.Planetary.sb_param_integral_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_param_integral_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_param_integral_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secular_parametric_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The universe-printing output identifies `secular_parametric_integral` with no universe parameter; its sets, products and calculus instances are all universe 0. Both first two helpers have `{E P H : Type u}` and the printed general induction telescope has `{E P : Type u}` before U/Q/mu, then `(k : ℕ) {H : Type u}` with precisely its three codomain instances. There is no unused outer-H premise. ProperSpace E and the measure/topology hypotheses are genuine standing conditions of the stronger general helper; none is added to the signed real theorem.

3. Kernel replay (one invocation; all new lemma declarations reside in this single module):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.ParametricIntegral > .lake/abi-scratch/S4Kernel.out 2>&1
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.SecularBox.ParametricIntegral
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/S4Lint.out 2>&1
```

Exit 1. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (822 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is precisely the generated-root exception allowed by the audit brief and handoff. No other lint failure was emitted. `KAM.lean` was not regenerated. ABI checking internally invokes Lean, so lint was run only after kernel replay finished, with the same thread limit and inherited nice priority.

The temporary signed-copy probe and all three captured validation logs were removed from `.lake/abi-scratch/` after their results were transferred here. No production files were edited. Final report whitespace and scope checks pass.


Static checks: `git diff --check inp...HEAD` exits 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (exit 0). A declaration search across KAM finds exactly one occurrence defining each of the four names, all in this module. All are inside `namespace KAM.Planetary`; no root name shadowing. Module header, copyright, public imports, docstring, exposed public section and 157-line size satisfy the module and size rules. There are no forbidden proof escapes, resource overrides or EuclideanSpace uses.

Project import closure: `KAM.Frozen.Planetary.Defs.Phase`, `KAM.Frozen.Defs.HamiltonianVectorField`, `KAM.Frozen.Defs.IsDiophantine`, `KAM.Frozen.Defs.SymplecticForm`. All four are SEALED definitions in the manifest. No frozen theorem or provider import appears, directly or transitively.

## Uncertainties, errata and deviations

No suspected source or blueprint defect found within S4. No change to a frozen statement or definition and no mathematical deviation introduced. The statement/source scope distinction above is retained: package smoothness is not full Part 8 closure, nor proof of downstream S5 or frozen headlines. The generated-root note is the only validation exception, and its exact result is recorded above. No unresolved validation remains.
