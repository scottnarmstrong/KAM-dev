# B5-NF independent package audit 1

Date: 2026-11-03. Worktree: `/root/code/KAM-inp-b5nf`.
Audited HEAD: `b4bf9142ede89c9a1a4aa2891825877787895e84`.
Comparison ref `inp`: `e24669961b91521d0e3af783b46316c7a8098a0f`.
Prover commit: `71a046f4a`; the three-dot comparison includes its subsequent merges.

## Verdict

**PASS WITH NOTES** for B5-NF and `KAM.EffectiveStability.torusNormalForm_confinement`.
The normal-form identities and the drift estimate are proved from the stated source
premises. No mathematical failure was found. There is **no frozen B5-NF anchor or
provider** in this package, so this is acceptance of ordinary theorem infrastructure,
not a seal approval or completion of the certificate-to-confinement route.

The notes are substantive scope boundaries: `hG` and `hD3` remain B5-ROUTE obligations,
the design table's allocation of the Cauchy estimate to B5-NF exceeds what this
package implements, and lint reports the expressly permitted stale generated root.
The focused audit instructions and package brief expressly permit the quantitative
third-derivative bound as a premise.

Read: AGENTS, PLAN, DECISIONS, the generic package-audit brief, B5-NF's original brief
and B1-common brief, SPEC, FREEZE-PROPOSAL, B5-DESIGN, OWNER-DECISIONS OD-B13–15,
B5-NF-handoff (including AUDIT FOCUS), and program-b-plan §3.4, lines 426–457.
The applicable statement specification is Track B's design and package brief;
there is no B5-NF node in blueprint-I/N/P or frozen I/N/P theorem to substitute for it.
The user's exact worktree report destination overrides the generic brief's main-worktree destination.

## Refutation checks

1. **First-order normal form is derived.** `Basic.lean:39–44` bundles only
   differentiability of the physical Hamiltonian on the torus, invariance, and energy.
   It contains no normal-form or drift conclusion. `torusNF_dG_J` first differentiates
   the chart in `(0,J)`, uses the first component of invariance to identify the
   momentum derivatives with `Dx ω'`, and cancels the transpose inverse with `Dx`.
   It proves the identity for arbitrary `J`, stronger than the requested basis-vector
   identity. `torusNF_G_zero` uses energy directly. The algebraic definition of `R`
   alone would not prove any vanishing derivative; those steps are actually paid here.
2. **Vanishing and derivative order.** The zero-section energy function is constant,
   hence its angle derivative is zero. The action derivative is the constant
   `ω'·J`; differentiating it in the angle direction, then using Hessian symmetry,
   proves `torusNF_d2G`. The two derivative-transfer lemmas use an open-neighborhood
   identity, so they do not silently differentiate an equality known only at one point.
   `torusNFRem_d2` has exactly the requested angle/action order. This is second-order
   vanishing in actions: no vanishing of the action/action Hessian is claimed.
3. **Sharp constant.** Taylor's segment is `(φ,tJ)`, `0 ≤ t ≤ 1`, inside `cyl c` by
   `hw` and strict `b j < c j`. Two real comparison arguments bound the first
   derivative by `m t` and the function by `m t²/2`. The inputs are the already-proved
   zero first and mixed second derivatives. The product norm is the maximum norm,
   `‖(0,J)‖ = ‖J‖`, and `‖(e_i,0)‖ = 1`. Thus the result is exactly
   `C₃ * ‖J‖² / 2`, with no dimension factor. For `n=0` the indexed drift conclusion
   is vacuous, and the generic theorem and confinement do not introduce a hidden
   nonempty-index assumption.
4. **Premises and constants.** `hG` is regularity of the actual pullback on the open
   cylinder; `hD3` bounds its actual third derivative there for all three directions.
   Neither is a vanishing or drift conclusion in disguise. The evaluated nested
   continuous-linear-map estimate uses sup norms, so a future bound on scalar
   components must first be converted to this bound, retaining any dimension factors.
   `C₃`, `B`, and `η` are supplied constants constrained by explicit inequalities;
   there is no broadened existential dependence. Strict outer-cylinder room is an
   intentional hypothesis needed for ordinary Fréchet derivatives at the stopped boundary.
5. **Confinement conclusion.** Compared every conjunct with `Torus.lean:61–73`.
   A fresh Lean probe copied B1-T's conclusion, substituted
   `H := hR`, `Ψ := torusChartMap u v`, `Ψinv := torusChartInvMap u v`, and proved it
   by applying B5-NF with all explicit arguments in order. It elaborated. Lifetime
   `T₁>T`, physical ODE in `V`, agreement with every local solution, endpoint-inclusive
   bounds, image membership, and both action bounds are preserved.
   `0 ≤ η j` and `0 < b j` are derived using the stated margin, `hηB`, and `hw₀`.
6. **Periodicity.** Chart equivariance turns `Ψ(w+angleShift k)` into
   `Ψ w+angleShift k`; `hper` supplies physical periodicity at precisely those points.
   Actions and the linear part are unchanged. The cylinder is invariant under angle
   shifts. Consequently this restricted premise pays B1-T's full remainder-periodicity
   premise on the open cylinder; global periodicity of `hR` or `V` is unnecessary.
7. **Smoke.** `torusNF_smoke_torus` proves differentiability, invariance and energy
   for the linear Hamiltonian; `torusNF_smoke_rem` proves the remainder is identically
   zero. `torusNF_smoke_confinement` actually applies the audited corollary with
   `C₃=0`, `η=0`, and identity chart/inverse. Its exported conclusion deliberately
   selects the zero-action-drift clauses; the stronger ODE/uniqueness result is
   obtained internally by that application, not claimed in the smoke signature.

## Declaration-by-declaration review

All names below are in `KAM.EffectiveStability`. All 26 public theorems were included
in the fresh axiom probe. Generated structure constructor/projection declarations
are covered by the structure row.

| Node | Declaration | Verdict | Reason / note |
|---|---|---|---|
| Taylor helper | `abs_le_of_abs_deriv_le_nfT` | PASS | Actual derivative comparison on `[0,1]`; zero initial data and both signs handled. |
| Taylor helper | `hasDerivAt_clm_path_nfT` | PASS | Chain rule and continuous evaluation; arbitrary real normed carriers. |
| Item 3 helper | `fderiv_taylor_bound_nfT` | PASS | General normed-space bound with sharp `1/2`; no completeness premise. |
| Torus object | `torusNFGraph` | PASS | Intended graph on the whole carrier. |
| Torus inputs | `TorusNFTorus` | PASS | Source identities and local differentiability only. |
| Remainder object | `torusNFRem` | PASS | Literal pullback minus affine action part everywhere. |
| Linear object | `torusNFLin` | PASS | Correct continuous linear functional. |
| Linear helper | `torusNFLin_apply` | PASS | Evaluates to the intended finite sum. |
| Remainder helper | `torusNFRem_eq` | PASS | Functional identity with continuous linear part. |
| Linear helper | `clm_apply_zero_snd` | PASS | Basis expansion of arbitrary action vector. |
| Chart helper | `torusChartMap_fderiv_zero_snd` | PASS | Derives exact zero-section action derivative of chart. |
| Item 1 | `torusNF_dG_J` | PASS | Derived from invariance; arbitrary action direction strengthens requested basis form. |
| Item 1 | `torusNF_G_zero` | PASS | Derived from energy and zero-section chart identity. |
| Regularity helper | `torusNF_G_differentiableAt` | PASS | Chain rule with explicit differentiability source. |
| Item 2 helper | `torusNF_dG_phi` | PASS | Derivative of zero-section constant energy. |
| Domain helper | `zero_mem_cyl_nf` | PASS | Positive radii give zero-section membership. |
| Item 2 helper | `torusNF_d2G` | PASS | Constant action derivative plus Hessian symmetry. |
| Item 2 helper | `fderiv_torusNFRem` | PASS | Correct derivative subtraction on open cylinder. |
| Item 2 helper | `fderiv_fderiv_torusNFRem` | PASS | Neighborhood equality removes affine Hessian. |
| Item 2 | `torusNFRem_zero` | PASS | Correct remainder value on zero section. |
| Item 2 | `torusNFRem_dJ` | PASS | Correct action derivative; C³ ambient setting is explicit. |
| Item 2 | `torusNFRem_dphi` | PASS | Correct angle derivative in same setting. |
| Item 2 | `torusNFRem_d2` | PASS | Correct angle/action Hessian entry. |
| Item 2 | `torusNFRem_shift` | PASS | Image-restricted physical periodicity suffices. |
| Item 3 | `torusNF_drift` | PASS WITH NOTES | Sharp conditional estimate; hG/hD3 remain route inputs. |
| Item 4 | `torusNormalForm_confinement` | PASS WITH NOTES | Exact specialized B1-T conclusion; same unresolved analytic inputs. |
| Smoke object | `torusNFLinearHam` | PASS | Intended affine Hamiltonian on all phase space. |
| Smoke helper | `torusNFLinearHam_fderiv` | PASS | Correct everywhere derivative. |
| Item 5 | `torusNF_smoke_torus` | PASS | Builds all three source fields. |
| Item 5 | `torusNF_smoke_rem` | PASS | Remainder identically zero as a function. |
| Item 5 | `torusNF_smoke_confinement` | PASS | Calls item 4 with zero drift and obtains constant actions. |

## Definition classification

There are four new `def`s and one `structure`, no `abbrev`:

| Object | Classification | Whole-carrier / fallback assessment |
|---|---|---|
| `torusNFGraph` | Geometric graph | `(φ+u φ,v φ)` everywhere; no choice/default. |
| `TorusNFTorus` | Prop-valued source-data bundle | Exactly differentiability, invariance, energy; no assumed hard normal-form step. |
| `torusNFRem` | Exact analytic remainder | `hR(Ψ w)−(E0+Σω'j Jj)` everywhere; no truncation or fallback. |
| `torusNFLin` | Continuous linear map | Finite sum of weighted action projections, including the empty sum. |
| `torusNFLinearHam` | Smoke Hamiltonian | Exact affine function everywhere. |

The chart's inverse-matrix implementation is inherited, not a new definition here;
its inverse identities are used under `TorusChartData`, never on unsupported singular data.

## Hygiene and independent checks

All commands ran from `/root/code/KAM-inp-b5nf`. Define the displayed command prefix:

```sh
CAP='systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1'
```

The commands below were executed with that literal prefix (no resource-budget
overrides). Each Lean/Lake/kernel invocation completed before the next started;
the lint command also inherited the cap and thread setting for its ABI Lean subprocess.

### Targeted build

```sh
$CAP /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b5nf KAM.EffectiveStability.TorusNormalFormSmoke
```

Exit 0, exact output:

```text
[inp-gate] slot 1 acquired 04:38:11 for KAM.EffectiveStability.TorusNormalFormSmoke
Build completed successfully (2896 jobs).
```

This targets the smoke module and its import closure, which includes all six
package modules. No clean, cache retrieval, library-root build, or opt-in application build.

### Kernel replay

```sh
$CAP lake env leanchecker --verbose KAM.EffectiveStability.TorusNormalForm KAM.EffectiveStability.TorusNormalForm.Basic KAM.EffectiveStability.TorusNormalForm.Remainder KAM.EffectiveStability.TorusNormalForm.Drift KAM.EffectiveStability.TorusNormalForm.Taylor KAM.EffectiveStability.TorusNormalFormSmoke
```

Exit 0, exact output:

```text
replaying KAM.EffectiveStability.TorusNormalFormSmoke
replaying KAM.EffectiveStability.TorusNormalForm.Remainder
replaying KAM.EffectiveStability.TorusNormalForm.Basic
replaying KAM.EffectiveStability.TorusNormalForm.Taylor
replaying KAM.EffectiveStability.TorusNormalForm.Drift
replaying KAM.EffectiveStability.TorusNormalForm
```

This is the prescribed module replay, not a fresh replay of all Mathlib dependencies.

### Axioms and conclusion probe

```sh
$CAP lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B5NFAudit1.lean
```

Exit 0. The scratch file imported `TorusNormalFormSmoke`, printed axioms of every
theorem in the declaration table, and elaborated the copied B1-T conclusion probe
described above. Exact output:

```text
'KAM.EffectiveStability.torusNormalForm_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFLin_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFRem_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.clm_apply_zero_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartMap_fderiv_zero_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_dG_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_G_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_G_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_dG_phi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.zero_mem_cyl_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_d2G' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_torusNFRem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_fderiv_torusNFRem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFRem_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFRem_dJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFRem_dphi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFRem_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFRem_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.abs_le_of_abs_deriv_le_nfT' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.hasDerivAt_clm_path_nfT' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_taylor_bound_nfT' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNFLinearHam_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_smoke_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_smoke_rem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusNF_smoke_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There were no warnings or other diagnostics.
Frozen-provider type equality and a frozen seal-body probe are **not applicable**:
no B5-NF frozen anchor exists. The replacement probe validates the actual requested
consumer conclusion and the full explicit argument application, without inventing an anchor.
Scratch probe removed after checking.

### Source lint, names, imports and protected files

```sh
$CAP sh scripts/lint_sources.sh
```

Exit 1 solely for the permitted stale generated root. Exact combined output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4562 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.828s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The generic audit brief expressly permits this generated-root exception. The
parenthesized root part identifies the generated import listing needing regeneration;
no generated root was edited. All other lint stages passed. The ABI receipt covers
314 core frozen declarations; the two listed opt-in application anchors receive
file-hash checking only in this run, exactly as reported by the tool.

Short-name command (exit 0):

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b5nf KAM.EffectiveStability.TorusNormalForm.Taylor KAM.EffectiveStability.TorusNormalForm.Basic KAM.EffectiveStability.TorusNormalForm.Remainder KAM.EffectiveStability.TorusNormalForm.Drift KAM.EffectiveStability.TorusNormalForm KAM.EffectiveStability.TorusNormalFormSmoke
```

Exact output: `short-name check OK (no reused public short name)`.

Fresh six-file checks found no forbidden token, override, carrier, missing module
header, or line-width violation. Files have respectively Taylor 115, Basic 119,
Remainder 145, Drift 65, facade 96, smoke 95 lines; maximum widths are 100, 100,
100, 98, 98, 97. All use copyright/module/public imports/module docstring/public
section; definitions are in an `@[expose] public noncomputable section`.

The transitive local import closure contains 50 modules, including 20 frozen
definition files and **no frozen theorem or provider**. Thus there is no imported
DRAFT_SORRY anchor or provider chain to launder a proof. The physical field and
symplectic signs agree with the read frozen definitions; the phase carrier remains
`(Fin n → ℝ) × (Fin n → ℝ)`. No application module is imported.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff inp...HEAD -- KAM/Root lakefile.lean
```

All exit 0 with empty output. The complete three-dot diff has only the six Lean
files and B5-NF-handoff, 713 added lines. This audit changes only this report;
there is no state-changing git operation and no source or frozen repair.

## Retained obligations, documentation discrepancy and errata

**N1 — B5-ROUTE analytic inputs remain unpaid.** `TorusNormalForm.lean:48–54`
requires `ContDiffOn ℝ 3 (hR ∘ torusChartMap u v)` and the evaluated third-derivative
bound. B5-CHART currently proves only a C² chart. C³ regularity of `hR` by itself
does not upgrade a C² chart to C³. The route must prove the stronger regularity of
the actual pullback (for example from analytic torus/chart data), quantitative
`hD3` on the entire cylinder, and image containment. It must also transport
B5-LAG's real-restriction invariance/energy into `torusNFGraph` and keep the actual
frequency `ω'=s∞ω*`. This report does not certify any of those subsequent steps.

**N2 — documentation allocation discrepancy.** `docs/tracks/B/B5-DESIGN.md:49`
lists B5-NF's contents as including “the third-derivative Cauchy bound”. This package
does not derive that bound from holomorphic data; it takes it as `hD3`.
The original NF brief, item 3, explicitly starts “if `‖D³ (hR ∘ Ψ)‖ ≤ C₃`”, and its
last paragraph says the bound is “to be discharged later by Cauchy estimates in
B5-ROUTE”; the handoff focus repeats that allocation. Acceptance is under that
explicit focused contract. Reconcile the design row when assembling the route;
do not report this package as having proved a Cauchy estimate.

No suspected defect in a pinned mathematical source, B5-CHART statement, B5-LAG
statement, or frozen definition was found. N2 is an internal scope discrepancy,
not a claimed mathematical source erratum. No audit-introduced mathematical
deviation. The handoff's evaluated-form and image-periodicity changes are faithful
to the allowed source premises. There is no heartbeat or file-size design signal.
