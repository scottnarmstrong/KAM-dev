# W3-MAIN independent package audit 1

**Overall verdict: FAIL for complete source-node fidelity.** The weak-regularity estimate has the wrong cubic constant (F1), and the full quantitative/integral conclusion of `bpW:w3:Yseries` is not exported (F2). Local analytic objects also have unrestricted public carriers with totalized series/inverse semantics (F3). These findings do not refute the proved, domain-restricted remainder, conjugacy, or frozen coordinatewise transport theorems.

## Scope and frozen inputs

Auditor: `maud-wpka-1`, 2026-10-31. Report-only audit in `/root/code/KAM-inp-wpka`, physically `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpka`. No implementation, frozen file, manifest, generated root, or git history was edited. Temporary evidence was generated under `.lake/abi-scratch/` and removed after transcription.

- HEAD: `d65ed073653cfc3a00ecbc1dfebdf6a0b1363b60`.
- `inp` at audit entry: `d7af5a6475637acf5e1502a4145ed2acdbdf4654`.
- Merge base for `git diff inp...HEAD`: `ee1e80f1c6923e85d659dcd737c68b8e6409c852`.
- Reviewed delta: 27 new implementation modules, 3,737 implementation lines; 27 generated import lines in `KAM/Root/Wave.lean`; 86-line handoff. Entire delta: 29 files, 3,850 insertions.
- Blueprint: `blueprint-W/parts/w3-birkhoff.tex`, SHA256 `1e09a1eb1b06815116809f1f45e996b1ba79962ebfb755e3c75b797e5a19b161`.
- Handoff: `docs/tracks/W/audits/W3-MAIN-handoff.md`, SHA256 `ac9b9acb14ffa6e504f29e22495efa61dbdfe388110b73dab1505a2433e45542`.
- Manifest: SHA256 `8859fe7f8bae7ca904585d0b72a6c23601d848c66febefdc7e5c74adb2300555`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the requested external package audit brief, the entire handoff, the six assigned blueprint statements and their proofs, relevant standing definitions and imported implementation interfaces, W-STATEMENTS, and the frozen Wave clause (4) and definitions. Applied `lean-statement-audit` to source correspondence and definition semantics. `docs/tracks/W/statement.md` does not exist: the actual statement document is `docs/tracks/W/W-STATEMENTS.md`; its draft banner is superseded by D41 and the manifest.

**Scope discrepancy:** this checkout's 86-line handoff contains no `AUDIT FOCUS` section and no `Not done` section despite line 5's reference. No unseen override was invented. The six labels listed at lines 3–5 control the mathematical scope. W3-MAIN is infrastructure, with no provider or frozen seal in the delta. Provider-equality/seal probes are therefore N/A. `wave.nlw2.v1`, export `KAM.Wave.nlw2`, remains `DRAFT_SORRY` / **FROZEN_UNPROVED**. Its clause (4) is a comparison target, not an imported proof dependency or a theorem closed by this package.

The P96-W PDF is not present at `sources/poschel1996_wave_CMH_71_269.pdf` in this checkout or the two main checkouts inspected. This audit checks the pinned repository blueprint and adopted normalization interfaces; it does not claim a new independent reading of the original printed pages. The source registry records P96-W SHA256 `77f083dc4f3d45802460c880a588ef227065810aa93cc963ff7684714d25d6a2`.

## Node verdicts

All implementation exports below are in `KAM.Wave`. PASS here means the listed, domain-restricted theorem matches the stated slice; it does not seal W-NLW2.

| Node / clause | Lean declarations | Verdict | Reason |
|---|---|---|---|
| `main` (i) | `birkK_eq`, `norm_birkK1_le`, `norm_birkK2_le`, `norm_birkK_le`, `birkK_analyticOnNhd`, `birkK_rho` | PASS WITH NOTES | Correct `5+5=10` sextic constant; analyticity proved on the larger `40 C_F‖w‖²<1` ball; public-definition qualification F3. |
| `main` (ii), complex | `birkK1_field`, `birkK2_field`, `birkK_field`, `norm_birkXK1_le`, `norm_birkXK2_le`, `norm_birkXK_le`, `birkXK_analyticAt`, `birkK_isClassA` | PASS WITH NOTES | Correct `44+22=66`, higher-weight target, field identity, analyticity and reality; F3. |
| `main` (ii), real | `birkK_real`, `birkXK_real`, `birkK_real_fderiv`, `birkK_real_gradient` | PASS WITH NOTES | Actual real restriction and Hamiltonian differential identity, with coefficients at output weight `p+1`; F3. |
| `main` (iii) | imported `birkQuart_isClassA`, `norm_birkQuartX_le`, `QuartNormal`, `birkHamBar_birkZR` | PASS WITH NOTES | Reuses quartic producers; corrected action formula is consumed, not assumed. Prior quartic proofs are dependencies, not re-audited packages. |
| `main` (iv) | `birk_conjugacy` | PASS | Produces both the higher-weight image point and conjugacy on the embedded ball; no assumed conjugacy/inverse result in its binders. |
| `Yseries` | `lieV`, `norm_lieV_le`, `summable_lieV`, `lieV_identity`, `hasFPowerSeriesOnBall_lieV`, `birkV_identity`, `hasDerivAt_Qseries` | FAIL | F2: convergence and analytic series are genuine, but the exact coefficient-sum bound and integral identification are absent. |
| `real-restrict` | `real_restrict`, `real_restrict_fun` | PASS | Both analytic restriction and equality with the unprojected real value; works for either weighted target via the common weighted-coordinate carrier; omits unneeded open/invariant-set premises, so is stronger. |
| `gamma-real` (i) | `birkGammaR_analyticOnNhd` | PASS WITH NOTES | Real analyticity established; explicit named real coefficient-series characterization from blueprint lines 784–786 is not exported (N1); F3. |
| `gamma-real` (ii) | `birkGammaR_sub` | PASS WITH NOTES | Gives higher-weight correction and `6√2 C_F‖x‖³`; norm factor `(10/9)√2<2` implies asserted image containment. F3. |
| `gamma-real` (iii) | `birkGammaR_inv`, `birkGammaR_injOn`, `birkGammaR_surj`, `birkGammaR_hasFDerivAt`, `birkGammaR_symplectic` | PASS WITH NOTES | Correct real ball (`320`), half-ball (`1280`), inverse, derivative and actual `Σ dq∧dp` form. F3. |
| `gamma-real` (iv) | `birkAction_birkZR`, `birkHamBar_birkZR`, `birkLambda_birkZR`, `birkH_gammaR` | PASS | Correct actions `(q²+p²)/2` and actual normal-form identity. |
| `transport-tori` | `birk_transport_tori`, `birk_transport_tori_real`, `birk_transport_tori_frozen_coord`, `birk_transport_tori_frozen` | PASS WITH NOTES | Directional theorem is stronger than requiring full differentiability. Frozen derivative form additionally assumes the source's full differentiability; coordinatewise form does not need it. Integral cubic bridge requires `a>0`, as stated. |
| `transport-tori-weak` | `birk_transport_tori_weak`, `birk_transport_tori_weak_real` | FAIL | F1: higher-weight membership and transport hold, but norm conclusion uses `2C_*` instead of `C_*`. |
| Weak transport, frozen clause (4) only | `birk_transport_tori_weak_frozen_coord`, `birk_transport_tori_weak_frozen` | PASS | The exact frozen invariance slice survives F1; these statements do not promise the sharper norm estimate. |

## Findings and refutation attempts

### F1 — major: weak-regularity conclusion is quantitatively weaker

Blueprint `w3-birkhoff.tex:837–838` requires

```text
‖Ψ(θ)‖₊ ≤ ‖DΨ(θ)ν‖ + C_*‖Ψ(θ)‖³ + C'_K‖Ψ(θ)‖⁵.
```

`MainWeak.lean:100–103,120–135` and `MainRealWeak.lean:28–42` instead export `2 * waveCubicConst p` in the cubic term. The constant is the same `C_*`, not a differently named enlarged constant. The handoff openly records this deviation at lines 47–49; disclosure does not establish the original conclusion.

Refutation attempt: expanded `birkRestField` and inspected its norm proof, `MainWeak.lean:92–114`. It applies the triangle inequality to the two quartic field estimates separately. The blueprint's stronger estimate at lines 853–855 uses a single quartic coefficient family with disjoint supports. No combined-field estimate is supplied here. Nonnegativity allows weakening `C_*` to `2C_*`, never the reverse. **SURVIVED.** Required repair: prove and consume the combined quartic estimate, or obtain an explicit revised blueprint ruling. No counterexample to the sharper mathematical statement is claimed.

### F2 — major: `Yseries` completion lacks its literal quantitative/integral exports

Blueprint `w3-birkhoff.tex:621–630` requires continuous coefficients of the actual integrand

```text
Y(t,w) = DΓ_t(w)⁻¹ X_Z′(Γ_t w) − X_Z′(w),
Σ_j ‖Y_j‖ ρ₁^(2j+3) ≤ 4 C_* ρ₁³,
∫₀¹ Y(t,w) dt = Σ_j Y_j(w,…,w)/(j+1),
```

with the specified formal series and reality. The implementation instead constructs pullback coefficients `V_n`; the integrand coefficients would be `Y_0=0`, `Y_n=V_n` for `n≥1`. `MainK2d.lean:26–57` verifies `V_0=X_Z′` and the embedded pullback identity. `YSeries2.lean:105–158` proves an individual coefficient estimate, and `YSeries3.lean:74–95` proves summability of evaluated vectors. `YSeries4.lean:59–123` proves a genuine formal series and analyticity for bounded scalar multipliers. These are useful proofs.

Refutation attempt: searched every new `Main*`/`YSeries*` export for integral identities, coefficient-norm summability and its `4 C_*` sum bound. There is no integral theorem. `hasDerivAt_Qseries` proves an antiderivative, and `birkK2_field` uses a zero-derivative argument; neither statement identifies a Bochner integral. Also, the pointwise coefficient majorant alone sums to `4/(1−1/8)=32/7` times the cubic scale if applied without the missing zero-term refinement; it is not itself the requested `4` sum estimate. This arithmetic is an audit of the available bound, not a claim that `4` is false. The nonexistent export `summable_norm_lieV` appears only in the `YSeries2` docstring.

The alternate triangular-recursion route is mathematically legitimate for the proved remainder theorem, and its use of symplecticity/invertibility can identify the pullback on the valid ball. It does not make the unexported quantitative/integral conclusions proved. **SURVIVED as a source-node completion gap.** Required repair: export coefficients of the actual subtracted integrand, their operator-norm sum bound, and the exact integral/formal-series/reality characterization; alternatively explicitly narrow the node's approved contract. No new hypothesis may assume those results.

### F3 — major definition-contract limitation: local objects exported on unrestricted carriers

Blueprint `w3-birkhoff.tex:613–619,687–690,780–782` defines the inverse/integrand/remainder/real coordinate change on specified balls. The new definitions accept arbitrary points of the ambient Banach carrier. The sharpest examples are:

- `MainK1.lean:39`: `birkBF w := Ring.inverse (birkAF … w)` with no unit or ball argument. `birkInvData` supplies inverse semantics only under `40 C_F‖w‖²<1`.
- `MainK2a.lean:52–54`: `birkXK2` is a bare `tsum` on **all** `BirkSpace`; absolute convergence and its Hamiltonian-field characterization are proved only on `160 C_F‖w‖²<1`.
- `MainGamma.lean:28`: `birkGammaR` is global, although its source domain is `320 C_F‖x‖²<1` and its meaning is mediated by the locally characterized flow series.

Refutation attempt: traced the globally defined sums, the inverse data, `exists_rho1`, and every analyticity/field theorem. Their ball hypotheses are explicit and prevent invalid use by the inspected theorems; however, none restricts the exported definition's carrier or supplies global convergence/inverse semantics. Mathlib's totalized `tsum`, `fderiv`, and `Ring.inverse` cannot replace the missing public domain. This does **not** assert that divergence or noninvertibility has been exhibited at a particular point. It is the fail-closed public-carrier/default-semantics issue in the applied definition audit. **SURVIVED for literal public-definition fidelity.**

For the affected local source objects: `BODY_MATCH: OK on the source ball`; `PUBLIC_CARRIER: FAIL`; `WELL_DEFINEDNESS: FAIL as an unrestricted source object, proved locally`; `CHARACTERIZATION: FAIL globally, proved locally where cited`; `CHOICE_INDEPENDENCE: N/A` (no arbitrary choice construction); `DEFINITION_VERDICT: FAIL`. Restrict the source-facing API to the valid domain or obtain an explicit extension policy with justified semantics. The local theorems remain meaningful and axiom-clean. Finite-degree coefficient families, block maps, real projections, and the everywhere-defined quartic polynomials do not have this defect.

### Notes

- **N1, explicit real-series interface:** `gamma-real` (i), blueprint lines 784–786, specifies the actual real multilinear coefficients, not merely existence of some real-analytic expansion. `birkGammaR_analyticOnNhd` obtains real analyticity by restriction/composition. No new theorem states `HasFPowerSeriesOnBall` with the displayed real coefficients. The underlying complex flow has its series definition, so this is a missing explicit characterization, not evidence of false real analyticity. Do not cite this export alone as the full coefficient-level clause.
- **N2, handoff inventory:** line 12 says 23 new modules; the delta contains 27 after the four Round-2 additions. There are 133 public theorems and 41 definitions/abbreviations. The largest file has 275 lines. The handoff's 25-declaration axiom sample is expanded to all 174 declarations in this audit.
- **N3, generated root:** the broad protected-path diff including `KAM/Root` is nonempty: precisely 27 generated public imports. The exact brief command excluding `KAM/Root` is empty. The producer's applicable W brief explicitly permits running `scripts/gen_root_imports.py` and committing its output (`w-prover.md:43–45`), and the handoff records regeneration. This is recorded as an authorized producer workflow exception, not a mathematical defect. This auditor did not regenerate or edit a root.

No new suspected false statement in P96-W is asserted. The current weak blueprint estimate is not diagnosed as false merely because Lean proves a weaker estimate. Adopted coefficient/action/sign corrections are consumed through the existing producers; their original-page verification was not repeated. Deviations introduced by this auditor: none.

## Binder, carrier and dependency review

The common representation is weighted `lp` coordinates: a `BirkSpace` value at weight `p+1` is **not** the same physical sequence at weight `p`; `birkEmbed a (p+1) p` supplies the coordinate change. `BirkReal` is definitionally the frozen `WaveSpace` at `(a,p)=(1,1)`. The inclusions and `coeffW` identities are used explicitly; no Euclidean-space substitution occurs. The symplectic sign is `DK(h)=ω(X_K,h)`, giving `(∂_pK,−∂_qK)`.

The table records individual logical binders of the principal interfaces; data/instances are classified separately. Applicable bin totals are per listed interface, with shared binders counted once per interface. RULED and EXCESS counts are zero: findings concern conclusions/domains, not smuggled result assumptions.

| Interface | Binder | Bin | Source / reason |
|---|---|---|---|
| all mass-dependent main exports | `m : ℝ` | TYPING | Mass parameter. |
| same | `hm : 0<m` | STANDING | W3 standing data, blueprint line 22. |
| weighted main exports | `a : ℝ` | TYPING | Weighted-space parameter. |
| same | `p : ℝ` | TYPING | Weighted-space parameter. |
| same | `ha : 0≤a` | STANDING | W3 standing data. |
| same | `hp : 1/2≤p` | STANDING | W3 standing data. |
| remainder bounds/field | `w` | TYPING | Arbitrary point. |
| same | `hw : 160 C_F‖w‖²<1` | SOURCE | Exactly `w∈B_ρ₁`; positive `C_F` is proved. |
| field/gradient identities | `v` / `u` / `h` | TYPING | Arbitrary test direction. |
| conjugacy | `y` | TYPING | Source point represented at higher weight. |
| same | `hy` | SOURCE | Embedded source point lies in `B_ρ₁`. |
| real gamma/gradient | `x` | TYPING | Real weighted point. |
| same | `hx : 320 C_F‖x‖²<1` | SOURCE | Exactly `x∈B^E_r₁`. |
| real surjectivity | `y` | TYPING | Target point. |
| same | `hy : 1280 C_F‖y‖²<1` | SOURCE | Exactly the half-ball. |
| real symplecticity | `ξ` | TYPING | Arbitrary tangent vector. |
| same | `η` | TYPING | Arbitrary tangent vector. |
| real restriction | `U` | TYPING | Domain set; no openness assumption needed for local analyticity. |
| same | `f` | TYPING | Source map. |
| same | `hf` | SOURCE | Analytic source map. |
| same | `hρ` | SOURCE | Equivariance with real structure. |
| scalar real restriction | `P` | TYPING | Scalar source map. |
| same | `hP` | SOURCE | Analytic source scalar. |
| same | `hreal` | SOURCE | Source reality identity. |
| strong transport | `ν` | TYPING | Direction/frequency; no Diophantine premise required. |
| same | `Ψ` | TYPING | Higher-weight-valued torus map. |
| same | `hΨ` | SOURCE | Pointwise source-ball membership. |
| same | `hder` | SOURCE | Directional differentiability and actual normal-form equation. |
| same | `θ` | TYPING | Arbitrary evaluation point. |
| real strong transport | `hρ` | SOURCE | Real torus, conditional clause of source. |
| same | `hapos : 0<a` | SOURCE | Required for integral cubic identification; algebraic coordinate identity exists without it. |
| weak transport | `ν` | TYPING | Frequency direction. |
| same | `Ψ` | TYPING | Base-weight-valued map. |
| same | `D` | TYPING | Explicit directional derivative values. |
| same | `hΨ` | SOURCE | Pointwise ball membership. |
| same | `hder` | SOURCE | Derivative exists into base weight. |
| same | `heq` | SOURCE | Source invariance equation in weight `p−1`, not an assumed transported equation. |
| same | `θ` | TYPING | Evaluation point. |
| real weak transport | `hρ` | SOURCE | Real input, as source conditional clause. |
| same | `hapos` | SOURCE | Integral cubic identification. |
| frozen fderiv strong/weak | `hdiff` | SOURCE | Blueprint full differentiability; needed because `fderiv` is totalized. |
| frozen specializations | `hp : 1/2≤1` | TYPING | Closed arithmetic fact, inhabited by `by norm_num`; not a mathematical restriction. |
| coordinate conclusions | `j : ℕ+` | TYPING | Every physical Dirichlet mode; no finite-mode restriction. |

In the table: TYPING 22, STANDING 3, SOURCE 18, RULED 0, EXCESS 0 (binder-name alternatives in a single row denote separate interfaces, not a bundled logical assumption). Generic multilinear helpers additionally use Banach-space instances, degree/cardinality equalities, symmetry, summability, norm bounds, and recursion inequalities. Those are their explicitly conditional calculus hypotheses, not assumptions of `birkK_isClassA` or transport. In particular `norm_sub_le_quart` assumes a generic class-A input, but `MainK` supplies it from `birkQuart_isClassA`; `seq_bound`'s recursion bound is proved before its use in `norm_lieV_le`.

Expanded `IsBirkClassA`: open domain; rho-invariance; scalar reality; scalar analyticity; Hamiltonian differential identity; field analyticity. All six are conclusions of `birkK_isClassA`. `IsBirkQuartCoef` expands to permutation symmetry, conjugate-negation symmetry, and the coefficient bound; `birkCoefZ_isCoef` proves all three using the coefficient supports. `birkInvData` proves invertibility, not a theorem premise. The conjugacy proof uses the original quadratic form only where defined, cancels via the homological identity, and obtains equality from symplecticity, surjectivity of the derivative, and nondegeneracy. No unbounded linear field on the base space is silently treated as bounded.

Term-level consumer inspection: `MainK2e` consumes `birkV_identity`, the variational equation and symplecticity to prove the field identity. `MainRealWeak` derives the higher-weight lift using `birkXLamInv` and supplies it to `birk_transport_tori_real`. `MainFrozenForm:49–54,118–122` rewrites `coeffW_one_one` and `cubicGrad_eq_waveCubic` to reach frozen clause (4). Lines 92–97 and 138–143 prove differentiability and invoke `frozen_invariance_iff_waveXw`; no invariance conclusion is fed back as a premise.

Independent project import walk: 133 project modules in closure; no provider and no frozen theorem. Nine frozen definition modules are reached: Coeff, CubicGrad, EllWeight, IsClassicalSolution, Lam, ReconU, ReconV, SineMode, WaveSpace. All nine manifest entries are SEALED. No DRAFT_SORRY theorem is imported.

## Verification evidence

The user's D53 wrapper overrides the older generic `nice -n 5` invocation instructions. Every Lean/Lake process started by this audit ran inside:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Invocations were serialized, including the lint ABI subprocess. No heartbeat, recursion-depth or synthesis override was set.

**Lint:** exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 \
  /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpka
```

Exit 0. Complete output:

```text
check_lean_modules: PASS (3688 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

**Axioms:** generated `.lake/abi-scratch/W3-MAIN-audit-probe.lean` by importing the 27 delta modules and issuing `#print axioms KAM.Wave.<name>` once for each of the 174 declarations in the inventory below. Probe SHA256 `3d20697e3d43e57a524956fdd812c765a942a4376e10e469d2fba6aac73474f9`. Exact invocation:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 lake env sh -c \
  'LEAN_PATH="/root/code/KAM-inp-wpka/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/W3-MAIN-audit-probe.lean'
```

Exit 0; 174 axiom output lines, no other diagnostics. Every line has exactly the form

```text
'KAM.Wave.<inventory name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or project axiom. This is independent fresh evidence, broader than the handoff sample.

**Targeted builds:** `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpka KAM.Wave.Birkhoff.MainFrozenForm KAM.Wave.Birkhoff.MainRealId`. The inspected driver holds a compile-gate slot and executes the exact D53 wrapper around one `lake build <Module>` at a time. These two terminal modules cover all 27 implementation modules through their import closures. Both targeted Lake builds completed successfully; the driver process itself returned 1 because its final command is `[ $rc -ne 0 ] && { ...; exit $rc; }`, whose false test is the script's final status after a successful last build. Complete success markers (deprecation warnings omitted):

```text
[w_build] slot 1: KAM.Wave.Birkhoff.MainFrozenForm (23:05:59)
Build completed successfully (3412 jobs).
[w_build] slot 1: KAM.Wave.Birkhoff.MainRealId (23:06:03)
Build completed successfully (3411 jobs).
```

Thus: each `lake build` exit 0; `w_build.sh` aggregate exit 1 due to the observed driver return-status defect. No `FAILED`, error or kill diagnostic. This external script was not edited. Existing deprecation/unused-argument warnings are nonblocking. The Lake job counts include reused dependency jobs, not a clean library rebuild.

**Kernel replay and short names:** the user states the launcher already ran these. The launcher's output, exit status and exact command are explicitly unavailable in this pane. No rerun was needed to establish the source-contract findings, and no invented exit code is recorded. Kernel replay/name-check status in this report is **launcher-attested, not independently observed**. Compilation/axiom inspection does not replace that distinction.

**Static checks:** `git diff --check inp...HEAD`: exit 0, empty output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output. The separately inspected generated-root diff has only the 27 new imports (N3). Lint confirms module headers, proof-escape rules, width and size; largest new file is `MainK1.lean`, 275 physical lines. No source repair was made.

## Complete declaration and definition inventory

Every row below was axiom-checked with exactly the allowed three axioms. The theorem verdict is for its actual type; PASS does not claim that a helper alone closes its whole blueprint node. Definition rows classify literal constructions separately from their local semantic qualifications.

| Node | Declaration (file:line) | Verdict | Reason / definition classification |
|---|---|---|---|
| `Yseries` | `blockEquiv` (BlockMap.lean:38) | PASS | Literal finite block-index equivalence; no choice or default. |
| `Yseries` | `blockMap` (BlockMap.lean:43) | PASS | Literal multilinear block composition; arbitrary arities, with exact size equality. |
| `Yseries` | `blockMap_apply` (BlockMap.lean:55) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `blockMap_const` (BlockMap.lean:60) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_blockMap_le` (BlockMap.lean:65) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `symmMulti` (BlockMap.lean:89) | PASS | Literal finite permutation average; factorial is nonzero. |
| `Yseries` | `symmMulti_apply` (BlockMap.lean:94) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `symmMulti_perm` (BlockMap.lean:101) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `symmMulti_const` (BlockMap.lean:108) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_symmMulti_le` (BlockMap.lean:116) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `hasFDerivAt_diag_symm` (BlockMap.lean:135) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `fderiv_comp_birkGamma` (MainConj.lean:28) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birk_conjugacy` (MainConj.lean:44) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport, frozen form` | `birk_transport_tori_frozen_coord` (MainFrozenForm.lean:32) | PASS | Exact frozen coordinatewise or differentiable weak-space invariance slice; no seal claim. |
| `transport, frozen form` | `birk_lt_forty_of_lt_160` (MainFrozenForm.lean:57) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport, frozen form` | `birkGamma_differentiableAt_one` (MainFrozenForm.lean:64) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport, frozen form` | `birk_transport_tori_frozen` (MainFrozenForm.lean:73) | PASS | Exact frozen coordinatewise or differentiable weak-space invariance slice; no seal claim. |
| `transport, frozen form` | `birk_transport_tori_weak_frozen_coord` (MainFrozenForm.lean:101) | PASS | Exact frozen coordinatewise or differentiable weak-space invariance slice; no seal claim. |
| `transport, frozen form` | `birk_transport_tori_weak_frozen` (MainFrozenForm.lean:125) | PASS | Exact frozen coordinatewise or differentiable weak-space invariance slice; no seal claim. |
| `gamma-real` | `birkGammaR` (MainGamma.lean:28) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `gamma-real` | `norm_birkZR_sq_le` (MainGamma.lean:32) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkZR_dom` (MainGamma.lean:38) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaR_analyticOnNhd` (MainGamma.lean:46) | PASS WITH NOTES | Real analyticity; explicit real coefficient-series characterization not exported (N1). |
| `gamma-real` | `birkGamma_one_fixed` (MainGamma.lean:66) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaR_sub` (MainGamma.lean:79) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaR_inv` (MainGamma.lean:122) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaR_injOn` (MainGamma.lean:133) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaR_surj` (MainGamma.lean:141) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaD_rho` (MainGammaSympl.lean:27) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkOmegaR` (MainGammaSympl.lean:58) | PASS | Literal weighted real symplectic sum under standing nonnegative weights; no unrestricted off-source bilinear claim certified. |
| `gamma-real` | `birkOmega_birkZR` (MainGammaSympl.lean:62) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaR_hasFDerivAt` (MainGammaSympl.lean:68) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `gamma-real` | `birkGammaR_symplectic` (MainGammaSympl.lean:83) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkLambda_rho` (MainK.lean:30) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_sub_le_quart` (MainK.lean:42) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkK1` (MainK.lean:71) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkK2` (MainK.lean:75) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkK` (MainK.lean:80) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkK_eq` (MainK.lean:86) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkHamG_isClassA` (MainK.lean:96) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkHamZ_isClassA` (MainK.lean:102) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkHamGX_le` (MainK.lean:108) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkHamZX_le` (MainK.lean:114) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_quart_comp_sub_le` (MainK.lean:121) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkK1_le` (MainK.lean:153) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `hasDerivAt_birkLambda_gamma` (MainK.lean:161) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkK2_le` (MainK.lean:179) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkK_le` (MainK.lean:211) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkK_analyticOnNhd` (MainK.lean:221) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkK_rho` (MainK.lean:238) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkPsi` (MainK1.lean:28) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkXi` (MainK1.lean:32) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkAF` (MainK1.lean:35) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkBF` (MainK1.lean:39) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkPsi_embed` (MainK1.lean:44) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkPsi_analyticAt` (MainK1.lean:53) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXi_embed` (MainK1.lean:63) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkInvData` (MainK1.lean:90) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXK1` (MainK1.lean:145) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkK1_field` (MainK1.lean:150) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkXK1_le` (MainK1.lean:196) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXK1_analyticAt` (MainK1.lean:242) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkNz` (MainK2a.lean:28) | PASS | Literal cubic map 4∇z; operator bound proved. |
| `main` | `birkNz_const` (MainK2a.lean:32) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkNz_le` (MainK2a.lean:38) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkVn` (MainK2a.lean:47) | PASS | Literal specialization of recursively constructed coefficients. |
| `main` | `birkXK2` (MainK2a.lean:52) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `exists_rho1` (MainK2a.lean:60) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXK2_analyticAt` (MainK2a.lean:75) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `fderiv_birkLambda_eq` (MainK2b.lean:27) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birk_DLam_homological_diff` (MainK2b.lean:34) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `hasDerivAt_dLambda_gamma` (MainK2c.lean:25) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkVn_zero_const` (MainK2d.lean:26) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkV_identity` (MainK2d.lean:42) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `uqF` (MainK2d.lean:64) | PASS | Literal antiderivative coefficients: zero constant term, V_n/(n+1). |
| `main` | `summable_birkVn` (MainK2d.lean:69) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `hasDerivAt_Qseries` (MainK2d.lean:80) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkK2_field` (MainK2e.lean:28) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkY_le` (MainK2f.lean:26) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXK2_eq_Q` (MainK2f.lean:105) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkXK2_le` (MainK2f.lean:130) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXK` (MainK3.lean:27) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `main` | `birkK_field` (MainK3.lean:32) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `norm_birkXK_le` (MainK3.lean:60) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXK_analyticAt` (MainK3.lean:69) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkK_isClassA` (MainK3.lean:76) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkCoefZ` (MainQuart.lean:28) | PASS | Literal difference of quartic coefficient masks; coefficient conditions proved. |
| `main` | `birkCoefZ_isCoef` (MainQuart.lean:30) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkHamG` (MainQuart.lean:52) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamGX` (MainQuart.lean:54) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamBar` (MainQuart.lean:56) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamBarX` (MainQuart.lean:58) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamNor` (MainQuart.lean:60) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamNorX` (MainQuart.lean:62) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamTan` (MainQuart.lean:64) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamZ` (MainQuart.lean:66) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamZX` (MainQuart.lean:68) | PASS | Literal existing quartic polynomial/field specialization; global construction justified by coefficient bound. |
| `main` | `birkHamZ_eq` (MainQuart.lean:71) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkHamG_eq` (MainQuart.lean:84) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birk_homological_Z` (MainQuart.lean:90) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `BirkReal` (MainReal.lean:29) | PASS | Literal product of two real lp spaces; max norm, frozen WaveSpace representation. |
| `real-restrict` | `birkZR` (MainReal.lean:32) | PASS | Literal continuous real-linear complex-coordinate inclusion. |
| `real-restrict` | `birkPi` (MainReal.lean:35) | PASS | Literal real projection of the complex-coordinate inverse; identities prove real-form semantics. |
| `real-restrict` | `birkZR_apply` (MainReal.lean:40) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `norm_birkReal` (MainReal.lean:42) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `norm_birkZR_le` (MainReal.lean:45) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `birkPi_birkZR` (MainReal.lean:50) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `norm_birkPi_le` (MainReal.lean:56) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `birkZR_birkPi` (MainReal.lean:64) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `birkRho_birkZR` (MainReal.lean:69) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `real-restrict` | `real_restrict` (MainReal.lean:72) | PASS | Full real restriction identity plus analyticity; stronger domain assumptions than needed omitted. |
| `real-restrict` | `real_restrict_fun` (MainReal.lean:86) | PASS | Full real restriction identity plus analyticity; stronger domain assumptions than needed omitted. |
| `main / gamma-real` | `birkK_real_fderiv` (MainRealId.lean:32) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main / gamma-real` | `coeffW_birkPi_embed_fst` (MainRealId.lean:57) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main / gamma-real` | `coeffW_birkPi_embed_snd` (MainRealId.lean:62) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main / gamma-real` | `birkK_real_gradient` (MainRealId.lean:72) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main / gamma-real` | `birkActionR` (MainRealId.lean:83) | PASS | Literal physical modal action (q²+p²)/2. |
| `main / gamma-real` | `birkGbarR` (MainRealId.lean:87) | PASS | Literal finite tangential sum plus normal action sum on standing weights; real quartic identity proved. |
| `main / gamma-real` | `birkAction_birkZR` (MainRealId.lean:93) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main / gamma-real` | `birkHamBar_birkZR` (MainRealId.lean:101) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main / gamma-real` | `birkLambda_birkZR` (MainRealId.lean:113) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main / gamma-real` | `birkH_gammaR` (MainRealId.lean:124) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkK_real` (MainRealK.lean:27) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `main` | `birkXK_real` (MainRealK.lean:40) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori` | `birkTransportQP` (MainRealTori.lean:32) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `transport-tori` | `coeffW_birkPi_fst` (MainRealTori.lean:37) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori` | `coeffW_birkPi_snd` (MainRealTori.lean:46) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori` | `birkTransport_coeff_aux` (MainRealTori.lean:59) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori` | `waveCubic_coeffW_eq_waveTriSeq` (MainRealTori.lean:128) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori` | `birk_transport_tori_real` (MainRealTori.lean:139) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `birk_transport_tori_weak_real` (MainRealWeak.lean:29) | FAIL (node fidelity) | Actual weaker bound is valid; source cubic constant is C_*, exported constant 2C_* (F1). |
| `transport-tori` | `birk_transport_tori` (MainTori.lean:27) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `birkXLamInv` (MainWeak.lean:27) | PASS | Literal bounded reciprocal diagonal; positive mass proves denominators nonzero globally. |
| `transport-tori-weak` | `birkXLamInv_apply` (MainWeak.lean:36) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `birkXLam_mu_ne` (MainWeak.lean:40) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `birkXLam_birkXLamInv` (MainWeak.lean:48) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `birkXLamInv_birkXLam` (MainWeak.lean:53) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `norm_birkXLamInv_le` (MainWeak.lean:58) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `embedRatio_succ` (MainWeak.lean:66) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `birkEmbed_birkXLamInv` (MainWeak.lean:74) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `transport-tori-weak` | `birkRestField` (MainWeak.lean:92) | FAIL (carrier) | Literal local construction, globally exported: F3; local characterization retained. |
| `transport-tori-weak` | `norm_birkRestField_le` (MainWeak.lean:100) | FAIL (node fidelity) | Actual weaker bound is valid; source cubic constant is C_*, exported constant 2C_* (F1). |
| `transport-tori-weak` | `birk_transport_tori_weak` (MainWeak.lean:120) | FAIL (node fidelity) | Actual weaker bound is valid; source cubic constant is C_*, exported constant 2C_* (F1). |
| `Yseries` | `slotMap` (YSeries.lean:35) | PASS | Literal insertion/uncurrying of multilinear maps. |
| `Yseries` | `slotMap_const` (YSeries.lean:41) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_slotMap_le` (YSeries.lean:45) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `lieSymF` (YSeries.lean:60) | PASS | Literal finite symmetrization of smoothing coefficients. |
| `Yseries` | `lieNsum` (YSeries.lean:64) | PASS | Literal finite antidiagonal coefficient composition. |
| `Yseries` | `lieV` (YSeries.lean:69) | PASS | Literal well-founded triangular recursion; no assumed response witness. |
| `Yseries` | `lieV_eq` (YSeries.lean:78) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `lieV_eval` (YSeries.lean:90) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `comp_lieBlockT` (YSeries.lean:105) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `comp_lieMultiF` (YSeries.lean:117) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `comp_lieSymF` (YSeries.lean:129) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `lieDer_eq_symm` (YSeries.lean:138) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `map_lieSymF_cons` (YSeries.lean:152) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_lieT_le'` (YSeries2.lean:32) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_lieBlockT_le` (YSeries2.lean:42) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_lieNsum_le` (YSeries2.lean:53) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_lieV_term_le` (YSeries2.lean:80) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_lieV_le` (YSeries2.lean:105) | PASS WITH NOTES | Valid stated series helper; full quantitative/integral Yseries node remains open (F2). |
| `Yseries` | `hasSum_bil_cauchy` (YSeries3.lean:26) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_lieV_apply_le` (YSeries3.lean:66) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `summable_lieV` (YSeries3.lean:74) | PASS WITH NOTES | Valid stated series helper; full quantitative/integral Yseries node remains open (F2). |
| `Yseries` | `clm_real_smul` (YSeries3.lean:97) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `lieV_identity` (YSeries3.lean:103) | PASS WITH NOTES | Valid stated series helper; full quantitative/integral Yseries node remains open (F2). |
| `Yseries` | `lieSeriesV` (YSeries4.lean:32) | PASS | Literal degree placement; zero coefficients in exactly the unused degrees, as source requires. |
| `Yseries` | `lieSeriesV_const` (YSeries4.lean:39) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `norm_lieSeriesV_le` (YSeries4.lean:48) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `hasFPowerSeriesOnBall_lieV` (YSeries4.lean:59) | PASS WITH NOTES | Valid stated series helper; full quantitative/integral Yseries node remains open (F2). |
| `Yseries` | `analyticAt_lieV` (YSeries4.lean:116) | PASS WITH NOTES | Valid stated series helper; full quantitative/integral Yseries node remains open (F2). |
| `Yseries` | `summable_odd_geom` (YSeriesNum.lean:25) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `odd_geom_partial_le` (YSeriesNum.lean:35) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |
| `Yseries` | `seq_bound` (YSeriesNum.lean:49) | PASS | Matches its actual calculus/normal-form helper type; no excess premise. |

## Closeout

The three former Round-2 missing interfaces are present: frozen clause (4), real differential/action identities, and real `(Q,P)` transport. They are not the remaining blockers. Retain F1's exact unpaid cubic estimate and F2's missing coefficient-sum/integral characterization; do not mark the full six-node package complete. F3 separately prevents unrestricted source-definition approval. No frozen theorem is seal-ready on this report's authority.

Checks completed: entire three-dot delta read; principal statements and source binders compared; all 41 new definitions classified; dependency/consumer paths inspected; all 174 declarations freshly axiom-checked; prescribed slim lint passed; both targeted Lake builds succeeded (driver exit-status defect recorded); launcher-only replay/name evidence identified honestly; no implementation repair. The only deliverable is this report.
