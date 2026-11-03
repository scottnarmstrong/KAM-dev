# Handoff B5-CHART (worktree /root/code/KAM-inp-b5chart, branch inp-b5chart)

## Files (all new, 753 lines total, each < 200)
`KAM/EffectiveStability/TorusChart.lean` (facade + corollary + smoke test),
`TorusChart/{Inverse,Matrix,Algebra,Map,Deriv,Symplectic}.lean`. Import order: Inverse, Matrix, Algebra,
Map, Deriv, Symplectic, TorusChart. No file outside `KAM/EffectiveStability/TorusChart*` touched.

## Statements (final signatures; namespace KAM.EffectiveStability, `x = torusChartX u = id + u`)
Data (hypotheses bundled, no conclusion-shaped premise):
```
structure TorusBaseData (u) (κ : ℝ) : Prop  -- baseSmooth : ContDiff ℝ 3 u, baseContract : κ < 1,
                                            -- baseBound : ∀ φ, ‖fderiv ℝ u φ‖ ≤ κ
def TorusPeriodic u := ∀ φ (k : Fin n → ℤ), u (φ + fun i => (k i : ℝ)) = u φ
structure TorusChartData (u v) (κ : ℝ) : Prop extends TorusBaseData u κ where
  uPeriodic : TorusPeriodic u
  vPeriodic : ∀ φ k, v (φ + fun i => (k i : ℝ)) = v φ
  vSmooth : ContDiff ℝ 2 v
  lagrangian : ∀ φ i j, ∑ l, (fderiv ℝ (torusChartX u) φ (Pi.single i 1)) l * (fderiv ℝ v φ (Pi.single j 1)) l
                      = ∑ l, (fderiv ℝ (torusChartX u) φ (Pi.single j 1)) l * (fderiv ℝ v φ (Pi.single i 1)) l
```
Item 1 (Inverse.lean):
```
def torusChartX u φ := φ + u φ ;  def torusChartXinv u y := Function.invFun (torusChartX u) y
theorem torusChartX_injective / torusChartX_surjective (h : TorusBaseData u κ)
theorem torusChartXinv_left  (h) φ : torusChartXinv u (torusChartX u φ) = φ
theorem torusChartXinv_right (h) y : torusChartX u (torusChartXinv u y) = y
theorem torusChartXinv_lipschitz (h) y z : (1 - κ) * ‖xinv y - xinv z‖ ≤ ‖y - z‖
theorem torusChartXinv_continuous (h) : Continuous (torusChartXinv u)
theorem torusChartXinv_contDiff (h : TorusBaseData u κ) : ContDiff ℝ 3 (torusChartXinv u)
theorem torusChartXinv_shift (h) (hp : TorusPeriodic u) y k : xinv (y + ↑k) = xinv y + ↑k
def torusChartDxEquiv (h) φ : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)   -- coe = fderiv ℝ (torusChartX u) φ
theorem torusChartDxEquiv_symm_norm (h) φ : ‖((torusChartDxEquiv h φ).symm : _ →L[ℝ] _)‖ ≤ 1 / (1 - κ)
```
Items 2–3 (Map.lean):
```
def torusChartMap u v w := (torusChartX u w.1, v w.1 + torusChartInvT u w.1 *ᵥ w.2)
def torusChartInvMap u v q := (torusChartXinv u q.1,
    (torusChartJac u (torusChartXinv u q.1))ᵀ *ᵥ (q.2 - v (torusChartXinv u q.1)))
-- torusChartJac u φ i j = fderiv ℝ (torusChartX u) φ (Pi.single j 1) i ; torusChartInvT u φ = ((torusChartJac u φ)ᵀ)⁻¹
theorem torusChartMap_contDiff (h : TorusChartData u v κ) : ContDiff ℝ 2 (torusChartMap u v)
theorem torusChartMap_shift (h) w k : torusChartMap u v (w + KAM.ODE.angleShift k) = torusChartMap u v w + KAM.ODE.angleShift k
theorem torusChartMap_zero φ : torusChartMap u v (φ, 0) = (torusChartX u φ, v φ)
theorem torusChartInvMap_map (h) w : torusChartInvMap u v (torusChartMap u v w) = w
theorem torusChartMap_invMap (h) q : torusChartMap u v (torusChartInvMap u v q) = q
```
Item 4 (Symplectic.lean):
```
theorem torusChartMap_symplectic (h : TorusChartData u v κ) (w a b : (Fin n → ℝ) × (Fin n → ℝ)) :
  KAM.symplecticForm (fderiv ℝ (torusChartMap u v) w a) (fderiv ℝ (torusChartMap u v) w b) = KAM.symplecticForm a b
```
Item 5 (TorusChart.lean):
```
theorem torusChart_isCanonical (h : TorusChartData u v κ) :
  IsCanonicalChart (torusChartMap u v) (torusChartInvMap u v) univ univ
theorem torusChartData_zero : TorusChartData (n := n) (fun _ => 0) (fun _ => 0) 0
theorem torusChartMap_zero_data w : torusChartMap (fun _ => 0) (fun _ => (0 : Fin n → ℝ)) w = w
```

## Deviations from the request (none are signature changes that make it false)
* `v` needs only `ContDiff ℝ 2` (brief said 3); `u` is `C³` (needed for `Ψ ∈ C²`). Weaker premises than requested.
* `κ`, `u`, `v` are explicit parameters (`torusChartMap u v`), `κ` appears only in the hypotheses.
* `xinv` is `Function.invFun` (no hypothesis in the definition); its properties need `TorusBaseData`.

## Approach
`x` bijective via `ContractingWith` fixed point of `φ ↦ y − u φ`; `Dx` equivalence by injectivity
(`‖Dx y‖ ≥ (1−κ)‖y‖`) in finite dimension; `C³` inverse by `ContDiffAt.to_localInverse` + `localInverse_unique`.
`(Dx)^{-T}` is the Mathlib matrix inverse of the transposed Jacobian, entries smooth through Cramer's rule
(`det` polynomial, `adjugate`). Symplecticity: component formula for `DΨ` (`HasFDerivAt` product/sum rule),
then the pure matrix identity `torusChart_symplectic_algebra` using `BᵀA = 1`, `dBᵀA + BᵀdA = 0`
(differentiated identity), symmetry of `D²x` (`IsSymmSndFDerivAt`) and Lagrangian symmetry `(Dx a)·(Dv b) = (Dx b)·(Dv a)`.

## Checks (all run in /root/code/KAM-inp-b5chart)
* `b_build.sh` each module in order (Inverse, Matrix, Algebra, Map, Deriv, Symplectic, TorusChart): all "Build completed successfully".
* `b_lean.sh` on each of the 7 files: no output (no warnings).
* `sh scripts/lint_sources.sh`: OK / FROZEN-ANCHOR GUARD OK / ABI HASHES OK.
* line-length check (>100): `[]`.
* `main_shortname_check.py` on all 7 modules: "short-name check OK", rc=0.
* no `sorry`/`set_option` in the files.
* `#print axioms` of torusChartMap_symplectic, torusChart_isCanonical, torusChartMap_contDiff, torusChartXinv_contDiff,
  torusChartDxEquiv_symm_norm, torusChartMap_shift, torusChartMap_invMap, torusChartMap_zero_data:
  all `[propext, Classical.choice, Quot.sound]`.

## Design signals / errata
None (no heartbeat issues; every file elaborates in a few seconds). No source defects found.
Note for B5-NF/ROUTE: `torusChartDxEquiv`/`torusChartJac` are the objects to relate `∂_p H(K) = Dx ω'` to; the
Lagrangian premise is stated with `fderiv ℝ (torusChartX u)`, i.e. `x = id + u` unfolded by `torusChartX`.

## AUDIT FOCUS (kam-b1)
Track B, program B5 (overnight D71; nothing frozen; OD-B13; design docs/tracks/B/B5-DESIGN.md item 2). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B5-CHART.md and brief-B1-common.md; plan §3.4 (Chart) (/root/code/KAM/docs/explorations/
program-b-plan.md lines 426-457). Consumer: B1-T torus_confinement chart premises and ChartChain.IsCanonicalChart. Scope: prover
commit e1c5bb40b (seven TorusChart modules) and merges. Check: (1) TorusBaseData/TorusChartData bundle only source premises
(regularity, κ < 1 projection bound, periodicity, the Lagrangian condition Dxᵀ Dv symmetric) — no chart conclusion is
assumed; (2) the global inverse of x = id + u (contraction / invFun) and its C³ regularity, lattice equivariance;
(3) the explicit Ψinv is a two-sided inverse for ALL points; (4) TRACE the symplecticity computation: it must use the
Lagrangian condition essentially (it is false without it); (5) C² of Ψ from C³ u and C² v; (6) hygiene (AGENTS rules 3, 4,
7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
