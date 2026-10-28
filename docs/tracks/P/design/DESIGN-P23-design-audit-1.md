# DESIGN-P23 independent design audit 1

Overall verdict: **FAIL** (one major source-contract omission, F1). The 33 submitted theorem signatures elaborate, and no false numerical estimate or changed frozen object was found. The failure is that the oscillator step exports fewer conclusions than its assigned blueprint/packet contract; signature elaboration does not detect that omission.

Audit scope: `docs/tracks/P/design/P23-LEAN-DESIGN.md`, commit `6d3620a`, compared with `inp...HEAD`; shared signatures SHA256 `9787bb3880222405f9227793a297a9abbce768731d8783dbe113c820d92ace14`. Read AGENTS.md, PLAN, DECISIONS, the audit brief and designer handoff. Compared the three Part 2/3 blueprint files directly and the live shared graph packets `P-p1p2.nodes.md` and `P-p3.nodes.md`. No production, frozen, manifest, blueprint, graph or original signature file was edited.

## Findings

### F1 — MAJOR — `osc_iter` drops the inherited oscillator step contract

Locators: shared signatures L394–426 (Appendix A of the design); `blueprint-P/parts/p2-averaging.tex` L183–195, `bpP:p2:osc-iter`; live `docs/graph/P/packets/P-p1p2.nodes.md` L1914–1947. The packet explicitly requires **“All conclusions of N iterative ... including ... periodic ... reality under the inherited realness premises”**. The inherited theorem is `blueprint-N/parts/p6-normal-form.tex` L93–105, clauses (a)–(e).

The signature concludes holomorphy, injectivity, symplecticity, a remainder bound and component displacements only on the twice-shrunk domain. It omits fast-lattice equivariance and conditional reality of the generator, normal form, remainder and map. It also omits the larger three-halves-loss holomorphy/maps-to and displacement domains, the inverse-flow law, gauge derivative estimate, and bound/class of the normal-form increment. The Hamiltonian identity is recoverable from its explicit definition of `fp`; the other missing assertions are not projections of the returned conjunction.

Consumer: P23-15 `osc_averaging`, signatures L310–332, needs a real map with periodic defect, and real `g,fs`. Part 2 L219 inherits reality/periodicity through every oscillator step. P23-13 is the package assigned the anisotropic transfer, but its only theorem export `osc_iter` does not provide these inherited properties. The ordinary N theorem cannot be instantiated directly to repair this: it Fourier-expands all angles and uses isotropic action/angle domains; oscillator variables here are bounded dynamical Cartesian coordinates. The design itself correctly rejects that instantiation.

This finding does not assert a counterexample to the smaller conjunction that was written. It fails the brief's fidelity/consumer gate: proving exactly that conjunction does not deliver the assigned step contract. Fix by restoring the inherited conclusions on the same explicit map, or supplying separately named, audited companion signatures from P23-13 before releasing the finite oscillator averaging package. Do not add reality/periodicity as unconditional input assumptions about the output map.

A complete replacement signature follows. It retains all original premises and the quantitative remainder expression; reality remains a conditional conclusion under source realness premises. This proposed strengthening is a repair target, not a proved theorem or an independently elaborated replacement.

```lean
theorem osc_iter {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} {gj : Fin J → CHam (n + m)}
    {rj rpj rqj Sj Mj : Fin J → ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hg : ∀ j, oscClass D (rj j) (rpj j) (rqj j) (Sj j) (gj j) ∧
      oscBound D (rj j) (rpj j) (rqj j) (Sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ rp ≤ rpj j ∧ rq ≤ rqj j ∧ S ≤ Sj j) :
    let Ψ := oscStepMap D r rp rq S ρ ρp ρq σ K h f
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + coeff (oscFunction f) (oscPack z).2 0
    let fp := fun z => h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) -
      h (firstBlock (b := m) z.2) - gp z
    let d := min (ρ * σ) (ρp * ρq)
    let Rsum := ∑ j, max (max (ρ / (rj j - r + ρ)) (σ / (Sj j - S + σ)))
      (max (ρp / (rpj j - rp + ρp)) (ρq / (rqj j - rq + ρq))) * Mj j
    let φ := oscGen K h f
    let O := oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
    let U := oscDom D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    let u := δ / (2 * π * α * d)
    let V := oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    oscClass D r rp rq S φ ∧
    oscBound D r rp rq S φ (δ / (2 * π * α)) ∧
    DifferentiableOn ℂ Ψ U ∧ MapsTo Ψ U O ∧ Set.InjOn Ψ V ∧
    (∀ z ∈ U, ∀ k : Fin n → ℤ,
      Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) =
        Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
    (∀ z ∈ V, flow (KAM.hamiltonianVectorFieldℂ φ) O (-1) (Ψ z) = z) ∧
    oscClass D r rp rq S gp ∧
    oscBound D r rp rq S (fun z => gp z - g z) δ ∧
    (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) =
      h (firstBlock (b := m) z.2) + gp z + fp z) ∧
    (∀ z ∈ U, oscGauge ρ ρp ρq σ (Ψ z - z) ≤ u) ∧
    (∀ z ∈ V, ∀ v,
      oscGauge ρ ρp ρq σ (fderiv ℂ Ψ z v - v) ≤
        2 * u * oscGauge ρ ρp ρq σ v) ∧
    (∀ z ∈ U, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp
      ((1 - 2 * exp 1 * (1 + (m : ℝ)) * δ / (2 * π * α * d))⁻¹ *
        (2 * (1 + (m : ℝ)) / (2 * π * α * d) * (Rsum + δ) + exp (-(2 * π * K * σ))) * δ) ∧
    (∀ z ∈ U,
      ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρ) ∧
      ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ δ / (exp 1 * (2 * π * α) * σ) ∧
      ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρp) ∧
      ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ δ / (2 * π * α * ρq)) ∧
    (RealOn (oscDom D r rp rq S) (fun z => h (firstBlock (b := m) z.2)) →
      RealOn (oscDom D r rp rq S) g → RealOn (oscDom D r rp rq S) f →
      RealOn (oscDom D r rp rq S) φ ∧ RealOn (oscDom D r rp rq S) gp ∧
      RealOn V fp ∧
      ∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ U →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) := sorry
```

### N1 — MINOR — Keep the N wrappers identified as selected views

`direct` L106–113 and `direct_step` L211–240 expose selected conclusions of N's fuller homological and iterative interfaces. Unlike F1, the full non-oscillator results are explicitly retained as upstream dependencies, with exact names in the reuse table: `homological_direct`, `iterative_direct_a`–`_e`. The proposed substitution `p_N=2`, `alpha_N=2α/q` preserves both the effective divisor and every `q/α` coefficient, including `q=1`. Missing wrapper projections can therefore be obtained from that same upstream theorem and same explicit generator/map. Keep those upstream calls explicit in prover briefs; do not advertise the shorter wrappers themselves as the entire N contract. In particular, `nfb` needs integer translations, and N `_a` supplies them for this exact flow.

### N2 — MINOR — The private limit interfaces remain to be audited

The 131-node table is complete, with no duplicate or missing scoped node. Several limit/measure statements are local obligations of `two_scale_kam`, not among the 33 theorem commands. The shared-witness contract describes the right estimates and explicitly forbids conclusion-shaped source assumptions, but does not yet supply the private conditional helper signatures for P23-17–21. Follow its stated audit requirement when those signatures are written. A node-table row or the public existential theorem is not an implementation receipt for those private package interfaces.

### N3 — MINOR — Preserve validation and source-provenance limits

The signature test passes; full worktree source lint does not (see checks). No new theorem is proved, no provider is sealed and `sorryAx` remains. The carried CP10 errata are blueprint reports, not fresh PDF verifications in this audit. The known blueprint corrections are correctly disclosed: target-width denominator `S₀-S+σ`; nonincreasing `Ehat` after the stated normalization at fixed `E,L`; large-domain averaging map with restricted assertions; a general real conjugation bridge; and a real derivative-limit bridge. No further pinned-source defect is alleged here.

## Per-signature verdicts

Names are in `KAM.Planetary` unless indicated. PASS means the submitted signature is a faithful applicable target or an explicitly identified reusable view; it does not mean the proof exists. Auxiliary bridge labels name the source obligation they implement.

| Lean theorem (signature lines) | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `block_bridge` (79) | `bpP:p2:conv#data` | PASS | Definitionally the frozen fast/slow restrictions. |
| `conv_data` (82) | `bpP:p2:conv#data` | PASS | Exact frozen action tube; coefficient/geometric strip dictionary. |
| `direct` (106) | `bpP:p2:direct`, N `bpN:p6:homological` | PASS | Correct selected solve/norm view; complete N interface retained (N1). |
| `split` (128) | `bpP:p2:split` | PASS | Fast-mode support and both divisors preserved; three-halves-loss domain. Full generator bound is also `direct`. |
| `nfb` (162) | `bpP:p2:nfb` | PASS | Same joint map/functions, reality, lattice, weighted remainder and 3/9 constants. |
| `avg` (187) | `bpP:p2:avg`, `bpP:p3:avg` | PASS | Explicit width conversion; strict `64e` hypothesis implies the bundled `128` bound. |
| `direct_step` (211) | `bpP:p2:direct`, N `bpN:p6:iterative` | PASS | Same explicit generator, flow and remainder; correct denominator and weights; full N projections retained (N1). |
| `s_osc_data` (271) | `bpP:p2:s-osc#data` | PASS | Flatten/unflatten in frozen coordinate order. |
| `osc_bracket` (273) | `bpP:p2:osc-bracket` | PASS | Correct four-radius losses and factor `m`; fixed-parameter norm semantics. |
| `ob_field` (286) | `stepP:p2:ob-field` | PASS | Correct gauge and minimum loss product. |
| `osc_averaging` (310) | `bpP:p2:osc-averaging` | PASS | Full intended finite-averaging statement; its package dependency is blocked by F1. |
| `averaged_remainder` (336) | `bpP:p2:averaged-remainder` | PASS | `μP`, exact logarithmic cutoff, separate correction and `με^5` tail. |
| `ob_der` (368) | `stepP:p2:ob-der` | PASS | Correct target angular width; all four Cauchy losses positive in application. |
| `osc_iter` (394) | `bpP:p2:osc-iter` | **FAIL** | Missing inherited conclusions and larger domains, F1. |
| `rem_norm` (511) | `bpP:p3:rem-norm` | PASS | Corrects documented blueprint sign; `initialL` unchanged, radius increases, error decreases. |
| `period_dictionary` (518) | `bpP:p3:period-dictionary` | PASS | `x,K,rhoHat,eHat` invariant under the displayed scalar changes. |
| `period_dictionary_field` (534) | `stepP:p3:pd-dyn` | PASS | Conformal pure-angle chart and Hamiltonian division match frozen field. |
| `use5` (546) | `bpP:p2:use5` | PASS | Symplectic reciprocal action scaling; oscillators unchanged. |
| `use5_constants` (556) | `bpP:p2:use5` | PASS | Scalar identities and smallness equivalence survive scaling. |
| `period_dictionary_coeff` (568) | `stepP:p3:pd-subst` | PASS | Coefficients and finite norm bound divided by `2π`. |
| `rem_norm_blocks` (575) | `bpP:p3:rem-norm` | PASS | Row restrictions controlled by the CLM operator norm. |
| `ext_ift` (580) | `bpP:p3:ext-ift` | PASS | Actual inverse with image openness, maps-to and derivative inverse law. |
| `ext_neumann` (588) | `bpP:p3:ext-neumann` | PASS | Actual equivalence, forward identity and inverse norm at most 2. |
| `ball` (594) | `bpP:p3:ball` | PASS | Positive radius/bound made explicit; image-ball and inverse estimate on correct carriers. |
| `lip_sup` (606) | `bpP:p3:lip-sup` | PASS | Arbitrary base, frozen tube, `4NA/r`; dimension zero is harmless. |
| `step` (614) | `bpP:p3:step` | PASS | Source premises only, common inverse witness, domain repair, all block and quadratic constants. |
| `iterative` (668) | `bpP:p3:iterative` | PASS | Common existential sequences; correct composition order and geometric/error recurrences. |
| `sums` (720) | `bpP:p3:sums` | PASS | Abstract recurrence lemma; nonnegative sequences and weighted geometric domination. |
| `fourier_compact` (734) | `bpP:p3:fourier-compact` | PASS | Common holomorphic strip, bounded periodic sequence; all Frechet derivative orders on every inner closed strip. |
| `real_symplectic_conjugation` (751) | `stepP:p3:inv-conj` | PASS | Frozen real field; open-domain holomorphic real symplectic map; no assumed conjugation identity. |
| `real_curve_limit` (763) | `stepP:p3:inv-lim` | PASS | Real locally uniform function/derivative convergence gives `HasDerivAt` at every time. |
| `cover` (770) | `bpP:p3:cover` | PASS | Actual ambient bijection, two-sided metric bound and inverse displacement; empty base/zero eta allowed. |
| `two_scale_kam` (782) | `bpP:p3:two-scale-kam` | PASS | Full family, same witnesses, frozen lattice torus, block bounds, local/bounded-global inverse and exact cell complement constant. Dependency route still subject to F1/N2. |

## Definitions, frozen objects and consumers

Definition verdict: **PASS**. `CPhase`, `CHam`, `realBase`, `coefficientDom`, `realTube`, `geometricWidth` are transparent carrier/width adapters. `firstBlock`, `lastBlock`, `TwoDiv`, `firstGen`, `setting`, `directMap` use the stated blocks, divisor and explicit flow. `oscPack`, `oscUnpack`, `oscFunction`, `oscParams`, `oscDom`, `oscClass`, `oscBound`, `oscGauge`, `oscGen`, `oscStepMap` encode Fourier expansion only in the fast angles, with parameter order `(I,p,q)` and phase order `((θ,q),(I,p))`. `WSummable` accompanies every weighted sum bound, preventing a junk-zero sum argument. No oscillator angle periodicity is assumed.

`ScaleData`, `constants`, `cutoff`, `rhoHat`, `eHat`, `kamConstant`, `complementConstant`, `initialL`, `nextScale`, `seq`, `realFreq`, `dioBase`, `omegaSet`, `oscPeriodChart`, `limitmap_data` implement the displayed formulas, set restrictions and scaling. Numerical formula definitions are total; theorems guard their mathematical use with positive source data. `DirectHyp`, `AvgHyp`, `OscHyp`, `KamHyp` contain source premises, bounds and typing data, with no solution/limit/measure conclusion field. There are no added global instances on bare functions or matrices. Empty sets are allowed without selecting arbitrary default stages.

Frozen-object verdict: **PASS**. Read the frozen `Phase`, `Fast`, `Slow`, `ActionNbhd`, `HamiltonianVectorField`, `HamiltonianVectorFieldC` and `SymplecticForm` definitions. The complex form is the landed canonical form; the real field is literally the frozen field on the real part of the same complex Hamiltonian. `block_bridge` supplies the block adapter. The P1 `IsLatticeTorus` and `twoScaleDiophantine` fixtures preserve their upstream definitions and binder order; these are temporary upstream fixtures, not purported new frozen definitions. Remove them in favor of owner imports on landing. No provider or frozen theorem anchor is imported.

Consumer verdict: **FAIL for the P23-13 → P23-15 oscillator step boundary (F1); PASS for the reviewed final public consumer contract**. Searched I/N/P consumers, including I, N Parts 7/11/12 and P Parts 4/5. The relevant downstream P consumers are Part 5 averaging (L169–179), KAM hypotheses/application (L198–225), location/torus reconstruction (L240–266), and cell/measure assembly; Part 4 frequency dictionary and budget (L145–155, L190–220). No I/N proof consumes the oscillator output. N Part 6's cross-reference to P direct is an observation about the divisor hypothesis, not a circular proof input.

The final torus uses `IsLatticeTorus KAM.ODE.angleShift Hr ... ω (K ω)`. P1 `cyl_pipeline` takes that same unscaled period-one parameterization after Part 5 establishes the chart pullback and target-domain bridge. Those equality/domain obligations remain explicitly in Part 5. Frequencies are divided by `2π` once. The measure conclusion uses the half-open unit angle cell and exactly `1+(1+2^n)(1+(4/3)^n)`; no measurability assumption is silently added for arbitrary `D`. Source inverse-frequency estimates have the local threshold and bounded-base qualification, not a global unbounded-set claim.

Package verdict: **PASS with F1 interface repair required**. The 22 packages and 10 waves form a forward dependency order; expected files are 150–800 lines with splitting planned before 1200, below the 1500-line cap. Source-free setting definitions are placed before their consumers; the optional `TwoScale/Setting` split avoids a Step/Setting cycle. Limit packages retain common witnesses and do not assume `IterationWorks` or a limit-existence field. No proof-provider closure is claimed.

## Independent checks

- `git diff inp...HEAD`: exactly the design document, 1189 added lines. No state-changing git command used.
- Signature copy elaboration run once through `inp_sig_check.sh /root/code/KAM-inp-design-p23 .drafts/scratch/P23Signatures.lean`, with `LEAN_NUM_THREADS=1`, `nice -n 5`; the gate runs `lake env lean` against the shared inp build. Exit **0**; exactly **33** `declaration uses sorry` warnings, no errors or other warnings.
- `#print axioms nfb`, `osc_averaging`, `step`, `iterative`, `two_scale_kam`: each **`[propext, sorryAx, Classical.choice, Quot.sound]`**. These are signature fixtures, not proof closure.
- Appendix A equals the shared signatures byte for byte. All three blueprint SHA256 values match the design receipt and the shared checkout. Independently matched the table to live packet statement sources: **131 records, 131 unique mapped rows, no missing or extra node**.
- Mathlib probe in `.lake/abi-scratch/P23AuditNames.lean`: the five exact cited names `Convex.norm_image_sub_le_of_norm_fderiv_le`, `ContractingWith.exists_fixedPoint`, `Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`, and `hasDerivAt_of_tendsto_locally_uniformly_on'` all resolve and print the expected types. The derivative-limit theorem accepts an open set, locally uniform derivative convergence, eventual differentiability and pointwise function convergence, which `real_curve_limit` supplies on `univ`. `HasStrictFDerivAt.to_localInverse` also resolves. The exploratory probe exits **1** solely because an additional uncited candidate name, `ContinuousLinearEquiv.ofOperatorNormSubSelf_lt_one`, is unknown; that name is not asserted by the design and is not a finding against it. No signature re-elaboration was run. Probe deleted afterwards.
- `LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh`: exit **1**. Output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; ABI probe then fails `unknown module prefix 'KAM'`, with the worktree `.lake/build/lib/lean` lacking the project build overlay. This reproduces the handoff's environment limitation, not an ABI-drift diagnosis. No overlay, dependency, or library rebuild attempted. The linter's own temporary Lean file is removed by its `finally` block.
- No new production Lean module exists to target-build: this is a report-only audit, with the required signature elaboration above. Lean invocations were sequential within this audit, single-threaded and at nice level 5; no heartbeat, recursion, or synthesis-budget override was used.
- Final report whitespace and theorem-table coverage checks: **PASS**. Original signatures remain unchanged; only the requested report is a new visible worktree change. The explicitly requested scratch signature copy remains in `.drafts/scratch/`.

The remaining uncertainty is proof feasibility of the proposed strengthening and the private shared-witness limit interfaces. No result here seals P-G or proves an analytic source gap closed. Repair F1 and audit the returned same-map properties before assigning the oscillator finite iteration against this interface.
