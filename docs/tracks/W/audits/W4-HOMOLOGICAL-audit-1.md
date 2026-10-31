# W4-HOMOLOGICAL independent audit 1

Verdict: **FAIL as an unconditional source-facing package**. The proofs checked on the intended source domains pass with notes, and the representative model is mathematically faithful there. Two public-interface issues remain: unrestricted, potentially divergent pairings (F1), and headline exports that still take intermediate proof gates as hypotheses (F2). Neither finding is a counterexample to the bounded homological equation. No provider or seal is present or approved.

## Scope, authority and frozen inputs

Date: 2026-10-31. Auditor: `maud-wpja-1`. Focused, tier-2 correspondence audit, with a separate adversarial/refutation pass and compiled composition probes. This is a report-only audit; no implementation, source, frozen file, manifest, root, history, or existing handoff was edited. The user authorized capped checks, scratch probes, and this exact report path. No delegation, network access, commit, or push was needed.

* Worktree: `/root/code/KAM-inp-wpja`, resolving to `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpja`.
* Target HEAD: `7de5b4e0b026248276662eddf40672717df509c8`.
* Comparison `inp`: `ba270772d4dfe54965e03af2033bd21182545318`; the main inp checkout also has this HEAD.
* Comparison performed: `git diff inp...HEAD -- KAM/Wave/Homological`: 46 added modules, 9041 physical lines. Per-file SHA256 values are below. The SHA256 of the sorted concatenation `filename + " " + file_sha256 + "\n"` is `bc4085a96b359f767103379935452bdeba7c840e6425e5f179c395a53b90b90d`.
* Authoritative W4: `blueprint-W/parts/w4-homological.tex`, identical in this worktree, `inp`, and `/root/code/KAM-inp`; SHA256 `d5c2d6de2b8317b34fc0745600b48616345db1e45acd3d6ea3b5742ac71a6baa`.
* Generalization authority: current inp `blueprint-W/parts/w5-kamstep.tex`, SHA256 `d8daf4af9d63da34ae860d2ce9aeefec0a5fe8e7d603cdddb26af6f463e5153c`; identical to `git show inp:blueprint-W/parts/w5-kamstep.tex`. Only the standing weights and `bpW:w5:w4-general` were used; W5 implementation is out of scope.
* Live handoff SHA256 `f3253735c29fb33b4aae0a7acb91c7888d8a8fa0b1d10347bcaa86b65baac945`. Its uncommitted AUDIT FOCUS was present at entry and was preserved.
* Brief: `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, SHA256 `316d17309e362cccf5ee0c182cfe3142c9fad9cd4b8c295332d751d4a334d37d`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the brief, the handoff, and `docs/tracks/W/W-STATEMENTS.md` (there is no `docs/tracks/W/statement.md`). Applied the manuscript-audit and lean-statement-audit protocols. The user-specified D53 wrapper and slim lint override the older generic build/lint instructions. Provider/frozen-type item 1 is N/A, as explicitly directed by AUDIT FOCUS. Regenerated roots are authorized; the branch also contains W5 files, which were excluded from mathematical review.

## Findings and refutation

### F1 — FAIL: public weak-pairing carriers admit divergent inputs

Anchors at the frozen HEAD:

* `Lie.lean:85`: `def homPair0 (x x' : ℕ+ → ℂ) : ℂ := ∑' j, x j * x' j`.
* `Lie.lean:93,98`: `homLieSeq` and `homWeakBracket` use this operation on unrestricted sequences.
* `Lie.lean:101–104`: the docstring says “valid whenever the two pairings are defined (here: whenever they are summable)”, but `homWeakBracket_eq_neg_lieN` has no such hypotheses.
* `LemmaOneFin.lean:34–37`: `homPairOmega_gen` accepts arbitrary `W : ℕ+ → ℝ` and `c z : HomL2`; it takes no frequency-growth or summability evidence.
* `LemmaOneEquation.lean:49–53`: the public `homLieN_gen` inherits that unrestricted frequency carrier. `PPlusOne.lean` aliases it and the pairing at `pb = p+1` without narrowing that carrier.

The source `bpW:w4:lie` defines an actual absolutely convergent weak pairing under the frequency hypotheses. Its proof obtains this from smoothing and Cauchy–Schwarz; it does not assign zero to divergent pairings.

Concrete refutation of whole-carrier fidelity: `x_j=x'_j=1` is an allowed input to `homPair0`. Its series does not converge, but the exported definition returns `0` by Lean's totalized `tsum`. Both assertions were compiled, with exit 0:

```lean
example : ¬ Summable (fun _ : ℕ+ => (1 : ℂ)) := by
  simp [summable_const_iff]
example : homPair0 (fun _ => 1) (fun _ => 1) = 0 := by
  unfold homPair0
  simp only [one_mul]
  exact tsum_eq_zero_of_not_summable (by simp [summable_const_iff])
```

The defect also occurs with the representative carrier, not just raw sequences: take `a=p=0`, `pb=1`, `c_j=z_j=1/j` in `HomL2`, and `W_j=(j+2)j²`. Then `D_j=1/(j+2)` and every term in `homPairOmega_gen` is `1`. The two vectors are square summable; the pairing is divergent. This counterexample is mathematical evidence, not a separately compiled construction of those lp vectors.

Adversarial check: the headline equation supplies `|W_j| ≤ K0(j+2)` and `1 ≤ p+pb`, or the guarded derivative supplies (G). `homPairOmega_eq_clm_gen` and `homNOmega_embed_gen` then identify the sums with genuine bounded bilinear forms. Thus **no reliance on a divergent sum was found in those intended-domain applications**. This refutes a claim of an incorrect bounded equation, but does not refute the public-carrier finding. Likewise a literal `tsum` formula is syntactically correct; it does not give an actual pairing on the whole declared carrier. The unrestricted weak-bracket theorem remains true for these totalized operations and therefore cannot itself certify summability.

Disposition: source-definition/public-carrier failure, not a kernel soundness failure. Proposed repair, not applied: keep raw totalized operations explicitly internal and expose a source-domain pairing/weak bracket with the required carrier evidence, together with its convergent-sum characterization. A later valid-domain theorem alone does not change the current exported definition's carrier.

### F2 — FAIL for literal headline fidelity; CONDITIONAL helpers have checked suppliers

`bpW:w4:lemma1` assumes frequency hypotheses and Melnikov conditions. The exports advertised as its statements instead accept intermediate estimates:

* `LemmaOneBounds.lean:258`: `homLemma1_fieldBound_gen` assumes `hm : HomMultBounds τ α w W`.
* `Lemma1.lean:42`: `homLemma1_lipschitz_gen` assumes two `HomMultBounds` and `hL : HomMultLip ...`.
* `LemmaOneAll.lean:181`: `homLemma1_equation_all_gen` assumes `HomMultBounds`, `hK0`, and `hΩ`.
* The corresponding original-name corollaries in `PPlusOne.lean` retain these gates. They specialize `pb`; they do not assemble the source hypotheses.

`HomMultBounds` (`LemmaOneF.lean:38–51`) expands to multiplier bounds, Schur-bound fields and nonzero-divisor obligations. `HomMultLip` (`LemmaOneLip.lean:42–53`) expands to inverse-divisor difference bounds. These are conclusions of the divisor proof, not premises of the source Lemma 1. They are legitimate hypotheses of distinct conditional helpers, but the helpers alone are not the literal source theorem. No source-premise headline wrapper was located in the audited 46 modules.

Adversarial check: the suppliers are real, proved results, not missing mathematics: `homMultBounds_of`, `homMultLip_of`, and `homOmega_le` derive these gates from `HomFreqHyp`, `HomMelnikov`, positivity and parameter membership. The audit compiled source-premise applications of the all-vector equation and the Lipschitz bound, supplying every gate from these producers. Both passed; the exact probe is retained below. The coefficient-difference bounds of part (iv) also passed a composition probe using `homCoeff_sub_banach` and `homNhat_coeff_bounds_gen` on `R₁.homSub R₂`.

Disposition: **CONDITIONAL as individual exported helpers; BRIDGED as mathematical package derivations; FAIL if advertised as exact source-premise exports.** This is a packaging/fidelity finding, not an unpaid analytic estimate. The strict brief rejects extra source-facing premises even when producers exist elsewhere. Proposed repair, not applied: retain the helpers under clearly conditional identities and add public source-premise assembly wrappers, applying the suppliers inside their proofs. The audit's scratch examples are evidence and do not constitute new package exports.

## Source-node/declaration ledger

Here PASS means the indicated bounded/source-domain mathematical statement was supported; it does not waive F1 or F2, or assert a frozen seal. `_gen` declarations have `pb` as the target exponent; original-name declarations are in PPlusOne unless stated otherwise.

| Source node / clause | Lean declarations | Verdict | Reason / boundary |
|---|---|---|---|
| index, pairing | `homWt`, `HomNormal`, `homNormLp`, `homNorm`, `homPair_le`, `norm_homPair_le`, `homNormal_mul` | PASS | Positive weights at `J=j+2`; no conjugation; actual weighted membership and absolute convergence. |
| melnikov, divisors | `HomFreqHyp1`, `HomFreqHyp`, `HomMelnikov`, `homDelta0/Plus/Minus/P/P'/Q`, `homWeightQ`, `homDivGen_bounds`, six `homDelta*_bound` | PASS | Correct exclusions; repeated indices in P retained; Q weight is max, not `1+|i-j|`; weak tail is sufficient for the same difference estimate. |
| wave (i) | `waveFreqTan`, `waveFreqNor`, `waveMomega`, `waveMOmega`, `homFreqHyp1_wave`, `homFreqHyp_wave` | PASS | Correct angular frequencies, row-sum constant, shifted tail; bounded B replaces a finite supremum by an arbitrary valid upper bound. |
| wave (ii) | `homJapW_reindex`, `homJap_le_japW_le`, `homMelnikov_of_melnikovW`, `homMelnikovW_of_melnikov` | PASS | Zero total mass gives equality; otherwise ratio ≤3; correct directions and α/3. |
| fourier-ops (i),(iii) | `homCoeff_clm`, `homCoeff_sub_banach`, `homSolve_intertwine`, `homSolve_clm` | PASS WITH NOTES | Summability is an explicit premise of low-level linear-image helpers, supplied by `homSolve_spec` in solves. |
| fourier-ops (ii) | `homPartial_differentiableOn`, `homCoeff_partial` | PASS | Correct `2πik_i`; derivative holomorphy handles nonseparable Banach targets. |
| lattice (i) | `waveSphere_card` | PASS | `4N` for N≥1; integer-coordinate L1 shells. |
| lattice (ii),(iii) | `waveS_zero_value`, `waveS_zero_le`, `waveS_le`, `waveS_summable` | PASS | Correct coth formula, real power and positive-loss domains. |
| lattice (iv) | `waveA`, `waveBW`, `waveC`, `waveBWconst`, `waveSum_A_le_waveBW`, `waveBW_le` | PASS ON SOURCE DOMAIN | A0=1 even at τ=0; four terms added separately, with multiplicity; exponent `2τ+3`. Bare raw sums also admit off-source losses; do not interpret their off-domain totalization as convergent sums. |
| schur (i) | `homHadamardOp`, `homHadamardCLM`, `norm_homHadamardCLM_le`, `homNormalEntry_hadamard_gen` | PASS | Constructed bounded operator has the prescribed entries and `c K_S` bound. |
| schur transpose | `homHadamard_transpose_entry`, `homSolve_entry_symm_gen` | PASS WITH NOTES | First theorem transposes representative entries; source transpose is weighted. The second theorem uses `homNormalEntry_gen`, correctly transporting source symmetry/transposition. Do not substitute raw representative transpose for source transpose. |
| schur (ii), ops | `homLamCLM_gen`, `homHadamardOp_lam_gen`, `norm_homLam_hadamard_le_gen`, `homDualNorm_gen`, `norm_le_of_pairing_le` | PASS WITH NOTES | Λ is left multiplication by D; it commutes entrywise with Hadamard division. The model avoids needing a Riesz construction for its actual consumers; see model discussion. |
| schur (iii) | `norm_homHadamardOp_diag_le`, `homDiagonal_bound_gen`, `homDiagonal_bound` | PASS | Diagonal norm improves to c; `(j+2)^(pb-p)` and original `(j+2)` agree exactly at pb=p+1. |
| solve (i) | `homSolve_spec`, `isHomComp_solve` | PASS ON SOURCE DOMAIN | Weighted absolute summability, size, holomorphy, periodicity and coefficients. Uniform convergence follows from the same summable majorant. |
| solve (ii) | `homSolve_sub_le`, image/sub-image bounds | PASS | Same m and parameter factor; coefficient difference split into data and multiplier terms. |
| solve (iii),(iv) | `homSolve_partial`, `homSolve_intertwine`, `homSolve_clm` | PASS WITH NOTES | Derivative data bounded on original strip; no extra lost strip or mode power. Low-level commutation helpers require the produced summability evidence. |
| HolomorphicBanach | `differentiableOn_fderiv_of_isOpen_pi_banach` | PASS | Compact-ball image spans a closed separable Banach subspace; complete local argument described below. |
| Taylor class, coordinates, domain | `HomTaylor_gen`, `homRval_gen`, `homRy/Rz/Rzb/Ru/Rv/Rtheta_gen`, `HomDomain`, `homXnorm_gen`, `homNorm_le_uv` | PASS ON SOURCE DOMAIN | Eight components, symmetric P/P', transpose Qt on strip; independent z and zb; correct max tangential norms, sum normal domain and 2π factors. |
| extract | `polyEval2`, `polyExtract`, `polyExtract_one` | PASS | Roots-of-unity coefficient extraction, including mixed coefficient; genuine finite polynomials, not assumed extraction estimates. |
| components (i),(ii) | `homComp_first_gen`, `homComp_angle_gen`, component extraction and polarization helpers | PASS | Angle derivatives are controlled in dual/bilinear norms; no mistaken bound on the stronger operator norm of ∂P. |
| lie (i),(ii) | `homLie_Omega_mem`, `homLie_pairing_summable_gen`, `homWeakBracket_eq_neg_lieN` | PASS ON SOURCE DOMAIN / FAIL PUBLIC CARRIER | Correct weighted convergence theorem; unrestricted bracket export has F1. General pairing theorem needs `1≤p+pb`. |
| lie (iii), equation coefficients | `homEq_a`, `homEq_b`, `homEq_cp/cm/P/P'/Q_gen`, `homLemma1_equation_gen` | CONDITIONAL | Divisors have correct signs and resonant omissions; finite-support identity proved from conditional multiplier data, F2. |
| lie (iv), guard | `HomGuard`, `homGuard_one_one`, `homGuard_of_cond`, `not_homGuard_of_lt`, `homNOmegaCLM`, `homNfun_hasFDerivAt`, `homLemma_lie_iv_gen` | PASS WITH NOTES | N itself is a genuine bounded quadratic form under (G). Displayed vector has zero θ component; N is independent of θ, so its DN value equals that on the full Hamiltonian field. |
| lemma1 (i) | `homSolveTaylor_gen`, `homLemma1_zero_modes_gen`, `homSolveTaylor_isReal_gen`, `homNhatTaylor_isReal_gen` | CONDITIONAL / BRIDGED | Correct class, zero modes and reality; solve carries multiplier gate, F2. |
| lemma1 (ii), all vectors | `homLemma1_equation_all_gen`, `homLemma1_equation_all` | CONDITIONAL / BRIDGED | Continuity via bounded DΩ and finite-support truncations; source-premise composition compiled. Domain is all y,z,zb, not only D(s,r). |
| lemma1 (iii), uniform | `homF_compBounds_gen`, `homXnorm_le_of_components_gen`, `homLemma1_fieldBound_gen` | CONDITIONAL / BRIDGED | `C1=7+10K_S`, exactly the original field norm and B/α; no new parameter dependence in C1. |
| lemma1 (iii), Lipschitz | `homMultLip_of`, `homF_sub_compBounds_gen`, `homLemma1_lipschitz_gen` | CONDITIONAL / BRIDGED | Correct `εL+2Mε/α`, difference Hamiltonian; compiled source-premise composition. |
| lemma1 (iv) | `homNhatTaylor_gen`, `homNhatTaylor_val_gen`, `homNhat_coeff_bounds_gen`, `homNhat_fieldBound_gen`, `homNhat_lipschitz_gen` | PASS ON SOURCE DOMAIN | Correct mean diagonal, `2πε`, power-weighted coefficient bound and 2ε field bound. Coefficient differences follow by compiled subtraction, not merely a claim from the field bound. |
| lemma2 and (4) | `homLamNorm`, `homLemma2`, `homKS_lt_29`, `waveBW_le` | PASS WITH NOTES | Arithmetic assembly of the preceding bounds; `3C1<108`, M>0 and `0≤λ≤α/M`, positive σ≤1. It is an inequality between explicit bounds, not a new theorem supplying the field estimates. |
| p_plus specialization | PPlusOne abbreviations and corollaries | PASS WITH NOTES | Direct pb=p+1 instances, including conversion of rpow exponent 1 to multiplication; original frequency type is `HomFreqHyp1`, not the weakened `HomFreqHyp`. The handoff explicitly discloses that naming exception. |

## Expanded binder audit of the all-vector headline helper

This table audits the actual signature at `LemmaOneAll.lean:181` as a putative replacement for source Lemma 1(ii). It explains F2. TYPING includes ordinary value data, not logical assumptions. STANDING for the generalized statement means the actual W5 setting `a=p=1`, or a broader explicitly conditional helper range; it does not assert that the interval alone implies `1≤p+pb` for every p≥0. SOURCE references are `bpW:w4:lemma1`, `bpW:w4:index`, and W5's Weights / `bpW:w5:w4-general`. RULED count is zero.

| Binder / expanded field | Bin | Source or reason |
|---|---|---|
| `a` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `p` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `pb` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `s` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `σ` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `τ` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `α` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `K0` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `w` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `W` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `r` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `ε` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `R` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `θ` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `y` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `z` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `zb` | TYPING | Real parameter, vector, frequency data, Taylor datum or evaluation point. |
| `ha` | STANDING | W4 index: a≥0. |
| `hp` | STANDING | W4 index: p≥0. |
| `hpb` | STANDING | Weaker than the W5 interval lower bound; original pb=p+1 implies it. |
| `hp1` | STANDING | Automatic at the actual W5 standing p=1; original pb=p+1 also implies it. |
| `hr` | SOURCE | r>0. |
| `hτ` | SOURCE | τ≥0. |
| `hα` | SOURCE | α>0. |
| `hσ` | SOURCE | σ>0. |
| `hσs` | SOURCE | σ<s. |
| `hX` | SOURCE | Exactly the pointwise field bound on HomDomain; ComponentsFirst.lean:32 expands it to ∀ θ y z zb, HomDomain → homXnorm≤ε. |
| `hθ` | SOURCE | Evaluation on the output strip. |
| `hm.a0` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.dp` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.dm` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.P.off` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.P.diag` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.P'.off` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.P'.diag` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.Q.off` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.Q.diag` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.Qt.off` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.Qt.diag` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.nz0` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.nzp` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.nzm` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.nzP` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.nzP'` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hm.nzQ` | EXCESS | Intermediate divisor/multiplier fact; supplied by homMultBounds_of, not a source Lemma 1 premise. |
| `hK0` | EXCESS | Intermediate nonnegative bound constant; constructed from 1+M0. |
| `hΩ` | EXCESS | Intermediate growth bound; proved by homOmega_le. |
| `R.comp_a0.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_a0.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_a0.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.comp_b.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_b.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_b.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.comp_cp.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_cp.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_cp.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.comp_cm.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_cm.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_cm.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.comp_P.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_P.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_P.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.comp_P'.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_P'.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_P'.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.comp_Q.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_Q.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_Q.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.comp_Qt.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: DifferentiableOn on the source strip. |
| `R.comp_Qt.2.1` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Period one in each angle coordinate on the strip. |
| `R.comp_Qt.2.2` | SOURCE | Defining Taylor-class condition, bpW:w4:taylor: Existence of a uniform component norm bound on the strip. |
| `R.symP` | SOURCE | bpW:w4:taylor: Symmetry of P entries on the strip. |
| `R.symP'` | SOURCE | bpW:w4:taylor: Symmetry of P' entries on the strip. |
| `R.transQ` | SOURCE | bpW:w4:taylor: Qt is the source entrywise transpose of Q on the strip. |

Counts for this expanded helper, including the 27 defining proof fields carried by R: **SOURCE 34, STANDING 4, TYPING 17, RULED 0, EXCESS 19**. It fails the exact-source binder test. In the compiled source-premise composition, all 19 excess obligations are supplied inside the proof; none is left to the caller. That demonstrates repairability, not identity of the existing helper's type with the source theorem.

The other headline gate is fully expanded as follows. Each row applies separately to each parameter point in the Lipschitz helper.

| HomMultLip field | Content | Classification as a source Lemma 1 premise |
|---|---|---|
| a0 | Scalar inverse-divisor difference estimate | EXCESS; producer homMultLip_of |
| dp | Positive normal multiplier difference estimate | EXCESS; same producer |
| dm | Negative normal multiplier difference estimate | EXCESS; same producer |
| P.off | Off-diagonal P inverse estimate | EXCESS; same producer |
| P.diag | Diagonal P inverse estimate | EXCESS; same producer |
| P'.off | Off-diagonal P' inverse estimate | EXCESS; same producer |
| P'.diag | Diagonal P' inverse estimate | EXCESS; same producer |
| Q.off | Off-diagonal Q inverse estimate | EXCESS; same producer |
| Q.diag | Diagonal Q inverse estimate | EXCESS; same producer |
| Qt.off | Off-diagonal transposed-Q inverse estimate | EXCESS; same producer |
| Qt.diag | Diagonal transposed-Q inverse estimate | EXCESS; same producer |

`HomCompBounds_gen` is also an intermediate estimate bundle, not a source assumption: b, cp, cm, P, Q, Qt, P', da, db, dcp, dcm, dP, dP', dQ. The assembly theorem taking it is conditional; `homF_compBounds_gen` and `homF_sub_compBounds_gen` prove these fields at their use sites. `HomFieldBound_gen` and `isRealTaylor` are genuine source predicates, not conclusion-shaped witness packages. `HomTaylor_gen`'s eight regularity fields each expand to differentiability, periodicity and boundedness; its symmetry and transpose fields are exactly the defining Taylor-class conditions.

## Model, norms, generalization and holomorphic argument

Put `wq(j)=ω_(a,q)(j+2)`. A representative `ẑ∈HomL2` corresponds to the actual sequence `z_j=ẑ_j/wq(j)`. Positivity of wq makes this bijective with the weighted space, and the squared norms agree term by term. Reindexing j↦J=j+2 identifies this with the normal subspace whose first two wave coordinates vanish. This is the source's *Representatives* realization, not a restriction to finite-support vectors.

For an operator representative A, `homNormalEntry_gen` is `Aij wp(j)/wpb(i)`. Thus it represents exactly a bounded map from weight p to weight pb, with the same operator norm. With `D_i=1/(wp(i)wpb(i))`, `ΛA=DA`; its bilinear evaluation is `∑(DA ẑ)_i ẑ'_i`. The norm equals the operator norm of DA: Cauchy–Schwarz gives one inequality, and testing against normalized coordinatewise conjugation gives the reverse (`norm_le_of_pairing_le`). Likewise the dual norm on gradient representatives is `‖D ĉ‖`. Entry symmetry in `homNormalEntry_gen`, not symmetry of raw Aij, is the source symmetry. `homLam_entry_eq_gen` and `homLam_entry_symm_gen` transfer it correctly. This explains why the angle estimates must use Λ∂P and Λ∂Q rather than the stronger norms of ∂P and ∂Q themselves.

Every bounded complex bilinear form on l2 has such a bounded operator representative by the accepted W4-E5 repair (insert coordinatewise conjugation to use sesquilinear Riesz). The code's concrete bilinear consumers only need operators and the norm formula, so avoiding a fresh formal Riesz transfer is sound for those consumers. **Limit:** no new public Lean isometric equivalence between this model and every W1 normal-subspace/bilinear-form type is supplied by W4. Mathematical model fidelity is supported; arbitrary future cross-interface Lean applications are not certified by prose. W5 code was not audited.

Normalization check: Fourier characters have period 1; tangential fields contain `(2π)⁻¹`, angular frequencies are used in the divisors; z=(u+iv)/√2, zb=(u−iv)/√2; the normal Hamiltonian field is `(-iF_zb,iF_z)`. The field norm uses the sum of the normal u/v norms and max tangential norms. `homNfun_hasFDerivAt` proves the actual derivative on the phase Banach carrier; setting the irrelevant θ input to zero in `homLemma_lie_iv_gen` changes no DN value.

Generalization: most `_gen` estimates are stronger than the requested smoothing interval, needing only `p≤pb`, with no upper bound. The all-vector equation and the uniform frequency-pairing estimate additionally use `1≤p+pb`. This follows in the actual W5 setting `a=p=1` (W5 source lines 35–36 and 149–152), and at pb=p+1 for all p≥0. **Do not infer it from pb∈[p+1/2,p+1] alone for arbitrary p≥0.** For example p=0,pb=1/2 does not satisfy it; the generalized source's proof itself uses p=1. Thus no failing W5 specialization was found. The frequency structures implement exactly the weak j^(1/2) tail and its Lipschitz analogue; `HomFreqHyp1.toHyp` preserves constants. The coefficient bound changes to `(j+2)^(pb-p)|Ωhat_j|≤ε`, and PPlusOne restores the original bound exactly. The 72 disclosed helper-name exceptions do not silently change an old declaration's meaning; they simply have no old-name export here.

`HolomorphicBanach.lean:54–132`: choose a positive closed ball inside the open domain. Its continuous image is compact and hence separable. The closed complex linear span F0 is separable and complete. Difference quotients of f along complex lines lie in F0 and converge there by closedness, so all derivative values lie in F0. Corestrict the map on the ball, apply the existing second-countable theorem to its derivative, then compose with the continuous inclusion F0→F. The auxiliary g uses zero when f(w)∉F0, but on a neighborhood of every point used, g=f exactly. Its fallback is private to the proof, with eventual equality proved before derivative transfer; no exported off-domain definition or junk value is used. No separability hypothesis has been smuggled onto the public target.

## Definition classification

The package has 104 public `def` sites, 30 `abbrev` sites and 7 `structure` sites (141 in total), plus the private closed-span helper. These are classified by family here; the per-file declaration inventory below enumerates every site. Ordinary explicit construction from a proved norm bound is not a choice from an unproved existence assumption.

| Family | Classification | Whole-carrier/source assessment |
|---|---|---|
| Shells, weights, finite moments, divisor formulae, wave frequencies/constants, polynomial evaluation | Literal formula or finite construction | Correct arithmetic and indexing. waveFreq* carries positive mass. |
| HomNormal, homNormLp, homNorm, HomL2, HomOp, HomPhase | Weighted-membership predicate, typed representative and type aliases | Correct spaces and norms; no default membership witness. |
| HomFreqHyp/1, HomMelnikov/ W, HomGuard, HomDomain, IsHomComp, HomTaylor_gen, HomFieldBound_gen, isRealTaylor | Literal source predicates/classes | Defining fields match the source setting; interpreting parameters still requires the source's standing ranges. |
| HomHadamardBound, HomDivisorBound, HomMultBounds, HomMultLip, HomCompBounds_gen | Intermediate proof predicates/bundles | Legitimate as helper contracts; not interchangeable with source premises, F2. |
| Hadamard operators/CLMs, diagonal/embedding operators, entry functionals | Constructed bounded maps with entry specifications | Actual bounds/entry equalities are proved; no arbitrary witness selection. |
| homPairF, homPairL2, homPairRep_gen, homDualNorm_gen, homLamCLM_gen | Convergent pairings and explicit operator/norm formulae | HomL2 and typed weight bounds ensure convergence on their entire typed vector carriers. |
| homNOmegaCLM, homNfun, homDN, homDiagW_gen | Guarded bounded bilinear form, polynomial and actual derivative | Growth/guard evidence is in their construction; characterized by sum/evaluation and HasFDerivAt theorems. |
| homCoeff, homSolve, homPartial, waveS, waveBW | Raw Bochner/Fourier/derivative/sum operations | Source fidelity established only on the stated regularity and positive-strip/loss domains. Their raw total functions are not independently certified as source objects off those domains. |
| homPair0, homLieSeq, homWeakBracket, homPairOmega_gen, homLieN_gen | Public raw potentially divergent pairings/brackets | **FAIL public carrier**, F1. The compiled constant-sequence example exhibits actual totalization. |
| homRval_gen, gradient formulae, homXnorm_gen, homSub, homSolveTaylor_gen, homNhatTaylor_gen, homNhat_gen | Explicit polynomial/component constructions | Correct on source domains; solve boundedness is supplied by its proved spec, Nhat matches its typed Taylor polynomial there. They do not repair F1 by changing its carriers. |
| PPlusOne abbreviations | Literal specialization | pb=p+1 by definition; no replacement object or extra construction. |
| private spanClosure and local g | Closed span; local corestriction used in a proof | Eventual equality on the actual ball justifies g; no source-definition substitution. |

For the source-labelled weak-pairing semantic unit:

```text
BODY_MATCH: OK on the source summability domain
PUBLIC_CARRIER: FAIL
WELL_DEFINEDNESS: FAIL as a convergent pairing on its declared unrestricted carrier
CHARACTERIZATION: FAIL on that whole carrier (not a failure of the restricted identities)
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: FAIL
```

For the guarded normal form `homNOmegaCLM`/`homNfun` and its derivative:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: OK (bounded diagonal and l2 pairing)
CHARACTERIZATION: OK (homNOmegaCLM_apply, homDN_apply, homNfun_hasFDerivAt)
CHOICE_INDEPENDENCE: N/A (explicit construction)
DEFINITION_VERDICT: PASS
```

## Verification commands and actual outcomes

All Lean/Lake work in this audit was serial, under D53. No heartbeat, recursion-depth or synthesis budget override was used. The single-file invocations had this exact prefix (the second env supplies the slim-worktree import overlay):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 env LEAN_PATH=.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean lake env lean .lake/abi-scratch/maud-wpja-1-<probe>.lean
```

| Probe | Outcome |
|---|---|
| import | Exit 0; imports Divisors and WaveReindex together, prints `KAM.Wave.homL1_neg (l : ℕ+ →₀ ℤ) : KAM.Wave.homL1 (-l) = KAM.Wave.homL1 l`. |
| main | Exit 0; imports all W4 modules except WaveReindex, runs 392 `#print axioms` commands. |
| reindex | Exit 0; imports WaveReindex, runs 11 `#print axioms` commands. |
| compose, first version | Exit 0; two unused-variable warnings in the auxiliary exponent example. |
| carrier | Exit 0, no output; proves nonsummability and totalized zero for constant homPair0 inputs. |
| compose, final version | Exit 0, no output; all-vector source-premise equation, coefficient differences, exponent specializations, and source-premise Lipschitz field bound. |

The 403 public theorem declaration sites (402 distinct names) have only standard axioms. Exact counts by reported set: 400 sites `[propext, Classical.choice, Quot.sound]`; 2 `[propext]`; 1 `[propext, Quot.sound]`. This includes every main result named in the handoff and the private-proof dependency closure of HolomorphicBanach. The main/reindex split checks the two separately defined `homL1_neg` sites in their respective imports. The sorted per-declaration census is retained below; no sorryAx or project axiom occurred.

Lint command, exit **0**:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpja
```

Actual output:

```text
check_lean_modules: PASS (3610 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

Targeted build was requested through the current track-W serial capped gate:

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpja KAM.Wave.Homological.PPlusOne
```

Actual beginning: `[w_build] slot 1: KAM.Wave.Homological.PPlusOne (21:41:19)`.
Actual final Lake line: `Build completed successfully (3303 jobs).` Existing warnings were replayed (unused tactics/variables/simp arguments and deprecated names), not Lean errors. **The driver process nevertheless exited 1.** Its last loop-body command is `[ $rc -ne 0 ] && { ...; exit $rc; }`; when Lake succeeds this conditional returns 1 and is propagated by the script. No `[w_build] FAILED ...` line occurred. Record Lake success and driver-status defect separately; do not report a clean driver exit. No repair was made to that external script. The driver itself executes the required `systemd-run ... nice -n 10 env LEAN_NUM_THREADS=1 lake build` wrapper and holds the compile gate. No library clean or from-scratch rebuild was requested.

Kernel replay/name checks: the user says the launcher ran them. Their output is unavailable in this audit's history, so **no independent replay exit code is asserted**. No replay was rerun: fresh imports, the complete axiom census, source review and the bounded build were sufficient for the findings here. This is explicitly different from claiming that unseen launcher output passed.

Other exact checks:

* `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no output. No protected anchor/manifest changes. `KAM/Root/Wave.lean` is changed and explicitly authorized by the focus.
* `git diff --exit-code -- KAM/Wave/Homological`: exit 0; the audited source bytes were unchanged locally.
* W4 inventory: 46 files; maximum physical file length **809** (`LemmaOneLipBounds.lean`), below 1500. The older handoff's “under 710” statement is stale.
* `rg` for forbidden escapes/options and `EuclideanSpace` in W4: no matches. No W4 import of a provider, frozen anchor, root or KamStep module was found. The lint's module/line-width checks passed.
* Duplicate source declaration: `KAM.Wave.homL1_neg` at Divisors.lean:72 and WaveReindex.lean:82. The types agree and the combined-import probe passes. This is a naming/hygiene note, **not** a demonstrated import failure. Distinctive naming or a shared import would avoid the duplicate.

## Errata, uncertainties and closeout

No new mathematical defect in the pinned W4 blueprint was confirmed. The accepted W4-E5 repair is mathematically adequate for the representative argument. Existing source deviations remain visible: the P96-K square-sum replacement, max-versus-1+gap divisor factor, omission of the constant mode, altered constants and period-one normalization. None was silently repaired or used as a new premise.

Report-only deviations/operational observations: the external w_build script's success-status propagation defect, the stale “under 710” handoff count, and the duplicate theorem name above. No implementation deviations were introduced by the auditor. No conclusion about W5 implementation, graph closure, frozen theorem closure, or a full independent rerun of launcher kernel replay is made.

Closeout: source/domain/normalization review completed at the depth stated here; all public theorem axioms checked; lint passed; targeted Lake build succeeded with the recorded driver-status caveat; source-premise composition and the negative carrier example compiled. **F1 and F2 remain open.** F1 needs source-correct exported carriers; F2 needs source-premise public assembly (or the completeness claim must explicitly be limited to conditional infrastructure). The mathematical computations and proofs on the intended domains are supported; unconditional source-package acceptance is withheld. Scratch probes/logs were copied into this report where needed and deleted after verification. The only audit-created repository file is this report.

## Reproducible final composition probe

```lean
import KAM.Wave.Homological.PPlusOne
open KAM KAM.Wave

example {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ τ α a p pb s σ r ε : ℝ}
    (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hp1 : 1 ≤ p + pb)
    (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (R : HomTaylor_gen a p pb s)
    (hX : HomFieldBound_gen ha hp hpb r ε R)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ))
    (y : Fin 2 → ℂ) (z zb : HomL2) :
    homLieN_gen ha hp hpb (ω ξ) (Ω ξ)
      (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R) θ y z zb
      + homNhat_gen R y z zb = homRval_gen ha hp hpb R θ y z zb - homCoeff R.a0 0 := by
  exact homLemma1_equation_all_gen ha hp hpb hp1 hr hτ hα hσ hσs
    (homMultBounds_of h hα hH hξ) (by linarith [h.consts_nonneg.1])
    (homOmega_le h hξ) R hX hθ y z zb

example {a p pb s r εL d : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hr : 0 < r) (hs : 0 < s) (R₁ R₂ : HomTaylor_gen a p pb s)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * d) (R₁.homSub R₂)) :
    ‖homCoeff R₁.b 0 - homCoeff R₂.b 0‖ ≤ 2 * Real.pi * (εL * d) ∧
    ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
      ‖homNormalEntry_gen a p pb (homCoeff R₁.Q 0 - homCoeff R₂.Q 0) j j‖ ≤ εL * d := by
  obtain ⟨hb, _, hQ⟩ := homNhat_coeff_bounds_gen ha hp hpb hr hs (R₁.homSub R₂) hXL
  have eb : homCoeff (R₁.homSub R₂).b 0 = homCoeff R₁.b 0 - homCoeff R₂.b 0 :=
    homCoeff_sub_banach hs R₁.comp_b.1 R₂.comp_b.1 0
  have eQ : homCoeff (R₁.homSub R₂).Q 0 = homCoeff R₁.Q 0 - homCoeff R₂.Q 0 :=
    homCoeff_sub_banach hs R₁.comp_Q.1 R₂.comp_Q.1 0
  exact ⟨eb ▸ hb, fun j => eQ ▸ hQ j⟩

example {a p pb : ℝ} (_ha : 0 ≤ a) (_hp : 0 ≤ p) (hl : p + 1 / 2 ≤ pb)
    (_hu : pb ≤ p + 1) (hpair : 1 ≤ p + pb) : p ≤ pb ∧ 0 ≤ p + pb := by
  constructor <;> linarith

example {pb : ℝ} (hl : 1 + 1 / 2 ≤ pb) : 1 ≤ 1 + pb := by linarith

example {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ τ α a p pb s σ r ε εL : ℝ}
    (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (hr : 0 < r) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (hεL : 0 ≤ εL) {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par)
    (R₁ R₂ : HomTaylor_gen a p pb s)
    (hX₁ : HomFieldBound_gen ha hp hpb r ε R₁) (hX₂ : HomFieldBound_gen ha hp hpb r ε R₂)
    (hXL : HomFieldBound_gen ha hp hpb r (εL * ‖ξ - ζ‖) (R₁.homSub R₂)) :
    HomFieldBound_gen ha hp hpb r
      ((7 + 10 * homKS) * (waveBW τ σ / α * (εL + 2 * (Mω + MΩ) * ε / α) * ‖ξ - ζ‖))
      ((homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) R₁).homSub
       (homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hζ) R₂)) := by
  exact homLemma1_lipschitz_gen ha hp hpb hr hτ hα
    (by linarith [h.consts_nonneg.2.1, h.consts_nonneg.2.2]) (norm_nonneg _) hεL hσ hσs
    (homMultBounds_of h hα hH hξ) (homMultBounds_of h hα hH hζ)
    (homMultLip_of h hα hH hξ hζ) R₁ R₂ hX₁ hX₂ hXL
```

## Frozen per-file inventory

All paths below are relative to `KAM/Wave/Homological/` at the target HEAD.

| File | SHA256 | Public theorem sites | Definition/alias/structure sites |
|---|---|---:|---:|
| AngleSupport.lean | `2afac078406d44bf54138f1aa081b2122d09aac2163502eef5d017a23a9a37d5` | 7 | 2 |
| CohEq.lean | `0e49aae5e888cbe8e8f0da9b8911f4850d06257e928994eff95bb058efd3cb85` | 5 | 0 |
| ComponentsAngle.lean | `0726dfaaeebc8cfe87f0eebcc11a661f84a99bcf00faad01ac2fd7e30ac2a88a` | 8 | 0 |
| ComponentsAngleQ.lean | `9d629ec9d99a9881ad7fdd5cde1f9dd67c45361e334486eeb8674077435029df` | 3 | 0 |
| ComponentsBasic.lean | `a3ae6c52f6f319aa118d89985fba242100ce9f9f4f0db21baf785c7568a73ae6` | 7 | 0 |
| ComponentsFirst.lean | `b04fae4cee2b6a1e0c5e43afac207d2047fe7d969d111af5ab4090372ab0c6e5` | 2 | 1 |
| Divisors.lean | `91cddc7ddc7557a5894f3b3696d6c5ab4df0019847a177575eeadc58ddb218d1` | 18 | 1 |
| DivisorsConcrete.lean | `39adc9b0fff1256faf50eb0016de16e711815764975e8c58d684eb561bbc48f6` | 18 | 1 |
| Extract.lean | `036d248993a8247686bc5c2479979dcd7204aba031cf5c6f006cc12fedfd8caa` | 6 | 1 |
| HolomorphicBanach.lean | `826f5c0b3970d0c3d8a4dbfaae07c99309235781a10f27964fa92db95b31cc7c` | 1 | 0 |
| Index.lean | `21cfb83ed80b80baf2699ede8ec42d4112d46267ddb6d159eace3dc33ea44f4d` | 11 | 4 |
| Lattice.lean | `7681f3478f1472bb1177bb66d7448cbf335f3440b2b64d916208b67ae01fe52b` | 8 | 1 |
| LatticeBW.lean | `016f6f18ba9af57ed8e239216690b698129df3a71d4ba42fdbcc54d463079b56` | 9 | 4 |
| LatticeCount.lean | `80bf44a452f93a5461d1b02ba82b7acf3dc4b1b2d371e1e84ac943c1ff9033ac` | 3 | 1 |
| Lemma1.lean | `781b85a6c1da63e5c2719705771ebad29b95209b4e2d4a44366330388257dc82` | 7 | 1 |
| LemmaOneAll.lean | `6f3d26f8db959426b0eca07d3d726109ebc81c0731f31690b07eaa45b9b8edad` | 14 | 1 |
| LemmaOneAssembly.lean | `70c0192a631e5803ed537a426279f49d59704c91880fca0dbddef98e9dda0c17` | 5 | 1 |
| LemmaOneBounds.lean | `b81c426f2a9eb442cb8b21cd63c0942e9e09cff9b23b5baac5ad74231dcb4889` | 8 | 0 |
| LemmaOneEq.lean | `eb8ee2c20b1977484b99bb2d43fa1508c90f3adeefa370eaf1e1f25094008773` | 2 | 0 |
| LemmaOneEqFam.lean | `dfc9694061dcff7aac5ce525d35ea5277b13d7d0809c35d0d61db20d0544eda8` | 9 | 0 |
| LemmaOneEquation.lean | `bd6c444d2d28ea46c95827973bd9ad2838256025b22b37166adf8706cc1f6fb0` | 12 | 4 |
| LemmaOneF.lean | `eb943f36c637be1267c4c4cfb22f60476c831abd6ecb300b50db1955a472800b` | 15 | 10 |
| LemmaOneFin.lean | `2170910d8a83f6dace0bbc476428e83955773045c1c64306ba2cbb73f95ec49d` | 5 | 2 |
| LemmaOneLip.lean | `0a00e256ce932640854fa0dd810aceb568f93783504fb8f4dd855b0acffcd1b1` | 5 | 2 |
| LemmaOneLipBounds.lean | `84bac5eb008cab6cd598c5817a3ec4241dd6924cbd87e48f04e29cf647ef5e27` | 21 | 0 |
| LemmaOneLipDiff.lean | `d6829934186b58d7defc912dc3e627bfd43126d91546aeb5ce02b7b4c6cb89ae` | 11 | 0 |
| LemmaOneMult.lean | `9013e69258bae5a3204f3d4e7abd0bc92106e33ee4976eb0666500ec6b9a450b` | 14 | 8 |
| Lie.lean | `437bd31c790125cdb0a5447347d86cbe2ca8e3a48c44262aeb3615a40302e4fd` | 7 | 4 |
| LieDeriv.lean | `a617aec6f545ceee78e9bafa518f6bbd520eca63eb94ecd6d0d09182d79648bb` | 12 | 10 |
| Melnikov.lean | `13ac437ab776f61e3ec97f430ee1794b94d8e0e489cb5c9dfe1eb43d22205c15` | 2 | 15 |
| NhatTaylor.lean | `ca0b2f4c61478954b228a37f3f3d3d6c6ad074e1eaa64a1c4dc9b09502512a28` | 7 | 1 |
| NormalOps.lean | `75432993bb728bb22e4a41c88356b0ce4b1b682a4e6be9483340f664438b84ba` | 15 | 6 |
| NormalPol.lean | `1ce6a53f4fe0b6674839b5545bf12e1d3e076dc3103652663da142aaa6fffe25` | 13 | 2 |
| PPlusOne.lean | `97017a0f53fbc333921746e5506bbfba87f5faf25111f3ffd7c53fa8411511da` | 28 | 27 |
| RealF.lean | `98d703e4c734c32413d3f8eb766b71b83c14f75edd0f3d5dd7f2d4efcb4a5aba` | 3 | 1 |
| RealSolve.lean | `f68ea36c4c85dd455c6c775aef6e595d2421eaf0eb8553f2b2c6102a8a5a0577` | 11 | 0 |
| Schur.lean | `0e14b05cdb04679770c6020724d4f0d5247475455b9671226992a03ce62ff399` | 20 | 7 |
| Solve.lean | `3c7d28377968429f8334a1bf9ad26d9f5d698505e59d51a244caac1894ed3316` | 5 | 2 |
| SolveDeriv.lean | `fbe8be8a992eaff3e9c95e64df371db08371f94a587598acf5ddcf85de9c5c87` | 6 | 1 |
| SolveImage.lean | `ac5fc04a262e31b55d1e663f81fbeb4783c0308d3ef032b10349550e9ab42724` | 4 | 0 |
| SolveImageSub.lean | `b7415ea66fa6a9b398538134bb7ed559530b7e7a5499dc455cdfa2bd54a6d5eb` | 2 | 0 |
| SolveLinear.lean | `6e8e5e5010b039342d5d750176c8b32d294befa0b26c8be54e1ca7635febd9f0` | 6 | 0 |
| Taylor.lean | `10bff40e3faa081265ce2db5bedddc19afafb0787d63bb2dc1bdbfb097a6cc84` | 8 | 13 |
| TaylorSub.lean | `51cfc8f1c0d430afe36f6feee80f1e89a203dd8bac953af310fda290ac332ac6` | 3 | 1 |
| Wave.lean | `9736d83d736cf138635c4249ab7b1fc3e6a70664e61ecf39f0272937118337d4` | 6 | 4 |
| WaveReindex.lean | `7ef7ff239f1fb586fcd7720b9a7f3788557af093a27bdc489596534f42f44fea` | 11 | 2 |

## Complete public theorem axiom census

Every row has axiom verdict PASS. The semantic/source verdict is the applicable source-node row above; an axiom PASS does not override F1/F2. P=propext, C=Classical.choice, Q=Quot.sound.

| Declaration site | Export (namespace KAM.Wave) | Axioms |
|---|---|---|
| AngleSupport.lean:40 | `homEntryCLM_apply` | [P, C, Q] |
| AngleSupport.lean:46 | `homNormEntryCLM_apply_gen` | [P, C, Q] |
| AngleSupport.lean:50 | `homNormalEntry_partial_gen` | [P, C, Q] |
| AngleSupport.lean:62 | `homNormalEntry_partial_symm_gen` | [P, C, Q] |
| AngleSupport.lean:78 | `homLam_entry_eq_gen` | [P, C, Q] |
| AngleSupport.lean:95 | `homLam_entry_symm_gen` | [P, C, Q] |
| AngleSupport.lean:102 | `homPairRep_eq_gen` | [P, C, Q] |
| CohEq.lean:32 | `homCoeff_continuous_of` | [P, C, Q] |
| CohEq.lean:36 | `homCoeff_add` | [P, C, Q] |
| CohEq.lean:49 | `homCoeff_sub` | [P, C, Q] |
| CohEq.lean:54 | `homCoeff_smul` | [P, C, Q] |
| CohEq.lean:61 | `homCohEq_scalar` | [P, C, Q] |
| ComponentsAngle.lean:33 | `homRtheta_y_gen` | [P, C, Q] |
| ComponentsAngle.lean:41 | `homRtheta_z_gen` | [P, C, Q] |
| ComponentsAngle.lean:51 | `homRtheta_zb_gen` | [P, C, Q] |
| ComponentsAngle.lean:62 | `homAngle_a_gen` | [P, C, Q] |
| ComponentsAngle.lean:75 | `homAngle_b_gen` | [P, C, Q] |
| ComponentsAngle.lean:129 | `homQuad_of_unit` | [P, C, Q] |
| ComponentsAngle.lean:151 | `homAngle_z_gen` | [P, C, Q] |
| ComponentsAngle.lean:191 | `homAngle_zb_gen` | [P, C, Q] |
| ComponentsAngleQ.lean:32 | `homRtheta_zzb_gen` | [P, C, Q] |
| ComponentsAngleQ.lean:46 | `homAngle_Q_gen` | [P, C, Q] |
| ComponentsAngleQ.lean:91 | `homComp_angle_gen` | [P, C, Q] |
| ComponentsBasic.lean:32 | `homUV_le` | [P, C, Q] |
| ComponentsBasic.lean:48 | `homDomain_y` | [P, C, Q] |
| ComponentsBasic.lean:55 | `homDomain_z` | [P, C, Q] |
| ComponentsBasic.lean:65 | `homDomain_zb` | [P, C, Q] |
| ComponentsBasic.lean:75 | `homDomain_zzb` | [P, C, Q] |
| ComponentsBasic.lean:90 | `homAffine_bound` | [P, C, Q] |
| ComponentsBasic.lean:103 | `homXnorm_parts_gen` | [P, C, Q] |
| ComponentsFirst.lean:37 | `homFieldBound_nonneg_gen` | [P, C, Q] |
| ComponentsFirst.lean:46 | `homComp_first_gen` | [P, C, Q] |
| Divisors.lean:35 | `homMom_add` | [P, C, Q] |
| Divisors.lean:38 | `homMom_neg` | [P, C, Q] |
| Divisors.lean:44 | `homMom_single` | [P, C, Q] |
| Divisors.lean:47 | `homPairL_add` | [P, C, Q] |
| Divisors.lean:51 | `homPairL_neg` | [P, C, Q] |
| Divisors.lean:57 | `homPairL_single` | [P, C, Q] |
| Divisors.lean:61 | `homL1_add_le` | [P, C, Q] |
| Divisors.lean:72 | `homL1_neg` | [P, C, Q] |
| Divisors.lean:77 | `homL1_single` | [P, C, Q] |
| Divisors.lean:80 | `homJap_eq` | [P, C, Q] |
| Divisors.lean:82 | `homL1_zero` | [P, C, Q] |
| Divisors.lean:84 | `homMom_zero` | [P, C, Q] |
| Divisors.lean:86 | `homPairL_zero` | [P, C, Q] |
| Divisors.lean:89 | `homL1_cast` | [P, C, Q] |
| Divisors.lean:95 | `abs_homPairZ_le` | [P, C, Q] |
| Divisors.lean:103 | `homPairZ_sub` | [P, C, Q] |
| Divisors.lean:111 | `homDivGen_diff_le` | [P, C, Q] |
| Divisors.lean:139 | `homDivGen_bounds` | [P, C, Q] |
| DivisorsConcrete.lean:38 | `homDivisorBound_of_gen` | [P, C, Q] |
| DivisorsConcrete.lean:49 | `homZ_mem` | [P, C, Q] |
| DivisorsConcrete.lean:57 | `homNe_zero_of_mom` | [P, C, Q] |
| DivisorsConcrete.lean:60 | `homDelta0_bound` | [P, C, Q] |
| DivisorsConcrete.lean:67 | `homJap_neg_single` | [P, C, Q] |
| DivisorsConcrete.lean:72 | `homJap_single` | [P, C, Q] |
| DivisorsConcrete.lean:77 | `homJap_pair` | [P, C, Q] |
| DivisorsConcrete.lean:84 | `homJap_neg_pair` | [P, C, Q] |
| DivisorsConcrete.lean:88 | `homJap_diff` | [P, C, Q] |
| DivisorsConcrete.lean:92 | `homL1_pair_le` | [P, C, Q] |
| DivisorsConcrete.lean:97 | `homDeltaPlus_bound` | [P, C, Q] |
| DivisorsConcrete.lean:108 | `homDeltaMinus_bound` | [P, C, Q] |
| DivisorsConcrete.lean:119 | `homDeltaP_bound` | [P, C, Q] |
| DivisorsConcrete.lean:131 | `homDeltaP'_bound` | [P, C, Q] |
| DivisorsConcrete.lean:143 | `homDeltaQ_bound` | [P, C, Q] |
| DivisorsConcrete.lean:160 | `one_le_homWeightQ` | [P] |
| DivisorsConcrete.lean:162 | `homWeightQ_ge_abs` | [P] |
| DivisorsConcrete.lean:164 | `homWeightP_ge_abs` | [P, Q] |
| Extract.lean:44 | `sum_I_pow` | [P, C, Q] |
| Extract.lean:49 | `sum_weighted_polyEval2` | [P, C, Q] |
| Extract.lean:123 | `norm_I_pow` | [P, C, Q] |
| Extract.lean:127 | `polyExtract_mul_le` | [P, C, Q] |
| Extract.lean:190 | `polyExtract` | [P, C, Q] |
| Extract.lean:202 | `polyExtract_one` | [P, C, Q] |
| HolomorphicBanach.lean:54 | `differentiableOn_fderiv_of_isOpen_pi_banach` | [P, C, Q] |
| Index.lean:41 | `homWt_pos` | [P, C, Q] |
| Index.lean:43 | `ellWeight_succ_exponent'` | [P, C, Q] |
| Index.lean:49 | `homWt_succ` | [P, C, Q] |
| Index.lean:66 | `homNorm_nonneg` | [P, C, Q] |
| Index.lean:69 | `norm_homNormLp_apply` | [P, C, Q] |
| Index.lean:73 | `homNorm_hasSum` | [P, C, Q] |
| Index.lean:81 | `summable_tsum_mul_le` | [P, C, Q] |
| Index.lean:98 | `one_le_homWt_mul` | [P, C, Q] |
| Index.lean:116 | `homPair_le` | [P, C, Q] |
| Index.lean:136 | `norm_homPair_le` | [P, C, Q] |
| Index.lean:145 | `homNormal_mul` | [P, C, Q] |
| Lattice.lean:38 | `waveS_zero_eq` | [P, C, Q] |
| Lattice.lean:45 | `waveS_zero_value` | [P, C, Q] |
| Lattice.lean:50 | `wave_coth_le_one_add_inv` | [P, C, Q] |
| Lattice.lean:74 | `waveS_zero_le` | [P, C, Q] |
| Lattice.lean:82 | `waveGeom_partial_le` | [P, C, Q] |
| Lattice.lean:105 | `waveSphere_card_le_of_kamL1` | [P, C, Q] |
| Lattice.lean:126 | `waveS_finset_le` | [P, C, Q] |
| Lattice.lean:155 | `waveS_le` | [P, C, Q] |
| LatticeBW.lean:47 | `waveC_nonneg` | [P, C, Q] |
| LatticeBW.lean:50 | `waveA_ge_one` | [P, C, Q] |
| LatticeBW.lean:58 | `waveS_summable` | [P, C, Q] |
| LatticeBW.lean:66 | `waveS_le_waveC` | [P, C, Q] |
| LatticeBW.lean:92 | `waveS_le_waveBWconst` | [P, C, Q] |
| LatticeBW.lean:98 | `waveBW_pointwise` | [P, C, Q] |
| LatticeBW.lean:131 | `waveBW_summable` | [P, C, Q] |
| LatticeBW.lean:146 | `waveSum_A_le_waveBW` | [P, C, Q] |
| LatticeBW.lean:166 | `waveBW_le` | [P, C, Q] |
| LatticeCount.lean:34 | `waveSphere_fiber_card_eq` | [P, C, Q] |
| LatticeCount.lean:49 | `waveSphere_fiber_card_lt` | [P, C, Q] |
| LatticeCount.lean:72 | `waveSphere_card` | [P, C, Q] |
| Lemma1.lean:42 | `homLemma1_lipschitz_gen` | [P, C, Q] |
| Lemma1.lean:67 | `HomTaylor_gen.ext_of` | [P, C, Q] |
| Lemma1.lean:75 | `homCoeff_sub_banach` | [P, C, Q] |
| Lemma1.lean:82 | `homNhatTaylor_sub_gen` | [P, C, Q] |
| Lemma1.lean:109 | `homNhat_lipschitz_gen` | [P, C, Q] |
| Lemma1.lean:119 | `homKS_lt_29` | [P, C, Q] |
| Lemma1.lean:139 | `homLemma2` | [P, C, Q] |
| LemmaOneAll.lean:33 | `homPairRep_eq'_gen` | [P, C, Q] |
| LemmaOneAll.lean:36 | `continuous_homPairRep_right_gen` | [P, C, Q] |
| LemmaOneAll.lean:41 | `continuous_homPairRep_op_gen` | [P, C, Q] |
| LemmaOneAll.lean:50 | `continuous_homRval_gen` | [P, C, Q] |
| LemmaOneAll.lean:70 | `continuous_homRtheta_gen` | [P, C, Q] |
| LemmaOneAll.lean:91 | `continuous_homRz_gen` | [P, C, Q] |
| LemmaOneAll.lean:97 | `continuous_homRzb_gen` | [P, C, Q] |
| LemmaOneAll.lean:104 | `one_le_homWt` | [P, C, Q] |
| LemmaOneAll.lean:112 | `homWt_mul_ge` | [P, C, Q] |
| LemmaOneAll.lean:132 | `norm_homLamD_mul_le_gen` | [P, C, Q] |
| LemmaOneAll.lean:150 | `homPairOmega_eq_clm_gen` | [P, C, Q] |
| LemmaOneAll.lean:161 | `truncLp_apply_not_mem` | [P, C, Q] |
| LemmaOneAll.lean:170 | `tendsto_truncLp` | [P, C, Q] |
| LemmaOneAll.lean:181 | `homLemma1_equation_all_gen` | [P, C, Q] |
| LemmaOneAssembly.lean:57 | `norm_homPairRep_le_gen` | [P, C, Q] |
| LemmaOneAssembly.lean:62 | `norm_homPairRep_op_le_gen` | [P, C, Q] |
| LemmaOneAssembly.lean:78 | `norm_le_of_domain` | [P, C, Q] |
| LemmaOneAssembly.lean:86 | `norm_add7_le` | [P, C, Q] |
| LemmaOneAssembly.lean:99 | `homXnorm_le_of_components_gen` | [P, C, Q] |
| LemmaOneBounds.lean:32 | `waveBW_nonneg` | [P, C, Q] |
| LemmaOneBounds.lean:40 | `homPartial_clm` | [P, C, Q] |
| LemmaOneBounds.lean:51 | `homLamDiag_comm_homTdp_gen` | [P, C, Q] |
| LemmaOneBounds.lean:61 | `homLamDiag_comm_homTdm_gen` | [P, C, Q] |
| LemmaOneBounds.lean:71 | `homLam_comm_hadamard_gen` | [P, C, Q] |
| LemmaOneBounds.lean:83 | `norm_sum_mul_le_of_sum_norm` | [P, C, Q] |
| LemmaOneBounds.lean:92 | `homF_compBounds_gen` | [P, C, Q] |
| LemmaOneBounds.lean:258 | `homLemma1_fieldBound_gen` | [P, C, Q] |
| LemmaOneEq.lean:31 | `homFamily_eq` | [P, C, Q] |
| LemmaOneEq.lean:59 | `homFamily_eq_nonres` | [P, C, Q] |
| LemmaOneEqFam.lean:36 | `HomHadamardBound.norm_le'` | [P, C, Q] |
| LemmaOneEqFam.lean:48 | `homInv_resonance` | [P, C, Q] |
| LemmaOneEqFam.lean:66 | `homEq_a` | [P, C, Q] |
| LemmaOneEqFam.lean:82 | `homEq_b` | [P, C, Q] |
| LemmaOneEqFam.lean:115 | `homEq_cp_gen` | [P, C, Q] |
| LemmaOneEqFam.lean:146 | `homEq_cm_gen` | [P, C, Q] |
| LemmaOneEqFam.lean:178 | `homEq_P_gen` | [P, C, Q] |
| LemmaOneEqFam.lean:207 | `homEq_P'_gen` | [P, C, Q] |
| LemmaOneEqFam.lean:237 | `homEq_Q_gen` | [P, C, Q] |
| LemmaOneEquation.lean:65 | `homLop_add` | [P, C, Q] |
| LemmaOneEquation.lean:69 | `homLop_sum1` | [P, C, Q] |
| LemmaOneEquation.lean:76 | `homLop_sum2` | [P, C, Q] |
| LemmaOneEquation.lean:97 | `homRtheta_fin_gen` | [P, C, Q] |
| LemmaOneEquation.lean:110 | `homRval_fin_gen` | [P, C, Q] |
| LemmaOneEquation.lean:123 | `homPairOmega_Rz_gen` | [P, C, Q] |
| LemmaOneEquation.lean:140 | `homPairOmega_Rzb_gen` | [P, C, Q] |
| LemmaOneEquation.lean:158 | `homLop_sumK` | [P, C, Q] |
| LemmaOneEquation.lean:167 | `homBlk_sym` | [P, C, Q] |
| LemmaOneEquation.lean:184 | `homBlk_Q` | [P, C, Q] |
| LemmaOneEquation.lean:215 | `homBlk_c` | [P, C, Q] |
| LemmaOneEquation.lean:238 | `homLemma1_equation_gen` | [P, C, Q] |
| LemmaOneF.lean:53 | `ne_zero_of_divisorBound` | [P, C, Q] |
| LemmaOneF.lean:63 | `homMultBounds_of` | [P, C, Q] |
| LemmaOneF.lean:113 | `norm_homTscal_le` | [P, C, Q] |
| LemmaOneF.lean:119 | `norm_homTvec_le` | [P, C, Q] |
| LemmaOneF.lean:125 | `norm_homTdp_le` | [P, C, Q] |
| LemmaOneF.lean:128 | `norm_homTdm_le` | [P, C, Q] |
| LemmaOneF.lean:131 | `norm_homTP_le` | [P, C, Q] |
| LemmaOneF.lean:135 | `norm_homTP'_le` | [P, C, Q] |
| LemmaOneF.lean:139 | `norm_homTQ_le` | [P, C, Q] |
| LemmaOneF.lean:143 | `norm_homTQt_le` | [P, C, Q] |
| LemmaOneF.lean:148 | `isHomComp_solve` | [P, C, Q] |
| LemmaOneF.lean:157 | `homCoeff_congr` | [P, C, Q] |
| LemmaOneF.lean:166 | `homSolve_congr` | [P, C, Q] |
| LemmaOneF.lean:176 | `homSolve_hadamard_entry_gen` | [P, C, Q] |
| LemmaOneF.lean:198 | `homSolve_entry_symm_gen` | [P, C, Q] |
| LemmaOneFin.lean:43 | `homOp_apply_fin` | [P, C, Q] |
| LemmaOneFin.lean:48 | `homPairRep_fin_gen` | [P, C, Q] |
| LemmaOneFin.lean:54 | `homPairRep_op_fin_gen` | [P, C, Q] |
| LemmaOneFin.lean:68 | `homPairOmega_fin_gen` | [P, C, Q] |
| LemmaOneFin.lean:75 | `homPairOmega_op_fin_gen` | [P, C, Q] |
| LemmaOneLip.lean:35 | `homLipC_nonneg` | [P, C, Q] |
| LemmaOneLip.lean:56 | `homInv_eq` | [P, C, Q] |
| LemmaOneLip.lean:63 | `norm_homInv_sub` | [P, C, Q] |
| LemmaOneLip.lean:72 | `norm_homInv_sub_le` | [P, C, Q] |
| LemmaOneLip.lean:84 | `homMultLip_of` | [P, C, Q] |
| LemmaOneLipBounds.lean:31 | `homSolveTaylor_Q_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:36 | `homLam_comm_homTP_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:46 | `homLam_comm_homTP'_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:55 | `homLam_comm_homTQ_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:65 | `homPartial_sub_comp_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:73 | `homPartial_clm_sub` | [P, C, Q] |
| LemmaOneLipBounds.lean:93 | `homLipField_b` | [P, C, Q] |
| LemmaOneLipBounds.lean:128 | `homLipField_cp` | [P, C, Q] |
| LemmaOneLipBounds.lean:164 | `homLipField_cm` | [P, C, Q] |
| LemmaOneLipBounds.lean:200 | `homLipField_P` | [P, C, Q] |
| LemmaOneLipBounds.lean:240 | `homLipField_Q` | [P, C, Q] |
| LemmaOneLipBounds.lean:275 | `homLipField_Qt` | [P, C, Q] |
| LemmaOneLipBounds.lean:310 | `homLipField_P'` | [P, C, Q] |
| LemmaOneLipBounds.lean:350 | `homLipField_dcp_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:412 | `homLipField_dcm_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:474 | `homLipField_dP_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:535 | `homLipField_dP'_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:597 | `homLipField_dQ_gen` | [P, C, Q] |
| LemmaOneLipBounds.lean:657 | `homLipField_da` | [P, C, Q] |
| LemmaOneLipBounds.lean:708 | `homLipField_db` | [P, C, Q] |
| LemmaOneLipBounds.lean:788 | `homF_sub_compBounds_gen` | [P, C, Q] |
| LemmaOneLipDiff.lean:32 | `kamEntry_sub'` | [P, C, Q] |
| LemmaOneLipDiff.lean:37 | `norm_homTscal_sub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:51 | `norm_homTvec_sub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:68 | `norm_homTdp_sub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:83 | `norm_homTdm_sub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:98 | `homHadamardCLM_sub` | [P, C, Q] |
| LemmaOneLipDiff.lean:108 | `norm_hadSub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:114 | `norm_homTP_sub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:121 | `norm_homTP'_sub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:128 | `norm_homTQ_sub_le` | [P, C, Q] |
| LemmaOneLipDiff.lean:135 | `norm_homTQt_sub_le` | [P, C, Q] |
| LemmaOneMult.lean:37 | `norm_homInv_le` | [P, C, Q] |
| LemmaOneMult.lean:70 | `homDP_symm` | [P, C, Q] |
| LemmaOneMult.lean:75 | `homDP'_symm` | [P, C, Q] |
| LemmaOneMult.lean:83 | `norm_mult_le_of_bound` | [P, C, Q] |
| LemmaOneMult.lean:91 | `homHadamardBound_of_weight` | [P, C, Q] |
| LemmaOneMult.lean:103 | `homWeightQ_abs` | [P, C, Q] |
| LemmaOneMult.lean:117 | `norm_homMultA0_le` | [P, C, Q] |
| LemmaOneMult.lean:126 | `norm_homMultDp_le` | [P, C, Q] |
| LemmaOneMult.lean:135 | `norm_homMultDm_le` | [P, C, Q] |
| LemmaOneMult.lean:145 | `homDP_bound` | [P, C, Q] |
| LemmaOneMult.lean:165 | `homDP'_bound` | [P, C, Q] |
| LemmaOneMult.lean:185 | `homDQ_norm_le` | [P, C, Q] |
| LemmaOneMult.lean:198 | `homDQ_bound` | [P, C, Q] |
| LemmaOneMult.lean:205 | `homDQt_bound` | [P, C, Q] |
| Lie.lean:41 | `homOmega_le` | [P, C, Q] |
| Lie.lean:58 | `homLie_Omega_mem` | [P, C, Q] |
| Lie.lean:70 | `homLie_pairing_summable_gen` | [P, C, Q] |
| Lie.lean:87 | `homPair0_comm` | [P, C, Q] |
| Lie.lean:103 | `homWeakBracket_eq_neg_lieN` | [P, C, Q] |
| Lie.lean:120 | `homGuard_one_one` | [P, C, Q] |
| Lie.lean:142 | `homNOmega_le_gen` | [P, C, Q] |
| LieDeriv.lean:49 | `norm_homEmbedCoef_le_gen` | [P, C, Q] |
| LieDeriv.lean:72 | `norm_homNcoef_le` | [P, C, Q] |
| LieDeriv.lean:89 | `homNOmegaCLM_apply` | [P, C, Q] |
| LieDeriv.lean:97 | `homNOmega_embed_gen` | [P, C, Q] |
| LieDeriv.lean:114 | `homNOmega_comm` | [P, C, Q] |
| LieDeriv.lean:129 | `homLomega_apply` | [P, C, Q] |
| LieDeriv.lean:152 | `homNfun_hasFDerivAt` | [P, C, Q] |
| LieDeriv.lean:161 | `homDN_apply` | [P, C, Q] |
| LieDeriv.lean:171 | `homLemma_lie_iv_gen` | [P, C, Q] |
| LieDeriv.lean:198 | `homWt_eq` | [P, C, Q] |
| LieDeriv.lean:205 | `homGuard_of_cond` | [P, C, Q] |
| LieDeriv.lean:234 | `not_homGuard_of_lt` | [P, C, Q] |
| Melnikov.lean:67 | `rpow_half_le_self` | [P, C, Q] |
| Melnikov.lean:73 | `HomFreqHyp1.toHyp` | [P, C, Q] |
| NhatTaylor.lean:35 | `kamEntry_diagCLM` | [P, C, Q] |
| NhatTaylor.lean:41 | `isHomComp_const` | [P, C, Q] |
| NhatTaylor.lean:72 | `homNhatTaylor_val_gen` | [P, C, Q] |
| NhatTaylor.lean:98 | `homPartial_const` | [P, C, Q] |
| NhatTaylor.lean:103 | `homNhat_coeff_bounds_gen` | [P, C, Q] |
| NhatTaylor.lean:120 | `homNhat_fieldBound_gen` | [P, C, Q] |
| NhatTaylor.lean:164 | `homLemma1_zero_modes_gen` | [P, C, Q] |
| NormalOps.lean:45 | `homPP` | [P, C, Q] |
| NormalOps.lean:50 | `norm_homLamD_le_gen` | [P, C, Q] |
| NormalOps.lean:64 | `norm_homLamDiag_le_gen` | [P, C, Q] |
| NormalOps.lean:68 | `homLamDiag_apply_gen` | [P, C, Q] |
| NormalOps.lean:75 | `homLamCLM_apply_gen` | [P, C, Q] |
| NormalOps.lean:79 | `norm_homLamCLM_apply_le_gen` | [P, C, Q] |
| NormalOps.lean:84 | `kamEntry_homLamCLM_gen` | [P, C, Q] |
| NormalOps.lean:88 | `homHadamardOp_lam_gen` | [P, C, Q] |
| NormalOps.lean:97 | `norm_homLam_hadamard_le_gen` | [P, C, Q] |
| NormalOps.lean:113 | `homDualNorm_le_gen` | [P, C, Q] |
| NormalOps.lean:119 | `homL2_pair_le` | [P, C, Q] |
| NormalOps.lean:132 | `memℓp_homConj` | [P, C, Q] |
| NormalOps.lean:141 | `norm_homConjL2` | [P, C, Q] |
| NormalOps.lean:150 | `tsum_mul_homConjL2` | [P, C, Q] |
| NormalOps.lean:160 | `norm_le_of_pairing_le` | [P, C, Q] |
| NormalPol.lean:35 | `homPairF_summable` | [P, C, Q] |
| NormalPol.lean:38 | `homPairF_add_left` | [P, C, Q] |
| NormalPol.lean:45 | `homPairF_smul_left` | [P, C, Q] |
| NormalPol.lean:51 | `homPairF_comm` | [P, C, Q] |
| NormalPol.lean:54 | `homPairF_add_right` | [P, C, Q] |
| NormalPol.lean:58 | `homPairF_smul_right` | [P, C, Q] |
| NormalPol.lean:61 | `norm_homPairF_le` | [P, C, Q] |
| NormalPol.lean:71 | `homPairL2_apply` | [P, C, Q] |
| NormalPol.lean:73 | `homPairL2_comm` | [P, C, Q] |
| NormalPol.lean:75 | `homPairL2_single_right` | [P, C, Q] |
| NormalPol.lean:86 | `homCLM_eq_zero_of_basis` | [P, C, Q] |
| NormalPol.lean:101 | `homPairL2_symm_of_entries` | [P, C, Q] |
| NormalPol.lean:123 | `norm_le_of_quadratic` | [P, C, Q] |
| PPlusOne.lean:38 | `homPlusOne_le` | [P, C, Q] |
| PPlusOne.lean:40 | `homPlusOne_pp` | [P, C, Q] |
| PPlusOne.lean:118 | `homComp_angle` | [P, C, Q] |
| PPlusOne.lean:131 | `homComp_first` | [P, C, Q] |
| PPlusOne.lean:139 | `homLemma1_lipschitz` | [P, C, Q] |
| PPlusOne.lean:150 | `homNhat_lipschitz` | [P, C, Q] |
| PPlusOne.lean:156 | `norm_homLamD_mul_le` | [P, C, Q] |
| PPlusOne.lean:162 | `homLemma1_equation_all` | [P, C, Q] |
| PPlusOne.lean:172 | `homXnorm_le_of_components` | [P, C, Q] |
| PPlusOne.lean:180 | `homF_compBounds` | [P, C, Q] |
| PPlusOne.lean:188 | `homLemma1_fieldBound` | [P, C, Q] |
| PPlusOne.lean:196 | `homLam_comm_homTQ` | [P, C, Q] |
| PPlusOne.lean:202 | `homNhatTaylor_val` | [P, C, Q] |
| PPlusOne.lean:208 | `homNhat_fieldBound` | [P, C, Q] |
| PPlusOne.lean:214 | `homLemma1_zero_modes` | [P, C, Q] |
| PPlusOne.lean:222 | `norm_homLamCLM_apply_le` | [P, C, Q] |
| PPlusOne.lean:227 | `homHadamardOp_lam` | [P, C, Q] |
| PPlusOne.lean:233 | `norm_homLam_hadamard_le` | [P, C, Q] |
| PPlusOne.lean:239 | `homSolveTaylor_isReal` | [P, C, Q] |
| PPlusOne.lean:245 | `homNhatTaylor_isReal` | [P, C, Q] |
| PPlusOne.lean:251 | `homLemma1_equation` | [P, C, Q] |
| PPlusOne.lean:260 | `homEq_Q` | [P, C, Q] |
| PPlusOne.lean:272 | `homLipField_dQ` | [P, C, Q] |
| PPlusOne.lean:285 | `homF_sub_compBounds` | [P, C, Q] |
| PPlusOne.lean:297 | `homLemma_lie_iv` | [P, C, Q] |
| PPlusOne.lean:307 | `homDiagonal_bound` | [P, C, Q] |
| PPlusOne.lean:311 | `homNhat_coeff_bounds` | [P, C, Q] |
| PPlusOne.lean:318 | `homLie_pairing_summable` | [P, C, Q] |
| RealF.lean:48 | `homSolveTaylor_isReal_gen` | [P, C, Q] |
| RealF.lean:148 | `homCoeff_zero_im` | [P, C, Q] |
| RealF.lean:156 | `homNhatTaylor_isReal_gen` | [P, C, Q] |
| RealSolve.lean:31 | `homConj_character_real` | [P, C, Q] |
| RealSolve.lean:39 | `homCoeff_conj` | [P, C, Q] |
| RealSolve.lean:50 | `homSolve_conj_real` | [P, C, Q] |
| RealSolve.lean:64 | `conj_homInv` | [P, C, Q] |
| RealSolve.lean:71 | `homPairZ_neg` | [P, C, Q] |
| RealSolve.lean:75 | `homMultA0_conj` | [P, C, Q] |
| RealSolve.lean:85 | `homMultDp_conj` | [P, C, Q] |
| RealSolve.lean:92 | `homMultDm_conj` | [P, C, Q] |
| RealSolve.lean:99 | `homDP_conj` | [P, C, Q] |
| RealSolve.lean:106 | `homDP'_conj` | [P, C, Q] |
| RealSolve.lean:113 | `homDQ_conj` | [P, C, Q] |
| Schur.lean:47 | `homKS_lt` | [P, C, Q] |
| Schur.lean:53 | `one_le_homKS` | [P, C, Q] |
| Schur.lean:63 | `HomHadamardBound.homNonneg` | [P, C, Q] |
| Schur.lean:66 | `HomHadamardBound.dominated` | [P, C, Q] |
| Schur.lean:76 | `HomHadamardBound.schur` | [P, C, Q] |
| Schur.lean:86 | `homHadamardOp_hasSum` | [P, C, Q] |
| Schur.lean:91 | `norm_homHadamardOp_le` | [P, C, Q] |
| Schur.lean:96 | `homHadamard_entry` | [P, C, Q] |
| Schur.lean:110 | `homOp_hasSum` | [P, C, Q] |
| Schur.lean:127 | `homOp_ext_entries` | [P, C, Q] |
| Schur.lean:133 | `kamEntry_add` | [P, C, Q] |
| Schur.lean:137 | `kamEntry_smul` | [P, C, Q] |
| Schur.lean:153 | `homHadamardCLM_apply` | [P, C, Q] |
| Schur.lean:157 | `norm_homHadamardCLM_le` | [P, C, Q] |
| Schur.lean:163 | `homHadamard_transpose_entry` | [P, C, Q] |
| Schur.lean:171 | `norm_homHadamardOp_diag_le` | [P, C, Q] |
| Schur.lean:194 | `homNormalEntry_hadamard_gen` | [P, C, Q] |
| Schur.lean:202 | `ellWeight_succ_exponent` | [P, C, Q] |
| Schur.lean:209 | `ellWeight_div_ellWeight` | [P, C, Q] |
| Schur.lean:218 | `homDiagonal_bound_gen` | [P, C, Q] |
| Solve.lean:50 | `norm_homCoeff_le` | [P, C, Q] |
| Solve.lean:58 | `homCoeff_nonneg_bound` | [P, C, Q] |
| Solve.lean:64 | `homSolve_term_le` | [P, C, Q] |
| Solve.lean:92 | `homSolve_spec` | [P, C, Q] |
| Solve.lean:132 | `homSolve_sub_le` | [P, C, Q] |
| SolveDeriv.lean:45 | `homScalar_torusCoeff_fderiv` | [P, C, Q] |
| SolveDeriv.lean:103 | `homPartial_differentiableOn` | [P, C, Q] |
| SolveDeriv.lean:111 | `homPartial_periodic` | [P, C, Q] |
| SolveDeriv.lean:122 | `homCoeff_partial` | [P, C, Q] |
| SolveDeriv.lean:158 | `fderiv_fourierSumVec_single` | [P, C, Q] |
| SolveDeriv.lean:215 | `homSolve_partial` | [P, C, Q] |
| SolveImage.lean:39 | `homSolve_image_eq` | [P, C, Q] |
| SolveImage.lean:51 | `homSolve_image_bound` | [P, C, Q] |
| SolveImage.lean:66 | `homSolve_partial_image_eq` | [P, C, Q] |
| SolveImage.lean:92 | `homSolve_image_partial_bound` | [P, C, Q] |
| SolveImageSub.lean:33 | `homSolve_image_sub_bound` | [P, C, Q] |
| SolveImageSub.lean:61 | `homSolve_image_partial_sub_bound` | [P, C, Q] |
| SolveLinear.lean:36 | `homTorusAverage_clm` | [P, C, Q] |
| SolveLinear.lean:46 | `homContinuous_restrict` | [P, C, Q] |
| SolveLinear.lean:54 | `homCoeff_clm` | [P, C, Q] |
| SolveLinear.lean:69 | `clm_fourierSumVec_of_summable` | [P, C, Q] |
| SolveLinear.lean:80 | `homSolve_intertwine` | [P, C, Q] |
| SolveLinear.lean:101 | `homSolve_clm` | [P, C, Q] |
| Taylor.lean:79 | `homSqrt2_ne` | [P, C, Q] |
| Taylor.lean:83 | `norm_homSqrt2` | [P, C, Q] |
| Taylor.lean:87 | `homSqrt2_sq` | [P, C, Q] |
| Taylor.lean:111 | `homSqrt2_inv` | [P, C, Q] |
| Taylor.lean:118 | `homRz_eq_gen` | [P, C, Q] |
| Taylor.lean:130 | `homRzb_eq_gen` | [P, C, Q] |
| Taylor.lean:174 | `homXnorm_nonneg_gen` | [P, C, Q] |
| Taylor.lean:183 | `homNorm_le_uv` | [P, C, Q] |
| TaylorSub.lean:32 | `IsHomComp.homSub` | [P, C, Q] |
| TaylorSub.lean:40 | `homPartial_sub` | [P, C, Q] |
| TaylorSub.lean:48 | `homNormalEntry_sub_gen` | [P, C, Q] |
| Wave.lean:42 | `lam_one_lt_two` | [P, C, Q] |
| Wave.lean:46 | `actionA_pos` | [P, C, Q] |
| Wave.lean:52 | `waveFreqTan_sub` | [P, C, Q] |
| Wave.lean:64 | `abs_waveFreqTan_sub_le` | [P, C, Q] |
| Wave.lean:113 | `homFreqHyp1_wave` | [P, C, Q] |
| Wave.lean:150 | `homFreqHyp_wave` | [P, C, Q] |
| WaveReindex.lean:38 | `homSumW_eq` | [P, C, Q] |
| WaveReindex.lean:46 | `homJapW_reindex_nonneg` | [P, C, Q] |
| WaveReindex.lean:68 | `homSum_neg` | [P, C, Q] |
| WaveReindex.lean:74 | `homJap_neg` | [P, C, Q] |
| WaveReindex.lean:78 | `homJapW_neg` | [P, C, Q] |
| WaveReindex.lean:82 | `homL1_neg` | [P, C, Q] |
| WaveReindex.lean:89 | `homJapW_reindex` | [P, C, Q] |
| WaveReindex.lean:154 | `homL1_eq_zero_iff` | [P, C, Q] |
| WaveReindex.lean:167 | `homJap_le_japW_le` | [P, C, Q] |
| WaveReindex.lean:180 | `homMelnikov_of_melnikovW` | [P, C, Q] |
| WaveReindex.lean:191 | `homMelnikovW_of_melnikov` | [P, C, Q] |

## Complete definition-site inventory

The family classifications above apply to each enumerated public definition/alias/structure. No omission from the axiom census is a semantic approval of an unrestricted raw definition.

| Site | Kind | Export (namespace KAM.Wave) |
|---|---|---|
| AngleSupport.lean:36 | def | `homEntryCLM` |
| AngleSupport.lean:43 | def | `homNormEntryCLM_gen` |
| ComponentsFirst.lean:32 | def | `HomFieldBound_gen` |
| Divisors.lean:33 | def | `homMom` |
| DivisorsConcrete.lean:29 | def | `HomDivisorBound` |
| Extract.lean:39 | def | `polyEval2` |
| Index.lean:39 | def | `homWt` |
| Index.lean:56 | def | `HomNormal` |
| Index.lean:60 | def | `homNormLp` |
| Index.lean:64 | def | `homNorm` |
| Lattice.lean:35 | def | `waveS` |
| LatticeBW.lean:31 | def | `waveA` |
| LatticeBW.lean:35 | def | `waveBW` |
| LatticeBW.lean:40 | def | `waveC` |
| LatticeBW.lean:44 | def | `waveBWconst` |
| LatticeCount.lean:31 | def | `waveSphere` |
| Lemma1.lean:129 | def | `homLamNorm` |
| LemmaOneAll.lean:145 | def | `homDiagW_gen` |
| LemmaOneAssembly.lean:35 | structure | `HomCompBounds_gen` |
| LemmaOneEquation.lean:38 | def | `homRval_gen` |
| LemmaOneEquation.lean:49 | def | `homLieN_gen` |
| LemmaOneEquation.lean:57 | def | `homNhat_gen` |
| LemmaOneEquation.lean:63 | def | `homLop` |
| LemmaOneF.lean:38 | structure | `HomMultBounds` |
| LemmaOneF.lean:85 | def | `homTscal` |
| LemmaOneF.lean:89 | def | `homTvec` |
| LemmaOneF.lean:93 | def | `homTdp` |
| LemmaOneF.lean:97 | def | `homTdm` |
| LemmaOneF.lean:101 | def | `homTP` |
| LemmaOneF.lean:104 | def | `homTP'` |
| LemmaOneF.lean:107 | def | `homTQ` |
| LemmaOneF.lean:110 | def | `homTQt` |
| LemmaOneF.lean:224 | def | `homSolveTaylor_gen` |
| LemmaOneFin.lean:34 | def | `homPairOmega_gen` |
| LemmaOneFin.lean:40 | def | `homSent_gen` |
| LemmaOneLip.lean:32 | def | `homLipC` |
| LemmaOneLip.lean:42 | structure | `HomMultLip` |
| LemmaOneMult.lean:35 | def | `homInv` |
| LemmaOneMult.lean:44 | def | `homMultA0` |
| LemmaOneMult.lean:48 | def | `homMultDp` |
| LemmaOneMult.lean:52 | def | `homMultDm` |
| LemmaOneMult.lean:56 | def | `homDP` |
| LemmaOneMult.lean:60 | def | `homDP'` |
| LemmaOneMult.lean:64 | def | `homDQ` |
| LemmaOneMult.lean:68 | def | `homDQt` |
| Lie.lean:85 | def | `homPair0` |
| Lie.lean:93 | def | `homLieSeq` |
| Lie.lean:98 | def | `homWeakBracket` |
| Lie.lean:116 | def | `HomGuard` |
| LieDeriv.lean:43 | abbrev | `HomPhase` |
| LieDeriv.lean:47 | def | `homEmbedCoef_gen` |
| LieDeriv.lean:66 | def | `homEmbed_gen` |
| LieDeriv.lean:70 | def | `homNcoef` |
| LieDeriv.lean:85 | def | `homNOmegaCLM` |
| LieDeriv.lean:126 | def | `homLomega` |
| LieDeriv.lean:133 | def | `homPrZ` |
| LieDeriv.lean:138 | def | `homPrY` |
| LieDeriv.lean:143 | def | `homNfun` |
| LieDeriv.lean:147 | def | `homDN` |
| Melnikov.lean:33 | def | `homPairZ` |
| Melnikov.lean:36 | def | `homL1` |
| Melnikov.lean:39 | def | `homJap` |
| Melnikov.lean:42 | def | `homPairL` |
| Melnikov.lean:45 | def | `homZ` |
| Melnikov.lean:51 | structure | `HomFreqHyp` |
| Melnikov.lean:60 | structure | `HomFreqHyp1` |
| Melnikov.lean:88 | def | `HomMelnikov` |
| Melnikov.lean:94 | def | `homDelta0` |
| Melnikov.lean:97 | def | `homDeltaPlus` |
| Melnikov.lean:101 | def | `homDeltaMinus` |
| Melnikov.lean:105 | def | `homDeltaP` |
| Melnikov.lean:109 | def | `homDeltaP'` |
| Melnikov.lean:113 | def | `homDeltaQ` |
| Melnikov.lean:117 | def | `homWeightQ` |
| NhatTaylor.lean:47 | def | `homNhatTaylor_gen` |
| NormalOps.lean:48 | def | `homLamD_gen` |
| NormalOps.lean:61 | def | `homLamDiag_gen` |
| NormalOps.lean:72 | def | `homLamCLM_gen` |
| NormalOps.lean:106 | def | `homPairRep_gen` |
| NormalOps.lean:110 | def | `homDualNorm_gen` |
| NormalOps.lean:139 | def | `homConjL2` |
| NormalPol.lean:33 | def | `homPairF` |
| NormalPol.lean:66 | def | `homPairL2` |
| PPlusOne.lean:43 | abbrev | `HomTaylor` |
| PPlusOne.lean:46 | abbrev | `homNormalEntry` |
| PPlusOne.lean:48 | abbrev | `homNormEntryCLM` |
| PPlusOne.lean:50 | abbrev | `homLamD` |
| PPlusOne.lean:52 | abbrev | `homLamDiag` |
| PPlusOne.lean:55 | abbrev | `homLamCLM` |
| PPlusOne.lean:58 | abbrev | `homPairRep` |
| PPlusOne.lean:61 | abbrev | `homDualNorm` |
| PPlusOne.lean:64 | abbrev | `homRy` |
| PPlusOne.lean:66 | abbrev | `homRz` |
| PPlusOne.lean:68 | abbrev | `homRzb` |
| PPlusOne.lean:70 | abbrev | `homRu` |
| PPlusOne.lean:72 | abbrev | `homRv` |
| PPlusOne.lean:74 | abbrev | `homRtheta` |
| PPlusOne.lean:78 | abbrev | `homXnorm` |
| PPlusOne.lean:82 | abbrev | `HomFieldBound` |
| PPlusOne.lean:85 | abbrev | `HomTaylor.homSub` |
| PPlusOne.lean:87 | abbrev | `HomTaylor.isRealTaylor` |
| PPlusOne.lean:89 | abbrev | `homRval` |
| PPlusOne.lean:93 | abbrev | `homLieN` |
| PPlusOne.lean:97 | abbrev | `homNhat` |
| PPlusOne.lean:100 | abbrev | `homPairOmega` |
| PPlusOne.lean:103 | abbrev | `homSent` |
| PPlusOne.lean:106 | abbrev | `homSolveTaylor` |
| PPlusOne.lean:110 | abbrev | `homNhatTaylor` |
| PPlusOne.lean:112 | abbrev | `homEmbed` |
| PPlusOne.lean:114 | abbrev | `HomCompBounds` |
| RealF.lean:39 | def | `HomTaylor_gen.isRealTaylor` |
| Schur.lean:39 | abbrev | `HomL2` |
| Schur.lean:42 | abbrev | `HomOp` |
| Schur.lean:45 | def | `homKS` |
| Schur.lean:59 | structure | `HomHadamardBound` |
| Schur.lean:82 | def | `homHadamardOp` |
| Schur.lean:143 | def | `homHadamardCLM` |
| Schur.lean:190 | def | `homNormalEntry_gen` |
| Solve.lean:42 | def | `homCoeff` |
| Solve.lean:46 | def | `homSolve` |
| SolveDeriv.lean:38 | def | `homPartial` |
| Taylor.lean:43 | def | `IsHomComp` |
| Taylor.lean:50 | structure | `HomTaylor_gen` |
| Taylor.lean:77 | def | `homSqrt2` |
| Taylor.lean:93 | def | `homRy_gen` |
| Taylor.lean:96 | def | `homRz_gen` |
| Taylor.lean:100 | def | `homRzb_gen` |
| Taylor.lean:104 | def | `homRu_gen` |
| Taylor.lean:108 | def | `homRv_gen` |
| Taylor.lean:145 | def | `homRtheta_gen` |
| Taylor.lean:157 | def | `homU` |
| Taylor.lean:160 | def | `homV` |
| Taylor.lean:163 | def | `HomDomain` |
| Taylor.lean:167 | def | `homXnorm_gen` |
| TaylorSub.lean:55 | def | `HomTaylor_gen.homSub` |
| Wave.lean:36 | def | `waveFreqTan` |
| Wave.lean:40 | def | `waveFreqNor` |
| Wave.lean:58 | def | `waveMomega` |
| Wave.lean:62 | def | `waveMOmega` |
| WaveReindex.lean:30 | def | `homJapW` |
| WaveReindex.lean:33 | def | `HomMelnikovW` |
