# W4-COMPLETE independent package audit 1

Verdict: **PASS WITH NOTES** for the requested W4 completion exports. No source-fidelity failure found in the four requested clauses. This is an infrastructure/package audit, not a seal of `nlw2` or a re-audit of landed W4-HOMOLOGICAL.

## Scope and revision

Audited `HEAD a6520ca6a05499d666ebafe8c0aeba47699e891f`, compared with `inp 374c4202af6305d3e9616c734679f970da6f7744` using `git diff inp...HEAD`. The comparison contains five new `KAM/Wave/Homological/Complete*.lean` modules, the handoff, and **also** five generated imports in `KAM/Root/Wave.lean`. Thus “ONLY new Complete files” describes the substantive Lean changes, not literally the entire diff. The root change is precisely the five module imports, consistent with the handoff's recorded generator run. No existing Homological module changed. `KAM/Frozen/`, `manifest/`, `KAM.lean`, and `README.md` have empty diffs. No repository file other than this report was edited by this audit; the temporary axiom probe is removed after checking.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the named package-audit brief and W4-COMPLETE handoff, the relevant W4 blueprint clauses, and the Track W statement document `docs/tracks/W/W-STATEMENTS.md` (there is no `docs/tracks/W/statement.md`). There is no new frozen anchor/provider pair here, so provider-type/seal-body probes are inapplicable. Existing W4 results are treated as the previously audited dependencies specified by the user; only their types/definitions needed to understand these new compositions were inspected.

## Source-facing clauses

| Blueprint clause | Exports | Verdict | Reason |
|---|---|---|---|
| `bpW:w4:lie` (iii), lines 518–524 | `homLemma_lie_iii`, `_gen` | PASS | Arbitrary Taylor F, finite normal support, exact seven component rules and finite polynomial expansion. No solve, Melnikov gate, or conclusion-shaped premise. |
| `bpW:w4:lemma1` (i), lines 644–645 | `homLemma1Complete_zero_modes`, `homLemma1Complete_real`, `_gen` versions | PASS | Gate constructed internally from frequency/Melnikov premises; all three zero modes, real F and Nhat, real tangential/normal mean frequencies. |
| `bpW:w4:lemma1` (ii), lines 646–648 | `homLemma1Complete_equation`, `homLemma1Complete_bracket`, `homLemma1Complete_guarded`, `_gen` versions | PASS WITH NOTES | Full strip × all actions × all normal vectors; correct constant term and signs; actual DN used only under G. Carrier/general-p qualifications detailed below. |
| `bpW:w4:lemma2`, lines 743–758 | `homLemma2Complete`, `_gen` | PASS WITH NOTES | Correct two inequalities, domains, lambda range, C1, 3C1<108 and exponent 2tau+3; extended-real best-constant formulation is stronger than finite-bound setting. |

### Lie coefficients

The component operator is `(2*pi)^(-1) sum w_l partial_l g - i lambda g`; the proved Fourier multiplier is `i(<k,w>-lambda)`. Its lambda values are `0, 0, Omega_j, -Omega_j, Omega_i+Omega_j, Omega_j-Omega_i, -(Omega_i+Omega_j)`. These give exactly delta0, deltaPlus, deltaMinus, deltaP, deltaQ, deltaPprime, including zero at `(k,i,j)=(0,j,j)` for Q. In particular the Q sign follows the source monomial `Q_ij z_j zbar_i`.

`homTrueCoord a q x j = x_j / weight(a,q,j+2)` undoes the stored weighted representative. The product identities at CompleteLieExpand:39,48 show that both vector and true matrix coefficients reproduce the existing weighted pairings. The expansion at :169 uses symmetry of P/Pprime and the true transpose of Q at theta in the strip. A single finite S supporting both vectors loses no finitely supported pair (take their union). The main conjunction :304/:356 is for general F and includes every Fourier coefficient identity. Requiring theta in the strip is the source evaluation domain; `0<s` is recovered from that membership. The generic hC is carrier evidence, not an assumed coefficient conclusion; the W4 headline constructs it from the frequency bound.

### Zero modes, reality and equation

CompleteZeroReal:50,79 construct `homMultBounds_of h hAlpha hH hXi` inside the statement. There is no user-supplied multiplier bound or reality of F assumption. Returning `HomTaylor ... (s-sigma)` carries membership in the source Taylor class. The Q zero mode is stated in true entries, not just representative entries. The reality theorem returns both F and Nhat reality and imaginary parts zero for the means of b and the true diagonal of Q. Dropping the unused field bound/radius from these results strengthens the source statement.

CompleteEquation:59 uses actual true gradients and the carrier-guaranteed convergent weak pairings. Its equality to `-L_N F` is proved termwise, rather than defining the bracket to be the desired answer. At :86 the full field includes the theta slot `(2*pi)^(-1) F_y`, y slot `-(2*pi)^(-1) F_theta`, and embedded normal slots `-i F_zbar`, `i F_z`. The guard proof at :95 compares the existing Frechet derivative `homDN` with the source-domain `homLieN_gen`. The theta slot does not affect DN because N is theta independent. The three-way equation retains the constant `a_hat_0` on the correct side and imposes no D(s,r) restriction on its evaluation variables.

Notes on premises and rule 6:

* The original W4 `homLemma1Complete_equation` constructs carrier evidence and proves all three forms from source premises. It has no extra carrier/summability/solution-equation assumption.
* The separate `homLemma1Complete_bracket` takes a proof hC to identify the bracket's proof-indexed argument. This is redundant carrier typing evidence, supplied by `homOmegaCarrier_of_bound`; the combined equation export demonstrates that it is not an unpaid analytic premise. The proof changes hC by definitional equality, not by a new assumption.
* General-p `_gen` equation results require `1 <= p + pb`. These are expressly general-p companions, not unconditional versions of W4 with arbitrary smoothing. At `pb=p+1`, `p>=0` discharges this inequality automatically; all original W4 headlines preserve the source hypotheses. This audit does not certify a stronger unrestricted W5 generalization.
* Conditional algebraic helpers have separate names: `homNormalEntry_gen_eq_zero_of_kamEntry`, `homNhat_coeffs_real_of_isReal`, the `homSum2_swap_*` lemmas, and the CLM coefficient helper. Their explicit algebraic premises are proved where used; none substitutes a conditional statement for a source-facing result.
* `HomFreqHyp` uses the landed weaker j^(1/2) tail assumptions. The blueprint j-tail premise implies it with the **same constants** via `HomFreqHyp1.toHyp` (Melnikov:73). These exports are stronger in frequency hypotheses, not weakened source conclusions.

### Lambda-weighted field norm

`homFieldSup_gen` takes the supremum over all parameters and all points of **HomDomain(s',r)** of the existing `homXnorm_gen`. Its normal term is the sum of u- and v-gradient norms in the smoothing space, not the product max norm on the lower-regularity `HomPhase`. Thus the new full field definition has not silently replaced the source field norm. `HomDomain` uses the source `||u||+||v||<r`, `||y||<r^2`, and complex strip. The field norm includes both period-one factors and the r^-2 and r^-1 scalings (Taylor:163–172).

`homFieldLip_gen` uses distinct parameters and the field of the componentwise subtraction `HomTaylor_gen.homSub`, divided by the max norm of their parameter difference. On the source strip, differentiation and all gradient/bilinear operations are linear in Taylor components (`homPartial_sub` and the subtraction definition), so this is exactly the norm of the difference of fields. There is no same-parameter quotient, extra parameter regularity premise, scalar-Hamiltonian norm, or coefficient norm substitution. The two `_le_ofReal_iff` results prove the best-constant interpretation for nonnegative finite bounds.

`homLamFieldNorm_gen = sup + ofReal(lambda)*lip` is faithful for `r>0, lambda>=0` on the source domains. ENNReal retains infinity for unbounded fields, and uses `0*infinity=0`, so at lambda=0 the expression is precisely the uniform norm even for a non-Lipschitz family. Empty parameter sets and absent distinct pairs have supremum zero. Negative lambda is totalized by ofReal to zero outside the source parameter range; no theorem relies on that extension. Values at nonpositive r or strip choices outside the component's source strip likewise carry no source-norm claim here.

The finite-supremum branches recover pointwise bounds with `ofReal_toReal` and invoke the landed field/Lipschitz estimates. Infinite branches use positive constants to justify multiplication by top. The main proof uses `lambda * (2M/alpha) <= 2`, giving exactly `3*C1*B/alpha`. C1 remains `7+10*homKS`, independent of all family data; the last estimate uses the pinned `waveBWconst tau` and exponent `2*tau+3`. Finite epsilon/epsilonL assumptions are unnecessary in this extended-real strengthening; restricted to the blueprint's finite setting it gives the stated inequalities.

## Every new public declaration

All declarations below are in `KAM.Wave`. Generic helper premises are local algebra/typing assumptions; the source-facing conclusions are the headlines above.

| Node | File:line | Declaration | Verdict | Role / fidelity |
|---|---|---|---|---|
| `bpW:w4:lemma1(ii)` | CompleteEquation:49 | `homOmegaCarrier_true` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:59 | `homWeakBracketN_gen` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:69 | `homWeakBracketN_eq_neg_lieN_gen` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:86 | `homHamField_gen` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:95 | `homDN_hamField_gen` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:112 | `homLemma1Complete_bracket_gen` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:136 | `homLemma1Complete_guarded_gen` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:161 | `homLemma1Complete_equation_gen` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:189 | `homWeakBracketN` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:195 | `homHamField` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:204 | `homLemma1Complete_equation` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:229 | `homLemma1Complete_bracket` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma1(ii)` | CompleteEquation:243 | `homLemma1Complete_guarded` | PASS | Convergent weak bracket, full Hamiltonian field, guarded derivative identification, or source equation composition. |
| `bpW:w4:lemma2` | CompleteLemma2:48 | `homFieldSup_gen` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:55 | `homFieldLip_gen` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:64 | `homLamFieldNorm_gen` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:68 | `homFieldSup_le_ofReal_iff` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:75 | `homPar_norm_sub_pos` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:79 | `homFieldLip_le_ofReal_iff` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:92 | `homWaveBW_pos` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:103 | `homNhat_fieldSup_le` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:117 | `homNhat_fieldLip_le` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:139 | `homSolveFamily_gen` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:145 | `homSolve_fieldSup_le` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:167 | `homSolve_fieldLip_le` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:214 | `homLemma2Complete_gen` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:264 | `homLamFieldNorm` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lemma2` | CompleteLemma2:270 | `homLemma2Complete` | PASS | Best uniform/Lipschitz constants, positive lattice constant, solve family, or exact weighted-norm estimate. |
| `bpW:w4:lie(iii)` | CompleteLie:47 | `homTrueCoord` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:50 | `homTrueCoordCLM` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:53 | `homTrueCoordCLM_apply` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:58 | `homLieComp` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:63 | `homCoeff_homLieComp` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:104 | `homCoeff_homLieComp_clm` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:122 | `homNormalEntry_fun_eq` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:126 | `homTrueCoord_fun_eq` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:131 | `homLieComp_coeff_a` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:139 | `homLieComp_coeff_b` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:148 | `homLieComp_coeff_cp` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:157 | `homLieComp_coeff_cm` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:165 | `homLieComp_coeff_P` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:175 | `homLieComp_coeff_Q` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLie:185 | `homLieComp_coeff_P'` | PASS | True-coordinate/CLM interpretation or exact scalar Fourier multiplier, specialized to the named source component. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:39 | `homTrueCoord_mul_eq` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:48 | `homNormalEntry_mul_eq` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:61 | `homRval_fin_true_gen` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:80 | `homPartial_trueCoord` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:86 | `homPartial_normalEntry` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:94 | `homPartial_proj` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:102 | `homLieComp_vec_term` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:118 | `homLieComp_mat_term` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:137 | `homSum2_swap_sym` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:145 | `homSum2_swap_trans` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:169 | `homLieN_fin_expansion_gen` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:304 | `homLemma_lie_iii_gen` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lie(iii)` | CompleteLieExpand:356 | `homLemma_lie_iii` | PASS | Weighted-to-true conversion, derivative linearity, finite algebra, or full general-F coefficient expansion. |
| `bpW:w4:lemma1(i)` | CompleteZeroReal:41 | `homNormalEntry_gen_eq_zero_of_kamEntry` | PASS | Zero modes/reality; true-entry conversion or distinctly named conditional helper as appropriate. |
| `bpW:w4:lemma1(i)` | CompleteZeroReal:50 | `homLemma1Complete_zero_modes_gen` | PASS | Zero modes/reality; true-entry conversion or distinctly named conditional helper as appropriate. |
| `bpW:w4:lemma1(i)` | CompleteZeroReal:63 | `homNhat_coeffs_real_of_isReal` | PASS | Zero modes/reality; true-entry conversion or distinctly named conditional helper as appropriate. |
| `bpW:w4:lemma1(i)` | CompleteZeroReal:79 | `homLemma1Complete_real_gen` | PASS | Zero modes/reality; true-entry conversion or distinctly named conditional helper as appropriate. |
| `bpW:w4:lemma1(i)` | CompleteZeroReal:92 | `homLemma1Complete_zero_modes` | PASS | Zero modes/reality; true-entry conversion or distinctly named conditional helper as appropriate. |
| `bpW:w4:lemma1(i)` | CompleteZeroReal:103 | `homLemma1Complete_real` | PASS | Zero modes/reality; true-entry conversion or distinctly named conditional helper as appropriate. |

## Definition classification

* `homTrueCoord`: exact inverse weight coordinate; weights are strictly positive for all real a,q, so no zero-divisor fallback.
* `homTrueCoordCLM`: the same coordinate as a bounded linear functional, checked by its apply theorem.
* `homLieComp`: literal differential/multiplication expression; derivative evaluation is used under source differentiability in the coefficient and expansion theorems.
* `homWeakBracketN_gen`: actual source weak bracket with convergent pairings; no junk tsum branch because hC supplies summability on the full vector carrier.
* `homHamField_gen`: actual full Hamiltonian field in stored coordinates, with correct continuous embedding of normal gradients.
* `homFieldSup_gen`, `homFieldLip_gen`, `homLamFieldNorm_gen`: extended-real best constants described above; no unbounded real-supremum fallback.
* `homSolveFamily_gen`: pointwise landed solution, with multiplier evidence constructed from source assumptions at each subtype parameter; no choose/default family.
* `homWeakBracketN`, `homHamField`, `homLamFieldNorm`: exact `pb=p+1` specializations of the general definitions.

No new structure or hidden typeclass assumption. Definitions that must unfold are in the exposed public noncomputable sections.

## Validation

All invocations were serialized. The user-specified D53 cap supersedes the generic brief's priority: `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>`. The lint script and its Lean children ran inside that scope; builds use `w_build.sh`, whose per-module command has exactly that wrapper and takes the compile gate.

1. `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpl`: **exit 0**, output:

```text
check_lean_modules: PASS (3758 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The ABI output explicitly excludes the opt-in band theorems from elaboration in this run; those were checked by file hash only. No certificate application was built.

2. `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/maud-wpl-1.lean`: **exit 0**. The probe imports the five new modules and issues `#print axioms KAM.Wave.<name>` for each of the 50 new public theorems in the declaration table. Exactly 50 result lines; all report the same allowed axiom set, no other output:

```text
'KAM.Wave.homOmegaCarrier_true' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homWeakBracketN_eq_neg_lieN_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homDN_hamField_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_bracket_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_guarded_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_equation_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_guarded' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homFieldSup_le_ofReal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homPar_norm_sub_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homFieldLip_le_ofReal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homWaveBW_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNhat_fieldSup_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNhat_fieldLip_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homSolve_fieldSup_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homSolve_fieldLip_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma2Complete_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma2Complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homTrueCoordCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homCoeff_homLieComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homCoeff_homLieComp_clm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNormalEntry_fun_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homTrueCoord_fun_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_coeff_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_coeff_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_coeff_cp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_coeff_cm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_coeff_P' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_coeff_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_coeff_P'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homTrueCoord_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNormalEntry_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homRval_fin_true_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homPartial_trueCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homPartial_normalEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homPartial_proj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_vec_term' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieComp_mat_term' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homSum2_swap_sym' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homSum2_swap_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLieN_fin_expansion_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma_lie_iii_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma_lie_iii' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNormalEntry_gen_eq_zero_of_kamEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_zero_modes_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homNhat_coeffs_real_of_isReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_real_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_zero_modes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma1Complete_real' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpl KAM.Wave.Homological.CompleteZeroReal KAM.Wave.Homological.CompleteEquation KAM.Wave.Homological.CompleteLemma2`: **exit 0**, three serial capped/gated targeted builds (the CompleteEquation import closure includes CompleteLie and CompleteLieExpand). Exact gate/success lines:

```text
[w_build] slot 3: KAM.Wave.Homological.CompleteZeroReal (04:29:31)
Build completed successfully (3304 jobs).
[w_build] slot 3: KAM.Wave.Homological.CompleteEquation (04:29:36)
Build completed successfully (3306 jobs).
[w_build] slot 3: KAM.Wave.Homological.CompleteLemma2 (04:29:41)
Build completed successfully (3304 jobs).
```

These are successful incremental build checks using the existing artifacts, not claims that every dependency was freshly recompiled. Build output also replays pre-existing PPlusOne tactic-linter warnings; no new Complete module warning or error was reported. No default-heartbeat elaboration failure or memory-cap failure was observed.

4. Kernel replay and public short-name checks: the user says these were already run by the launcher, whose output is unavailable in this turn. Not rerun; no independently observed replay exit code or name-check output is asserted. This uses the user's explicit allowance to avoid repeating replay, not an inference from the axiom probe.

5. `git diff --check inp...HEAD`: exit 0, no output. New-file static forbidden-token scan: no matches; line counts 258, 285, 196, 402, 112 for CompleteEquation, CompleteLemma2, CompleteLie, CompleteLieExpand, CompleteZeroReal respectively. Headers/module/imports/docstrings/public sections checked; no forbidden escapes, override, provider/root imports, or oversized file in the new modules. The only protected/generated-path delta is the documented generated `KAM/Root/Wave.lean` import list. Initial working tree was clean.


## Uncertainties, errata and deviations

No new suspected blueprint defect or pinned-source erratum found in this delta. The source's previously declared deviations (Banach Fourier route, B^W, constants, constant term and period-one factors) are preserved; this audit does not reopen them or independently re-read P96-K. The handoff's excluded continuity portion of `bpW:w4:lie` (i) remains outside this completion scope. No graph node outside the four requested clauses is certified by this report.

The generated root diff and the stronger/weaker-assumption conventions above are documented scope/representation notes, not source-result failures. The brief's provider-seal procedure is inapplicable to this additive infrastructure package. Launcher replay/name-check results were not visible; they are not claimed here as independently observed outputs.

## Byte scope

| File | SHA256 |
|---|---|
| `KAM/Wave/Homological/CompleteEquation.lean` | `a32b498160720a094d3cc59cfc0c68e0af81026a144f19f3ebd00dc999619b32` |
| `KAM/Wave/Homological/CompleteLemma2.lean` | `3f236c5d418eeb413c14cf3452fb2bbaace609b9297da3f8f750de35b54949b3` |
| `KAM/Wave/Homological/CompleteLie.lean` | `dcef7504615b4283d8d75bda403e82c7a0859178d5f0935dc4151cc02273c38e` |
| `KAM/Wave/Homological/CompleteLieExpand.lean` | `1fe69ad6b259f9e10fb95a4b180f4824f8065ae6501452c0995e7802a80810f9` |
| `KAM/Wave/Homological/CompleteZeroReal.lean` | `593f845fda7868af9a6338972611755759c0cd4b027168c5766e98d1801a7e4b` |
| `blueprint-W/parts/w4-homological.tex` | `d5c2d6de2b8317b34fc0745600b48616345db1e45acd3d6ea3b5742ac71a6baa` |
