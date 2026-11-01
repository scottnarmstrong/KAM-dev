# W5-AA independent audit 1

**Overall verdict: FAIL (F1, public-definition carriers).** The source-weight theorem statements/proofs for `bpW:w5:action-angle` (i)–(vi) and `bpW:w5:initial` pass their comparison, with hygiene notes, but the package does not pass the required whole-carrier definition audit. Four exported series definitions accept parameters where their series diverge. Builds and axiom checks succeed; neither fixes this semantic defect. No frozen `nlw2` sealing or step-theorem approval is claimed.

## Scope, snapshot, and authority

Audit date: 2026-11-01 UTC. Tier 2 focused source/package audit, full round 1 of item 3 only. Checkout `/root/code/KAM-inp-wpja5b` resolves to `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpja5` (also named `/root/code/KAM-inp-wpja5`). Audited HEAD `7185220102d1fbbee3c11b78b2f19569818d8a3e`; live `inp` at comparison time `d3a2c262b6b99851b768298de443febdd8630cb5`; merge base `ba0ef7f41f06f24d16b542e3f9852c70ccb59696`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, W5-R2-handoff.md item 3, and the W5-AA proper handoff. `docs/tracks/W/statement.md` from the generic brief does not exist; the actual frozen wave definitions and `docs/tracks/W/W-STATEMENTS.md` are the relevant statement surface. The checkout's DECISIONS ends at D51; the current prompt supplies binding D53 and D60. The explicit worktree report destination and item-3 scope override the generic brief's main-worktree destination and provider-oriented template.

`git diff inp...HEAD` has 135 files / 22686 additions, including earlier W5 infrastructure. Only the eleven `ActionAngle*` / `Initial*` modules (3207 lines total, each at most 430 lines) are reviewed as new implementation. The two handoffs identify the source claims. Step delta items 1–2, W6/W8 consumers and prior W3/W4 package proofs are not re-audited; dependencies are checked at the interfaces used here. No provider or frozen theorem is supplied by this package; provider/frozen-type and seal-copy probes are N/A.

Source: `blueprint-W/parts/w5-kamstep.tex`, SHA256 `d8daf4af9d63da34ae860d2ce9aeefec0a5fe8e7d603cdddb26af6f463e5153c`, standing conventions lines 33–39, action-angle statement lines 614–659 and proof 661–694, initial statement/proof lines 696–731. The source and the audited modules remain byte-identical at closeout. During validation, the parallel part-A auditor advanced the shared HEAD to `459f66582017a74a08ea457e9092538ae5437940` with only `docs/tracks/W/audits/W5-R2A-audit-2.md` added. `git diff --stat 71852201..459f6658` confirms this documentation-only delta; all eleven module hashes and the blueprint hash still match the snapshot. I did not make that commit or review its out-of-scope conclusions.

| File under KAM/Wave/KamStep | Lines | SHA256 |
|---|---:|---|
| ActionAngle.lean | 425 | `c722f3fe87a273ba5654af95278c2baab027be4c6a41c29f3968294f76db7ddc` |
| ActionAngleConj.lean | 234 | `15dcc8f29cd440fdd9681e9bdaf8b9f4796e22573ea8d5cc08b4f6d4fd1cec53` |
| ActionAngleDeriv.lean | 348 | `49e595a046e428d40548f50bfbb470fd49aacaa5854015b16b8391d060f9a078` |
| ActionAngleDomain.lean | 235 | `2e247595a8045cfc7b2f18901fa41494e595a68357bd0bb706367c1df00e4cf9` |
| ActionAngleField.lean | 274 | `2b1b6edcb5ca3493b8efcc021db66f99f7468b3db8610c2ca4e6376026004b4b` |
| ActionAngleGbar.lean | 235 | `93b1c5ffeaf0ae7be6b4aceee2b81594ca9d9a8d8bd85c0cbb66b40d3959277c` |
| ActionAngleNormal.lean | 290 | `a43e7aa4925a25301acb81aa219a159e11d333fbb235fb5cbd2359aa32a1eb36` |
| ActionAngleQt.lean | 253 | `8a257cfa47a9053045817f7a19877ec09a65932fd1bd60d3e4ba16bca704e2ba` |
| ActionAngleSymp.lean | 225 | `afaa0f05a424fa7168d697b3829a3788df0f2222437709ff1b1f9bd21aaf4ddc` |
| Initial.lean | 258 | `034774aef4bbbef8c436d933714659d33d380836efc48345d3771ec64829cfc8` |
| InitialBound.lean | 430 | `3ae43c124aed92215c3d4551069b531d4f7d75cdb53d7e7b8dd3297e00a1b3ea` |

## Per-label verdict

| Anchor / source label | Overall | Theorem component | Definition component |
|---|---|---|---|
| bpW:w5:action-angle (i)–(vi) | FAIL | PASS WITH NOTES at the source weights a=p=1 | F1: aaNfun, aaQt, aaGbarR, birkOmegaMix have overbroad public carriers |
| bpW:w5:initial | PASS WITH NOTES in its fixed-weight statement | PASS WITH NOTES; source-only frequency witness compiles | aaEpsIn, aaPfun and aaXP used here have the required source guards; this does not repair F1 in their auxiliary dependencies |

## Source reconstruction and result ledger

Standing source weights are **a=p=1**. More general Lean results with `0≤a`, `p≥1/2` or arbitrary q are extensions; these guards do not add a premise to the fixed-weight source result. The carriers are weighted representatives: `KamPhase = ℂ²×ℂ²×ℓ²×ℓ²`, `BirkSpace = ℓ²(Bool×ℕ+)`. Normal representatives are at Dirichlet J=j+2. `homWt a q j = ellWeight a q (j+2)`. Finite-dimensional norms are sup norms; normal Birkhoff norm is Hilbert, KAM normal norm is a sum.

The source formula is A_{±i}=√(ξ_i+y_i) exp(∓2πiθ_i), A_{±J}=(u_{J−2}±iv_{J−2})/√2 in actual coordinates. Physical coordinates are obtained by dividing stored coordinates by their weights. The derivative tangential block is `(Y/(2√(ξ+y))∓2πi√(ξ+y)Θ)exp(∓2πiθ)`; both explicit inverse identities are proved. The form is the mixed bilinear pairing, with tangential factor 2π. Normal form and conjugacy retain the normal z*zbar terms, the explicit W3 remainder, and the p+1→p−1 embeddings.

| Source clause/node | Declaration (all in KAM.Wave) | Verdict | Evidence / reason |
|---|---|---|---|
| (i) | `aaMap_differentiableOn` (ActionAngle.lean:264) | PASS | Joint complex holomorphy on the open aaDomJ, not merely fixed-parameter holomorphy. |
| (i) | `aaMap_add_tau` (ActionAngle.lean:299) | PASS | Period-one translation in each angle; stronger global formula identity. |
| (i) | `aaMap_real` (ActionAngle.lean:326) | PASS | StepReal and positive real ξ+y imply birkRho-fixed image. |
| (i) | `aaMap_linearTorus` (ActionAngle.lean:373) | PASS | Exact equality to complexified frozen linearTorus, including √2 and minus sine. |
| (ii) | `aaMap_domain` (ActionAngleDomain.lean:174) | PASS | c_A=2200; strict norm-square bound and Re(ξ+y)>r²; omits unused 0<s. |
| (ii) | `aaMap_mem_ball` (ActionAngleDomain.lean:216) | PASS | Actual open ball with radius √(c_A(t+r²)). |
| (ii) | `aaMap_mem_birkBall1` (ActionAngleDomain.lean:223) | PASS | W3 ball membership supplied by the explicit smallness assumption. |
| (iii) | `hasFDerivAt_aaMap` (ActionAngleDeriv.lean:188) | PASS | aaDer is the actual Fréchet derivative at weight p. |
| (iii) | `aaDerInv_aaDer` (ActionAngleDeriv.lean:278) | PASS | Left inverse on every q-representative space. |
| (iii) | `aaDer_aaDerInv` (ActionAngleDeriv.lean:315) | PASS | Right inverse on every q-representative space. |
| (iii) | `aaDer_symp` (ActionAngleSymp.lean:167) | PASS | Mixed q,q′ form; summability under q+q′≥0; no erased weight embeddings. |
| (iv) | `aaMap_normalForm` (ActionAngleNormal.lean:215) | PASS | Exact H′∘A=e+N+P, with subtype K on the W3 ball. |
| (iv) | `aaOmega0_ofReal` (ActionAngleNormal.lean:104) | PASS | Tangential complex frequencies identify with waveFreqTan. |
| (iv) | `aaOmegaN0_ofReal` (ActionAngleNormal.lean:113) | PASS | Normal complex frequencies identify with waveFreqNor at J=j+2. |
| (v) | `aaQt_hasFDerivAt` (ActionAngleQt.lean:210) | PASS | Actual derivative and Hamiltonian pairing of explicit polynomial Q̃. |
| (v) | `aaP_isSmoothing` (ActionAngleField.lean:209) | PASS | Full IsSmoothing on D(s,r), including holomorphy of scalar and p+1 field. |
| (v) | `aaPfun_real` (ActionAngleField.lean:236) | PASS | Real scalar perturbation on its guarded source domain. |
| (v) | `aaPfun_add_tau` (ActionAngleField.lean:227) | PASS | Periodic perturbation, formula valid globally. |
| (v) | `aaConjugacy` (ActionAngleConj.lean:125) | PASS | Full vector identity in W^(p−1), with inclusions from p+1 explicit. |
| (vi) | `aaNormal_norm_le` (ActionAngleDomain.lean:70) | PASS | First half of the sum/Hilbert normal norm comparison. |
| (vi) | `aaNormal_norm_ge` (ActionAngleDomain.lean:77) | PASS | Second half, factor √2. |
| initial/i-q | `kamNorm_aaXQt_le` (InitialBound.lean:263) | PASS | Polynomial field ≤r² in p+1=2 KAM norm. |
| initial/i-g | `kamNorm_aaDerInv_normal_le` (InitialBound.lean:103) | PASS | Conditional zero-tangential inverse estimate; tangential vanishing proved at use. |
| initial/i-k | `kamNorm_aaDerInv_le` (InitialBound.lean:119) | PASS | Inverse estimate 3/r+2√T/r², with T supplied as t+r². |
| initial | `kamNorm_aaXP_le` (InitialBound.lean:374) | PASS | Exact ε_in with W3 constant C′_K=66 C_* C_F. |
| initial/i-par | `aaXP_lipschitz` (Initial.lean:158) | PASS | 4ε_in/ρξ in the p+1 KAM norm; no assumed Lipschitz bound. |
| initial | `initialPerturbation` (Initial.lean:219) | PASS | All six conclusion groups; removed 0<s and r≤1 strengthen the source statement. |

Clause (vi)'s second comparison `‖x‖_E≤‖Zx‖≤√2‖x‖_E` is intentionally reused from W3 (`norm_le_norm_birkZ`, `norm_birkZ_le`, Birkhoff/Coords.lean), not re-proved. At the torus, `birkReal (linearTorus ξ hξ θ)` is the complex inclusion of the actual frozen real torus, not a changed torus.

For initial, `ε_in=(1+2C_*)r²+66C_*C_F(c_A(t+r²))^(5/2)(3/r+2√(t+r²)/r²)`. The constants depend on m exactly as W3 allows; c_A is the absolute literal 2200. The parameter-Lipschitz constant is uniform in ξ,w. `FamBound` expands to existential nonnegative ε₀,ε₁ with ε₀+λ ε₁≤ε, a uniform field bound, and a uniform difference bound. The proof provides ε₀=ε_in and ε₁=4ε_in/ρξ. No norm or supremum is silently replaced.

`HomFreqHyp1` expands to nonnegative M₀,Mω,MΩ, j-weighted frequency tail about j+2, tangential Lipschitz, and j-weighted normal Lipschitz. Its weight is j, exactly the existing W4 frequency interface; it is not the weaker j^(1/2) version. The `∀ B≥0, (∀ξ∈Π, |<b,ξ>|≤B) → ...` conjunct is a uniform specialization, not an extra outer theorem premise. A compiled scratch witness produces B=3t/2 from hPar and `norm_aaBdot_le`; hence the unconditional source frequency clause is obtainable without new data. `aaOmega0_ofReal` / `aaOmegaN0_ofReal` give the needed frequency identifications. The final tangential Lipschitz conclusion uses `measNA` from the source frequency-coordinate interface.

## Expanded binder audit (rule 6)

Bins: T=TYPING; S=SOURCE; A=STANDING; R=RULED; E=EXCESS. Binders are enumerated individually in each cell; a shared parameter is counted for each declaration it occurs in. None of the source-facing theorems has a user-supplied result bundle, field bound, inverse, derivative identity, smoothing conclusion, or frequency hypothesis.

| Source-facing declaration(s) | T binders | S logical binders | A binders | R / E |
|---|---|---|---|---|
| aaMap_differentiableOn | a,p | none | none | 0 / 0 |
| aaMap_add_tau | a,p,ξ,w,k | none | none | 0 / 0 |
| aaMap_real | a,p,ξ,w | hw=StepReal w; hpos=∀i,0<ξ_i+Re y_i | none | 0 / 0 |
| aaMap_linearTorus | ξ,θ | hξ=∀i,0<ξ_i | none | 0 / 0 |
| aaMap_domain; aaMap_mem_ball | s,r,t,ξ,w | hs≤1/8; hr>0; ht>0; hξ=‖ξ‖≤t; hre=∀i,2r²≤Re ξ_i; hw∈D(s,r) | none | 0 / 0 |
| aaMap_mem_birkBall1 | m,s,r,t,ξ,w | hs;hr;ht;hρ₁=c_A(t+r²)<ρ₁²;hξ;hre;hw as above | hm>0 | 0 / 0 |
| hasFDerivAt_aaMap | a,p,ξ,w | hw=∀i,0<Re(ξ_i+y_i) | none | 0 / 0 |
| aaDerInv_aaDer | a,q,ξ,w,W | hw=positive real part | none | 0 / 0 |
| aaDer_aaDerInv | a,q,ξ,w,V | hw=positive real part | none | 0 / 0 |
| aaDer_symp | a,q,q′,ξ,w,W,W′ | hqq′=0≤q+q′;hw=positive real part | ha=0≤a | 0 / 0 |
| aaMap_normalForm | m,a,p,ξ,w | h=Aξw∈Bρ₁ | hm>0;ha=0≤a;hp=1/2≤p | 0 / 0 |
| aaOmega0_ofReal | m,ξ,i | none | hm>0 | 0 / 0 |
| aaOmegaN0_ofReal | m,ξ,j | none | hm>0 | 0 / 0 |
| aaQt_hasFDerivAt | m,a,p,w | none | hm>0;ha=0≤a;hp=0≤p | 0 / 0 |
| aaP_isSmoothing | m,s,r,t,ξ | hs;hr;ht;hρ₁;hξ;hre as in (ii) | hm>0 | 0 / 0 |
| aaPfun_add_tau | m,a,p,ξ,w,k | none | hm>0;ha=0≤a;hp=1/2≤p | 0 / 0 |
| aaPfun_real | m,a,p,ξ,w | hw=StepReal;hpos=positive real part;hB=Aξw∈Bρ₁ | hm>0;ha=0≤a;hp=1/2≤p | 0 / 0 |
| aaConjugacy | m,a,p,ξ,w | hw=positive real part;hB=Aξw∈Bρ₁ | hm>0;ha=0≤a;hp=1/2≤p | 0 / 0 |
| aaNormal_norm_le; aaNormal_norm_ge | w | none | none | 0 / 0 |
| kamNorm_aaXQt_le | m,s,r,w | hr>0;hw∈D(s,r) | hm>0 | 0 / 0 |
| kamNorm_aaXP_le | m,s,r,t,ζ,w | hs;hr;ht;hρ₁;hζ;hre;hw | hm>0 | 0 / 0 |
| aaXP_lipschitz | m,s,r,t,ρξ,Par,ξ,ξ′,w | hs;hr;ht;hρξ>0;hPar (expanded below);hρ₁;hξ∈Par;hξ′∈Par;hw∈D | hm>0 | 0 / 0 |
| initialPerturbation | m,s,r,t,ρξ,Par | hs;hr;ht;hρξ>0;hPar (expanded below);hρ₁ | hm>0 | 0 / 0 |

`StepReal w` expands to real θ,y,u,v (every coordinate has zero imaginary part), precisely source reality. hPar has exactly the source tube condition, expanded as follows, with no other fields:

| Expanded hPar binder/condition | Bin | Source |
|---|---|---|
| ζ:Fin 2→ℂ | T | complex parameter in w5-kamstep.tex:698–699 |
| ∃ ξ∈Par, ‖ζ−aaOfReal ξ‖<ρξ (antecedent of implication) | S | “for some ξ∈Π” in the same lines |
| ∀ i:Fin 2, 2r²≤Re ζ_i | S | real-part margin in line 699 |
| ‖ζ‖≤t | S | sup norm bound in line 699 |

Counting outer logical assumptions of initialPerturbation after splitting hPar's two conclusions: S=7, A=1, R=0, E=0; outer data binders T=6. The nested tube antecedent and ζ are separately enumerated above, not additional assumptions on Π. Implicit binders in the fixed concrete normed spaces are the existing standard instances; there are no extra project typeclasses to unbundle.

The distinct helper `hasFDerivAt_comp_aaMap` assumes a derivative and Hamiltonian pairing of a general G. Those are appropriate *conditional helper* inputs, not the source result: aaP_isSmoothing_of actually constructs them from W3's proved class-A and K-field interfaces. Its V-open/domain hypotheses are supplied by kamDomain_isOpen and (ii). The normal inverse estimate's htan is discharged by birkQuartX_tangential. Other coordinate/summability/calculus helpers are individually inventoried below; none is substituted for an endpoint while retaining its proof obligation as a new source premise.

## Definition classification

Every new definition/abbreviation appears in the declaration inventory. There are 47, no new structures and no project choice of an unproved witness. Classifications:

| Definitions | Classification and whole-carrier meaning |
|---|---|
| aaSqrt; aaS; aaE; aaTanCoord | Literal principal cpow root and exponentials; source root branch is Re>0. cpow's total formula is not asserted to be a holomorphic branch outside that domain. |
| aaShiftFun; aaShift; aaUnshift | Literal zero insertion at J=1,2 and index shift/restriction J=j+2; the zero branch is the specified absence of normal modes, not an analytic fallback. |
| aaNormal; aaTan; aaTanBuild; aaMap | Explicit continuous normal map and finite tangential sum; all source-coordinate equations proved. The same formula defines the total map; only its source domain is used for analytic/inverse conclusions. |
| aaDomJ | Exact open positive-real-part domain. |
| aaDerTanL; aaDer; aaEv; aaInvTheta; aaInvY; aaDerInv | Explicit derivative/inverse formulas on representatives; divisions are nonzero where used, by positive real part and strictly positive weights. Outside that domain no inverse claim is made. |
| aaCA | Absolute literal 2200. |
| aaBdot; aaEnergy; aaOmega0; aaOmegaN0; aaZZ | Literal finite/pair coordinate formulas and source frequency formulas. |
| aaNfun; aaQt; aaGbarR; birkOmegaMix | **FAIL (F1)**: literal series syntax, but the *declared* public weight carriers are unrestricted and include divergent series. Convergence proved only for guarded source ranges does not validate those complete definition carriers. |
| aaKext; aaXKext | Deliberately named auxiliary zero extensions of the subtype-defined W3 maps, not replacements for the source K off its domain. isExtension is proved immediately; every substantive use establishes ball membership and reduces to the original subtype map. No derivative or bound is obtained from the outside-zero branch. |
| aaPfun; aaXP | Literal perturbation sum and explicit pulled-back field. Their meaning as a Hamiltonian/field is proved on the open source domain with Aξw∈Bρ₁. |
| aaCoefC; aaCoefD; aaCoefE | Explicit quartic coefficients and exact weight ratios. |
| aaBq; aaSfun; aaDiagE; aaXQt | Bounded quadratic form and diagonal polynomial field; equality to series and Hamiltonian characterization proved, not assumed. |
| aaPrY; aaPrU; aaPrV; aaOfReal | Standard projections and real-to-complex inclusion, faithful on their whole carriers. |
| aaXNcoef; aaXNdiag; aaXN | Explicit Ω/(j+2) multiplier representing the p→p−1 normal field; boundedness proved. |
| aaEpsIn | Literal source bound with fixed W3 constants and c_A=2200. |

For F1's four definitions: BODY_MATCH=FAIL on the whole declared carrier (divergent sum totalizes to zero); PUBLIC_CARRIER=FAIL; WELL_DEFINEDNESS=FAIL on that carrier; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=FAIL. For the other literal definitions: BODY_MATCH=OK on the explicit formula/domain; PUBLIC_CARRIER=OK as the separately named literal/auxiliary object; WELL_DEFINEDNESS=N/A_LITERAL or supplied bounded-operator construction; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.

The named zero extensions aaKext/aaXKext are a separate case: they explicitly define an auxiliary extension of an existing subtype map and prove agreement on that subtype. They are not approved as globally analytic source K/X_K. The principal cpow and coordinate-formula helpers similarly carry no global branch/inverse claim. In contrast, F1 definitions name the source series object itself and expose unconstrained weight inputs without an alternative mathematical object/extension characterization. “Only use the good inputs” does not satisfy the brief's whole-carrier definition check.

## Refutation pass and notes

### F1 — exported source series have broader carriers than their convergence domain (FAIL; survived refutation)

At HEAD above:

- ActionAngleNormal.lean:64–66: `def aaNfun (a p : ℝ) ... := ... + ∑' j, aaOmegaN0 ... (j+2) * aaZZ a p w j`.
- ActionAngleNormal.lean:68–71: `def aaQt (a p : ℝ) ... := ... + ∑' j, 3 * aaBdot ... / (2 * Real.pi * lam ... (j+2)) * aaZZ a p w j`.
- ActionAngleGbar.lean:38–39: `def aaGbarR (a p : ℝ) ... := ∑' J, if 3 ≤ (J : ℕ) then ... * birkAction a p w' J else 0`.
- ActionAngleSymp.lean:36–37: `def birkOmegaMix (a q q' : ℝ) ... := I * ∑' l, ... * birkCoord a q y l * birkCoord a q' y' (birkNeg l)`.

These inputs contain no a/p/sum-of-exponents guard. The definitions are source formulas at valid weights; the problem is their complete exported carrier. Source w5-kamstep.tex:33 fixes “Throughout a=p=1”; lines 620–626 define A into the intended weighted phase space; lines 641–648 define N and Q̃ as convergent Hamiltonian sums. The declared Lean series additionally accept the following inputs, where the mathematical series do not exist:

**Counterexample for N and Q̃.** Fix m=1, a=0, p=−1. Let J=j+2 and take real representatives `u_j=1/J`, `v_j=0`, θ=0. This is an admissible HomL2 input since Σ_{J≥3}1/J²<∞. Here homWt(0,−1,j)=1/J and aaZZ=1/2 at every j. For N take ξ=0 and y=0. Its normal summands are λ_J/2>0, which do not tend to zero. For Q̃ take y=(1,0). Then aaBdot(y)=1/λ₁>0 and the normal terms are `3/(4π λ₁ λ_J)`. Since `J≤λ_J=√(J²+1)≤√2 J`, their sum diverges by comparison with the harmonic series. Multiplying u by any fixed positive factor and y by any small positive factor leaves divergence, so this is not cured by small-radius inputs.

**Counterexample for aaGbarR.** At a=0,p=−1 choose `w'_(+,J)=w'_(-,J)=1/J` for J≥3 and zero at J=1,2. This belongs to BirkSpace. Actual birkCoord equals 1 on both normal signs, so birkAction=1, while `birkActionB(J,i)=3/(2π λ_J λ_i)`. The normal series again diverges harmonically.

**Counterexample for birkOmegaMix.** Let a=0,q=q'=−1. Let y have coordinates 1/J on the positive sign and zero on the negative sign; let y' have the reverse support with values 1/J (J≥3, zero otherwise). Both are ℓ². The actual coordinates after division by weight J^(−1) equal 1. Every positive-sign pairing term is 1 and every negative-sign term is 0. The series diverges. Lean's totalized `tsum` assigns zero to these divergent series; it is not the source Hamiltonian/pairing.

**Independent adversarial recheck:** tried (a) the standing a=p=1 convention, (b) the hypotheses of summable_norm_lam_aaZZ/summable_coef_aaZZ, summable_aaGbarR and summable_birkOmegaMix, (c) the producer's explicitly guarded theorem uses, and (d) the zero-extension helper explanation. All protect actual theorem applications and explain why the theorem ledger passes. None appears in the four public definition carriers or supplies a source-defined meaning at the counterexample inputs. This is the required distinction between theorem validity and whole-carrier definition fidelity. No owner ruling allowing these four totalized source-series definitions was located in the supplied authority.

**Repair criterion (not implemented):** restrict the source-facing definitions to their valid weight/domain carriers (for example, fix a=p=1 where that is the source scope, or bind explicit sufficient weight guards), or provide a separately named auxiliary totalization and expose the faithful source object on its actual carrier. Do not merely add the same guards to downstream theorems: those already have them. Re-audit the resulting declaration types/bodies and users. No frozen file needs to be changed to report this issue.

Other candidate defects were refuted as follows:

1. **Possibly erased q spaces:** refuted by explicit weight denominators in mixed Ω and stepSymp and by the birkEmbed/kamHomEmbed maps in aaConjugacy. Both inverse directions are proved on each q separately.
2. **Possible assumption of smoothing/field bounds:** refuted by aaQt_hasFDerivAt, the W3 class-A/K-field applications, and explicit construction of IsSmoothing. hV is an unused open-set helper binder, not an assumed smoothing result.
3. **Conditional initial frequency clause:** refuted by the compiled source-premise-only B=3t/2 witness described above.
4. **Zero-extension contamination:** refuted by hB at every analytic/field/size use; aaKext_isExtension and aaXKext_isExtension reduce to W3 maps before derivative estimates.
5. **Changed initial arithmetic:** the code uses a coarser tangential polynomial estimate `13/(8π²) r²` and normal `9/(4π) r²`; it proves their sum ≤r². This differs from the blueprint proof's intermediate r²/8 and 3r²/4 but proves the identical final bound, uniformly in m. Likewise the domain proof uses tangential ≤2199(t+r²) plus normal <r², reaching c_A=2200; it does not need the printed sharper 2173 intermediate bound.

N1 (hygiene, survived; no mathematical blocker): fresh targeted builds emit 33 distinct warning locations within the eleven audited files, from deprecated names and unused binders/simp arguments. Thus **warning-clean acceptance is not established**. In particular ActionAngleField.lean:162:63 reports unused hV; ActionAngleGbar.lean:71:43 unused i; ActionAngleConj.lean:147–188 unused simp arguments. The report does not repair them. Exact warning lines are preserved below.

N2 (scope): `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `KAM/Root/Wave.lean` differs (129 added generated imports), already disclosed by the producer. I did not edit/regenerate the root; this is an existing generated integration change, not a modification to frozen declarations. The generic protected-path probe does not include root parts; the broader root change is explicitly recorded rather than silently treated as empty.

N3 (verification provenance): user states kernel replay and short-name checks were already run by the launcher. Their logs are unavailable in this auditor's visible history. I have not invented an observed replay exit code and have not repeated the replay. Local axiom/type and targeted-build checks are independent and reported below.

F1 is an implementation definition-carrier defect, not a suspected defect in the pinned blueprint. No suspected pinned-blueprint defect found in these clauses. The omitted premises 0<s (domain and initial) and r≤1 (initial), and coordinatewise conjugacy proof, are faithful stronger statements/proof-route deviations, not source repairs. The initial complex-root and auxiliary total-extension domains are explicit, not mathematical claims outside the source domain.

## Verification

All Lean/Lake activity initiated by this audit is serialized and under `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`. No heartbeat, recursion-depth or synthesis-heartbeat overrides; no library clean/update/cache action. Build gate waits were respected.

1. `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpja5b KAM.Wave.KamStep.ActionAngleConj KAM.Wave.KamStep.Initial` (driver wraps each target separately under the exact cap and compile gate): **exit 0**. Output contains:

```text
[w_build] slot 3: KAM.Wave.KamStep.ActionAngleConj (08:59:29)
Build completed successfully (3671 jobs).
[w_build] slot 3: KAM.Wave.KamStep.Initial (09:00:15)
Build completed successfully (3674 jobs).
```

The job counts include cached/replayed import dependencies, not a requested full-library build. Built tail modules: ActionAngleQt (9.2s), ActionAngleField (8.0s), ActionAngleConj (14s), InitialBound (16s), Initial (8.2s). Earlier package modules were replayed. The Mathlib marker check `find .lake/packages/mathlib -type f -newer .lake/abi-scratch/W5AA-mathlib-marker -print -quit` produced no paths.

2. Capped `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/W5AAIndependent.lean`: **exit 0**, no warnings/errors. Probe imported Initial and ActionAngleConj, printed axioms for all 233 inventoried declarations (186 theorems, 47 definitions/abbreviations), and elaborated the two-way inverse witness and source-only frequency witness. Output: 230 lines with `[propext, Classical.choice, Quot.sound]`, three with `[propext, Quot.sound]` (`pnat_sub_two_add_two`, `modeIdx_cases`, `modeIdx_ne_add_two`), zero other axioms. Main results individually print `[propext, Classical.choice, Quot.sound]`, including initialPerturbation, aaConjugacy, aaMap_normalForm, aaDer_symp, aaP_isSmoothing, aaMap_linearTorus, aaMap_differentiableOn, aaMap_real, aaMap_add_tau, aaMap_domain, aaMap_mem_birkBall1, hasFDerivAt_aaMap, aaDerInv_aaDer, aaDer_aaDerInv, aaPfun_real, aaPfun_add_tau, aaQt_hasFDerivAt, kamNorm_aaXP_le and aaXP_lipschitz.

3. Isolated lint rerun: **exit 0**, exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpja5b
```

Exact output:

```text
check_lean_modules: PASS (3964 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The first invocation overlapped the parallel step auditor's lint because the two aliases resolve to one checkout. It exited 1 with `rm: cannot remove .../.lake/w-overlay/KAM/Wave/KamStep: Directory not empty` and, after the shared overlay was removed, a missing `KAM/Frozen/Defs/ActionNbhd.olean` at ABI checking. It is superseded by the isolated successful rerun above, started only after the other same-checkout lint had finished. No cache was rebuilt to repair this temporary wrapper collision. The final lint proves source/module/frozen/ABI hygiene; it does not assert warning-clean elaboration or resolve F1. The two opt-in lunar exports were only checked by file hash, exactly as the output states.

4. `git diff --check inp...HEAD -- 'KAM/Wave/KamStep/ActionAngle*' 'KAM/Wave/KamStep/Initial*'`: **exit 0**, no output. Protected frozen/manifest/root-headline diff: empty as described in N2. Static imports have no provider or DRAFT theorem anchor; the only direct frozen import in the eleven modules is the frozen LinearTorus definition. Module format is uniform (copyright, module, imports, docstring, expose/public section). All 11 are below the size cap.

## Complete public-declaration ledger

One row per new named declaration; line anchors refer to the frozen HEAD above. `AA` denotes bpW:w5:action-angle. A helper PASS means its stated conditional/general identity is valid and used at its own scope, not that it independently closes the source node. Literal definitions are assessed by the definition table above. Every listed declaration also passed the axiom probe. Declaration-ledger counts: 229 PASS, four definition FAIL (F1), zero unclassified. Axiom cleanliness does not upgrade the four semantic FAILs.

| Node / support | File:line | Declaration | Verdict | Reason |
|---|---|---|---|---|
| AA (i) | ActionAngle.lean:48 | `aaSqrt` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:50 | `aaSqrt_sq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:52 | `aaSqrt_mul_self` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:54 | `aaSqrt_ne_zero` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:57 | `aa_ne_zero_of_re_pos` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:59 | `aa_mem_slitPlane_of_re_pos` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:63 | `aaSqrt_ofReal` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:68 | `differentiableAt_aaSqrt_comp` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:75 | `aaIdx_injective` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:79 | `aaShiftFun` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:82 | `pnat_sub_two_add_two` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:89 | `aaShiftFun_add_two` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:94 | `aaShiftFun_le_two` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:98 | `aaShiftFun_notMem_range` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:105 | `aaShift_hasSum_sq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:114 | `memℓp_aaShiftFun` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:118 | `aaShift` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:136 | `aaShift_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:138 | `norm_aaShift` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:147 | `aaNormal` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:155 | `aaNormal_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:161 | `aaTanCoord` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:165 | `aaTan` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:172 | `aaMap` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:175 | `aaDomJ` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (i) | ActionAngle.lean:177 | `isOpen_aaDomJ` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:186 | `modeIdx_cases` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:194 | `modeIdx_ne_add_two` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:203 | `aaTan_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:208 | `aaTan_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:214 | `aaTan_nor` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:220 | `aaNormal_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:225 | `aaMap_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:230 | `birkCoord_aaMap_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:236 | `aaMap_nor_true` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:242 | `aaMap_nor_false` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:250 | `lp_single_eq_smul` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:254 | `differentiableAt_aaTanCoord` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:264 | `aaMap_differentiableOn` | PASS | Joint complex holomorphy on the open aaDomJ, not merely fixed-parameter holomorphy. |
| AA (i) | ActionAngle.lean:279 | `aaTanCoord_add_tau` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:299 | `aaMap_add_tau` | PASS | Period-one translation in each angle; stronger global formula identity. |
| AA (i) | ActionAngle.lean:312 | `aaTanCoord_conj` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:326 | `aaMap_real` | PASS | StepReal and positive real ξ+y imply birkRho-fixed image. |
| AA (i) | ActionAngle.lean:344 | `birkSgn_true` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:346 | `birkSgn_false` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:349 | `aaTanCoord_eq_trig` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (i) | ActionAngle.lean:373 | `aaMap_linearTorus` | PASS | Exact equality to complexified frozen linearTorus, including √2 and minus sine. |
| AA (v)/a-conj | ActionAngleConj.lean:43 | `aaXNcoef` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-conj | ActionAngleConj.lean:47 | `norm_aaXNcoef_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleConj.lean:78 | `aaXNdiag` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-conj | ActionAngleConj.lean:81 | `aaXN` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-conj | ActionAngleConj.lean:89 | `birkSpace_ext_coord` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleConj.lean:96 | `aaDerTanL_kamHomEmbed` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleConj.lean:101 | `aaDerTanL_aaDerInv` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleConj.lean:108 | `aaGbarR_aaMap` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleConj.lean:125 | `aaConjugacy` | PASS | Full vector identity in W^(p−1), with inclusions from p+1 explicit. |
| AA (iii) | ActionAngleDeriv.lean:43 | `aaS` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:46 | `aaE` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:49 | `aaTanCoord_eq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:52 | `aaE_mul` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:57 | `aaE_ne_zero` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:59 | `aaS_ne_zero` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:62 | `aaS_mul_self` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:67 | `aaTanBuild` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:70 | `aaTanBuild_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:76 | `aaTanBuild_nor` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:83 | `aaDerTanL` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:91 | `aaDerTanL_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:100 | `aaDer` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:104 | `aaDer_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:112 | `aaDer_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:116 | `aaNormal_nor_true` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:120 | `aaNormal_nor_false` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:125 | `aaDer_nor_true` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:129 | `aaDer_nor_false` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:135 | `hasFDerivAt_aaS` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:159 | `hasFDerivAt_aaE` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:178 | `hasFDerivAt_aaTanCoord` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:188 | `hasFDerivAt_aaMap` | PASS | aaDer is the actual Fréchet derivative at weight p. |
| AA (iii) | ActionAngleDeriv.lean:206 | `memℓp_aaUnshift` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:213 | `aaUnshift` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:228 | `aaUnshift_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:231 | `aaEv` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:233 | `aaEv_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:237 | `aaInvTheta` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:244 | `aaInvY` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:249 | `aaDerInv` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iii) | ActionAngleDeriv.lean:255 | `aaDerInv_theta` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:263 | `aaDerInv_y` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:271 | `aaDerInv_u` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:274 | `aaDerInv_v` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleDeriv.lean:278 | `aaDerInv_aaDer` | PASS | Left inverse on every q-representative space. |
| AA (iii) | ActionAngleDeriv.lean:315 | `aaDer_aaDerInv` | PASS | Right inverse on every q-representative space. |
| AA (ii),(vi) | ActionAngleDomain.lean:41 | `aaCA` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (ii),(vi) | ActionAngleDomain.lean:45 | `aaTan_sq_hasSum` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (ii),(vi) | ActionAngleDomain.lean:64 | `norm_sq_aaNormal` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (ii),(vi) | ActionAngleDomain.lean:70 | `aaNormal_norm_le` | PASS | First half of the sum/Hilbert normal norm comparison. |
| AA (ii),(vi) | ActionAngleDomain.lean:77 | `aaNormal_norm_ge` | PASS | Second half, factor √2. |
| AA (ii),(vi) | ActionAngleDomain.lean:85 | `norm_sq_aaMap` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (ii),(vi) | ActionAngleDomain.lean:101 | `exp_half_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (ii),(vi) | ActionAngleDomain.lean:107 | `exp_pi_half_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (ii),(vi) | ActionAngleDomain.lean:127 | `aaTan_const_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (ii),(vi) | ActionAngleDomain.lean:152 | `norm_aaTanCoord_sq_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (ii),(vi) | ActionAngleDomain.lean:174 | `aaMap_domain` | PASS | c_A=2200; strict norm-square bound and Re(ξ+y)>r²; omits unused 0<s. |
| AA (ii),(vi) | ActionAngleDomain.lean:216 | `aaMap_mem_ball` | PASS | Actual open ball with radius √(c_A(t+r²)). |
| AA (ii),(vi) | ActionAngleDomain.lean:223 | `aaMap_mem_birkBall1` | PASS | W3 ball membership supplied by the explicit smallness assumption. |
| AA (v)/a-field | ActionAngleField.lean:41 | `aaDerInv_eq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:51 | `differentiableAt_aaS` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:55 | `differentiableAt_aaE` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:60 | `differentiableAt_aaDerInv_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:99 | `hasFDerivAt_comp_aaMap` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:117 | `aaXP` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleField.lean:127 | `birkHamNor_classA` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:131 | `aaKext_analyticOnNhd` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:134 | `aaXKext_analyticOnNhd` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:137 | `aaKext_field` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:143 | `differentiableAt_aaXQt` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:162 | `aaP_isSmoothing_of` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:209 | `aaP_isSmoothing` | PASS | Full IsSmoothing on D(s,r), including holomorphy of scalar and p+1 field. |
| AA (v)/a-field | ActionAngleField.lean:222 | `aaQt_congr` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:227 | `aaPfun_add_tau` | PASS | Periodic perturbation, formula valid globally. |
| AA (v)/a-field | ActionAngleField.lean:232 | `im_eq_zero_of_conj` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleField.lean:236 | `aaPfun_real` | PASS | Real scalar perturbation on its guarded source domain. |
| AA (v)/a-conj | ActionAngleGbar.lean:38 | `aaGbarR` | FAIL | F1: unguarded public weight carrier includes divergent series; tsum totalization is not the source object. |
| AA (v)/a-conj | ActionAngleGbar.lean:43 | `birkHamBar_eq_aa` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:54 | `norm_birkActionB_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:63 | `norm_birkAction_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:71 | `summable_aaGbarR` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:81 | `birkCoord_add_unit` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:86 | `birkAction_add_unit` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:100 | `hasDerivAt_birkHamBar_line` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:111 | `fderiv_birkHamBar_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:162 | `fderiv_birkHamBar_nor` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:211 | `birkHamBar_hamField` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:217 | `birkCoord_birkHamBarX_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-conj | ActionAngleGbar.lean:226 | `birkCoord_birkHamBarX_nor` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:45 | `aaBdot` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:48 | `aaEnergy` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:53 | `aaOmega0` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:57 | `aaOmegaN0` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:61 | `aaZZ` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:64 | `aaNfun` | FAIL | F1: unguarded public weight carrier includes divergent series; tsum totalization is not the source object. |
| AA (iv) | ActionAngleNormal.lean:68 | `aaQt` | FAIL | F1: unguarded public weight carrier includes divergent series; tsum totalization is not the source object. |
| AA (iv) | ActionAngleNormal.lean:78 | `aaKext` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:83 | `aaXKext` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:86 | `aaKext_isExtension` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:89 | `aaXKext_isExtension` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:93 | `aaPfun` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (iv) | ActionAngleNormal.lean:102 | `lamTan_eq_lam` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:104 | `aaOmega0_ofReal` | PASS | Tangential complex frequencies identify with waveFreqTan. |
| AA (iv) | ActionAngleNormal.lean:108 | `aaBdot_ofReal` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:113 | `aaOmegaN0_ofReal` | PASS | Normal complex frequencies identify with waveFreqNor at J=j+2. |
| AA (iv) | ActionAngleNormal.lean:121 | `aa_one_le_lam` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:128 | `stepZ_apply'` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:134 | `stepZb_apply'` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:140 | `birkAction_aaMap_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:148 | `birkAction_aaMap_nor` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:158 | `norm_lam_aaZZ_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:167 | `summable_norm_lam_aaZZ` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:175 | `summable_coef_aaZZ` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:184 | `norm_three_div_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:195 | `tsum_ite_three` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:207 | `actionA_symm` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iv) | ActionAngleNormal.lean:215 | `aaMap_normalForm` | PASS | Exact H′∘A=e+N+P, with subtype K on the W3 ball. |
| AA (v)/a-field | ActionAngleQt.lean:39 | `aaCoefC` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:42 | `aaCoefD` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:45 | `aaCoefE` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:49 | `aaCoefC_eq_real` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:53 | `norm_aaCoefC_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:60 | `norm_aaCoefE_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:76 | `norm_aaCoefD_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:89 | `aaBq` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:93 | `aaSfun` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:97 | `aaDiagE` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:100 | `aaXQt` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:107 | `aaBq_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:110 | `aaBq_comm` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:115 | `aaZZ_eq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:126 | `aaSfun_eq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:142 | `aaQt_eq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:153 | `aaPrY` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:157 | `aaPrU` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:162 | `aaPrV` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| AA (v)/a-field | ActionAngleQt.lean:167 | `hasFDerivAt_aaSfun` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:179 | `aaSfun_deriv_apply` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:188 | `homWt_succ_eq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:196 | `stepPairCLM_aaDiagE` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (v)/a-field | ActionAngleQt.lean:210 | `aaQt_hasFDerivAt` | PASS | Actual derivative and Hamiltonian pairing of explicit polynomial Q̃. |
| AA (iii) | ActionAngleSymp.lean:36 | `birkOmegaMix` | FAIL | F1: unguarded public weight carrier includes divergent series; tsum totalization is not the source object. |
| AA (iii) | ActionAngleSymp.lean:39 | `birkOmega_eq_birkOmegaMix` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:42 | `birkOmegaPlus_eq_birkOmegaMix` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:49 | `one_le_ellWeight_mul` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:62 | `norm_birkOmegaMix_term_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:73 | `summable_birkOmegaMix` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:79 | `aa_hasSum_pnat` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:121 | `birk_tsum_tan_nor` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:137 | `birkCoord_aaDer_tan` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:142 | `birkCoord_aaDer_nor_true` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:147 | `birkCoord_aaDer_nor_false` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:152 | `stepPairCLM_eq_tsum` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:156 | `aa_normal_pair` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| AA (iii) | ActionAngleSymp.lean:167 | `aaDer_symp` | PASS | Mixed q,q′ form; summability under q+q′≥0; no erased weight embeddings. |
| initial/i-par,i-freq | Initial.lean:43 | `aaOfReal` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| initial/i-par,i-freq | Initial.lean:45 | `norm_aaOfReal_sub` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:55 | `differentiableAt_aaS_param` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:59 | `differentiableAt_aaMap_param` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:69 | `differentiableAt_aaDerInv_param` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:103 | `differentiableAt_aaXP_param` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:121 | `aa_kamNorm_sub_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:128 | `aaEpsIn_nonneg` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:151 | `aaXP_bound_nbhd` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-par,i-freq | Initial.lean:158 | `aaXP_lipschitz` | PASS | 4ε_in/ρξ in the p+1 KAM norm; no assumed Lipschitz bound. |
| initial/i-par,i-freq | Initial.lean:219 | `initialPerturbation` | PASS | All six conclusion groups; removed 0<s and r≤1 strengthen the source statement. |
| initial/i-q,i-g,i-k | InitialBound.lean:38 | `aaEpsIn` | PASS | Literal/helper definition; carrier and guarded uses classified above. |
| initial/i-q,i-g,i-k | InitialBound.lean:44 | `norm_aaE_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:53 | `exp_two_pi_mul_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:58 | `norm_aaS_sq` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:62 | `le_norm_aaS` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:68 | `norm_aaS_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:73 | `norm_apply_le_lp` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:76 | `exp_one_le_ellWeight_two` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:86 | `norm_aaDerInv_normal_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:103 | `kamNorm_aaDerInv_normal_le` | PASS | Conditional zero-tangential inverse estimate; tangential vanishing proved at use. |
| initial/i-q,i-g,i-k | InitialBound.lean:119 | `kamNorm_aaDerInv_le` | PASS | Inverse estimate 3/r+2√T/r², with T supplied as t+r². |
| initial/i-q,i-g,i-k | InitialBound.lean:194 | `actionA_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:208 | `norm_aaCoefD_le'` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:230 | `norm_aaBq_self_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:240 | `lamTan_two_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:245 | `norm_aaBdot_le` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:263 | `kamNorm_aaXQt_le` | PASS | Polynomial field ≤r² in p+1=2 KAM norm. |
| initial/i-q,i-g,i-k | InitialBound.lean:352 | `birkNormalPart_aaMap` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:363 | `rpow_five_halves_of_sq_lt` | PASS | Supporting coordinate, summability, algebra, norm or calculus lemma; hypotheses retained at helper scope and discharged at source use. |
| initial/i-q,i-g,i-k | InitialBound.lean:374 | `kamNorm_aaXP_le` | PASS | Exact ε_in with W3 constant C′_K=66 C_* C_F. |

## Compiled source-only consumption witnesses

The transient probe, after importing Initial and ActionAngleConj, contained the following exact witnesses (successfully elaborated at default budgets):

```lean
open KAM.Wave

-- Independently reconstructed source clause (iii), with both inverse identities.
example (a q : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase)
    (hw : ∀ i, 0 < (ξ i + w.2.1 i).re) :
    (∀ W, aaDerInv a q ξ w (aaDer a q ξ w W) = W) ∧
    (∀ V, aaDer a q ξ w (aaDerInv a q ξ w V) = V) :=
  ⟨aaDerInv_aaDer a q hw, aaDer_aaDerInv a q hw⟩

-- The source's unconditional frequency assertion: produce B from its existing
-- parameter-neighbourhood premise, rather than adding a bound hypothesis.
example (m : ℝ) (hm : 0 < m) (s r t ρξ : ℝ)
    (hs : 0 < s ∧ s ≤ 1 / 8) (hr : 0 < r ∧ r ≤ 1) (ht : 0 < t) (hρξ : 0 < ρξ)
    (Par : Set (Fin 2 → ℝ))
    (hPar : ∀ ζ : Fin 2 → ℂ, (∃ ξ ∈ Par, ‖ζ - aaOfReal ξ‖ < ρξ) →
      (∀ i, 2 * r ^ 2 ≤ (ζ i).re) ∧ ‖ζ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) :
    HomFreqHyp1 Par (waveFreqTan m hm) (waveFreqNor m hm)
      (m / 2 + 3 / (2 * Real.pi) * (3 / 2 * t))
      (waveMomega m hm) (waveMOmega m hm) := by
  have h := initialPerturbation m hm hs.2 hr.1 ht hρξ Par hPar hρ₁
  apply h.2.2.2.2.1 (3 / 2 * t) (by positivity)
  intro ξ hξ
  have hb := (hPar (aaOfReal ξ) ⟨ξ, hξ, by simpa using hρξ⟩).2
  have he : aaBdot m hm (aaOfReal ξ) = (waveB m hm ξ : ℂ) := aaBdot_ofReal ξ
  have hh := norm_aaBdot_le (m := m) (hm := hm) (aaOfReal ξ)
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
```

## Exact in-scope build warning headers

```text
warning: KAM/Wave/KamStep/ActionAngleConj.lean:147:45: This simp argument is unused:
warning: KAM/Wave/KamStep/ActionAngleConj.lean:147:75: This simp argument is unused:
warning: KAM/Wave/KamStep/ActionAngleConj.lean:148:20: This simp argument is unused:
warning: KAM/Wave/KamStep/ActionAngleConj.lean:148:44: This simp argument is unused:
warning: KAM/Wave/KamStep/ActionAngleConj.lean:148:6: This simp argument is unused:
warning: KAM/Wave/KamStep/ActionAngleConj.lean:188:69: This simp argument is unused:
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:106:20: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:106:51: `ContinuousLinearMap.coe_sum'` has been deprecated: Use `FunLike.coe_sum` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:259:35: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:259:4: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:267:35: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:267:4: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:94:24: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:94:55: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead
warning: KAM/Wave/KamStep/ActionAngleDeriv.lean:95:4: `ContinuousLinearMap.coe_comp'` has been deprecated: Use `ContinuousLinearMap.coe_comp` instead
warning: KAM/Wave/KamStep/ActionAngleField.lean:162:63: Variable name `hV` is not explicitly referenced.
warning: KAM/Wave/KamStep/ActionAngleField.lean:194:28: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead
warning: KAM/Wave/KamStep/ActionAngleField.lean:194:59: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:131:12: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:131:23: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:131:55: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:132:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:132:23: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:171:31: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:185:33: `if_true` has been deprecated: Use `ite_true` instead
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:185:49: This simp argument is unused:
warning: KAM/Wave/KamStep/ActionAngleGbar.lean:71:43: Variable name `i` is not explicitly referenced.
warning: KAM/Wave/KamStep/ActionAngleQt.lean:231:13: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead
warning: KAM/Wave/KamStep/ActionAngleQt.lean:231:44: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead
warning: KAM/Wave/KamStep/ActionAngleQt.lean:232:35: `ContinuousLinearMap.coe_comp'` has been deprecated: Use `ContinuousLinearMap.coe_comp` instead
warning: KAM/Wave/KamStep/ActionAngleQt.lean:232:4: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead
warning: KAM/Wave/KamStep/ActionAngleQt.lean:237:36: `ContinuousLinearMap.neg_apply` has been deprecated: Use `neg_apply` instead
warning: KAM/Wave/KamStep/ActionAngleQt.lean:237:4: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead
```

## Closeout

Source clauses classified; source-facing rule-6 E count zero; **F1 remains open**, so the package is not approved. The source-weight theorem components are sound at the audited interfaces, and no suspected source erratum remains open. Only this report is a repository deliverable. Scratch probe files are deleted after verification; logs/inventory remain under .lake/abi-scratch for evidence. No implementation, frozen file, manifest, root or history edits were made by this audit. Final isolated lint exited 0; the source/module hash recheck passed; the report has 233 classified declaration rows (229 PASS and four FAIL). Kernel replay/short-name provenance remains the launcher statement, not a newly observed local exit code. No repair was attempted.
