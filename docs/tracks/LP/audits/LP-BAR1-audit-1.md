# LP-BAR1 independent package audit 1

Snapshot: `96fafe661576bb6a0e1427a7179746cd32c4597b`; base `inp-lp` = `96ffcbe9db1aed788432ed91946b8423fdfa6bd6`; `inp` = `e77a963cf4563cbdd613370fdb01b36e9985a527`. Scope: `git diff inp-lp...HEAD -- KAM`, also inspected `git diff inp...HEAD`. The StrongAMD diff is identical against both bases (SHA-256 `edb1a5131c11c172684639eae1bf75a018ba5e14c969cafe01a2b93086fe527b`). Eight new StrongAMD modules and eight generated root imports. No LP declaration is frozen; no seal-readiness or full MAIN Lemma 4 sharpness claim is made.

Authority: audit brief `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, LP-BAR1 handoff, MAIN as amended by AMENDMENTS (especially N8–N9), SPEC, OWNER-DECISIONS OD-1/OD-2, and component package briefs `docs/tracks/LP/packages/LP-{THR,MOM}.md`. The requested `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-BAR1.md` does not exist; no BAR1 brief was found in the supplied LP worktrees. The combined handoff explicitly defines BAR1 as THR + MOM and cites those component briefs, which are used here. Both component briefs are byte-identical to their copies under `/root/code/KAM-inp-lp/` (`cmp`, exit 0). Its historical merge hash `8f6f6e4d` is not the audited HEAD.

## LP-THR — PASS WITH NOTES

Items 1–8 of LP-THR match their exact intended statements. No excess premise or weakened conclusion found. MAIN L4's interior optimizer, geometric realization, and relative Laskar–Petit identification remain explicitly outside this package (N9 and component brief); the label “sharp thresholds” does not establish those omitted claims.

`pairFeasible` uses `a_j(1-v) ≤ a_i(1+u)`; `α = a_i/a_j`; `contactScale = min 1 ((1-α)/α)`; `contactPoint = (m t, 1-α-α m t)`, exactly MAIN (15). The contact minimizer scales both coordinates by `(b-a)/(a*u+b*v)`; positivity/order supply its positive denominator and `0<t≤1`. The parameterization theorem recovers `t=u/m` with `m>0`, proving both attainment and the least-value characterization over `[0,1]`.

`pairThreshold_isLeast` and `exists_pairThreshold_attained` prove the literal objective minimum for **every** total-helper input: the feasible set is compact and always contains `(1,1)`, even with zero masses or signed actions. Thus `sInf` never uses an empty/unbounded fallback. On the physical carrier, positivity, the strict competitor bound `< I_j`, contact and continuity require only positive masses, chamber membership, and `i<j`. Carrier versions reduce definitionally to the same helpers. No package consumer depends on off-chamber values.

`crossThreshold` uses exactly the adjacent indices `{i : Fin n // i.val+1<n}`. Empty real infima are zero (`crossThreshold` for `n≤1`, `starThreshold` for `n=0`). Existence/member, positivity and continuity statements carry `2≤n` for cross/strong or `1≤n` for star. The unconditional “≤ each member” lemmas take a member, which itself ensures nonemptiness. `orderedCrossThreshold` alone permits the empty-index case; it is a literal helper, and source-facing `orderedStrongThreshold` requires `2≤n`. These are OD-2 overnight APIs, not approval to freeze wider carriers.

`strongThreshold_eq_min_first` does not assume increasing actions (which unequal masses would invalidate): for each nonfirst index it uses `B_{i-1,i}<I_i`. `continuousOn_pairThreshold` works on `chamber ν × ℝ`, where both relevant axes and α are nonzero; it identifies the value with the infimum over the fixed compact nonempty interval and applies `IsCompact.continuous_sInf`. No continuity across collision of axes or zero-mass division is claimed.

Mechanical checks and declaration inventory follow below after the LP-MOM review.

## LP-MOM — PASS WITH NOTES

Items 1–9 match LP-MOM and MAIN L2–L3, planar. `keplerEnergy` is ν times MAIN's specific energy; the axis `-ν/(2E_total)`, action `ν√a`, eccentricity vector and cross product therefore have the correct normalization. `orbital_identities` assumes exactly positive mass, positive physical radius and negative Kepler energy for the selected planet. There is no prograde or nonradial premise. At `e=1`, its radial upper bound is proved from the vis-viva identity and nonnegative squared momentum, without dividing by `1-e`.

`strongAMD = ΣΛ-|L|` matches OD-1 and N8. Nonnegativity and the eccentricity-deficit inequality use `|L|≤Σ|L_i|≤ΣΛ_i`. Projection estimates follow from the nonnegative individual deficits. The margin assumption is exactly `∀ i, C≤Λ_i-m`, equivalent to the star-minimum form on the source carrier. `cross_sign_and_margin` proves per planet `L≠0`, `0<L_i*L` and `m≤|L_i|`; this gives the positive invariable-frame projection and its margin for either orientation. A `Fin n` planet argument makes the `n=0` instance vacuous; the nonnegative/deficit sum identities remain true there.

`totalMomentum_const` reuses the exact `ang_mom` conservation result for the frozen moving Hamiltonian on an order-connected time set. `strongAMD_sub_eq_sum` is correctly stronger than MAIN: expansion of the literal AMD and conservation of `L` cancel `|L|` without energy or radius assumptions. It does not assert physical validity of off-region osculating elements. `strongAMD_eq_physicalAMD` uses precisely `0≤L`, including `L=0`.

`reflectVec` uses `(finProdFinEquiv.symm j).2=1`, matching the frozen `bodyVector` packing. It reflects the second coordinate of **both** q and p. The involution preserves physical lengths, their differences, energies, actions, eccentricity magnitude, collision exclusion and Hamiltonian; each `L_i` and `L` changes sign. For negative `L`, reflection yields positive total momentum and unchanged strong AMD, so the signed AMD bridge applies after reflection. No unsupported orientation reduction remains.

The ODE proof uses `KAM.hamiltonianVectorField=(∂p H,-∂q H)` (the handoff's `KAM.Iso.hamiltonianVectorField` spelling is a namespace typo). The same reflection sign acts on both members of each canonical pair, hence preserves `Σdp∧dq`. The fderiv chain rule and involution yield `dH(Rz)(Rv)=dH(z)v`; evaluating the q and p basis vectors proves `X_H(Rz)=R X_H(z)` with the negative p-component retained. Differentiability at `z` is a genuine premise of the generic equivariance helper and is supplied by `IsMovingSolutionOn`; no nondifferentiability fallback is used. The solution predicate expands into domain membership (univ), Hamiltonian differentiability, the physical-time derivative equation, and noncollision, all preserved. Reflection requires no time reversal.

## Definition classification and full-carrier behavior

Every definition below has BODY_MATCH=OK, PUBLIC_CARRIER=OK for this unfrozen package/OD-2 scope, and DEFINITION_VERDICT=PASS. They are literal formulas, predicates, index/subtype aliases or explicit linear maps: WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A except the threshold minimum, whose characterization is proved by `pairThreshold_isLeast` and `exists_pairThreshold_attained` (CHARACTERIZATION=OK, WELL_DEFINEDNESS=OK). No arbitrary optimizer choice is exported. Finite-infimum member theorems characterize the other minima. The carrier notes do not authorize any future frozen off-source definition.

| Definition (all in `KAM.Planetary.StrongAMD`) | Classification and edge cases |
|---|---|
| `actionAxis` | Literal squared ratio; nonnegative for all inputs; ν_i=0 gives 0 under Lean division, excluded by physical theorems. |
| `chamber` | Literal positivity and strict pairwise axis ordering; empty dimension vacuous; alone does not encode positive masses. |
| `eccDeficit` | Literal `1-√(1-u²)`; D(0)=0, D(1)=1; for abs(u)>1 real sqrt gives D=1. Eccentricity consumers restrict to [0,1]. |
| `pairFeasible` | Literal closed unit-square inequality, including boundary/contact points; always nonempty. |
| `pairObjective` | Literal weighted sum; signed actions may give negative values, without invalidating compact attainment. |
| `pairThreshold` | Literal infimum, universally attained; on chamber with positive masses/i<j it is the source threshold. |
| `AdjIdx` | Subtype of precisely adjacent lower indices; empty for n=0,1. |
| `AdjIdx.upperIdx` | Literal successor with bound supplied by subtype proof; cannot wrap around. |
| `crossThreshold` | Literal finite infimum; 0 for n≤1; physical theorems require n≥2. |
| `starThreshold` | Literal finite infimum; 0 for n=0, I₀ for n=1. |
| `strongThreshold` | Literal min; n=0 gives 0, n=1 gives min(0,I₀); source results require n≥2. |
| `OrderedActions` | Exact chamber subtype; no new analytic premise hidden. |
| `orderedPairThreshold` | Same total helper on chamber and ordered pair; mass positivity remains explicit in theorems. |
| `orderedCrossThreshold` | Literal infimum of carrier pair values; still 0 for n≤1, explicitly a helper. |
| `orderedStrongThreshold` | Same strong threshold on chamber with required n≥2 argument. |
| `contactScale` | Literal (15); α=0 gives 0, outside (0,1) has no contact guarantee; all such uses prove 0<α<1. |
| `contactPoint` | Literal (15); no clamp or chosen minimizer; feasibility only asserted on source carrier with t∈[0,1]. |
| `contactObjective` | Literal composition; continuity proved on chamber×ℝ with positive masses. |
| `strongAMD` | Literal ΣΛ-abs(L); n=0 gives 0; unphysical energies/masses retain existing Kepler formula semantics only. |
| `reflectPlane` | Coordinate reflection on all ℝ², including zero. Conditional is exact coordinate selection, no fallback object. |
| `reflectSign` | Exact ±1 per second body coordinate; empty coordinate type for n=0. |
| `reflectVec` | Componentwise ±1, all vectors, involutive; empty vector preserved. |
| `reflectPhase` | Same reflection on q and p; all phases including collisions; invariance formulas hold even there. |
| `reflectVecCLM` | Explicit continuous linear packaging of reflectVec; no changed carrier/metric. |
| `reflectPhaseCLM` | Product continuous linear packaging; `reflectPhaseCLM_apply` verifies equality with reflectPhase. |

## Premise audit

For source-facing theorems all data binders (n, ν, I, indices, states, time sets, times, masses, functions, topology and finite-index instances) are TYPING. Expanded logical inputs below are SOURCE (or the documented OD-2 carrier convention); STANDING=0 hidden bundles, EXCESS=0, and no hidden result fields/instances were found. Mass normalization max ν=1 and n≥2 may be dropped where unnecessary, giving stronger elementary results.

| Expanded input | Bin | Authority / check |
|---|---|---|
| hν: ∀i, 0<ν_i | SOURCE | MAIN 11, L4 143; no positivity silently assumed through division. |
| hI / OrderedActions: ∀i, 0<I_i | SOURCE | MAIN 43; subtype expands literally. |
| hI / OrderedActions: ∀i<j, a_i<a_j | SOURCE | MAIN 43. |
| hij: i<j | SOURCE | MAIN 49, L4 pair domain. |
| hn: 1≤n / 2≤n; Nonempty finite-index instances | TYPING | Nonempty minima; MAIN n≥2. Local finite-index helpers state their own exact typing assumptions. |
| hu,hv,ht: unit-interval membership | SOURCE | MAIN 47–49, 151–152; expands into lower and upper endpoint bounds. |
| h: pair feasibility inequality | SOURCE | MAIN 48; the feasibility consumer assumes membership, not its threshold conclusion. |
| orbital hz: 0<ν_i | SOURCE | MAIN L2 112. |
| orbital hz: 0<physical radius_i | SOURCE | MAIN L2 q≠0, equivalent by Euclidean length. |
| orbital hz: Kepler energy_i<0 | SOURCE | MAIN L2 112; positive ν gives equivalent specific-energy sign. |
| momentum hz: the preceding three premises ∀i | SOURCE | MAIN L3 negative-energy nonsingular states. |
| hJ: J.OrdConnected | SOURCE | MAIN L3 connected interval of existence. |
| solution hz: ∀t∈J, action coordinate∈univ | TYPING | Frozen solution domain, tautological in this use. |
| solution hz: ∀t∈J, DifferentiableAt H(z t) | SOURCE | Classical solution to MAIN (1); prevents fderiv junk. |
| solution hz: ∀t∈J, HasDerivAt z (X_H(z t)) t | SOURCE | Actual ODE, not momentum/AMD conservation assumed. |
| solution hz: ∀t∈J, ∀i, positive star distance | SOURCE | MAIN 24 physical domain, NoCollision expansion. |
| solution hz: ∀t∈J, ∀i≠j, positive pair distance | SOURCE | MAIN 24 physical domain, NoCollision expansion. |
| hs,ht: s,t∈J | SOURCE | MAIN L3 along interval. |
| hk: C<Λ_k | SOURCE | Component brief item 6, sufficient single-index version of C<B_star. |
| hL: L>0, L<0, L≥0 or L≤0 | SOURCE | Explicit orientation cases/identity bridges; no orientation premise on orbital identities. |
| hm: m>0 | SOURCE | MAIN 137. |
| hC: ∀i, C≤Λ_i-m | SOURCE | MAIN 137 C≤B_star-m. |
| generic reflection hH: ∀w,H(Rw)=H(w) | SOURCE | Explicit equivariance helper premise; proved for movingHamiltonian before applying it. |
| generic reflection hd: DifferentiableAt H z | SOURCE | Classical chain-rule helper domain; supplied from actual solution predicate. |

Other local real-variable helpers explicitly take their own algebraic/ordering inputs. `orbital_scalar` is a distinctly named conditional algebra helper, **not** the source result: hm,hr,hs,hE,hEdef,haxis,hact,hecc2,hesq,hdot2,hnn,hD express respectively positive mass/radius, nonnegative squared momentum, negative energy, defining identities, the independently proved eccentricity identity and Cauchy bound. Its caller `orbital_identities` proves every one from source data before applying it (Orbital.lean 178–208). No such result-shaped input survives in the source-facing theorem. Likewise eccDeficit order/zero helpers assume exactly their own scalar antecedents, and the finite-infimum continuity helper assumes continuous constituents which its concrete consumers supply from proved results.

## Declaration inventory

Each row is one new public declaration; all names have prefix `KAM.Planetary.StrongAMD`. Locations are relative to `KAM/Planetary/StrongAMD/`. Definition edge cases and logical input expansion are tabulated above. PASS here is package-scoped, not frozen theorem closure.

| Location | Declaration | Verdict | Source / reason |
|---|---|---|---|
| Momentum.lean:41 | `strongAMD` | PASS | MAIN (2), OD-1; absolute total momentum. |
| Momentum.lean:60 | `totalMomentum_const` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:67 | `strongAMD_sub_eq_sum` | PASS | MAIN (13), stronger without negative-energy assumptions. |
| Momentum.lean:76 | `strongAMD_nonneg` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:86 | `strongAMD_eq_sum_sub_of_nonneg` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:95 | `strongAMD_eq_sum_add_of_nonpos` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:104 | `totalMomentum_ne_zero_of_strongAMD_lt` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:115 | `action_sub_strongAMD_le_cross_of_pos` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:130 | `action_sub_strongAMD_le_neg_cross_of_neg` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:146 | `cross_sign_and_margin` | PASS | MAIN 137; per-planet sign and absolute projection margin. |
| Momentum.lean:165 | `sum_action_mul_eccDeficit_le_strongAMD` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Momentum.lean:179 | `strongAMD_eq_physicalAMD` | PASS | MAIN L3 / LP-MOM items 4–8; exact conservation, projection or deficit identity. |
| Orbital.lean:37 | `planeSq_eccVector_identity` | PASS | MAIN L2 proof; eccentricity-square expansion, no sign of L. |
| Orbital.lean:57 | `planeDot_eccVector` | PASS | L2 radial algebra identity. |
| Orbital.lean:78 | `orbital_scalar` | PASS | Conditional algebra helper only; all inputs produced by orbital_identities. |
| Orbital.lean:159 | `orbital_identities` | PASS | MAIN L2 (11)–(12), all 10 conclusions; radial case retained. |
| Reflection.lean:36 | `reflectPlane` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:39 | `reflectSign` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:42 | `reflectVec` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:45 | `reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:47 | `reflectPhase_fst` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:48 | `reflectPhase_snd` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:50 | `reflectSign_mul_self` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:53 | `reflectVec_reflectVec` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:58 | `reflectPhase_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:61 | `reflectPlane_reflectPlane` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:64 | `reflectPlane_sub` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:68 | `reflectPlane_add` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:72 | `reflectPlane_smul` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:76 | `planeSq_reflectPlane` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:79 | `planeLength_reflectPlane` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:83 | `planeDot_reflectPlane` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:87 | `planeCross_reflectPlane` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:91 | `bodyVector_reflectVec` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:96 | `bodyVector_reflectPhase_fst` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:100 | `bodyVector_reflectPhase_snd` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:108 | `planeLength_reflectPhase_fst` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:112 | `planeLength_reflectPhase_sub` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:118 | `keplerEnergy_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:123 | `keplerAxis_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:127 | `keplerAction_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:131 | `keplerEccVector_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:137 | `planeLength_keplerEccVector_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:141 | `planeCross_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:146 | `totalMomentum_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:151 | `strongAMD_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:156 | `noCollision_reflectVec_iff` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:161 | `movingHamiltonian_reflectPhase` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:172 | `reflectVecCLM` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:176 | `reflectPhaseCLM` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:180 | `reflectPhaseCLM_apply` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:184 | `reflectVec_single` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:191 | `reflectVec_zero` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:194 | `single_eq_reflectSign_smul` | PASS | LP-MOM item 9 / N8; literal reflection algebra or invariant. |
| Reflection.lean:198 | `differentiableAt_reflectPhase` | PASS | Differentiability transported by the involution. |
| Reflection.lean:208 | `hamiltonianVectorField_reflectPhase` | PASS | N8 equivariance helper; true invariance/differentiability premises. |
| Reflection.lean:252 | `isMovingSolutionOn_reflectPhase_of` | PASS | N8 forward solution transport, all predicate fields supplied. |
| Reflection.lean:268 | `isMovingSolutionOn_reflectPhase_iff` | PASS | N8 two-way physical-time solution equivalence. |
| Threshold/Continuity.lean:30 | `contactScale` | PASS | MAIN (15); exact m(α). |
| Threshold/Continuity.lean:33 | `contactPoint` | PASS | MAIN (15); exact (u,v). |
| Threshold/Continuity.lean:38 | `contactObjective` | PASS | Exact composition with pair objective. |
| Threshold/Continuity.lean:41 | `continuous_actionAxis` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:47 | `isOpen_chamber` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:57 | `contactScale_pos` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:60 | `contactScale_le_one` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:62 | `mul_contactScale_le` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:69 | `alpha_bounds` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:78 | `contactPoint_mem` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:105 | `pairThreshold_isLeast_contact` | PASS | MAIN (15); attained full contact parameter minimum. |
| Threshold/Continuity.lean:135 | `pairThreshold_eq_sInf_contact` | PASS | MAIN (15); infimum equality, correct orientation. |
| Threshold/Continuity.lean:141 | `continuous_contactObjective` | PASS | MAIN L4 (15); scalar bounds or joint continuity with source domain. |
| Threshold/Continuity.lean:167 | `continuousOn_pairThreshold` | PASS | MAIN L4; compact fixed interval on chamber subtype. |
| Threshold/Defs.lean:30 | `actionAxis` | PASS | MAIN 45; squared ratio. |
| Threshold/Defs.lean:33 | `chamber` | PASS | MAIN 43; positive ordered axes. |
| Threshold/Defs.lean:37 | `eccDeficit` | PASS | MAIN 45; literal real square-root formula. |
| Threshold/Defs.lean:40 | `pairFeasible` | PASS | MAIN 47–49; correct inequality and endpoints. |
| Threshold/Defs.lean:45 | `pairObjective` | PASS | MAIN 49; exact weights. |
| Threshold/Defs.lean:49 | `pairThreshold` | PASS | OD-2; literal infimum and proved characterization. |
| Threshold/Defs.lean:53 | `AdjIdx` | PASS | Exact adjacent-pair index. |
| Threshold/Defs.lean:56 | `AdjIdx.upperIdx` | PASS | Bounded successor, no wrap. |
| Threshold/Defs.lean:60 | `crossThreshold` | PASS | OD-2; literal formula or definitional carrier equality. |
| Threshold/Defs.lean:64 | `starThreshold` | PASS | OD-2; literal formula or definitional carrier equality. |
| Threshold/Defs.lean:67 | `strongThreshold` | PASS | OD-2; literal formula or definitional carrier equality. |
| Threshold/Defs.lean:69 | `AdjIdx.lt_upperIdx` | PASS | Successor strictly exceeds lower index. |
| Threshold/Defs.lean:74 | `OrderedActions` | PASS | OD-2 chamber subtype. |
| Threshold/Defs.lean:78 | `orderedPairThreshold` | PASS | OD-2 exact carrier restriction. |
| Threshold/Defs.lean:82 | `orderedCrossThreshold` | PASS | Literal carrier finite infimum; empty-case note above. |
| Threshold/Defs.lean:86 | `orderedStrongThreshold` | PASS | OD-2 source carrier and n≥2. |
| Threshold/Defs.lean:89 | `orderedPairThreshold_eq` | PASS | OD-2; literal formula or definitional carrier equality. |
| Threshold/Defs.lean:92 | `orderedStrongThreshold_eq` | PASS | OD-2; literal formula or definitional carrier equality. |
| Threshold/Pair.lean:30 | `eccDeficit_nonneg` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:36 | `eccDeficit_mono` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:44 | `eccDeficit_eq_zero` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:54 | `eccDeficit_lt_one` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:59 | `continuous_eccDeficit` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:62 | `continuous_pairObjective` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:68 | `isCompact_pairFeasible` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:80 | `pairFeasible_nonempty` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:87 | `pairThreshold_isLeast` | PASS | MAIN L4; universal attained-minimum characterization. |
| Threshold/Pair.lean:97 | `exists_pairThreshold_attained` | PASS | LP-THR item 2 verbatim existential/minimality shape. |
| Threshold/Pair.lean:104 | `pairThreshold_le_of_feasible` | PASS | LP-THR item 8; no chamber restriction needed. |
| Threshold/Pair.lean:110 | `actionAxis_pos` | PASS | MAIN L4; elementary objective/feasible-set lemma with explicit scalar premises. |
| Threshold/Pair.lean:117 | `exists_contact_minimizer` | PASS | MAIN L4; scaling to contact preserves optimum. |
| Threshold/Pair.lean:157 | `pairThreshold_pos` | PASS | MAIN L4; chamber/order rule out zero eccentricities. |
| Threshold/Pair.lean:181 | `pairThreshold_lt` | PASS | MAIN (14); competitor (0,1-α). |
| Threshold/Strong.lean:30 | `exists_iInf_eq_of_finite` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:36 | `iInf_le_of_finite` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:39 | `continuousOn_iInf_of_finite` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:51 | `starThreshold_le` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:54 | `exists_starThreshold_eq` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:58 | `crossThreshold_le` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:62 | `nonempty_adjIdx` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:65 | `exists_crossThreshold_eq` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:70 | `strongThreshold_le_cross` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:73 | `strongThreshold_le_star` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:76 | `strongThreshold_le_pair` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:80 | `strongThreshold_le_action` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:85 | `strongThreshold_eq_member` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:94 | `crossThreshold_pos` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:99 | `starThreshold_pos` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:104 | `strongThreshold_pos` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:108 | `continuousOn_crossThreshold` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:114 | `continuousOn_starThreshold` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:120 | `continuousOn_strongThreshold` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:126 | `strongThreshold_eq_min_first` | PASS | MAIN (14); predecessor pair handles nonfirst actions. |
| Threshold/Strong.lean:148 | `orderedPairThreshold_pos` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:152 | `orderedPairThreshold_lt` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:156 | `continuous_orderedPairThreshold` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:160 | `orderedStrongThreshold_pos` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:164 | `continuous_orderedStrongThreshold` | PASS | MAIN (3)/(14); finite minimum API with required nonemptiness. |
| Threshold/Strong.lean:168 | `orderedStrongThreshold_eq_min_first` | PASS | MAIN (14) on exact carrier. |

## Mechanical verification (independent checks)

All Lean/Lake invocations were serial and used the D53 wrapper exactly:

```
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Targeted build command:

```
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-thr KAM.Planetary.StrongAMD.Orbital KAM.Planetary.StrongAMD.Momentum KAM.Planetary.StrongAMD.Reflection KAM.Planetary.StrongAMD.Threshold
```

This script acquires the compile gate and wraps each `lake build <Module>` individually with D53. Exact per-target completion output, in order:

```
Build completed successfully (9091 jobs).
Build completed successfully (9103 jobs).
Build completed successfully (9104 jobs).
Build completed successfully (9051 jobs).
```

No package warnings. The existing `KAM/Kepler/Energy.lean:106:35` (`hm`) and `:106:48` (`hκ`) unused-variable warnings were replayed. **Wrapper exit 1 despite all four successful builds:** its final `[ $rc -ne 0 ] && { ...; exit $rc; }` has status 1 when rc=0, which becomes the loop/script status. This is a helper-script reporting defect outside the audited diff, not an elaboration failure; no wrapper was edited.

Axiom check command (exit **0**):

```
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/lp_bar1_audit_1.lean
```

The temporary probe imports `KAM.Planetary.StrongAMD.Threshold` and `KAM.Planetary.StrongAMD.Reflection` and runs `#print axioms KAM.Planetary.StrongAMD.<name>` for **every one of the 131 inventory declarations**, including all 106 public theorems and all 25 definitions/abbreviations. Exact normalized output sets:

| Exports | Output |
|---|---|
| `AdjIdx`, `AdjIdx.upperIdx` | `does not depend on any axioms` |
| `AdjIdx.lt_upperIdx`, `nonempty_adjIdx` | `depends on axioms: [propext, Quot.sound]` |
| All other 127 exports in the inventory | `depends on axioms: [propext, Classical.choice, Quot.sound]` |

Thus every main result has precisely the standard triple, and no declaration depends on `sorryAx` or any project axiom. The probe is deleted after use. No provider/frozen type-match probe applies: this package creates no provider or frozen anchor. Semantic comparison is against the exact source-facing types in the diff and the component briefs.

Kernel replay and short-name checks: **not rerun**, as the user states the launcher already ran them. Their hidden pane output/exit codes are not represented as independently observed evidence here. The visible BAR1 handoff records successful `main_shortname_check.py` checks on eight modules, and successful earlier builds/lint on a historical snapshot. Current build/axiom/lint evidence in this report is independent of those older receipts.

Static checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. No frozen/manifest/README changes.
- `git diff inp-lp...HEAD -- KAM/Root/Planetary.lean`: exactly eight generated public imports of the new modules. Recorded generated-root change; auditor did not regenerate or edit it.
- Module line counts: Momentum 186; Orbital 212; Reflection 279; Threshold facade 20; Continuity 178; Defs 95; Pair 202; Strong 173. All far below 1500; module headers, public imports, docstrings and public sections present; exposed definitions use `@[expose] public noncomputable section`.
- `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option|KAM\.Provider|KAM\.Root' KAM/Planetary/StrongAMD`: no matches (rg exit 1). Direct imports contain no provider or frozen theorem; transitive axiom closure above excludes draft-sorry dependence.
- `git diff --check inp-lp...HEAD`: exit **2**, exactly `KAM/Planetary/StrongAMD/Threshold/Pair.lean:113: trailing whitespace.` The trailing space after `exact pow_pos (div_pos (hI.1 i) (hν i)) 2` is cosmetic and unmodified.

Source SHA-256 pins:

```
MAIN.md        68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b
AMENDMENTS.md  c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881
SPEC.md        ffd8a2793b9b37ca35e4a626d38d9af3c2f79d5cefa7c36e5e2aa844978dad22
LP-THR.md      89654791004db25f1ad07050f48d51f287ef49f76b6f4a3ba229cad379a95da4
LP-MOM.md      df607e64b266c5159f1548ca302bde3a6806995eeceb4bf9e028dd5bc18416f7
```

Lint command (only the prescribed wrapper; exit **0**):

```
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-thr
```

Complete output:

```
check_lean_modules: PASS (3669 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

## Findings, limitations, and combined verdict

**LP-BAR1: PASS WITH NOTES**, for LP-THR items 1–8 and LP-MOM items 1–9 at the pinned HEAD. No blocking mathematical defect, conclusion-shaped source hypothesis, unjustified off-carrier use, forbidden axiom, or source-fidelity failure was found. Builds, all-export axiom checks and prescribed lint succeeded, subject to the build-wrapper status defect documented above. Kernel replay/name checks are launcher-supplied, not independently rerun. No frozen LP anchor exists, so this verdict cannot authorize a seal or establish omitted sharpness claims.

Nonblocking notes:

1. **Audit authority pointer:** the requested LP-BAR1 brief is absent; the actual component briefs and combined handoff establish the bounded scope. The handoff's merge hash differs from the current audited HEAD; this report pins the actual bytes/base/diff.
2. **Future carrier decision:** OD-1/OD-2 remain overnight defaults. The total helpers are faithful literal formulas with proved on-carrier semantics; their off-source behavior, including empty finite infima, is recorded above. This audit does not settle future owner freeze choices.
3. **Scope boundary:** interior minimizers, geometric realization and the relative Laskar–Petit identification remain outside this package. No full sharpness/whole-MAIN-L4 closure is claimed.
4. **Cosmetic code finding:** Pair.lean:113 has one trailing space (`git diff --check` exit 2); source lint passes. No code repair was made.
5. **External build helper:** `lp_build.sh` ends with a false success guard and reports exit 1 after four successful builds. Its displayed per-target success messages and script body distinguish this from a failed target. Report to the orchestrator; not repaired here.
6. **Documentation:** BAR1 handoff's `KAM.Iso.hamiltonianVectorField` reference should read `KAM.hamiltonianVectorField`. LP-THR brief's opening definition range “§1 lines 51–64” is stale: actual chamber/formulas occur at MAIN 41–55. The exact formulas, read directly, match the implementation.

Suspected **mathematical source errata:** none in the audited MAIN L2–L4 material as amended. Accepted strengthening: `strongAMD_sub_eq_sum` drops negative-energy/nonzero-position assumptions because its algebra only needs momentum conservation. All such physical premises remain on the inequalities needing them. No deviations introduced by the auditor.

Repository edits by this audit: **only this report**. The `.lake/abi-scratch/lp_bar1_audit_1.lean` probe was removed; no state-changing git, source repair, generated-file edit, manifest change, build-budget override, or additional agent was used.
