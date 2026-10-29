# P11A-P7c prover handoff (branch inp-p11ap7c, 33170ae3; contains P7b (in audit), P7 round 1, P5; offloaded package run by the main orchestrator)


## Files (new, all under KAM/Planetary/Preparation/; Slow.lean facade NOT edited, P7d must add the imports)
- SlowDerivative.lean: p11SlowW, p11Jproj, fderiv_comp_Jf, fderiv_slowW_nat (d_rho W = Omega/2pi + d_rho Z),
  p11_slow_dotC_split (k.dh0 = k1.omega + eps k.dW), p11_scalar_step_bound (Cauchy), fderiv_append_slice.
- SlowDivisor.lean: p11SlowCenter, p11SlowBox (spec V), p11SlowZDom, Omega_lipschitz, re_dotC_Omega,
  dotC_Omega_lower, p11s2_spec, slowW_differentiableOn, **p11_slow_divisor** (as-nr, pure-slow + mixed,
  via fast_divisor / omega_lipschitz-style), p11_drho_of_clause6 (clause 6 at alpha=0 -> hdZ),
  p11SlowBox_subset_avg (spec box inside P7b's p11SlowAvgBox).
- SlowRates.lean: exact exponent identities slow_disp_rho/J/theta, slow_g_quad; **slow_b2_eventually** (as-b2, via e4).
- SlowSmall.lean: s1/s2 >= c/log^(tau+1) bounds; eventual lemmas slow_base_eventually, slow_pe_eventually
  (pi eps <= s2), slow_cz_eventually (K2 c (eps+eta1) <= gamma K2^-tau/8, uses p11eta1_source_rate),
  slow_R_eventually (Cauchy smallness), slow_pos.
- SlowConclude.lean: **p11_slow_conclude** (as-concl): aniso_avg with a=b=n, center, r1=s2, r2=pi eps, T=K2,
  alpha1=gamma/4 K2^-tau, alpha2=eps alpha1, E0=c0 eps^(5/2) log^(2tau+1); returns Psi,g2,f3 and clauses 9-28 of
  P11SlowSpecOf in spec order. c0 (actual f2 bound), cf0 (|coeff f2 0| <= cf0 eps^3) and c enter only via explicit
  lower bounds hcE,hcg,hcd1,hcd3, so g2/displacement constants do not depend on c.

## Hypothesis shapes vs P7b (checked after merge)
- p11SlowW C Z = fun I => p11SlowSec C I + Z I (rfl); h0 = p11SlowH0 matches my h3 (h0 = C.h∘J + eps*W) up to rfl.
- clause 6 of P7b (p11_slow_Z_jets) is exactly the hypothesis of p11_drho_of_clause6 (c := c from hc).
- p11_slow_f2_wbound is stated on p11SlowAvgBox with constant coth^(2n)*p11SlowC0*...; my hb is on p11SlowBox (spec V),
  c0 := coth^(2n)*p11SlowC0; use p11SlowBox_subset_avg to restrict. Needs hsm: 64 eps < rz^2 (implied by 3 eps <= rz^2/32).
- NOT supplied by either package, P7d must prove: (i) MW: sup bound of p11SlowW C Z on p11SlowZDom (constant in eps)
  for p11_slow_divisor; (ii) cf0: |coeff f2 I 0| <= cf0 eps^3 on V/2 (f^_0 = int f1∘(id,Pi), "size c eps^3"); (iii) hreal_h,
  hper, hreal_f, hf2 differentiability from P7b exports; (iv) hb2 for c via slow_b2_eventually (c0 = c) ; (v) choose
  c = max(c0, cf0+..., constants of hcd1/hcd3, p11SlowCZ) then eps2 from the eventually lemmas (all hypotheses of
  p11_slow_divisor are covered by slow_{base,pe,cz,R}_eventually with cZ = c(eps+eta1)).

## Checks
Gate builds of all five modules and SlowDivisor after merge: success, no warnings about sorry. scripts/lint_sources.sh: only the
generated-KAM.lean notice. #print axioms of p11_slow_divisor, p11_slow_conclude, slow_b2_eventually, slow_cz/R/pe/base_eventually,
p11_drho_of_clause6: propext, Classical.choice, Quot.sound only. No maxHeartbeats; files <= 489 lines.

## Uncertainties / deviations
- Design signal: first draft of p11_slow_conclude and of the smallness lemma hit the default heartbeat limit (nlinarith in
  large contexts); fixed by extracting arithmetic lemmas (g_bound_arith, small_arith_*) and generalizing, no overrides.
- Added hypothesis hcf0 : 0 <= cf0 and the (ii) bound above are P7d obligations (not assumptions of a source result).
- No errata found.

ORCHESTRATOR RULINGS: 23:35 split of P7's core (P7c = plan steps 3-4, parametric in P7b's outputs); 00:20 each piece audited as it finishes; P7d assembles avg_slow_of_spec and the signed wrappers (not findings here).

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (avg_slow, steps as-nr, as-b2, as-concl) and the P7 round-1 handoff (docs/tracks/P/audits/P11A-P7-handoff.md, plan steps 3-4); signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (P11SlowSpec clauses 9-28). Check: p11_slow_divisor (pure-slow and mixed), slow_b2_eventually, p11_slow_conclude returning clauses 9-28 in spec order with constants independent of c as claimed; the parametric hypotheses match P7b's actual exports (the handoff's shape table); no hypothesis P7d cannot discharge. Audit ONLY: KAM/Planetary/Preparation/SlowConclude.lean KAM/Planetary/Preparation/SlowDerivative.lean KAM/Planetary/Preparation/SlowDivisor.lean KAM/Planetary/Preparation/Slow.lean KAM/Planetary/Preparation/SlowRates.lean KAM/Planetary/Preparation/SlowSmall.lean  Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
Orchestrator note: helper append_eq_add was renamed p11Slow_append_eq_add (clash with KAM.Planetary.append_eq_add in PGAssembly/FrequencyLip, a different lemma).
