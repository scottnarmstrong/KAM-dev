# P11A-P7 prover handoff, round 1 (PARTIAL; branch inp-p11ap7)


Branch inp-p11ap7. All files below build through the gate, lint passes (except the pre-existing
"KAM.lean out of date", which I did not touch), no sorry/axiom/heartbeat overrides.

## Delivered (all sorry-free)
- `Preparation/SlowData.lean`: verbatim signed `p11Rescale`, `p11PreparedBox`, `p11K2`, `p11s2`,
  `P11SlowData`, `p11PartialVec` (long lines only re-wrapped) and unsigned `P11SlowSpecOf C Fast nu eps c A`
  (signed body, two lets replaced by parameters; `P11SlowSpec` will unfold to it by rfl).
- `Preparation/SlowCauchy.lean`: `p11PartialVec_norm_le` — sharp polydisc Cauchy bound
  `‖p11PartialVec α g J‖ ≤ (∏ (α i)!) * M / R^(∑ α i)` (needed for the Z jet clause), via
  one-variable `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
- `Preparation/SlowJets.lean`: `p11_jets_vanish_of_pow_bound` (‖F z‖ ≤ M‖z‖^4 ⇒ iteratedFDeriv ℂ j F 0 = 0, j<4;
  polarization via PGAssembly/JetsPolar) — feeds `polar_avg` clause (c) for the quartic remainder.
- `Preparation/SlowMean.lean`: `secular_extract`, `p11FastMean_differentiableOn`, `p11C_eq_fastMean`,
  `p11C_differentiableOn`, `p11R4`, `p11Gbar`, `p11G_decomp` (G = C + ΣΩ(x²+y²)/2 + R4 + Gbar),
  `p11R4_differentiableOn`, `p11R4_bound`, `p11R4_jets`.
- `Preparation/Slow.lean`: facade.

## NOT done (plan, for the next prover)
`avg_slow_of_spec` (statement: hC, hh : P11SecularHReal C, 1≤nu, eps1, Fast : ℝ → P11FastData n with
P11FastSpec C eps (Fast eps) for eps ≤ eps1 ⊢ ∃ eps2 c2, ... ∀ eps ≤ eps2, ∃ A, P11SlowSpecOf C (Fast eps) nu eps c2 A).
Intended construction (c2 = max of data constants, eps2 small):
1. `polar_avg` on R4 (S = MF/16, jets from `p11R4_jets`) and on Gbar (S = eta1) and on G; Z := AR+AB;
   h0 := h + eps(C+ΣΩρ/2π+Z); f2 := eps(G∘Π − (C+ΣΩρ/2π+Z)) + f1∘Π; clause 1 from the fast identity,
   clause 2 from linearity of `p11PolarAverage` on Re ρ>0; ∂ρ Z ≤ c(eps+eta1) by `cauchy_open` (radius πeps/4 for AR,
   π rz²/32 for AB); J-jets by `p11PartialVec_norm_le` with R = s1/4.
2. f2 sup bound c eps^{5/2} log^{2τ+1} (needs the exported eta1 rate, P5c) then weighted bound via
   `KAM.summableWeighted_torusCoeffW` (needs 1-periodicity of f1 in θ, derivable from lattice + F periodic).
3. divisor clause (pure-slow / mixed) with `fast_divisor`/`omega_lipschitz`; (B2) and displacement via `e4`.
4. apply `aniso_avg` (a=b=n, c=center, r1=s2, r2=πeps, T=K2, alpha1=γK2^-τ/4, alpha2=eps·alpha1) using E_a := c0 eps^{5/2}log^{2τ+1}
   (so that g2/displacement constants do not depend on c2), then repackage.
Signed wrappers (P11SlowSpec, avg_slow, p11SlowConstant, p11SlowData) not stated: inp-p11ap2f / inp-p11ap5w / P5c merges not performed.

## Checks
Gate builds of SlowData, SlowCauchy, SlowJets, SlowMean, Slow: success. `sh scripts/lint_sources.sh`: only the generated-KAM.lean notice.
No `#print axioms` run (no main theorem).

## Uncertainties / deviations / errata
- p11Rescale, p11PreparedBox are defined here as briefed although the design table lists them under Prepared; P8 must import, not redefine.
- Design note: the signed P11SlowSpec needs `Z` differentiable, which uses C.C = FastMean(·,0) (derived, `p11C_eq_fastMean`); no erratum found.
- The 650-line estimate is far too low (est. 2000+ lines for the remaining core).

ORCHESTRATOR RULINGS: 21:50/23:00 parametric core; 23:35 the core avg_slow is split into P7b, P7c, P7d (avg_slow itself and its steps are NOT findings here); 00:20 each piece audited as it finishes. This audit covers ONLY the round-1 deliverables.

AUDIT FOCUS: (a) the signed definitions p11Rescale, p11PreparedBox, p11K2, p11s2, P11SlowData, p11PartialVec in SlowData.lean = P11ASignatures.lean EXACTLY (only line wraps); (b) the UNSIGNED P11SlowSpecOf is the signed P11SlowSpec body with exactly the two lets (C := p11SecularData D, Fast := p11FastData D eps) replaced by parameters, so that P11SlowSpec unfolds to it by rfl; (c) p11PartialVec_norm_le (SlowCauchy), p11_jets_vanish_of_pow_bound (SlowJets) and the SlowMean decomposition and bounds are sound, with no added premise; (d) hygiene. Audit ONLY KAM/Planetary/Preparation/{SlowData,SlowCauchy,SlowJets,SlowMean,Slow}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
