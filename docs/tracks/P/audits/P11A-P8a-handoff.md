# P11A-P8a prover handoff (branch inp-p11ap8a, 3879a7ba; contains P7d; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/Preparation/PreparedBasic.lean` (~540 lines; imports PreparedData, SlowAverageDom,
  SlowSmall, SlowDivisor, Weighted.SupWeighted). No sorry/axiom; no heartbeat override. Lines <= 100.
- The signature file has no declarations for P8a, so these are exported helpers with distinct names;
  nothing signed is redefined, `prepared`/`amount` are NOT proved here (P8e assembles).

## What is exported (names, graph steps)
- `p11PreparedCoreOf C Fast A eps W` / `p11PreparedCore D nu eps W : P11PreparedData n`: the construction.
  `N I = (h0+g2)((A_eps (0,I)).2)/eps`, `P z = f3(A_eps z)/eps`, `chain z = C.chart (Re (Fast.map (polarC
  (Psi (A_eps (real z))))))`, `checkW := W` (free; P8b/P8c supply the frequency datum).
- `P11PreparedBasicSpec D nu eps c Q`: the clauses of `P11PreparedSpec` that concern only N, P, chain,
  copied verbatim (formulas + chain, DifferentiableOn N/P, periodicity of P, RealOn (N+P) and P, N real,
  `p11Bound V P (c eps^(nu+3/2) ell^(2 tau+1))`, `fixedHamiltonian ∘ chain = eps (N+P).re`). Omitted
  (P8b/P8c/P8e): smallV/fderiv bounds on W, checkW formula, jet bound, scalar bound.
- ONE existence theorem `p11_prepared_basic D hnu : ∃ eps3>0, ∀ eps ≤ eps3, ∀ c ≥ p11SlowConstant D nu,
  ∀ W, P11PreparedBasicSpec D nu eps c (p11PreparedCore D nu eps W)`. Generic form
  `p11_prepared_basic_of_spec` takes the three signed specs plus `eps*MF <= e^-1`, `pi eps <= s2`,
  `64 eps < rz^2`.
- Per-clause lemmas: `p11Rescale_mem_dom` / `p11Rescale_mem_box` (domain chain A_eps(E) in
  T_{sigma_3/6} x V_2/2; uses eps*pi >= 3 eps... i.e. 3/2 < pi/2), `p11Rescale_real`,
  `p11PreparedCoreOf_{N,P}_differentiableOn`, `_P_periodic`, `_N_real`, `_P_real`, `_NP_real`,
  `_P_bound` (pr-a; via new `p11_norm_le_of_wbound_open`: pointwise wn bound on an open action set => sup),
  `_chain_eq` (H_2∘A_eps = H∘(Phi^1∘Theta-hat∘Psi_2∘A_eps) = eps H-hat; polar image in the fast domain via
  `p11_polarC_mem`, reality via `p11_polarC_real`), `p11_secular_ham_chart`, helpers `p11Box_isOpen`,
  `p11Box_mono`, `p11_actionNbhd_norm_lt`, `p11_slowBox_re_pos`.
- Domain-chain facts for the Phi^1 / Theta-hat steps are inside `_chain_eq` (polarC(Psi y) in
  WorkingDom(sigma/6, s1/2, rz/2); Fast.map into WorkingDom(sigma, s1, rz) subset WorkingDom(2 sigma, 2 rC, rz)).
  The remark "N_eps depends on (r, rho') only" is by construction (N is a function of the action only).

## Checks
- Gate build `KAM.Planetary.Preparation.PreparedBasic`: success (9419 jobs); only `dif_pos` deprecation warnings
  (same idiom as SlowSigned/FastSigned).
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated; not edited); module check, frozen guard,
  ABI hashes PASS. Short-name clash check of all new public names against the rest of KAM: none.
- `#print axioms` of `p11_prepared_basic`, `p11PreparedCoreOf_chain_eq`, `p11PreparedCoreOf_P_bound`:
  `[propext, Classical.choice, Quot.sound]`.

## Notes for P8e / uncertainties / errata / deviations
- `c` threshold: spec constant `c >= p11SlowConstant D nu` (= c_2 of avg_slow). `eps3` is explicit but implicit
  in the proof (min of u/2, eps1, eps2, e^-1/MF, rz^2/65).
- The sup bound `p11Bound V P` is stated on V (strip sigma/72 x complex 1-nbhd of the box), as in the signed spec.
- No errata found; no deviation from signed statements (spec clauses copied verbatim).

ORCHESTRATOR RULING (OVERNIGHT 01:05): P11A-P8 split into P8a (pr-basic, pr-a: the construction of N, P, chain and the clauses about them), P8b (pr-in, pr-b, pr-c, pr-d), P8c (amount steps, parametric) and P8e (assembly of the signed prepared and amount). The signed prepared itself is NOT a finding here; P8e assembles it. Clauses this package leaves to P8b/P8e (W bounds, checkW formula, jet and scalar bounds) are not findings.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (prepared, steps pr-basic and pr-a) and the graph records NODE: stepP:p11:pr-basic / stepP:p11:pr-a in docs/graph/P/DEPGRAPH.md; signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (P11PreparedSpec, P11PreparedData, prepared). Check that P11PreparedBasicSpec's clauses are VERBATIM the corresponding clauses of P11PreparedSpec (so P8e can assemble without restating), that p11_prepared_basic gives them with eps3 before eps and c >= p11SlowConstant as the design orders the quantifiers, that pr-basic and pr-a are each stated literally by an export, and that no premise is added. Audit ONLY KAM/Planetary/Preparation/PreparedBasic.lean (PreparedData.lean was audited with P11A-P8). Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
