# GAP-A prover handoff (branch inp-gapa, 9988913f; off inp; offloaded gap-fill package run by the main orchestrator)


## Files (new, append-only; no landed file edited)
- `KAM/Nekhoroshev/Partial/ThresholdExplicit.lean` (N11-O2)
- `KAM/Planetary/PlanarTorsion/Homological/Reality.lean` (T8b)

## Node -> declaration (namespace KAM.Nekhoroshev / KAM.Planetary; all unsigned)
- `stepN:p11:final-time` -> `nthr_final_time`: C_T, c_2 > 0 (`PartialConstants.thrCT`, `thrC2`);
  closed form `blockTime mu = C_T mu^(-1/2) exp(c_2 mu^(-1/(2n)))` (`nthr_blockTime_closed`);
  Tendsto of `C_T mu^(1/2) exp((c_2/2) mu^(-1/(2n)))` to atTop along 𝓝[>] 0; exists mu_f > 0 such
  that for 0<mu<mu_f: `C_T mu^(1/2) e^(..) <= mu T_P e^(-mu^(-a_n))`, `1 <= C_T mu^(1/2) e^(..)`,
  and `mu⁻¹ exp(mu^(-a_n)) <= blockTime mu`.
- `stepN:p11:final-mu` -> `nthr_final_mu` (kappa stands for k, hypothesis 0 < kappa = source k>=1):
  explicit `thrMuA..thrMuE` (mu_a = 2 pi eps0/kappaC, mu_b = rho^(1/b_n),
  mu_c = (pi s cK/(3 sqrt n))^(2n), mu_d = (cK/(256 k rho R0))^(1/gamma_1),
  mu_e = (cK/R0)^(1/gamma_2); gamma_1 = 1/(2n)-2 b_n, gamma_2 = 1/(2n)-b_n, positive by
  `exponents`), all positive; exists mu_f (from final-time) with mu_0 = min of the six positive;
  for 0<mu<mu_0: eps<=eps0, mu^b_n<=rho, 6<=kappa mu, 256 k rho R0 mu^(-2 b_n) <= K mu,
  R0/(2 K mu) <= mu^b_n/2, plus the time comparison. Uses `PartialConstants`, `nthr_pos`,
  `nthr_K_eq`, `nthr_rpow_le_eventually` of Threshold; helpers `nthr_rpow_lt_of_lt`,
  `nthr_rpow_split_le`.
- `stepP:p11b:ho-def` -> `ho_def_conj` (conj(F_k/(i k.Omega)) = F_{-k}/(i(-k).Omega), for all k),
  `ho_def_real` (`chiComplex` has im = 0 and equals `(p11c_chi F freq I z : ℂ)`);
  `chiComplex`, `neg_mem_chiModes`.
- `stepP:p11b:ho-eq` -> `ho_eq_forward` ({chi,N_0} = F - F_0, = existing `chi_bracket`),
  `ho_eq_reversed` ({N_0,chi} = -(F - <F>)), via `p11c_bracket_antisymm`
  (from `symplecticForm_hamiltonianVectorField`, `symplecticForm_antisymm`).
  Convention: `p11c_bracket f g z = fderiv f z (X_g z)`, as in signed `homological`.

## Approach
final-time: block time rewritten with y = mu^(-1/(2n)) (K = cK y, kappa = 6 c_2 y, y^n = mu^(-1/2));
y^(T/E) <= (c_2/2) y eventually (T/E<1) and the exp/power limit give mu_f.
final-mu: each inequality from its mu_x via rpow monotonicity. Reality: star of a sum, pairing k <-> -k
by `Finset.sum_nbij'`.

## Checks
- `inp_lake_build.sh ... KAM.Nekhoroshev.Partial.ThresholdExplicit
  KAM.Planetary.PlanarTorsion.Homological.Reality` -> "Build completed successfully (9149 jobs)"
  (only pre-existing warnings from other files).
- `scripts/lint_sources.sh`: check_lean_modules PASS; frozen guard OK; ABI hashes OK; only message
  "KAM.lean is out of date" (not edited, per rule).
- `#print axioms` of nthr_final_time, nthr_final_mu, ho_def_conj, ho_def_real, ho_eq_forward,
  ho_eq_reversed: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, sorry, axiom; lines <= 100 cols; files 256 / 98 lines.

## Uncertainties / errata / deviations
- No signature file entries exist for these unsigned exports; statement shapes are mine (literal
  conclusions of the nodes). mu_f is existential (the source defines it by a limit).
- `nthr_final_mu` needs 0 < kappa (source k >= 1) for mu_d to be positive.
- No source errata found. No design signals.

ORCHESTRATOR RULING (OVERNIGHT 20:55): N11-O and T8 landed with four graph nodes left NOT_STARTED because the landed code states weaker or adapted forms. GAP-A appends exports to establish them; no signed statement changes.

AUDIT FOCUS: for EACH of the four graph records, read its NODE block in docs/graph/N/DEPGRAPH.md (stepN:p11:final-mu, stepN:p11:final-time) or docs/graph/P/DEPGRAPH.md (stepP:p11b:ho-def, stepP:p11b:ho-eq): SOURCE_CONCLUSION, LEAN_NOTE and the cited blueprint lines. Verdict per node: does the named export state that literal conclusion (constants as printed: mu_a..mu_e formulas, mu_0 = min, the five inequalities, T_P closed form with C_T and c_2, the divergence defining mu_f; conj(F_k/(i k.Omega)) = F_{-k}/(i(-k).Omega) and reality of the unprojected sum; {chi,N_0} = F - F_0 and {N_0,chi} = -(F - <F>)), using the landed Lean objects (PartialConstants, blockTime, p11c_chi, p11c_bracket) rather than re-definitions, with only source hypotheses? Note any deviation (e.g. kappa for the source k, inequalities rescaled by mu) and whether it is a faithful restatement. Also (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, landed files unchanged. Audit ONLY KAM/Nekhoroshev/Partial/ThresholdExplicit.lean and KAM/Planetary/PlanarTorsion/Homological/Reality.lean.
