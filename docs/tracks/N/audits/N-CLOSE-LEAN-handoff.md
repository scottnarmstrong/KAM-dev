# N-CLOSE-LEAN prover handoff (branch inp-ncloselean, e442187e; track N, run by the main orchestrator)


## Files
- NEW `KAM/Nekhoroshev/Assembly/HypothesesFull.lean` (public `hypotheses_check_full`).
- CHANGED `KAM/Nekhoroshev/Assembly/Confinement.lean`: added public `head_theorem1_setting`
  (one-line wrapper of the private `cf_setting`; no existing statement changed).
- `KAM.lean` is out of date (new module); orchestrator regenerates it (rule 10, not touched).

## Node -> declaration
`bpN:p10:hypotheses-check` -> `KAM.Nekhoroshev.hypotheses_check_full`
(items (a)-(h) in one conjunction, in the order a, b, c, d, e+setting+(g), f, h).

SOURCE_CONCLUSION: "(a) V ⊂ B(0,R)_s, U ⊂ B(0,5R/8) ⊂ B(0,R) ⊂ 𝓑_s(R), W = ℝⁿ × U ⊂ W_s, P ≠ ∅,
B(0,R/2) ⊂ P; (b) h holomorphic on V, real on U, complex Hessian operator norm ≤ B_c on V; (c) h is
ℓ,μ-quasi-convex on U, 0 < μ ≤ B_c; (d) r_0 ≤ ℓ/(2B_c); (e) f|_{T_{s_1}×V} ∈ 𝒪(r_0,s_1)^ℝ and
¦f¦_{r_0,s_1} ≤ ε′, 0 < ε′ ≤ ε_1, so (n,P,r_0,s_1,μ,B_c,ℓ,h,f|) is a Theorem-1 setting with constants
A, ε_1, a, R_0; (f) ‖ω_h(I_0)‖ ≥ ω_min > μ r_0/8 for I_0 ∈ B(0,R/2); (g) 0 < ω_min ≤ Ω_0(I_0) ≤ √n M,
T_0 = A² s_1/Ω_0 ≥ 2T; (h) H_{h,f} = (h+f)|_W real valued and X_{H_{h,f}} = X_{H^ℝ} on W".

Lean mapping (hypotheses: hn : 3 ≤ n, p.Pos, HeadHyp p h (H1-H4 etc.), IsAnalyticPerturbation p.R p.s ε f,
0 < ε ≤ p.eps0; V = polyNbhd (centralSet n R) r0, P = {J | ‖J‖ ≤ R/2}, W = univ ×ˢ ι⁻¹' V):
- (a): V ⊆ actionNbhd; real points of V in ball(5R/8), ball R, realActionDomain; W ⊆ Wdom n R s;
  P nonempty; actionBall (R/2) ⊆ P.
- (b): DifferentiableOn, real on U, Hessian operator bound by p.B.
- (c),(d): quasi-convexity inequality; 0 < mu ≤ B; r0 ≤ ell/(2 B).
- (e): InClass, RealOn, WBound with p.epsPrime ε, 0 < ε' ≤ eps1; ∃ S : Theorem1Setting P r0 s1 mu B ell h f
  with thmA mu B = p.A, thmEps0 = p.eps1, a = 1/(2n), r0/thmA = p.R0.
- (g): for I0 ∈ P ∩ actionBall(R/2): 0 < wmin ≤ Ω0 ≤ √n M and 2T ≤ thmA² s1 / Ω0, with
  Ω0 = (omega0Ball S I0 _).maximum (the setting's Ω_0).
- (f): hc_exc (strict μ r0/8 < wmin ≤ ‖ω_h‖, euclid norm).
- (h): on W, (h(ιI)+f(ιθ,ιI)).im = 0 and realHamiltonian h f = realH (h+f); for any Hlocal equal to
  realHamiltonian on W, the frozen fields agree with X of realH (h+f) on W.

## Checks
- `inp_lake_build.sh <wt> KAM.Nekhoroshev.Assembly.HypothesesFull`: Build completed successfully
  (3337 jobs); no warnings in my files.
- `main_shortname_check.py` (HypothesesFull, Confinement): OK.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected, generated); modules PASS, frozen/ABI OK.
- `#print axioms hypotheses_check_full`, `head_theorem1_setting`: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, no sorry, new file ~150 lines, lines ≤ 100.

## Uncertainties
- (a) "W ⊂ W_s" is stated as W ⊆ `Wdom n R s` (= ℝⁿ × B(0,R+s)); "B(0,R)⊂𝓑_s(R)" via realActionDomain.
- (f)/(g) are stated in the Euclidean `euclid` norm as in the existing pieces; (g) quantified over I0 ∈ P with I0 ∈
  B(0,R/2) (membership proof as an explicit argument since omega0Ball needs it).
- (h): X_{H_{h,f}} is the frozen field of realHamiltonian; realH-equality is definitional.
- No errata or deviations found.

CONTEXT: all six frozen N theorems are sealed and graph N is synced; bpN:p10:hypotheses-check was open because its (a)-(h) proposition was proved only in pieces (N10-2-audit-1:24: hypotheses_check does not claim the whole setting or the Omega0 specification; the setting assembly was the private cf_setting). This package adds hypotheses_check_full and the public wrapper head_theorem1_setting, changing no existing statement.

AUDIT FOCUS: does hypotheses_check_full state the node's COMPLETE literal SOURCE_CONCLUSION (docs/graph/N/DEPGRAPH.md node bpN:p10:hypotheses-check; blueprint-N Part 10), items (a)-(h) including (d) r0 <= l/(2 B_c), the Theorem-1 setting with its constants, and (g)'s Omega_0 specification, from its SOURCE_HYPOTHESES, with nothing omitted, no extra premise and the source's quantifier order? Is the setting in (e) the genuine Theorem-1 setting (not a weaker record)? Hygiene: names (KAM and Mathlib), lines <= 100, no native_decide or axiom; head_theorem1_setting does not change cf_setting. Verdict for the node: PROVED / not. Audit ONLY KAM/Nekhoroshev/Assembly/HypothesesFull.lean and the diff of KAM/Nekhoroshev/Assembly/Confinement.lean.
