# P-SEC prover handoff (branch inp-psec, 75a22aa8; track P, run by the main orchestrator)


Branch `inp-psec`, worktree /root/code/KAM-inp-psec. All work is NEW declarations in three NEW modules. No existing
statement was changed. Nothing under Frozen/, manifest/, Provider/, README.md or KAM.lean was touched.

## Files (all new)
- `KAM/Planetary/Preparation/SecDSource.lean` (316 lines): sec-D objects and identifications
- `KAM/Planetary/Preparation/SecESource.lean` (209 lines): A_eps, the eps-chart, E-domain mapping, complex H2 / H-hat
  identity, domain table
- `KAM/Planetary/Preparation/SecEFreq.lean` (247 lines): the frequency map and the normalized source formulas
- KAM.lean is NOT regenerated (rule 10). `scripts/lint_sources.sh` therefore reports
  "KAM.lean is out of date; run scripts/gen_root_imports.py". The orchestrator must regenerate it on landing.

## Approach
Each source object is a literal Lean definition that follows the blueprint display (p11-cp09-preparation.tex L145-153
for sec-D, L189-194 for sec-E). Each one is then identified with the implementation objects:
- the helpers `p11SlowH0` and `p11SlowF2` with a free correction Z;
- the parametric spec `P11SlowSpecOf`;
- the signed choose-or-default `p11SlowData`, under the D31 local specification guards;
- `p11PreparedCoreOf`.

The complex H2 identity uses only fields of `P11SlowSpecOf`: the identity h0+f2 = WorkingH o map o PolarC, MapsTo of
Psi, and the conjugation identity. It also uses the proved inclusion A_eps(E) in T_{sigma3/6} x V2/2, which needs
2 eps <= s2/2. So the existing identities DO cover the full source domain E, and no design decision is needed.

## Node -> declarations table

| node | source formula (quoted) | Lean declaration | file:line |
|---|---|---|---|
| sec-D | `P_eps={abs(Im zeta)_inf<sigma_F/6, abs(rho~_j-2 pi eps)<pi eps (forall j)}` | `p11PolarShell`, `mem_p11PolarShell`, `p11PolarShell_eq_prod`, `p11PolarShell_isOpen` | SecDSource.lean:44-68 |
| sec-D | `Re rho~_j > pi eps > 0` | `p11PolarShell_re_gt` (and `p11PolarShell_norm_lt`: abs rho~_j < 3 pi eps) | SecDSource.lean:70-87 |
| sec-D | `Pi(zeta,rho~) := Theta^(1)(zeta,rho~)` | `p11Pi`; `p11PolPt_eq_pi`; `p11PolarC_eq_pi` (p11PolarC = (id, Pi)) | SecDSource.lean:89-106 |
| sec-D | `abs(Pi(zeta,rho~))_inf <= sqrt(3 eps) e^{pi sigma_F/3}` | `p11Pi_norm_le` | SecDSource.lean:108 |
| sec-D | `G^(J,zeta,rho~)=G(J,Pi(zeta,rho~))` | `p11GHat` | SecDSource.lean:139 |
| sec-D | `G^_0 = int_{T^n} G^ d zeta` (raw average) | `p11GHat0`; `p11GHat0_eq_polarAverage` (rfl) | SecDSource.lean:142-147 |
| sec-D | `h_0(J,rho~)=h~(J)+eps G^_0(J,rho~)` | `p11SourceH0` | SecDSource.lean:150 |
| sec-D | `f_2=eps(G^-G^_0)+f_1 o (id,Pi)` | `p11SourceF2` | SecDSource.lean:155 |
| sec-D (correction Z) | `G^_0=C(J)+sum_j Omega~_j rho~_j+Z^` | `p11SlowH0_eq_source_iff`, `p11SlowF2_eq_source_iff` (helper = source iff Sec+Z = G^_0); `p11GHat0_eq_sec_add_Z` (Z = p11SlowZ AR AB = A R4 + A gbar on the box); `p11SlowH0_eq_source`, `p11SlowF2_eq_source` | SecDSource.lean:161-214 |
| sec-D (chosen datum) | h0, f2 as above on V2, T_{sigma3} x V2 | `P11SlowSpecOf.h0_eq_source`, `P11SlowSpecOf.f2_eq_source`; signed `p11SlowData_h0_f2_eq_source` (D31 guard) | SecDSource.lean:216-277 |
| sec-D (chosen Z) | `G^_0 = C + sum Omega~ rho~ + Z^` | `P11SlowSpecOf.Z_eq_source` | SecEFreq.lean:34 |
| sec-D | `sigma_3=sigma_F/12`, `alpha_(1)=gamma_0 K_2^{-tau_0}/4`, `alpha_(2)=eps gamma_0 K_2^{-tau_0}/4` | `p11Sigma3`, `p11Alpha21`, `p11Alpha22`, `p11_slow_divisor_alpha` | SecDSource.lean:41, 279-293 |
| sec-D | `K_2=3 nu_2/(pi sigma_3) log(1/eps)`, `s_2=min{s_1/4, gamma_0/(8L K_2^{tau_0+1})}` | `p11K2_s2_eq` | SecDSource.lean:295 |
| sec-D | `e^{-2 pi K_2 sigma_3/6}=eps^{nu_2}` | `p11_exp_K2` | SecDSource.lean:302 |
| sec-E | `rho~_0=(2 pi eps,...)`, `A_eps(theta,r,zeta,rho')=(theta,J_0+eps r,zeta,eps(2 pi 1+rho'))` | `p11RhoTilde0`, `p11SlowCenter_eq`, `p11Rescale_fst`, `p11Rescale_snd` | SecESource.lean:41-58 |
| sec-E | `commuting with all angle shifts` | `p11Rescale_shift` | SecESource.lean:60 |
| sec-E | `A_eps^*(dJ^dtheta+d rho~^dzeta)=eps(dr^dtheta+d rho'^dzeta)` | `p11Rescale_hasFDerivAt`, `p11Rescale_symplFormC` | SecESource.lean:66-92 |
| sec-E | `maps {abs r<2, abs rho'<pi/2} into 1/2 V_2 ... if 2 eps <= s_2/2` | `p11Rescale_mem_half`, `p11Rescale_mapsTo_half` (E into T_{sigma3/6} x V2/2). The iff itself already exists: `p11Rescale_polydisc_iff`, `p11Rescale_secE_iff` | SecESource.lean:103-136 |
| sec-E | `s=s_*:=sigma_3/6=sigma_F/72` | `p11Sigma3_div_six` | SecESource.lean:124 |
| sec-E | `H_2:=H o Phi^1_eps o Theta^ o Psi_2`, `H^_eps=(1/eps) H_2 o A_eps` | `p11H2`, `p11HHat` | SecESource.lean:139-147 |
| sec-E | `N_eps=(1/eps)(h_0+g_2)(J_0+eps r, eps(2 pi 1+rho'))`, `P_eps=(1/eps) f_3 o A_eps` | `p11PreparedCoreOf_NP` | SecESource.lean:149 |
| sec-E | `H^_eps = (1/eps) H_2 o A_eps = N_eps+P_eps` (full complex identity on E) | `P11SlowSpecOf.hHat_eq` | SecESource.lean:158 |
| sec-E | domain table: `K_eps+3 vartheta` gives `abs(J-J_0)<5/4 eps`, `abs(rho~_j-2 pi eps)<5/4 eps`; Cauchy discs `s_2/4`, `eps/4` fit in `1/2 V_2` (`eps<s_2/5`) | `p11Rescale_cauchy_box` | SecESource.lean:183 |
| sec-E | `omega^_eps=nabla_{(r,rho')} N_eps=(d_J h, d_rho~ h)(A_eps)` | `P11SlowSpecOf.preparedFreq_eq` | SecEFreq.lean:62 |
| sec-E | `omega^(1)=omega+eps d_J G^_0+d_J g_2`, `omega^(2)=Omega~+d_rho~ Z^+eps^{-1} d_rho~ g_2`, `omega^_eps=(omega^(1), eps omega^(2))` | `P11SlowSpecOf.freq_source` | SecEFreq.lean:103 |
| sec-E (already existing) | E; `K_eps=[-1/2,1/2]^{2n}` | `p11SecE`, `mem_p11SecE` (SecEDefs.lean:25-37); `p11PreparedBox` (SlowData.lean:34) | - |

## Checks (exact)
- `inp_lake_build.sh /root/code/KAM-inp-psec KAM.Planetary.Preparation.SecDSource KAM.Planetary.Preparation.SecESource
  KAM.Planetary.Preparation.SecEFreq`: rc=0, "Build completed successfully (9423 jobs).", with no warning in the three
  new files.
- `sh scripts/lint_sources.sh`: rc=1. Its only failure is "KAM.lean is out of date; run scripts/gen_root_imports.py",
  which is expected because rule 10 forbids touching KAM.lean. The other checks print: check_lean_modules PASS
  (1342 Lean files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK (144 frozen declarations).
- `main_shortname_check.py` on the 3 modules: "short-name check OK (no reused public short name)".
- No line is over 100 columns. There is no maxHeartbeats, sorry, axiom or native_decide, and no EuclideanSpace.

## #print axioms
All of the following depend on [propext, Classical.choice, Quot.sound]: p11Pi_norm_le, p11PolarShell_isOpen,
p11SlowF2_eq_source, p11SlowH0_eq_source, P11SlowSpecOf.f2_eq_source, p11SlowData_h0_f2_eq_source, p11_exp_K2,
p11Rescale_symplFormC, P11SlowSpecOf.hHat_eq, p11Rescale_cauchy_box, P11SlowSpecOf.preparedFreq_eq,
P11SlowSpecOf.freq_source, P11SlowSpecOf.Z_eq_source.

## Hypotheses used (no conclusion-shaped premises)
- The standing regime is 0 < eps, eps*M_F <= e^{-1} (eps <= eps_1), and 64 eps < r_z^2. The last one is the
  "eps <= eps_2 so that Pi(P_eps) in B_{r_z/4}" smallness, in the form the existing `p11_polarC_mem` uses.
- E-level results also assume 2 eps <= s2/2, which is the source's own mapping condition. The domain table assumes
  5 eps < s2, as the source does.
- Guards on chosen data: `P11SlowSpecOf C Fast nu eps c A`, `P11FastSpec`, and for the signed datum
  `∃ A, P11SlowSpec D nu eps (p11SlowConstant D nu) A`. These are the D31 "proved local specification guards".

## Uncertainties / notes for the auditor
- The complex H2 is stated with H in its holomorphic secular chart, `p11WorkingH C eps = h~ + eps F`, and
  Theta^ = (id, Pi) = `p11PolarC`. That is the complex object the implementation uses. The physical real H is linked
  only through the existing real chain (`p11PreparedCoreOf_chain_eq`, `fixedHamiltonian` field of `P11PreparedSpec`).
- In `freq_source`, omega^(2) uses the chosen datum's own Z (`A.Z`). That Z is identified with the source
  Z^ = G^_0 - C - sum Omega~ rho~ by `P11SlowSpecOf.Z_eq_source`. omega^(1) uses the literal G^_0 (`p11GHat0`).
- The theta / eps^* / N / mu / tau_D entries of the KAM datum are not re-stated here. They are covered by existing
  definitions (`p11PreparedBox`, the P11PreparedSpec constants, `bpP:p11:select`). I add only s_* = sigma_F/72.
- No suspected errata in the pinned source. Deviations: none.

CONTEXT: all 22 frozen theorems are sealed. Owner ruling D31 (docs/DECISIONS.md on main) accepts the choose-or-default records p11SlowData / p11PreparedData under their proved local specification guards, but requires the missing source objects of bpP:p11:sec-D#data and bpP:p11:sec-E#data first (P-GRAPH-CLOSE-audit-1, rows for those nodes and the paragraph 'missing source objects'). This package adds them in three NEW modules without changing any existing statement.

AUDIT FOCUS: for each source formula of the two nodes (graph records in docs/graph/P/DEPGRAPH.md, blueprint-P p11-cp09-preparation.tex L145-153 and L189-194), is the Lean object a LITERAL transcription (no fallback branch, no arbitrary choice beyond the D31-accepted records), and is each identification with the implementation object proved under only the D31 guards and genuine source premises (e.g. 2 eps <= s2/2), with no conclusion-shaped premise? Is the complex H2/H-hat identity the full complex identity on the full source domain E (not a real projection)? Are the definitions definition-confirmable (definition-node policy)? Hygiene: names (KAM and Mathlib), lines <= 100, no native_decide or axiom. Give a verdict per node: definition-confirmed and PROVED / not. Audit ONLY the three new modules KAM/Planetary/Preparation/{SecDSource,SecESource,SecEFreq}.lean.
