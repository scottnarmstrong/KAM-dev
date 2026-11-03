P='docs/explorations/program-b-plan.md'; F='docs/tracks/B/FREEZE-PROPOSAL.md'
def L(anchor,a,b,f=P): return f'{f}#{anchor}@L{a}-L{b}'
def FL(a,b): return L('b:freeze-2',a,b,F)
BS='b:brief2-proof-sequence'
nodes=[]
def node(id,kind,title,ss,ps,cid,hyp,quant,concl,cscope='none',deps=(),edges=(),frozen=None,note='-'):
    nodes.append(dict(id=id,kind=kind,title=title,ss=ss,ps=ps,cid=cid,hyp=hyp,quant=quant,concl=concl,cscope=cscope,deps=list(deps),edges=list(edges),frozen=frozen,note=note))
HVF='b:defs#hamiltonianVectorField'; SF='b:defs#symplecticForm'; OA='b:defs#oscillatorAction'; BR='b:defs#bracket'
node(HVF,'definition','Hamiltonian vector field X_H = (dH/dJ, -dH/dphi)',L('b:2.1',77,80),'-','kam.hamiltonianVectorField','H : Phase n -> R','n; H','defines X_H = (partial_J H, -partial_phi H) on Phase n',
     frozen=('KAM/Frozen/Defs/HamiltonianVectorField.lean','KAM.hamiltonianVectorField','kam.hamiltonianVectorField.v1','427a145572df4c3e14079cf88feb16d60e1cd92fcd1770faddd36ad706562ca6'))
node(SF,'definition','Repository symplectic form',L('b:2.1',85,86),'-','kam.symplecticForm','v, w : Phase n','n; v, w','defines symplecticForm(v,w) = sum_j (v.2 j * w.1 j - v.1 j * w.2 j)',
     frozen=('KAM/Frozen/Defs/SymplecticForm.lean','KAM.symplecticForm','kam.symplecticForm.v1','542b8d8eb08283f5c961a969dd96003cbb23fc447da8ea444498cb92a48f6d75'))
node(OA,'definition','Oscillator actions I_j(q,p) = (q_j^2 + p_j^2)/2',L('b:2.3',167,173),'-','planetary.oscillatorAction','q, p : Vec n','n; q, p; j','defines I_j(q,p) = (q_j^2 + p_j^2)/2',
     frozen=('KAM/Frozen/Planetary/Defs/OscillatorAction.lean','KAM.Planetary.oscillatorAction','planetary.oscillatorAction.v1','b37f7928355c64fc3555d65704a95ecdb67fe55bdd7bb2471ac609553f2a962a'))
node(BR,'definition','Poisson bracket convention {F,G} = sum_j (F_phi_j G_J_j - F_J_j G_phi_j); ad_chi F = {F,chi}',L('b:2.1',79,82),'-','b.def.bracket','F, G differentiable on Phase n','F, G','defines {F,G}; along a solution of X_G, d/dt F = {F,G}',
     deps=[HVF],edges=[(HVF,L('b:2.1',79,82),'the bracket is the derivative of F along X_G')],note='convention only; in the frozen B1-E text the bracket {I_j,R} is written out as q_j R_{p_j} - p_j R_{q_j} (FREEZE-PROPOSAL L59-L60, L80-L83)')
node('ext:ode#local','external','Local existence and uniqueness for C^1 (locally Lipschitz) vector fields (Picard-Lindelof)','external:repo-ode#local','-','ext.ode.local','vector field C^1 on an open set U; initial point in U','field, U, initial point; then exists eps>0','a unique local solution on (-eps, eps) in U; two solutions agree near a common time',
     note='repository KAM.ODE local theory (built on Mathlib IsPicardLindelof); invoked by "Handle T=0 by local existence" (L854) and by the uniqueness step')
node('ext:ode#compact-continuation','external','Continuation: a solution confined to a compact subset of the open domain of a C^1 field extends past both ends of a bounded interval','external:repo-ode#continuation','-','ext.ode.continuation','C^1 field on open U; solution on a bounded open interval staying in a compact K subset U','field, U, K; then the solution','the solution extends to a strictly larger open interval (both ends), still a solution in U',
     note='"the existing continuation theorem" (plan L850-L851); the repository KAM.ODE continuation library')
# shared steps
node('b:brief2#chart-transport','step','Symplectic field identity and chart transport: DPsi(w) X_{H o Psi}(w) = X_H(Psi w); chart solutions push forward to physical solutions',L(BS,852,853),L(BS,852,853),'b.step.chart-transport',
     'V open; H C^2 on V; Psi C^2 on the open chart domain D with Psi(D) subset V; DPsi preserves symplecticForm; symplecticForm nondegenerate; Psiinv o Psi = id on D',
     'n; H, Psi; then w in D; then any chart solution w(t) in D',
     'DPsi(w) is invertible and DPsi(w) X_{H o Psi}(w) = X_H(Psi w); H o Psi is C^2 on D (so X_{H o Psi} is C^1); if w solves w\' = X_{H o Psi}(w) in D then z = Psi o w solves z\' = X_H(z) in V and Psi(Psiinv(z t)) = z t with Psiinv(z t) = w t',
     deps=[HVF,SF],edges=[(HVF,L(BS,852,853),'both sides of the identity are Hamiltonian fields'),(SF,L(BS,852,853),'symplecticity of DPsi and nondegeneracy of symplecticForm give the identity and invertibility')],
     note='frozen premises: hH, hPsi, hPsiV, hPsisymp, hPsiinv (FREEZE-PROPOSAL L31-L37); no inverse regularity or open image is needed (OD-B3, left inverse)')
node('b:brief2#stopped-drift','step','Stopped drift: a scalar derivative bound |f\'| <= eta on an interval containing 0 gives |f(t) - f(0)| <= eta |t| in both time directions',L(BS,847,848),L(BS,847,848),'b.step.stopped-drift',
     'f differentiable on an interval I containing 0 with |f\'| <= eta there; eta >= 0','f, eta; then t in I','|f(t) - f(0)| <= eta |t| for t >= 0 and t <= 0',note='eta = 0 allowed, no division (L854-L855)')
node('b:brief2#uniqueness','step','Uniqueness on interval intersections',L('b:2.1',94,95),L(BS,853,853),'b.step.uniqueness',
     'V open; H C^2 on V (so X_H is C^1, hence locally Lipschitz); y, z solutions in V on order-connected intervals I, U containing 0 with y(0) = z(0)','solutions y, z; intervals I, U','y = z on I intersect U',
     deps=['ext:ode#local',HVF],edges=[('ext:ode#local',L(BS,853,853),'local uniqueness propagated along the interval intersection'),(HVF,L('b:2.1',90,95),'the solution notion HasDerivAt z (X_H (z t)) and C^1 regularity of X_H from H C^2')])
# B1-T
node('b:2.2#action-derivative','step','Cylinder action derivative J\'_j = -d_{phi_j} R along a chart solution',L(BS,848,848),L('b:2.2-source-and-proof',157,159),'b.step.torus-action-derivative',
     'H o Psi = N(J) + R(phi,J) on the open chart domain C_(b+eps); H o Psi C^2 there (chart-transport) and R differentiable there; w = (phi,J) solves w\' = X_{H o Psi}(w) in C_(b+eps)','w on an interval I; t in I; j',
     'J_j\'(t) = -partial_{phi_j} R(w(t)) (the N part does not depend on phi, differentiated through H o Psi - R)',
     deps=['b:brief2#chart-transport',HVF],edges=[('b:brief2#chart-transport',L(BS,848,848),'H o Psi is C^2 on C_(b+eps), from chart-transport conclusion, so fderiv(H o Psi) - fderiv R is the derivative of N(J)'),(HVF,L(BS,848,848),'J-component of X_{N+R} is -partial_phi (N+R) = -partial_phi R')],
     note='frozen version differentiates H o Psi - R, so no regularity of N is assumed (FREEZE-PROPOSAL L25-L27)')
node('b:2.2#first-exit','step','B1-T first-exit bootstrap: while |t| <= T a chart solution started in |J| <= a stays in |J_j| <= a_j + eta_j |t| < b_j (inside the chart domain)',L('b:2.2-source-and-proof',161,161),L(BS,849,850),'b.step.torus-first-exit',
     'eps > 0; |J_j(0)| <= a_j; eta_j >= 0; a_j + T eta_j < b_j; |d_{phi_j} R| <= eta_j on closed C_b; w a chart solution on an interval I containing 0 while it stays in C_(b+eps)',
     'for any such w and I (existence NOT assumed); then t in I with |t| <= T; j',
     'w(t) in closed C_b, |J_j(t) - J_j(0)| <= eta_j |t| and |J_j(t)| <= a_j + eta_j |t| < b_j, so w never reaches the boundary of C_(b+eps) for |t| <= T',
     deps=['b:2.2#action-derivative','b:brief2#stopped-drift'],
     edges=[('b:2.2#action-derivative',L(BS,849,850),'the derivative identity bounds |J_j\'| by eta_j while in closed C_b'),('b:brief2#stopped-drift',L('b:2.2-source-and-proof',161,161),'stopped drift applied on the sub-interval before the first exit from closed C_b, contradicted by the strict margin')],
     note='a_j >= 0 follows from |J_j(0)| <= a_j; eta = 0 and both time directions allowed (L847-L848, L854-L855); the reviewer rule L863-L864 (no assumed existence interval) is respected')
node('b:2.2#periodic-reduction','step','Periodic continuation: an angle-periodic C^1 chart field with solutions confined to a closed action box inside the domain continues past [-T,T]',L('b:2.2-source-and-proof',161,163),L(BS,850,852),'b.step.torus-periodic-reduction',
     'H o Psi = N(J) + R with R angle-periodic (so X_{H o Psi} is 1-periodic in phi); field X_{H o Psi} C^1 on C_(b+eps) by chart-transport; confinement of every chart solution to closed C_b for |t| <= T (first exit)',
     'w0 with |J0| <= a; T',
     'the chart solution from w0 exists on an open interval Ioo(-T1, T1) with T < T1 and stays in C_(b+eps)',
     deps=['b:2.2#first-exit','ext:ode#compact-continuation','ext:ode#local','b:brief2#chart-transport',HVF],
     edges=[('b:2.2#first-exit',L(BS,850,851),'confinement in the closed action box'),('ext:ode#compact-continuation',L(BS,851,852),'continuation applied on the compact fundamental cell [0,1]^n x closed box, transported by angle periodicity'),('ext:ode#local',L(BS,854,854),'T = 0 and the restart after integer angle shifts by local existence/uniqueness'),('b:brief2#chart-transport',L(BS,850,852),'C^1 regularity of the chart field X_{H o Psi}; its angle periodicity from hRper and H o Psi = N(J) + R'),(HVF,L(BS,850,852),'the continued field is the Hamiltonian field X_{H o Psi}')],
     note='lifted angles are unbounded, so the cylinder is not compact (L162-L163); periodicity of R (hRper, FREEZE-PROPOSAL L40-L41) replaces the plan\'s V/H/Psi periodicity premises (OD-B2)')
node('b:2.2#B1-T','theorem','B1-T: finite confinement in a canonical cylinder (frozen torus_confinement)',FL(24,54),L('b:2.2-source-and-proof',157,163),'effectiveStability.d72.torus_confinement',
     'a,b,eta : Vec n; eps > 0; T >= 0; eta_j >= 0; a_j + T eta_j < b_j; V open; H C^2 on V; Psi C^2 on C_(b+eps) := {abs J_j < b_j + eps}; Psi(C_(b+eps)) subset V; DPsi preserves symplecticForm; Psiinv o Psi = id on C_(b+eps); N : Vec n -> R; R differentiable on C_(b+eps), 1-periodic in phi; H(Psi w) = N(J) + R(w) on C_(b+eps); abs(fderiv R w (e_j,0)) <= eta_j on closed C_b; w0 with abs(J0_j) <= a_j',
     'n, a, b, eta, eps, T, V, H, Psi, Psiinv, N, R and their premises fixed; for every w0; then exists T1 > T and z',
     'z(0) = Psi(w0); for t in Ioo(-T1,T1): z(t) in V and z\'(t) = X_H(z(t)); every solution y in V on an order-connected I containing 0 with y(0) = Psi(w0) equals z on I intersect Ioo(-T1,T1); for every abs t <= T: Psi(Psiinv(z t)) = z t, abs(J_j(t) - J0_j) <= eta_j abs t and abs J_j(t) <= a_j + eta_j T, where (phi,J)(t) = Psiinv(z t)',
     'no unquantified constant',
     deps=['b:2.2#periodic-reduction','b:2.2#first-exit','b:brief2#uniqueness','b:brief2#chart-transport',HVF,SF],
     edges=[('b:2.2#periodic-reduction',FL(47,48),'existence on Ioo(-T1,T1) with T < T1'),('b:2.2#first-exit',FL(53,54),'drift and confinement bounds'),('b:brief2#uniqueness',FL(49,52),'uniqueness clause'),('b:brief2#chart-transport',FL(47,53),'z = Psi o w solves X_H in V and Psi(Psiinv(z t)) = z t'),(HVF,FL(48,48),'HasDerivAt z (X_H (z t))'),(SF,FL(35,36),'hPsisymp')],
     frozen=('KAM/Frozen/EffectiveStability/TorusConfinement.lean','KAM.EffectiveStability.torus_confinement','effectiveStability.d72.torus_confinement.v1','bc5bc3eca192d370415c8cd4916c61345fda22452343ea83734171747c129a54'),
     note='statement source = the exact frozen text (FREEZE-PROPOSAL §2, owner D72); mathematical source plan §2.2 L100-L136; deviations (minimal premises OD-B2, left-inverse chart OD-B3, n >= 1 dropped OD-B6) listed in FREEZE-PROPOSAL §6 L161-L166')
# B1-E
node('b:2.3#action-bracket','step','Oscillator action derivative (I_j o w)\' = {I_j, H o Psi} along a chart solution',L(BS,849,849),L(BS,848,849),'b.step.osc-action-bracket',
     'w solves w\' = X_{H o Psi}(w) in E_(b+eps); H o Psi C^2 there (chart-transport)','w on an interval I; t in I; j','(I_j o w)\'(t) = {I_j, H o Psi}(w(t))',
     deps=['b:brief2#chart-transport',OA,BR,HVF],edges=[('b:brief2#chart-transport',L(BS,848,849),'H o Psi is C^2 on E_(b+eps), from chart-transport conclusion, so I_j o w has derivative DI_j . X_{H o Psi}'),(OA,L(BS,849,849),'I_j is the frozen oscillator action'),(BR,L(BS,849,849),'derivative along X_G is the bracket with G'),(HVF,L(BS,849,849),'d/dt I(w) = DI . X_{H o Psi}')])
node('b:2.3#normal-form-commutes','step','Vanishing normal-form contribution: g = H o Psi - R = N o I gives {I_j, g} = 0',L('b:2.3-continuation',196,196),L(BS,849,849),'b.step.osc-normal-form-commutes',
     'g differentiable on E_(b+eps) and g = N o I there (N arbitrary)','g; j; w in E_(b+eps)','{I_j, g}(w) = 0',
     deps=[OA,BR],edges=[(OA,L('b:2.3-continuation',196,196),'g is a function of the actions, invariant under the I_j rotations'),(BR,L('b:2.3-continuation',196,196),'{I_j, .} is the derivative along the j-th rotation')],
     note='frozen version: rotation invariance of the differentiable H o Psi - R, no differentiability of N (FREEZE-PROPOSAL L60-L61); source states it as the algebraic lemma {I_j, N o I} = 0')
node('b:2.3#first-exit','step','B1-E first-exit bootstrap: while |t| <= T, 0 <= I_j(w(t)) <= a_j + eta_j |t| < b_j; no exit through I_j = 0',L('b:2.3-continuation',195,196),L(BS,849,850),'b.step.osc-first-exit',
     'eps > 0; I_j(w0) <= a_j; eta_j >= 0; a_j + T eta_j < b_j; |{I_j,R}| <= eta_j on closed E_b; w a chart solution on an interval I containing 0 while it stays in E_(b+eps)',
     'for any such w and I (existence NOT assumed); then t in I with |t| <= T; j',
     'w(t) in closed E_b, |I_j(w(t)) - I_j(w0)| <= eta_j |t| and 0 <= I_j(w(t)) <= a_j + eta_j |t| < b_j',
     deps=['b:2.3#action-bracket','b:2.3#normal-form-commutes','b:brief2#stopped-drift',OA],
     edges=[('b:2.3#action-bracket',L(BS,849,849),'derivative of I_j along w'),('b:2.3#normal-form-commutes',L(BS,849,849),'leaves {I_j,R}'),('b:brief2#stopped-drift',L(BS,849,850),'stopped drift applied on the sub-interval before the first exit from closed E_b'),(OA,L('b:2.3-continuation',195,195),'I_j >= 0 and I_j = 0 is an interior Cartesian point')],
     note='zero actions and eta = 0 without division (L854-L855); no assumed existence interval (L863-L864)')
node('b:2.3#compact-continuation','step','B1-E continuation via the compact Cartesian set closed E_b inside E_(b+eps)',L('b:2.3-continuation',196,196),L(BS,850,852),'b.step.osc-continuation',
     'closed E_b = {I_j <= b_j} compact (product of closed discs; b_j > 0 from a_j >= 0 and the margin) inside E_(b+eps); field X_{H o Psi} C^1 there by chart-transport; first-exit confinement for |t| <= T',
     'w0 with I(w0) <= a; T','the chart solution from w0 exists on Ioo(-T1, T1) with T < T1 and stays in E_(b+eps)',
     deps=['b:2.3#first-exit','ext:ode#compact-continuation','ext:ode#local',OA,'b:brief2#chart-transport',HVF],
     edges=[('b:2.3#first-exit',L(BS,850,851),'confinement in closed E_b'),('ext:ode#compact-continuation',L('b:2.3-continuation',196,196),'closed E_b provides continuation'),('ext:ode#local',L(BS,854,854),'T = 0 by local existence'),(OA,L('b:2.3-continuation',196,196),'compactness of closed E_b from I_j = (q_j^2+p_j^2)/2'),('b:brief2#chart-transport',L(BS,850,852),'C^1 regularity of the chart field X_{H o Psi}'),(HVF,L(BS,850,852),'the continued field is the Hamiltonian field X_{H o Psi}')])
node('b:2.3#B1-E','theorem','B1-E: Cartesian oscillator confinement, including zero actions (frozen oscillator_confinement)',FL(57,95),L('b:2.3-continuation',195,205),'effectiveStability.d72.oscillator_confinement',
     'a,b,eta : Vec n; eps > 0; T >= 0; eta_j >= 0; a_j + T eta_j < b_j; V open; H C^2 on V; Psi C^2 on E_(b+eps) := {I_j < b_j + eps}; Psi(E_(b+eps)) subset V; DPsi preserves symplecticForm; Psiinv o Psi = id on E_(b+eps); N : Vec n -> R; R differentiable on E_(b+eps); H(Psi w) = N(I(w)) + R(w) there; abs(q_j R_{p_j} - p_j R_{q_j}) <= eta_j on closed E_b; w0 with I_j(w0) <= a_j',
     'n, a, b, eta, eps, T, V, H, Psi, Psiinv, N, R and their premises fixed; for every w0; then exists T1 > T and z',
     'z(0) = Psi(w0); for t in Ioo(-T1,T1): z(t) in V and z\'(t) = X_H(z(t)); uniqueness on I intersect Ioo(-T1,T1) as in B1-T; for every abs t <= T: Psi(Psiinv(z t)) = z t, abs(I_j(Psiinv(z t)) - I_j(w0)) <= eta_j abs t and I_j(Psiinv(z t)) <= a_j + eta_j T',
     'no unquantified constant',
     deps=['b:2.3#compact-continuation','b:2.3#first-exit','b:brief2#uniqueness','b:brief2#chart-transport',HVF,SF,OA],
     edges=[('b:2.3#compact-continuation',FL(86,87),'existence on Ioo(-T1,T1)'),('b:2.3#first-exit',FL(92,95),'drift and confinement bounds'),('b:brief2#uniqueness',FL(88,91),'uniqueness clause'),('b:brief2#chart-transport',FL(87,92),'z = Psi o w and Psi(Psiinv(z t)) = z t'),(HVF,FL(87,87),'HasDerivAt z (X_H (z t))'),(SF,FL(70,72),'hPsisymp'),(OA,FL(66,69),'action domains and conclusion')],
     frozen=('KAM/Frozen/EffectiveStability/OscillatorConfinement.lean','KAM.EffectiveStability.oscillator_confinement','effectiveStability.d72.oscillator_confinement.v1','6ea8db1e9947d08a0c3cd70be06e80dc6e5cb64ac5d4c82902023f04dfd3ef4c'),
     note='statement source = exact frozen text (FREEZE-PROPOSAL §2, owner D72); mathematical source plan §2.3 L165-L193; deviations in FREEZE-PROPOSAL §6 L161-L166')

H='docs/tracks/B/FREEZE-PROPOSAL-HH.md'
def HL(a,b): return L('b:freeze-hh',a,b,H)
B1E='b:2.3#B1-E'; FI='b:4-first-instance'
node('b:3.2#lie-identity','step','Lie series with integral remainder for an exact time-one flow; remainder bound B/(m+1)!',L('b:3.2',343,354),L('b:3.2',353,356),'b.step.lie-identity',
     'chi with flow Phi_chi^s defined for 0 <= s <= 1 on the stated (outer complex) domain; H analytic there; |ad_chi^{m+1} H| <= B along the flow',
     'chi, H, m; then the domain points',
     'H o Phi_chi^1 = sum_{k<=m} ad_chi^k H / k! + integral remainder, and the remainder is bounded by B/(m+1)!',
     deps=[BR],edges=[(BR,L('b:3.2',347,349),'ad_chi F = {F,chi}; d/ds F o Phi^s = {F,chi} o Phi^s')],
     note='plan: "the existing taylor_lie is the starting point" (L354)')
node('b:3.2#chart-composition','step','Chart from generators: a composition of exact time-one flows is canonical, has the explicit inverse given by the reversed flows, and composed forward/inverse displacement bounds',L('b:3.2',355,356),L('b:3.2',398,402),'b.step.chart-composition',
     'generators chi_1..chi_m with flows for |s| <= 1 on nested domains with strict margins (§3.1 L317-L318)','the generators and domains',
     'Psi = Phi_{chi_1}^1 o ... o Phi_{chi_m}^1 is symplectic on its domain, Psiinv = reversed flows satisfies Psi(Psiinv z) = z and Psiinv(Psi w) = w where defined, discarded polynomial terms stay in R, and forward/inverse displacement bounds compose with the needed derivative factors',
     deps=[SF,HVF,'ext:ode#local','b:3.2#lie-identity'],edges=[('b:3.2#lie-identity',L('b:3.2',355,356),'the discarded polynomial terms remain in R'),(SF,L('b:3.2',355,355),'composition of exact flows remains canonical (symplectic)'),(HVF,L('b:3.2',355,355),'Hamiltonian flows of the generators'),('ext:ode#local',L('b:3.1',317,318),'every flow for -1 <= s <= 1 and its inverse exist on the domain')],
     note='"a truncated coordinate substitution is not the map being certified" (L356); the explicit inverse and the displacement bounds come from L316-L318, L321, L398-L402; "reversed flows" is the group property of exact flows (uniqueness, ext:ode#local), an inference not stated in the source')
node('ext:analysis#cauchy','external','Cauchy estimate: a holomorphic function bounded by E on a polydisc with margins delta has first derivatives bounded by E/delta on the inner set','external:analysis#cauchy-estimate','-','ext.analysis.cauchy','f holomorphic on complex discs of radius r + delta about the real points, |f| <= E there','f, E, r, delta','|partial f| <= E/delta on the discs of radius r',
     note='standard analytic input used by plan L368-L369 and L382-L384 without proof (repository Cauchy estimates)')
node('b:3.2#oscillator-drift','step','Oscillator drift bound: {I_j, R} <= eta_j from the retained residual polynomial plus Cauchy tails, propagated through the charts',L('b:3.2',373,385),L('b:3.2',387,402),'b.step.oscillator-drift',
     'residual R = retained polynomial P + Lie tails (lie-identity) on Cartesian complex discs with margins; radii w_j with w_j^2 >= 2 b_j, w_j >= 0 fixed before the arithmetic run',
     'j; w in closed E_b','|{I_j, R}(w)| <= eta_j = eta_finite + eta_Lie (+ eta_model + eta_rounding), each contribution propagated through later charts; finite part eta_poly = sum |alpha_j - beta_j| |c_ab| prod rho^(alpha+beta) (L378-L379); Cartesian tail contribution w_j E (1/dq_j + 1/dp_j) (L383-L384)',
     deps=['b:3.2#lie-identity',BR,OA,'b:3.2#chart-composition','ext:analysis#cauchy'],edges=[('b:3.2#lie-identity',L('b:3.2',383,384),'tail E bounded on the complex discs'),(BR,L('b:3.2',375,375),'{I_j, z^a zeta^b} = i(a_j - b_j) z^a zeta^b'),(OA,L('b:3.2',375,375),'I_j = z_j zeta_j'),('b:3.2#chart-composition',L('b:3.2',399,402),'propagate each contribution through later charts with derivative factors'),('ext:analysis#cauchy',L('b:3.2',382,384),'tail on Cartesian complex discs with margins gives w_j E (1/dq_j + 1/dp_j)')],
     note='the (Tail) series formula (L387-L397) applies to CL-style infinite majorants; the HH certificate uses finite Lie orders with the B/(m+1)! remainder')
node('b:3.1#checker-soundness','claim','Checker soundness: an accepted finite normal-form certificate yields the unique trajectory with the stated chart/original-coordinate bounds',L('b:3.1',324,333),L('b:3.1',335,340),'b.claim.checker-soundness',
     'supported Hamiltonian expression (exact polynomial first, L304-L306); finite certificate c with: H expression, parameter box and conventions; nested domains, radii and strict margins; generators chi_1..chi_m; normal form N and retained residual P; bounds on discarded terms; (divisor witnesses, producer-side only); forward/inverse displacement bounds and initial-set inclusions; drift bounds eta_j, observable bounds d_i, time T (L313-L322); checkNormalForm Hexpr c = true',
     'for every expression and certificate; every parameter in c.parameterBox; every z0 in c.initialRegion',
     'a unique Hexpr trajectory on an open interval containing [-c.T, c.T] (§2.1 convention), with the stated original-coordinate observable and domain bounds; chart, residual and continuation facts proved from the data',
     deps=[B1E,'b:3.2#chart-composition','b:3.2#lie-identity','b:3.2#oscillator-drift','b:2.3#transfer'],
     edges=[('b:2.3#transfer',L('b:3.1',322,322),'original-coordinate observable bounds (L329-L331) are the transfer formula'),(B1E,L('b:2.3',197,198),'the dynamics conclusion (continuation, confinement) is the B1-E sufficient-condition theorem applied to the proved chart data'),
            ('b:3.2#chart-composition',L('b:3.1',336,336),'"prove the chart ... facts": symplectic chart with explicit inverse'),
            ('b:3.2#lie-identity',L('b:3.1',336,336),'"residual ... facts": H o Psi = N o I + R with exact Lie identities'),
            ('b:3.2#oscillator-drift',L('b:3.1',319,322),'drift bounds eta_j for the B1-E bracket premise')],
     note='models the polynomial/oscillator (B1-E) case only; torus/Fourier-Taylor expressions (L358-L371) are out of this closure; B1-E use: "included once a finite normal form is certified" (L197-L198) with L335-L337; divisor witnesses are listed as inputs (L319) but soundness checks the identities directly: an arbitrary generator is allowed (L317) and a bad one fails the inequality (L337) (owner ruling OD-B12)')
node('b:4#model-identification','step','Model identification: the checker\'s exact Q(sqrt 2) polynomial is the HH Hamiltonian, smooth on all of phase space',L(FI,531,537),L('b:3.1',304,310),'b.step.hh-model',
     'Hexpr = I_1 - (sqrt 2/2) I_2 + q_1^2 q_2 - q_2^3/3 with exact coefficients in Q(sqrt 2) (supported algebraic constant)','w in Phase 2',
     'the evaluation of Hexpr at w equals the displayed H(w) (q = w.1, p = w.2); H is a polynomial, hence C^2 on V = all of Phase 2',
     deps=[OA,HVF],edges=[(OA,L(FI,535,535),'I_j = (q_j^2 + p_j^2)/2'),(HVF,HL(23,26),'the inlined H whose field X_H is the solution field')],
     note='"a polynomial that approximates a different H is a different model" (L308-L310); exact arithmetic over Q(sqrt 2) is the supported-constant case of L305')
node('b:4#certificate-accepted','step','The accepted HH certificate: checkNormalForm(HH, c) = true with the literals a_j = (81/10^6)^2, b_j = 10^-8, eta_j <= 10^-19, T = 10^10, d_j <= 10^-10',L(FI,545,553),L('b:3.1',338,340),'b.step.hh-certificate',
     'the identified HH model; a finite certificate c in the normalized chart (L546; no rescaling of coordinates or time, §3.3 L418-L424 does not apply)','j = 1, 2; the finite data',
     'checkNormalForm(HH, c) = true with a_j, b_j, eta_j, T, d_j (per j) for forward oscillator-action displacement on closed E_b and inverse displacement on the physical disc, and the initial-set inclusion of the physical disc in the inverse chart domain (L321)',
     deps=['b:4#model-identification'],edges=[('b:4#model-identification',L(FI,546,546),'the certificate is for the identified model, in its normalized chart')],
     note='computational leaf: a finite exact computation replayed in the kernel; producer untrusted (L338-L340); CL20\'s reported computation (L560-L566) only motivates the literals')
node('b:4#inverse-chart','step','Inverse chart on the physical disc: every physical z0 with I_j(z0) <= (1/12500)^2 equals Psi(w0) for w0 = Psiinv(z0) in the chart domain, with inverse action displacement <= d_j',L('b:2.2',153,155),L(FI,553,553),'b.step.hh-inverse-chart',
     'the certified chart Psi with explicit inverse (reversed flows) defined on the physical disc; inverse displacement bound from the certificate','z0 with I_j(z0) <= (1/12500)^2',
     'w0 = Psiinv(z0) lies in the chart domain, Psi(w0) = z0 and |I_j(w0) - I_j(z0)| <= d_j',
     deps=['b:3.2#chart-composition','b:4#certificate-accepted','b:3.1#checker-soundness',OA],edges=[('b:3.2#chart-composition',L('b:2.2',153,155),'"prove Q in Psi({...}) using the inverse chart"'),('b:4#certificate-accepted',L(FI,553,553),'inverse displacement bound on the physical disc'),('b:3.1#checker-soundness',L('b:3.1',321,321),'acceptance becomes the inverse displacement bound and initial-set inclusion on the actual chart'),(OA,L(FI,553,553),'oscillator-action displacement')],
     note='L153-L155 is the torus-section requirement, applied by analogy to the oscillator chart. DEVIATION (OD-B18, B3-READY): the Lean route bounds the inverse chart by a coordinate displacement tail and the disc estimate (sigma + tail)^2 <= a (oscillatorChain_physical_disc) instead of the action displacement d_j')
node('b:4#initial-inclusion','step','Initial-set inclusion: physical actions <= (1/12500)^2 give chart actions <= a_j',L(FI,555,555),L(FI,554,555),'b.step.hh-initial-inclusion',
     'I_j(z0) <= (1/12500)^2; w0 = Psiinv(z0) with |I_j(w0) - I_j(z0)| <= d_j <= 10^-10','z0; j',
     'I_j(w0) <= (1/12500)^2 + 10^-10 = 6.5e-9 < a_j = 6.561e-9',
     deps=['b:4#inverse-chart',OA],edges=[('b:4#inverse-chart',L(FI,555,555),'the inverse displacement d_j'),(OA,L(FI,540,540),'I_j in the initial set')],
     note='source inequality as stated; Lean route per the inverse-chart NOTE')
node('b:2.3#transfer','corollary','Oscillator observable transfer: |A_i(z(t)) - A_i(z0)| <= 2 d_i + |t| sum_j |L_ij| eta_j with L I in place of L J',L('b:2.3',201,201),L('b:2.2',143,150),'b.cor.osc-transfer',
     'z0 = Psi(w0) with I_j(w0) <= a_j; B1-E conclusion along w(t) = Psiinv(z(t)); static bound |A_i(Psi w) - (L I(w))_i| <= d_i on closed E_b','observable A, matrix L, d; t with |t| <= T',
     '|A_i(z(t)) - A_i(z0)| <= 2 d_i + |t| sum_j |L_ij| eta_j',
     deps=[B1E,OA],edges=[(B1E,L('b:2.3',201,201),'confinement and drift of the chart actions'),(OA,L('b:2.3',201,201),'L I uses the oscillator actions')],
     note='for HH: A = I (physical actions), L = id, d_i the forward action displacement')
node('b:4#physical-bounds','step','Physical output: I_j(z(t)) < b_j + d_j <= 101/10^10 and |I_j(z(t)) - I_j(z0)| <= 2 d_j + eta_j T <= 12/10^10',L(FI,556,557),L(FI,556,557),'b.step.hh-physical-bounds',
     'chart confinement I_j(w(t)) <= a_j + eta_j T <= 7.561e-9 < b_j and chart drift <= eta_j |t| (B1-E via soundness), w(0) = w0 from the initial inclusion; forward action displacement <= d_j on closed E_b','z0, z(t) = Psi(w(t)); t with |t| <= T = 10^10; j',
     'I_j(z(t)) < b_j + d_j <= 1.01e-8 = 101/10^10 and |I_j(z(t)) - I_j(z0)| <= 2 d_j + eta_j T <= 1.2e-9 = 12/10^10',
     deps=['b:3.1#checker-soundness','b:2.3#transfer','b:4#initial-inclusion','b:4#certificate-accepted',OA],
     edges=[('b:3.1#checker-soundness',L(FI,556,556),'chart confinement a_j + eta_j T < b_j'),('b:2.3#transfer',L(FI,557,557),'2 d_j + eta_j T is the transfer formula with A = I, L = id'),('b:4#initial-inclusion',L(FI,555,557),'the chart solution starts in I(w0) <= a_j'),('b:4#certificate-accepted',L(FI,556,557),'literals a, b, eta, T, d'),(OA,L(FI,557,557),'physical actions')],
     note='forward displacement only (z(t) = Psi(w(t))); the Lean route bounds I(z(t)) by a_j + eta_j T + d_j, which also gives < 101/10^10')
node('b:4#HH','theorem','Hénon–Heiles confinement (frozen henonHeiles_confinement)',HL(20,36),L(FI,545,559),'effectiveStability.d73.henonHeiles_confinement',
     'z0 : Phase 2 with I_j(z0) <= (1/12500)^2 for j = 1, 2; H = I_1 - (sqrt 2/2) I_2 + q_1^2 q_2 - q_2^3/3 with q = z.1, p = z.2 (inlined)',
     'for every z0 with the premise; then exists T1 > 10^10 and z',
     'z(0) = z0 and z\' = X_H(z) on Ioo(-T1,T1); every y with y(0) = z0 solving y\' = X_H(y) on an order-connected I containing 0 equals z on I intersect Ioo(-T1,T1); for every |t| <= 10^10 and j: I_j(z(t)) < 101/10^10 and |I_j(z(t)) - I_j(z0)| <= 12/10^10',
     'all literals explicit; no unquantified constant',
     deps=['b:3.1#checker-soundness','b:4#certificate-accepted','b:4#model-identification','b:4#inverse-chart','b:4#physical-bounds',HVF,OA],
     edges=[('b:3.1#checker-soundness',HL(22,32),'existence past 10^10 and uniqueness from the sound checker'),('b:4#certificate-accepted',HL(22,36),'the accepted HH certificate instantiates soundness with T = 10^10'),('b:4#model-identification',HL(23,31),'the inlined H is the certified model, V = all of Phase 2'),('b:4#inverse-chart',HL(21,22),'the solution starts at z0 = Psi(w0)'),('b:4#physical-bounds',HL(33,36),'the two physical bounds'),(HVF,HL(23,26),'HasDerivAt z (X_H (z t))'),(OA,HL(21,36),'oscillator actions in the premise (L21) and the conclusion (L33-L36)')],
     frozen=('KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean','KAM.EffectiveStability.henonHeiles_confinement','effectiveStability.d73.henonHeiles_confinement.v1','ecd0cc37042f3fbd267c8c113583f4e1ba70c7e974edc0ba299ce10f626295ea'),
     note='statement source = exact frozen text (FREEZE-PROPOSAL-HH, owner D73); mathematical target plan §4 L539-L543; plan-to-freeze: "unique solution through |t| <= 10^10" is stated in the §2.1 form (open Ioo(-T1,T1), T1 > 10^10, uniqueness on order-connected intervals through 0); library KAMHenonHeiles')
import json,sys
json.dump(nodes,open(sys.argv[1],'w'),indent=1)
