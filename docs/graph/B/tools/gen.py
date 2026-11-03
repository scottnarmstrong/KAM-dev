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
import json,sys
json.dump(nodes,open(sys.argv[1],'w'),indent=1)
