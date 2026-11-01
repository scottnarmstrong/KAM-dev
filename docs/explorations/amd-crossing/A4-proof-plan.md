> Source: `RESEARCH/PROOF-PLAN.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

# Paper-level proof plan: strong-AMD exponential safety

Status: a detailed mathematical construction and reuse plan, **not a completed formal proof**. Repository source snapshot: `/root/code/KAM`, `f5625f197c621ccc8045e8392a07e23fe0cb10fc`. No repository writes or builds. Labels: **[CITED]** inspected source theorem; **[ADAPTED]** an identified source with a changed domain/interface; **[NEW]** an argument supplied here for subsequent audit/formalization; **[OPEN RISK]** an obligation not yet independently checked or implemented.

The target fixes (n\ge2), positive normalized masses (m_i), a compact set \(\mathcal A\subset\{0<a_1<\cdots<a_n\}\), a margin \(\delta>0\), and, for the nonresonant route, \(\gamma_D>0\), \(\tau>n-1\). Constants precede both \(\mu\) and the initial state. Uniformity is over the **entire** allowed AMD sublevel and all phases, not a neighborhood of one secular orbit. An empty sublevel is permitted; a meaningful application supplies a witness.

## 1. Exact model and deterministic barrier

### 1.1 Normalization [CITED / ADAPTED]

Take (G=m_0=1), physical planet masses \(\mu m_i\), \(\max_i m_i=1\), and canonical momenta scaled by \(\mu\). After heliocentric reduction and division of the physical Hamiltonian by \(\mu\),

\[
 H_\mu(q,p)=\sum_i\left({|p_i|^2\over2m_i}-{m_i\over|q_i|}\right)
 +\mu\left({1\over2}\left|\sum_i p_i\right|^2-
 \sum_{i<j}{m_i m_j\over|q_i-q_j|}\right).
 \tag{M}
\]

This gives the original physical time in the normalized units. It is exactly `Planetary/Newtonian/Models.lean:movingHamiltonian_split` in the planar case. The Kepler actions are \(\Lambda_i=m_i\sqrt{a_i}\),
\(h(\Lambda)=-\sum m_i^3/(2\Lambda_i^2)\), and radian frequencies \(\omega_i=a_i^{-3/2}\). LP17 §2.1 (2)–(8) uses the same canonical heliocentric distinction; its symbol \(\mu=Gm_0\) must not be confused with our planet/star small parameter.

### 1.2 Attained pair threshold [ADAPTED / NEW]

Put \(D(u)=1-\sqrt{1-u^2}\) on \([0,1]\). For positive ordered axes define

\[
 B_{ij}(m,a)=\min_{\substack{u,v\in[0,1]\\a_i(1+u)\ge a_j(1-v)}}
       [m_i\sqrt{a_i}D(u)+m_j\sqrt{a_j}D(v)].
 \tag{G1}
\]

The feasible set is nonempty compact. If a minimizer has strict overlap, continuously decrease its eccentricities together until first contact; cost cannot increase. Thus (G1) equals LP17's contact minimum (§3, (26)–(30), published pp.3–4; arXiv v2 p.4). Its value is positive, since zero cost would force both eccentricities zero, incompatible with \(a_i<a_j\).

Use
\[
 B(m,a)=\min\left(\{\Lambda_i:1\le i\le n\}\cup
                    \{B_{i,i+1}:1\le i<n\}\right).                 \tag{G2}
\]
This is LP's strong threshold: evaluating at \(u=0,v=1-a_i/a_{i+1}\) proves \(B_{i,i+1}<\Lambda_{i+1}\), so only \(\Lambda_1\) is needed in addition to the pairs.

Continuity does not require differentiating a minimizer. For \(\alpha=a_i/a_j\in(0,1)\), write contact points as
\[
 u=t\min\{1,(1-\alpha)/\alpha\},\qquad v=1-\alpha(1+u),\quad 0\le t\le1.
 \tag{G3}
\]
The cost is continuous in \((m,a,t)\); a minimum over this fixed compact interval is continuous. The kink at \(\alpha=1/2\) causes no issue. Finite minima give continuity of B. On a compact action neighborhood define the modulus
\(\Omega_B(r)=\sup_{\|I-J\|_\infty\le r}|B(m,a(I))-B(m,a(J))|\), which tends to zero. A qualitative proof needs this modulus, not an asserted Lipschitz bound at endpoint eccentricity one.

### 1.3 Barrier and compactness [NEW, based on LP17]

In the planar prograde case \(C=\sum\Lambda_i-L\). In space \(C=\sum\Lambda_i-|L|\), with \(L=\sum q_i\times p_i\). Since
\[
 |L|\le\sum_i|L_i|=\sum_i\Lambda_i\sqrt{1-e_i^2},
 \qquad C\ge\sum_i\Lambda_iD(e_i),                         \tag{G4}
\]
the condition \(C<B\) excludes each adjacent radial overlap. It also excludes an individual zero angular momentum orbit: \(\Lambda_iD(e_i)\le C<\Lambda_i\).

For the quantitative closed sublevel \(C\le B-\eta\), \(\eta>0\), each \(|L_i|\ge\Lambda_i-C\ge\eta\). If \(\Lambda_i\le\Lambda_{\max}\), then
\[
 e_i\le e_*:=\sqrt{1-(\eta/\Lambda_{\max})^2}<1,\qquad
 a_i(1-e_i)\ge {a_{\min}\eta^2\over2\Lambda_{\max}^2}.       \tag{G5}
\]
Compactness of the axes/eccentricity constraint set and the strict pair barrier give a **uniform positive adjacent radial gap** \(d_*>0\). Hence positions are bounded, star and pair distances are bounded below, and the energy relation bounds momenta. These produce a compact subset of the regular Newtonian phase domain. They do not assert secular trajectories stay close to one another.

### 1.4 Candidate A identity [CITED / NEW]

Exact angular momentum conservation gives, in either dimension,
\[
 C(t)-C(0)=\sum_i[\Lambda_i(t)-\Lambda_i(0)].              \tag{G6}
\]
Consequently a supplied fast-action bound \(\|\Lambda(t)-\Lambda(0)\|_\infty\le r\) implies
\[
 B(m,a(t))-C(t)\ge\delta-nr-\Omega_B(r),                 \tag{G7}
\]
if initially \(C(0)\le B(m,a(0))-\delta\). This is the entire deterministic reduction. In an ODE application use it on the stopped regular interval first and then use compact continuation; do not assume ellipticity or secular confinement on the final horizon. Planar conservation already exists as `AMD/AngularMomentum.lean:ang_mom`; the vector version is new.

## 2. Planar analytic domain on the whole sublevel

### 2.1 Full slow balls, with the threshold indexed by the fast center [NEW]

Let \(\mathcal L=\{m\sqrt a:a\in\mathcal A\}\). Choose a fixed \(\kappa>0\) so its closed \(4\kappa\)-neighborhood has positive actions and ordered axes, and \(\Omega_B(4\kappa)\le\delta/16\). For a center \(I_c\in\mathcal L\), write \(B_c=B(m,a(I_c))\) and take the physical slow set
\[
 S_c=\{x=(\xi,\eta):A(x)\le B_c-\delta/2\},\qquad
 A(x)={1\over2}\sum_i(\xi_i^2+\eta_i^2).                \tag{D1}
\]
Only centers with \(B_c\ge\delta\) can carry an admissible initial state. Use the larger closed set \(A\le B_c-\delta/4\) and \(\|I-I_c\|\le2\kappa\) to construct an analytic collar. It satisfies
\(A\le B(m,a(I))-3\delta/16\). Thus every point, every periapse direction and every fast phase in this enlarged product is safe. This is stronger than verifying safety just on the initial energy or angular-momentum surface.

The union over centers is compact modulo angle periods. Because the gap between the two AMD levels is fixed and A has bounded gradient there, a fixed positive physical slow collar \(w_0\) around every \(S_c\) fits in the larger set after a small additional action/slow enlargement. The center family is compact, so all widths can be chosen uniformly. A single cutoff \(\min_c B_c\) is **not** used: it would discard legitimate high-threshold initial states.

### 2.2 Kepler map [CITED / ADAPTED]

The regular planar Poincaré chart already covers \(0<\Lambda\), \(\Gamma=(\xi^2+\eta^2)/2<\Lambda\). `Poincare/Chart.lean:analyticOnNhd_poincare` and `poincare_periodic`, and `Exponential/Dictionary.lean:poincareProd_image_prograde`, provide the real analytic periodic map and its range. Thus circular points are included; there is no division by eccentricity or choice of a periapse at \(e=0\).

For a direct complex proof, the scalar eccentric-anomaly equation has derivative \(1-e\cos E\), at least \(1-e_*>0\) on the real domain. A positive imaginary width \(\zeta\) with \(e_*\cosh\zeta<1\), and mean-anomaly width below \(\zeta-e_*\sinh\zeta\), provides a starting estimate; shrink further for complex eccentricity/action perturbations. At circular points use the regular Poincaré form of the equation. Exact quantitative references are Castan's Propositions 1.3 and 1.5, printed pp.25 and 28, equation (1.31). Translating their explicit widths to this larger family is future work; the qualitative uniform IFT/compact-extension argument is sufficient here.

### 2.3 Newtonian denominators and Fourier norm [ADAPTED / NEW]

Complexification uses the **bilinear** quadratic form \(z\cdot z\), not a Hermitian norm. For a real separation vector Q with \(|Q|\ge d\), \(|Q|\le R\), and complex displacement v with Euclidean length at most \(\zeta_q\),
\[
 |(Q+v)\cdot(Q+v)-|Q|^2|\le2R\zeta_q+\zeta_q^2.       \tag{D2}
\]
Choosing the right side below \(d^2/2\) keeps it in the right half-plane, defining a consistent holomorphic inverse-square-root branch. Apply this both to \(q_i\) and \(q_i-q_j\), using twice the position error in the latter. The recoil term is polynomial. Bounds on the chart then give a uniform analytic bound for the disturbing function.

Alternatively apply the existing `Exponential/ComplexTube.lean:tube` directly to the compact phase-cell family and its open safe neighborhood. It gives a periodic holomorphic extension with positive uniform widths. This is the cleanest qualitative Lean route. **[OPEN RISK]** The family-indexed compact-set packaging and agreement of extensions on overlaps need implementation; no new obstruction to existence is apparent.

Choose an available fast strip of width \(2s\), action width at least \(\kappa\), and slow width at least \(2w\). A sup bound M on that larger strip implies a weighted Fourier bound on width s:
\[
 \sum_{j\in\mathbb Z^n}\sup|f_j|e^{2\pi s|j|_1}
 \le M\left({1+e^{-2\pi s}\over1-e^{-2\pi s}}\right)^n.
 \tag{D3}
\]
Take F at least one and at least this bound for the period-one perturbation. F, s, w, \(\kappa\) depend only on fixed data and the AMD margin, not \(\mu\) or the selected phase/slow state.

## 3. One exact extended normal-form lemma [CITED]

This is the zero-resonance specialization of `KAM.Nekhoroshev.nf`, `KAM/Nekhoroshev/Partial/NormalForm.lean:604`, with the hypotheses from `Partial/Setting.lean:ExtNFHyp`. Source blueprint: `p11b-partial-nf.tex:bpN:p11:nf`. It is stated explicitly to avoid importing an action-angle-only lemma as a slow-variable theorem.

Let \(n,k\ge1\), \(S\subset\mathbb R^{2k}\), center \(I_c\), \(r,w,s,K,\alpha,\varepsilon>0\), \(L\ge0\), \(p>1\), and \(q=p/(p-1)\). Put \(\ell=w/r\), \(c_s=2\pi/\ell^2\). In period-one fast angles, use the weighted Poisson tensor with ordinary fast canonical block and slow block multiplied by \(c_s\). Let \(\mathcal D(r,s)\) be the max-norm complex r-tube around \(\{I_c\}\times(S/\ell)\), with \(|\operatorname{Im}\theta|_\infty<s\). Require:

1. \(h(I)\) is holomorphic on the complex action r-ball and real on real actions; \(f\) is holomorphic, fast-periodic and real on real points of \(\mathcal D(r,s)\), with weighted Fourier norm at most \(\varepsilon\).
2. For every integer \(j\ne0\), \(|j|_1\le K\), \(|j\cdot\partial h(I_c)|\ge\alpha\); on the action ball the complex frequency variation obeys the repository's Lipschitz bound L.
3. \(KLr\le\alpha/p\), \(64\pi ksr\le w^2\), \(2\pi Ks\ge6\), and \(\varepsilon\le\alpha r/(2^7qK)\).

Then there are \(\Psi,g,f_*\), with \(\Psi:\mathcal D(r/2,s/6)\to\mathcal D(r,s)\) holomorphic, injective, real, period-equivariant and canonical for that weighted tensor, such that
\[
 (h+f)\circ\Psi=h+g+f_*,\quad\partial_\theta g=0,
\]
\[
 \|g-\langle f\rangle\|_{r/2,s/6}\le {32qK\varepsilon^2\over\alpha r},\qquad
 \|f_*\|_{r/2,s/6}\le\varepsilon e^{-2\pi Ks/6},           \tag{N1}
\]
and, in scaled coordinates,
\[
 |\Delta I|_\infty\le{qK\varepsilon\over\alpha},\quad
 |\Delta\theta|_\infty\le{10q\varepsilon\over2\pi\alpha r},\quad
 |\Delta x_{scaled}|_\infty\le{qK\varepsilon\over8\alpha}.\tag{N2}
\]
In particular these imply \(|\Delta I|\le r/128\) and physical \(|\Delta x|\le w/1024\), by `nnf_disp_radius`.

To identify this with the physical Hamiltonian, set \(\theta=\lambda/(2\pi)\), \(x=\ell x_{scaled}\), and replace H by \(H/(2\pi)\). Then \(\dot\theta=\partial_IH/(2\pi)\), \(\dot I=-\partial_\lambda H\), and the slow equations have exactly the weighted coefficient \(c_s\). **There is no residual time rescaling.** `Partial/Domain.lean:domain_field_scaled` supplies the corresponding existing conversion pattern. The Diophantine constant for this h is \(\gamma_1=\gamma_D/(2\pi)\).

`Partial/Nonresonant.lean:nonresonant` additionally supplies the following already-proved transfer/first-fast-exit conclusion. For an actual solution starting at \(I_c\), if its physical slow coordinate remains in S between 0 and t, then
\[
 |I(u)-I_c|_\infty\le r/2\quad(u\in[0,t]),\qquad
 |t|\le{sr\over5\varepsilon}e^{2\pi Ks/6}.              \tag{N3}
\]
It uses `Partial/Preimage.lean:preimage` and handles original versus normalized actions. We do not assume an inverse map exists just because the forward map is close to identity.

## 4. Cutoff, exponent and first exit

### 4.1 Explicit parameter algebra [NEW]

Choose \(p=q=2\), a fixed \(L\ge1\) dominating the complex frequency Lipschitz constant, \(\varepsilon=\mu F\), and
\[
 a={1\over2(\tau+1)},\quad
 K=\left({\gamma_1^2\over4096L\varepsilon}\right)^a,
 \quad\alpha=\gamma_1K^{-\tau},\quad
 r={\alpha\over4LK}=16\sqrt{\varepsilon/L}.             \tag{E1}
\]
The library allows a real cutoff K; a floor is unnecessary. For small enough \(\mu\), \(K\ge1\), \(2\pi Ks\ge6\), \(r\le\kappa\), and \(64\pi ksr\le w^2\). Also
\[
 KLr=\alpha/4\le\alpha/2,\qquad
 {\alpha r\over256K}=4\varepsilon\ge\varepsilon.        \tag{E2}
\]
Thus all small-divisor and Lie-series conditions hold. The competing bounds are \(r\asymp\gamma_1 K^{-(\tau+1)}\) and \(\varepsilon\lesssim\gamma_1^2K^{-2(\tau+1)}\), explaining the exponent. They yield \(r/2=8\sqrt{F/L}\sqrt\mu\). If \(\tau=n-1/2\), then \(a=1/(2n+1)\), exactly the proposed exponent; \(\tau\) is not silently set to \(n\).

Choose
\[
 c={\pi s\over6}\left({\gamma_1^2\over4096LF}\right)^a,
 \qquad T(\mu)=e^{c\mu^{-a}}=e^{\pi sK/6}.              \tag{E3}
\]
Shrink \(\mu_*\) so \(sr/(5\varepsilon)\ge1\). Then (E3) is below (N3). Constants depend on the fixed data only.

### 4.2 Excluding slow exit with original angular momentum [NEW]

Start at any admissible state, choose center \(I_c=\Lambda(0)\), and use \(S_c\) from (D1). On a stopped regular interval before secular exit, apply (N3). Then (G6) gives
\[
 A(x(t))=C(t)\le B_c-\delta+nr/2\le B_c-7\delta/8
                                                               \tag{E4}
\]
after imposing \(nr/2\le\delta/8\). This is strictly inside \(S_c\), whose boundary is \(B_c-\delta/2\). A first secular exit is impossible. This uses the exact **original** AMD, not a claim that the near-identity transformation preserves AMD or that the secular normal form has stable motion.

At the same time
\[
 C(t)\le B(m,a(t))-\delta+nr/2+\Omega_B(r/2)
       \le B(m,a(t))-\delta/2.                            \tag{E5}
\]
The compact barrier (G5) yields positive separation, bounded momenta and a strict chart collar. Standard ODE continuation excludes a finite endpoint before T. Reversing time gives the symmetric interval. Local uniqueness on the regular physical domain yields the stated uniqueness. The existing `AMD/ConfinementExit.lean:amd_exit_forward`, `amd_exit_backward`, `AMD/MovingODE.lean:moving_ode` provide the planar pattern.

This is not circular: (N3) is invoked on each time segment already inside S; (E4) improves the boundary inequality on that segment, forbidding its first exit. Compact continuation then extends the original physical solution.

### 4.3 Budget and axis conversion [NEW / CITED]

| Budget | Sufficient condition |
|---|---|
| Positive ordered actions and analytic action collar | \(r\le\kappa\), fixed \(4\kappa\)-neighborhood chosen in §2 |
| Moving threshold | \(\Omega_B(r/2)\le\delta/8\) |
| Original AMD increase | \(nr/2\le\delta/8\) |
| Slow brackets | \(64\pi ksr\le w^2\) |
| Inverse/coordinate transfer | Already included in (N3), with (N2) and the preimage theorem |
| Genuine osculating radial error | \(2C_{osc}\mu\le d_*/2\), and stellar periapse error below half its lower bound |

The AMD/threshold budget actually leaves at least \(3\delta/4\); reporting \(\delta/2\) reserves room. Since \(a_i=(\Lambda_i/m_i)^2\), bounded \(\Lambda\) converts \(O(\sqrt\mu)\) action drift to \(O(\sqrt\mu)\) axis drift. This is already the algebra in `Exponential/Safety.lean:keplerAxis_drift_le`.

## 5. Spatial extension without secular reduction [ADAPTED / OPEN RISK]

The barrier (G4) is dimension-independent. Strong safety gives \(|L|>0\). Rotate the **initial** total angular momentum to the positive z-axis and keep this frame fixed; vector conservation keeps it aligned thereafter. Let \(G_i=|L_i|\), \(H_i=L_i\cdot e_z\), and use spatial Poincaré variables with actions
\[
 \Gamma_i=\Lambda_i-G_i={\xi_i^2+\eta_i^2\over2},\qquad
 Z_i=G_i-H_i={u_i^2+v_i^2\over2}.                       \tag{S1}
\]
On the actual orbit, \(C=\sum(\Gamma_i+Z_i)\). Moreover every individual summand is nonnegative, so
\(H_i=\Lambda_i-(\Gamma_i+Z_i)\ge\Lambda_i-C\ge\eta>0\).
Thus each orbit remains prograde relative to the invariable plane; both \(G_i\) and \(H_i\) are uniformly positive. The full ball \(\sum(\Gamma+Z)\le B_c-\delta/4\) lies inside \(\Gamma_i<\Lambda_i\), \(Z_i<G_i\), hence away from the retrograde singularity. Circular and coplanar points must be regularized, not excluded.

For **off-orbit points** in this enlarged ball, \(C_z=\sum\Lambda-L_z\), while the rotation-invariant AMD satisfies \(C\le C_z\). Therefore the entire ball is still collision-safe even if \(L_x,L_y\ne0\). This removes the need to construct a symplectic chart on the constrained level \(L_x=L_y=0\). The normal form acts on a genuine open full-dimensional neighborhood.

Use \(k=2n\) slow canonical pairs in (N1)–(N3). The fast dimension is still n, so the time exponent is unchanged. Rotation invariance makes constants independent of the chosen alignment. What remains substantial is a **regular analytic symplectic spatial chart with the exact identities (S1), onto property, complex collar, and Newtonian dictionary**, including e=0 and inclination=0. Classical Poincaré/regular-coordinate literature supplies the construction; this repository's existing planar chart does not prove it. The current `ComplexTube.tube` is also typed on `Phase (n+n)` with n fast angles: its gluing argument must be generalized to independent fast/slow dimensions before spatial use. These are concrete implementation/source-audit risks, not secular-dynamical hypotheses to add to Candidate B.

## 6. Genuine osculating corollary [NEW]

Hamilton's equations for (M) give actual heliocentric velocity
\[
 v_i=\dot q_i=p_i/m_i+\mu\sum_jp_j.                     \tag{O1}
\]
Define the physical two-body osculating convention using \(\kappa_i=1+\mu m_i\),
\[
 E_i^{osc}=|v_i|^2/2-\kappa_i/|q_i|,\quad
 a_i^{osc}=-\kappa_i/(2E_i^{osc}),\quad
 \mathbf e_i^{osc}=(|v_i|^2/\kappa_i-1/|q_i|)q_i
                  -(q_i\cdot v_i)v_i/\kappa_i.          \tag{O2}
\]
On the proved safe compact set, these differ from the canonical elements by \(O(\mu)\), uniformly for the **entire exponential time interval**, because this is a pointwise smooth-map estimate, not an accumulated integration error. Use the eccentricity vector and its norm; no differentiability of a periapse angle at e=0 is needed. The energy stays negative after shrinking \(\mu_*\).

By (G5), adjacent canonical radial annuli have gap \(d_*\); by (O2), actual osculating periapses/apoapses differ by at most \(C_{osc}\mu\). Hence
\(a_i^{osc}(1+e_i^{osc})<a_{i+1}^{osc}(1-e_{i+1}^{osc})\), and all osculating periapses are positive. This excludes intersection of the instantaneous conics and implies collision avoidance. It says nothing about a finite stellar surface or neglected forces. A separate observational input lemma is needed to start from intervals of actual osculating elements rather than canonical phase data.

## 7. Cheaper route: sharp LP with existing Nek77 exponents

**[ADAPTED]** Keep `partialConvex_nekhoroshev` unchanged. On each small fast box around a center use the full slow ball above, with an open slightly larger ball and a fixed collar. Normalize the perturbation by B0 as in `Exponential/Perturbation.lean:perturbation`; its small parameter is \(\nu=B_0\mu\). The Kepler Hessian is definite; the existing sign/time-reversal adapter applies.

The existing theorem gives a stopped fast drift \(\nu^{b_n}/2\) for \(\nu^{-1}e^{\nu^{-a_n}}\), where
\[
 a_n={2\over6n^2-3n+14},\qquad b_n={3\over6n^2-3n+14}.   \tag{K77}
\]
Choose a finite covering by smaller fast boxes, uniform enlarged slow levels with reserved margins, and take the minimum of their smallness thresholds and the maximum of their drift constants. Replace r/2 in (E4)–(E5) by this \(O(\mu^{b_n})\) drift. The erosion `innerCore D` in N's source must be supplied by the reserved physical slow collar. This produces a new planar strong-LP theorem for **all mean-motion frequencies**, including resonant ones, with no secular hypothesis.

It is not an immediate corollary of the old headline `planetaryExponentialSafety`, since an `AMDBox` can exclude points of the sharp curved region. It is an assembly upgrade using its internal engines. It is the recommended first milestone; the nonresonant improvement is a second adapter using the same geometry.

## 8. Status of the first unresolved analytic obligation

The request was a uniform exponential fast-angle normal form on the **entire enlarged** strong-AMD sublevel. On paper it reduces to three explicit steps: (a) full-product safe compactness from (G1)–(G5), (b) uniform analytic extension and Fourier bound from (D1)–(D3), and (c) the existing `nf` with fixed physical slow width and \(r\asymp\sqrt\mu\). These steps account for slow Poisson derivatives, preimages, circular states, all phases, and the moving threshold. No unexplained secular estimate remains.

**Planar status:** a concrete qualitative proof route is supplied; compact-family domain/adapter lemmas are not yet written or independently audited. **Spatial status:** the same argument is conditional on building and auditing the regular spatial chart package just specified, not on a dynamical secular assumption. **Explicit-constant status:** open; the current compact-extension proof gives existence only. No claim of practical masses, theorem closure, or completed formalization follows from this note.
