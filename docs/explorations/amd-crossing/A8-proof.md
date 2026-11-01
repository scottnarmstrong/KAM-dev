> Source: `PROOF/MAIN.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`. Claimed complete proof (PROOF/OPEN.md reads "None"); an independent refute-first audit is the first campaign gate.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

# Strong AMD and exponential safety

31 October 2026. Mathematical proof for subsequent Lean formalization.

**Result.** The planar theorem is proved in Theorem 15; the spatial theorem is proved in Theorem 19. Both have the sharp strong Laskar–Petit threshold, a fixed positive margin, action drift at most a constant times \(\sqrt\mu\), and time \(\exp(c\mu^{-1/(2(\tau+1))})\). Neither assumes anything about secular stability. These are paper proofs, not new Lean certificates. No assertion about novelty, useful numerical mass thresholds, or perpetual stability is made.

The analytic argument is supplied here rather than inferred from a formal secular expansion. It averages about the **linear** Hamiltonian with the initial Kepler frequencies, in a norm of Hamiltonian vector fields. The nonlinear Kepler term is part of the perturbation on an action tube of radius \(\sqrt\mu\). This gives a particularly short proof with arbitrary canonical slow variables and a fixed complex collar around their entire allowed real set. Lemma 13 also checks the finite-cutoff route already implemented in the repository; the Lean campaign can reuse that engine instead of implementing our alternative proof of the analytic lemma.

## 1. Data and precise conclusions

Fix an integer \(n\ge2\), numbers \(\nu_i>0\) with \(\max_i\nu_i=1\), a compact set
\[
\mathcal A\subset\{a\in\mathbb R^n:0<a_1<\cdots<a_n\},
\]
and \(\delta,\gamma>0\), \(\tau>n-1\). The empty compact set is allowed and gives a vacuous assertion. Space dimension is \(d=2\) or \(3\). Physical Euclidean lengths, denoted \(|\cdot|\), are distinguished from the maximum norm \(\|\cdot\|_\infty\) on action vectors and complex coordinate vectors.

Units are gravitational constant and stellar mass equal to one. Planet masses are \(m_i=\mu\nu_i\). On heliocentric positions \(q_i\) and scaled canonical momenta \(p_i\), use symplectic form \(\sum_i dp_i\wedge dq_i\), with \(\iota_{X_H}\Omega=-dH\), and the exact Hamiltonian
\[
 H_\mu=\sum_i\left({|p_i|^2\over2\nu_i}-{\nu_i\over|q_i|}\right)
 +\mu f(q,p),\qquad
 f={1\over2}\left|\sum_i p_i\right|^2-
       \sum_{i<j}{\nu_i\nu_j\over|q_i-q_j|}.                 \tag{1}
\]
Its open physical domain excludes \(q_i=0\) and \(q_i=q_j\). Solutions use physical time.

Define the specific canonical energy, canonical velocity and eccentricity vector by
\[
 v_i=p_i/\nu_i,\quad E_i=|v_i|^2/2-1/|q_i|,\quad
 \mathbf e_i=(|v_i|^2-1/|q_i|)q_i-(q_i\cdot v_i)v_i.
\]
When \(E_i<0\), put
\[
 a_i=-{1\over2E_i},\quad I_i=\Lambda_i=\nu_i\sqrt {a_i},\quad
 e_i=|\mathbf e_i|,\quad L_i=q_i\times p_i,
 \quad L=\sum_iL_i,\quad C=\sum_i I_i-|L|.                 \tag{2}
\]
In the plane the cross product is the oriented scalar determinant, and \(|L|\) is its absolute value. Equivalently embed the plane in \(\mathbb R^3\). A nondegenerate elliptic canonical state has \(E_i<0\) and \(e_i<1\). Our hypotheses below imply the latter condition; it need not be added independently.

Physical angular momentum and physical AMD are \(\mu L\) and \(\mu C\). Thus \(\delta\) is a fixed **normalized** AMD margin; its physical value is \(\mu\delta\). The splitting (1) always uses central Kepler parameter one, even though the physical star moves.

The action chamber is
\[
\mathcal Q=\{I:I_i>0,\ (I_1/\nu_1)^2<\cdots<(I_n/\nu_n)^2\}.
\]
For \(I\in\mathcal Q\), write \(a_i(I)=(I_i/\nu_i)^2\), \(D(u)=1-\sqrt{1-u^2}\), and
\[
 B_{ij}(I)=\min_{\substack{0\le u,v\le1\\
                  a_i(I)(1+u)\ge a_j(I)(1-v)}}
                    [I_iD(u)+I_jD(v)]\quad(i<j),
\]
\[
 B_{\rm cross}(I)=\min_{i<n}B_{i,i+1}(I),\qquad
 B_\star(I)=\min_i I_i,\qquad B(I)=\min(B_{\rm cross}(I),B_\star(I)).       \tag{3}
\]
The minima are genuine attained minima; Lemma 4 proves this and their continuity. These definitions are on their indicated carriers, without arbitrary values outside the action chamber.

The fast Hamiltonian and radian frequencies are
\[
 h(I)=-\sum_i{\nu_i^3\over2I_i^2},\qquad
 \omega_i(I)={\nu_i^3\over I_i^3}=a_i(I)^{-3/2}.             \tag{4}
\]
Our Diophantine condition is
\[
 |k\cdot\omega(I^0)|\ge\gamma |k|_1^{-\tau}
       \quad\text{for every }0\ne k\in\mathbb Z^n.          \tag{5}
\]
All angles in the proof have period \(2\pi\). Lemma 13 records the conversion to the repository's period-one normal-form convention.

**The common conclusion of Theorems 15 and 19.** There are positive constants
\(\mu_0,c,T_0,A_I,A_a,d_\star,d_{\rm pair},A_{\rm osc}\), depending only on \((d,n,\nu,\mathcal A,\delta,\gamma,\tau)\), such that for every \(0<\mu\le\mu_0\) and every initial state with \(q_i\ne0\), \(E_i<0\),
\[
 a(0)\in\mathcal A,\qquad (5),\qquad C(0)\le B(I^0)-\delta,              \tag{6}
\]
the unique maximal solution of (1) exists on \([-T_\mu,T_\mu]\), where
\[
 T_\mu=T_0\exp(c\mu^{-a}),\qquad a={1\over2(\tau+1)}.                  \tag{7}
\]
Initial pair collisions are excluded by (6), as proved below. On this interval the state is elliptic, \(I(t)\in\mathcal Q\), and
\[
 \|I(t)-I^0\|_\infty\le A_I\sqrt\mu,\qquad
 \|a(t)-a(0)\|_\infty\le A_a\sqrt\mu,
\]
\[
 |C(t)-C(0)|\le nA_I\sqrt\mu,\qquad
 C(t)\le B(I(t))-\delta/2,                                      \tag{8}
\]
\[
 a_i(t)(1-e_i(t))\ge d_\star,\qquad
 a_{i+1}(t)(1-e_{i+1}(t))-a_i(t)(1+e_i(t))\ge d_{\rm pair}.       \tag{9}
\]
Actual star distances and all planet-pair distances have the respective lower bounds in (9). The velocity-osculating elements defined in Lemma 16 have perihelion and aphelion radii within \(A_{\rm osc}\mu\) of the canonical ones; after the stated choice of \(\mu_0\), their star and adjacent-annulus gaps are at least \(d_\star/2\) and \(d_{\rm pair}/2\).

Here **no orbit crossing** means the strict ordering of the entire instantaneous radial annuli in (9), first for canonical elements and then for actual-velocity osculating elements. It is stronger than separation of the current positions. The theorem concerns all phases and all allowed secular states, not a selection of invariant tori. Setting \(\tau=n-1/2\) gives exponent \(1/(2n+1)\).

## 2. Exact dynamics and the sharp geometric barrier

### Lemma 1 — normalization and Newtonian reconstruction

**Statement.** For every \(d\in\{2,3\}\), positive \(\nu,\mu\), Hamiltonian (1) is the zero-total-momentum translation reduction of the Newtonian \((1+n)\)-body Hamiltonian, divided by \(\mu\), and uses unchanged time. Its solutions reconstruct Newtonian solutions with masses \((1,\mu\nu_1,\ldots,\mu\nu_n)\).

**Proof.** In barycentric coordinates let planet momenta be \(P_i=\mu p_i\), and \(P_0=-\sum_iP_i\). The canonical translation reduction has relative positions \(q_i=x_i-x_0\) and momenta \(P_i\): indeed \(\sum_{i=0}^nP_i\cdot dx_i=\sum_{i=1}^nP_i\cdot dq_i\). Its kinetic energy is
\(\sum_i|P_i|^2/(2\mu\nu_i)+|\sum_iP_i|^2/2\); its potential energy is \(-\sum_i\mu\nu_i/|q_i|-\sum_{i<j}\mu^2\nu_i\nu_j/|q_i-q_j|\). Both the symplectic form and Hamiltonian acquire the same factor \(\mu\) on substituting \(P_i=\mu p_i\). Cancelling this factor gives (1), with the same time variable.

For an explicit inverse set \(M=1+\mu\sum_i\nu_i\), \(x_0=-\mu\sum_i\nu_iq_i/M\), \(x_i=x_0+q_i\), \(\dot x_0=-\mu\sum_i p_i\), and \(\dot x_i=p_i/\nu_i\). Hamilton's equation
\[
 \dot q_i=p_i/\nu_i+\mu\sum_jp_j                               \tag{10}
\]
shows that the displayed velocities differentiate the displayed positions. The equations for \(\dot p_i\), obtained by differentiating the potentials in (1), are exactly Newton's equations after multiplying the planet momenta by \(\mu\). Pair differences are \(q_i-q_j\), and star differences are \(q_i\). This proves the claim. **Dependencies:** definitions. **Status: proved here.**

### Lemma 2 — elementary orbital identities

**Statement.** For every \(\nu>0\), \(q\ne0\), \(v=p/\nu\), and \(E=|v|^2/2-1/|q|<0\), definitions (2) satisfy
\[
 e^2=1+2E|q\times v|^2=1-|q\times v|^2/a\le1,
 \qquad |q\times p|=I\sqrt{1-e^2},                            \tag{11}
\]
and
\[
 a(1-e)\le |q|\le a(1+e),\qquad
 |p|^2=\nu^2(2/|q|-1/a).                                    \tag{12}
\]
These statements include the limiting radial case \(e=1\).

**Proof.** Expand the square of \((|v|^2-1/|q|)q-(q\cdot v)v\), using \(|q\times v|^2=|q|^2|v|^2-(q\cdot v)^2\), to get the first equality in (11). Substitution of \(2E=-1/a\) gives the rest. To verify (12), put \(r=|q|\) and \(\ell=q\times v\). The energy identity and the orthogonal radial/tangential decomposition give
\[
 (q\cdot v)^2=2r-r^2/a-|\ell|^2\ge0.
\]
Use \(|\ell|^2=a(1-e^2)\) and complete the square: \((r-a)^2\le a^2e^2\). The last identity is the energy definition. **Dependencies:** definitions. **Status: proved here.**

### Lemma 3 — exact angular momentum and the AMD identity

**Statement.** On every connected interval of existence of (1), \(L\) is constant. In the negative-energy region \(C\ge0\). If \(C<B_\star(I)\), then \(L\ne0\); relative to the unit vector \(\widehat L=L/|L|\), all individual projections \(H_i=L_i\cdot\widehat L\) are positive. On such an orbit
\[
 C(t)-C(0)=\sum_i(I_i(t)-I_i(0)),\quad
 C=\sum_i(I_i-H_i)\ge\sum_i I_iD(e_i).                       \tag{13}
\]
If \(C\le B_\star(I)-m\) for \(m>0\), then \(H_i\ge m\) for every \(i\). In the planar case choose the plane's orientation so that \(L>0\); all individual scalar angular momenta are then positive.

**Proof.** Differentiate \(\sum_iq_i\times p_i\). The recoil contribution from \(\dot q_i\) is \(\mu(\sum_jp_j)\times(\sum_ip_i)=0\); the other kinetic terms vanish individually. Central forces have zero torque. The two forces of each planet pair contribute a multiple of \((q_i-q_j)\times(q_i-q_j)=0\). Thus \(\dot L=0\), and the fundamental theorem of calculus gives constancy. By (11), \(|L|\le\sum_i|L_i|\le\sum_iI_i\), so \(C\ge0\). If \(L=0\), then \(C=\sum_iI_i\ge\min_iI_i\), a contradiction. Each \(I_i-H_i\) is nonnegative, since \(H_i\le|L_i|\le I_i\). Their sum is \(C\), hence \(H_i\ge I_i-C\). Finally \(H_i\le I_i\sqrt{1-e_i^2}\) proves the inequality in (13); its identity follows from constant \(|L|\). **Dependencies:** Lemmas 1–2. **Status: proved here.**

### Lemma 4 — attained, continuous, sharp thresholds

**Statement.** For all positive masses and \(I\in\mathcal Q\), every minimum in (3) is attained and positive. Each \(B_{ij}\) and \(B\) is continuous on \(\mathcal Q\). The pair minimum occurs at radial contact. It agrees, after division by \(I_j\), with the Laskar–Petit relative critical AMD for \(\alpha=a_i/a_j\) and mass ratio \(\nu_i/\nu_j\). Moreover
\[
 B_{ij}(I)<I_j,\qquad B(I)=\min(B_{\rm cross}(I),I_1).        \tag{14}
\]
The pair threshold is the exact least AMD at which two coplanar prograde ellipses with these axes can have touching radial annuli; the star threshold is the exact deficit needed for a radial degeneration.

**Proof.** The feasible subset of \([0,1]^2\) is closed and nonempty: \((0,1-\alpha)\) is feasible. The objective is continuous. At a feasible \((u,v)\), replace both coordinates by \(t(u,v)\), where \(t=(1-\alpha)/(\alpha u+v)\le1\). This gives contact and cannot increase the objective. Contact can be parameterized over the fixed interval \([0,1]\):
\[
 m(\alpha)=\min(1,(1-\alpha)/\alpha),\quad
 u=m(\alpha)t,\quad v=1-\alpha-\alpha m(\alpha)t.             \tag{15}
\]
The objective in (15) is jointly continuous in \((I,t)\). On every compact neighborhood inside \(\mathcal Q\) it is uniformly continuous; the inequality
\( |\min_tF(I,t)-\min_tF(J,t)|\le\sup_t|F(I,t)-F(J,t)|\)
proves continuity. A zero minimum would require \(u=v=0\), which cannot give contact because \(\alpha<1\). Finite minima preserve continuity and positivity. The competitor \((0,1-\alpha)\) gives \(B_{ij}\le I_jD(1-\alpha)<I_j\), proving (14).

For completeness, the minimizing eccentricities lie in \((0,1)^2\). At \(u=0\), increasing \(u\) along contact decreases the cost, since \(D'(0)=0\) and \(D'(1-\alpha)>0\). At an endpoint \(v=0\) with \(u<1\), decreasing \(u\) decreases the cost to first order. At \(u=1\), decreasing \(u\) by \(\epsilon\) lowers its cost by order \(\sqrt\epsilon\), while the increase in the other cost is at most order \(\epsilon\), since \(v\le1-\alpha<1\). If \(u=1,v=0\), the same comparison applies. Thus both eccentricities are nondegenerate. Place the inner aphelion and outer perihelion on the same ray, with opposite perihelion directions. The ellipses then touch at contact and their combined AMD is the minimum. Other planets can be circular and coplanar. A radial orbit has \(e=1\), hence eccentricity deficit \(I_i\); prograde ellipses with \(e\uparrow1\) approach that value. This is sharpness of the geometric threshold, not a statement that dynamics above threshold must collide.

Finally \(I_i/I_j=(\nu_i/\nu_j)\sqrt\alpha\), so division of the objective by \(I_j\) gives exactly the relative contact minimization. This identification is also checked against [Laskar–Petit, arXiv v2, §3–3.2, equations (26)–(39), pp.4–5](https://arxiv.org/pdf/1703.07125v2), and the corresponding published article. No optimizer formula from that source is needed. **Dependencies:** definitions, elementary compactness and calculus. **Status: proved here.**

### Lemma 5 — the uniform strong barrier

**Statement.** Let \(U\subset\mathcal Q\) be compact and \(m>0\). Over all negative-energy states with \(I\in U\) and \(C\le B(I)-m\), perihelia and adjacent-annulus gaps have uniform positive lower bounds depending only on \((n,\nu,U,m)\). The same holds for every list \(e\in[0,1]^n\) with \(\sum_iI_iD(e_i)\le B(I)-m\). All these states belong to a compact subset of the nonsingular physical region, and satisfy \(H_i\ge m\) in their invariable frame.

**Proof.** If an adjacent gap were nonpositive, its two eccentricities would be feasible for the corresponding minimum. Lemma 3 would give \(C\ge B_{i,i+1}\ge B\), a contradiction. Define
\[
 K_m=\{(I,e)\in U\times[0,1]^n:\sum_iI_iD(e_i)\le B(I)-m\}.
\]
It is compact, by Lemma 4. Every adjacent gap is positive on it. If it is nonempty, the minimum of the finitely many gaps over \(K_m\) is positive; call it \(d_{\rm pair}(U,m)\). If it is empty, take any positive constants and all the assertions are vacuous. In the nonempty case, write \(I_{\max}=\max_{I\in U,i}I_i\), \(a_{\min}=\min_{I\in U,i}a_i(I)>0\), and \(a_{\max}=\max_{I\in U,i}a_i(I)\). The deficit bound gives
\[
 \sqrt{1-e_i^2}\ge m/I_i\ge m/I_{\max},\qquad
 a_i(1-e_i)\ge {a_{\min}m^2\over2I_{\max}^2}.                \tag{16}
\]
The last inequality uses \(1-e=(1-e^2)/(1+e)\ge(1-e^2)/2\). In the nonempty case \(m\le I_{\max}\). Formula (12) bounds \(|q_i|\le2a_{\max}\) and \(|p_i|\le\nu_i\sqrt{2/d_\star}\). Ordered radial intervals imply \(|q_j-q_i|\ge d_{\rm pair}\) for all \(i<j\), by summing intervening gaps or simply ordering the endpoints. Energy remains at most \(-1/(2a_{\max})\). Closing these bounded inequalities gives a compact physical set with no zero denominator and no zero energy. Lemma 3 gives the projection bound. **Dependencies:** Lemmas 2–4. **Status: proved here.**

### Lemma 6 — the moving threshold and continuation

**Statement.** Fix compact \(\mathcal L\subset\mathcal Q\) and \(\delta>0\). There is a compact neighborhood \(U\subset\mathcal Q\) of \(\mathcal L\), and a function
\[
 \Omega_B(r)=\sup\{|B(I)-B(J)|:I,J\in U,\ \|I-J\|_\infty\le r\}
\]
with \(\Omega_B(r)\to0\) as \(r\downarrow0\). If a solution starts with \(I^0\in\mathcal L\), \(C_0\le B(I^0)-\delta\), and its actions stay within \(r\) of \(I^0\), where that tube lies in \(U\), then
\[
 C(t)\le B(I(t))-\delta+nr+\Omega_B(r).                      \tag{17}
\]
If the last two terms are at most \(\delta/2\), the solution cannot terminate at a finite time while those action and ellipticity conditions continue to hold. The same assertion applies backwards in time.

**Proof.** Choose a sufficiently small closed neighborhood of \(\mathcal L\) inside the open chamber. Uniform continuity of \(B\) on this compact set proves the modulus claim. Equation (17) follows by adding the action identity (13) and \(B(I^0)\le B(I(t))+\Omega_B(r)\). Lemma 5 supplies a compact nonsingular physical set, bounded momenta, and energies separated from zero. The vector field of (1) and its derivative are bounded on a neighborhood of this set. Along a solution, the bound on the vector field makes the trajectory Lipschitz in time; at a finite endpoint it has a limit in that compact set. A local solution exists there and is unique: on a small closed ball, the integral map \(z(t)=z_*+\int_0^tX_H(z(u))du\) is a contraction for a time smaller than both the ball radius divided by the field bound and the inverse derivative bound. Picard iteration gives a solution, and the same Lipschitz bound gives uniqueness by iterating the integral inequality. Gluing extends the previous solution. This also explains why loss of ellipticity cannot occur unnoticed: bounded actions put the energies a fixed distance below zero. Replacing the vector field by its negative proves the backwards assertion. **Dependencies:** Lemmas 3–5. **Status: proved here.**

## 3. The planar chart and its entire safe complex domain

### Lemma 7 — a regular planar canonical chart

**Statement.** For each \(\nu>0\), the following is a real analytic symplectic diffeomorphism, with angle read modulo \(2\pi\), from
\[
 I>0,\quad \lambda\in\mathbb T,\quad(x,y)\in\mathbb R^2,
 \quad\Gamma=(x^2+y^2)/2<I
\]
onto the positive-angular-momentum negative-energy planar region. Its form is \(dI\wedge d\lambda+dx\wedge dy\), its energy is \(-\nu^3/(2I^2)\), and its angular momentum is \(G=I-\Gamma\). In particular it is regular at circular orbits.

**Construction and proof.** Put
\[
 a=(I/\nu)^2,\quad s=1-\Gamma/I>0,\quad
 b_e=\sqrt{(1-\Gamma/(2I))/I},\quad k=b_ex,\quad l=-b_ey.
\]
Then \(k^2+l^2=1-s^2<1\). The eccentric longitude \(F\), modulo \(2\pi\), is the unique solution of
\[
 F-k\sin F+l\cos F=\lambda.                                 \tag{18}
\]
The derivative of the left side is \(D_F=1-k\cos F-l\sin F\ge1-\sqrt{k^2+l^2}>0\); its lift increases by \(2\pi\) per period and tends to both infinities. This proves existence and uniqueness. Local inversion is analytic: at a solution, the fixed-point map obtained by subtracting the equation divided by its nonzero derivative is a contraction on sufficiently small complex disks. Its iterates are holomorphic and converge uniformly on a smaller parameter disk, giving the analytic solution. Uniqueness patches the branches and gives \(F(\lambda+2\pi)=F(\lambda)+2\pi\).

Set
\[
 A=\begin{pmatrix}1-l^2/(1+s)&kl/(1+s)\\kl/(1+s)&1-k^2/(1+s)\end{pmatrix},
 \quad c(F)=(\cos F,\sin F),\quad c'(F)=(-\sin F,\cos F),
\]
\[
 q=a(Ac(F)-(k,l)),\qquad p={\nu\over\sqrt a}\,{Ac'(F)\over D_F}.       \tag{19}
\]
These formulas use no perihelion angle at zero eccentricity. When \(e=\sqrt{k^2+l^2}>0\), write \((k,l)=e(\cos\varpi,\sin\varpi)\), \(F=E+\varpi\). Formula (19) becomes the rotated expression
\[
 q=a(\cos E-e,s\sin E),\qquad
 p={\nu\over\sqrt a(1-e\cos E)}(-\sin E,s\cos E).             \tag{20}
\]
It gives the asserted energy, angular momentum, and eccentricity vector by multiplication. These identities extend to \(e=0\) by continuity.

Here is the symplectic calculation, including the exact differential. In unrotated coordinates (20), direct differentiation gives
\[
 p\cdot dq=2e\sin E\,dI+I(1+e\cos E)dE+I\sin E\,de.
\]
A varying perihelion rotation contributes \(G\,d\varpi\). With \(\ell=E-e\sin E\), this is
\[
 p\cdot dq=I\,d\ell+G\,d\varpi+d(2Ie\sin E)
          =I\,d\lambda+\Gamma\,d(-\varpi)+d(2Ie\sin E).
\]
Since \((x,y)=\sqrt{2\Gamma}(\cos\varpi,-\sin\varpi)\),
\(\Gamma d(-\varpi)=(x,dy-y,dx)/2\). Taking exterior derivatives proves symplecticity on \(e>0\), and analyticity extends it across \(e=0\).

For the inverse, recover \(a,I,G\) from energy and angular momentum; recover \((k,l)\) as the eccentricity vector, and hence \(x=k/b_e,y=-l/b_e\). The matrix \(A\) has positive eigenvalues \(1,s\); the vector \(A^{-1}(q/a+(k,l))\) is \(c(F)\). To check its length is one directly, use \(\mathbf e\cdot q=a(1-e^2)-|q|\), which follows by expanding the definition of \(\mathbf e\), and \(|q|^2=q\cdot q\). Equation (18) gives \(\lambda\) modulo \(2\pi\); no argument function is needed, since
\(e^{i\lambda}=e^{iF}\exp[-i(k\sin F-l\cos F)]\).
Momentum is recovered uniquely from the prescribed positive angular momentum and \(\mathbf e=v\times(q\times v)-q/|q|\). All inverse formulas are analytic on this region. This proves the global statement modulo the angle lattice. **Dependencies:** Lemma 2. **Status: proved here.**

### Lemma 8 — a whole-sublevel planar analytic neighborhood

**Statement.** Let \(\mathcal L=\{(\nu_i\sqrt{a_i})_i:a\in\mathcal A\}\), and \(\mathcal L_\delta=\{I^0\in\mathcal L:B(I^0)\ge\delta\}\). There are fixed positive \(r_*,s,b,M\), depending only on \((n,\nu,\mathcal A,\delta)\), such that for every \(I^0\in\mathcal L_\delta\), putting
\[
 \mathcal Z_0=\{z=(x_i,y_i)_i:\ |z|_2^2/2\le B(I^0)-\delta/4\},       \tag{21}
\]
the product chart of Lemma 7 and the exact pulled-back perturbation \(f\) are holomorphic on
\[
 \|I-I^0\|_\infty<r_*,\quad |\operatorname{Im}\lambda|_\infty<4s,
 \quad\operatorname{dist}_\infty(z,\mathcal Z_0)<4b.                   \tag{22}
\]
On a slightly smaller version of this domain the chart, momenta, \(f\), and all their first derivatives have bound \(M\). Every Newtonian denominator there has a single holomorphic branch, and its modulus is bounded away from zero. In physical coordinates the chart Hamiltonian equals \(h(I)+\mu f(I,\lambda,z)\), without a truncation. The ball in (21) contains every secular state allowed by the initial margin, with a fixed collar.

**Proof.** If \(\mathcal L_\delta\) is empty there is no initial state satisfying (6). Otherwise it is compact. Choose a compact chamber neighborhood \(U\) and a small fixed real action width \(r_g>0\) so that every \(4r_g\)-tube about \(\mathcal L_\delta\) lies in \(U\) and \(\Omega_B(4r_g)\le\delta/16\). For real \(\|I-I^0\|_\infty\le4r_g\) and \(z\in\mathcal Z_0\),
\[
 \sum_i\Gamma_i\le B(I^0)-\delta/4\le B(I)-3\delta/16.
\]
Consequently \(\Gamma_i<I_i\) with a fixed margin, all phases are safe by Lemma 5, and eccentricities are bounded by one fixed \(e_*<1\). The set of \((I^0,I,z,\lambda)\) so obtained, with angles in one closed period cell, is compact. The chart of Lemma 7 is analytic on an open neighborhood of it.

We spell out the uniform complex extension. At each real point, the construction in (18) uses a derivative at least \(1-e_*\). The entire functions sine and cosine have bounded first and second derivatives on disks of radius one about real points. Choose a fixed disk radius \(\rho>0\) small enough that the derivative of the Newton fixed-point map differs from zero by at most \(1/4\); choose a fixed parameter radius \(\eta>0\) small enough that this derivative remains at most \(1/2\), and its value at the original root is within \(\rho/2\) of that root. The map then preserves the \(\rho\)-disk and contracts by \(1/2\). Uniform convergence of its holomorphic iterates proves a bounded holomorphic local branch. The positive radicands and \(1+s\) in (19) also stay a fixed distance from zero after reducing \(\eta\). In every complexified real formula, sums of real squares become bilinear sums of complex squares, never Hermitian squared norms; norms used to estimate their sizes remain ordinary absolute-value norms.

One may equivalently glue these local extensions on complex balls centered at real points. The intersection of two such balls is convex, and when nonempty has a nonempty relatively open real intersection: take a point on the segment between their real centers. On that real intersection both extensions equal the same real analytic map. Expanding in a power series at a real point shows equality on a complex neighborhood, and the identity theorem on the connected intersection gives equality everywhere there. Translates of the angle cell patch by the same argument. A finite subcover of the compact real set, with half-sized balls, leaves a uniform complex neighborhood. Thus the periodic chart and disturbing function are single-valued on the angle torus, independently of \(I^0\) or \(\mu\). The auxiliary lift of \(F\) itself increases by \(2\pi\) around a period, as it should.

For the force denominators let \(d>0\) be a common real lower bound for \(|q_i|\) and \(|q_i-q_j|\), and \(Q\) a real upper bound for those lengths. If a complex vector \(w\) lies within Euclidean distance \(\eta_q\) of such a real vector \(w_0\), then
\[
 |w\cdot w-|w_0|^2|\le2Q\eta_q+\eta_q^2.
\]
Reduce the complex neighborhood until the right side is at most \(d^2/2\). Then \(\operatorname{Re}(w\cdot w)\ge d^2/2\); the square root with positive real part and its reciprocal are holomorphic, with reciprocal bounded by \(\sqrt2/d\). This explicitly applies to every star and pair denominator. The chart and its derivatives are bounded on a smaller compact complex neighborhood, by the displayed formulas and Cauchy's one-variable estimates. In particular \(f\) and its first derivatives have a uniform bound. Choose \(r_*,s,b\) so that (22), and a small enlargement needed for those derivatives, are inside this neighborhood. The product chart gives (4), so the split is exact. **Dependencies:** Lemmas 4–7. **Status: proved here.**

## 4. Exponential averaging with evolving slow variables

The next three lemmas include the analytic estimates rather than treating the secular coordinates as parameters in a Poisson bracket. They apply to any fixed number of canonical slow pairs.

### Lemma 9 — Fourier, Cauchy, and commutator estimates

**Statement.** Fix integers \(n\ge1,m\ge0\), a nonempty real compact set \(Z\subset\mathbb R^{2m}\), and \(r,b,s>0\). For \(1\le\rho\le4\) let
\[
 \mathcal D_\rho=\{\|I-I^0\|_\infty<\rho r,
  |\operatorname{Im}\theta|_\infty<\rho s,
  \operatorname{dist}_\infty(z,Z)<\rho b\}.                    \tag{23}
\]
The slow tube uses the maximum norm; \(Z\) need not be a polydisk or have a regular boundary. Hamiltonian fields in this section use the standard constant symplectic form in \((I,\theta,z)\); after dividing coordinates by \((r,s,b)\), its blocks have coefficients \(rs\) and \(b^2\). Set \(D=2n+2m\). For a periodic holomorphic vector field \(V\), use scaled components
\(\widehat V=(V_I/r,V_\theta/s,V_z/b)\), and define
\[
 \|V\|_\rho=\sum_{k\in\mathbb Z^n}
       \sup_{\|I-I^0\|<\rho r,\ \operatorname{dist}(z,Z)<\rho b}
           |\widehat V_k(I,z)|_\infty e^{\rho s|k|_1}.        \tag{24}
\]
For \(0<\sigma<\rho-1\), norms are monotone under restriction, mean and complementary Fourier projections have norm at most one, and
\[
 \|[V,W]\|_{\rho-\sigma}\le {2D\over\sigma}\|V\|_\rho\|W\|_\rho.    \tag{25}
\]
The Fourier tail with \(|k|_1>K\), on a strip narrowed by \(\sigma s\), has norm at most \(e^{-\sigma sK}\|V\|_\rho\). A uniform supremum bound for \(\widehat V\) on \(\mathcal D_4\) gives a finite bound on \(\|V\|_3\) depending only on that bound, \(n\), and \(s\).

**Proof.** Fourier coefficients are integrals over the real angle torus. Shift each contour, with sign opposite to its Fourier index, inside the holomorphic strip. A supremum bound \(M\) on width \(4s\) gives coefficient bound \(Me^{-4s|k|_1}\) on the parameter domain of \(\mathcal D_3\), by taking limits from narrower contours. Summing at width \(3s\) gives
\(M\sum_k e^{-s|k|_1}=M((1+e^{-s})/(1-e^{-s}))^n\).
Products of Fourier series have convolution coefficients, and \(|k+l|_1\le|k|_1+|l|_1\), giving the Banach-algebra estimate.

For action and slow derivatives, a complex coordinate disk of radius \(\sigma r\) or \(\sigma b\) about a point in the smaller tube lies in the larger tube, by the triangle inequality for distance to \(Z\). Cauchy's formula gives the derivative bound \(1/\sigma\) in scaled coordinates. For angles use
\(s|k_j|e^{-\sigma s|k|_1}\le1/(e\sigma)\).
Each of the \(D\) terms in a component of \(DV\,W-DW\,V\) is therefore bounded by the product of the norms divided by \(\sigma\). This gives (25). Removing the zero coefficient proves both projection claims. The tail estimate follows by extracting \(e^{-\sigma sK}\). Absolute convergence on smaller domains justifies multiplication and differentiation; truncation followed by the bounds gives the same results if an initial norm is defined by a limit. **Dependencies:** elementary contour integration and Cauchy's formula, with derivations above. **Status: proved here.**

### Lemma 10 — cohomology and a controlled Lie step

**Statement.** In Lemma 9, let \(\omega\) satisfy (5), let \(h_0=\omega\cdot(I-I^0)+c_0\), and let \(H=h_0+g+f\) be a real holomorphic Hamiltonian, with \(g\) independent of \(\theta\). Write \(E=\|X_f\|_\rho\), \(G=\|X_g\|_\rho\). For any loss \(0<\sigma<\rho-1\), there is a Hamiltonian generator \(\chi\), real on real points, satisfying
\[
 \omega\cdot\partial_\theta\chi=f-\langle f\rangle,
 \quad \|X_\chi\|_{\rho-\sigma/2}\le
 A\sigma^{-\tau}E=:u,\quad
 A=\gamma^{-1}\max\{1,(2\tau/(es))^\tau\}.                 \tag{26}
\]
There are constants \(c_D,B_D>0\), depending only on \(D\), such that if \(u/\sigma\le c_D\), its time-one map \(\phi\) is holomorphic, real, symplectic and periodic-equivariant on \(\mathcal D_{\rho-\sigma}\), and
\[
 H\circ\phi=h_0+g+\langle f\rangle+f_+,
 \qquad\|X_{f_+}\|_{\rho-\sigma}\le
                   B_D{u\over\sigma}(G+E).                 \tag{27}
\]
The map and the negative-time map each move points by at most \(u\) in scaled coordinates wherever the intervening collar is available. Their derivatives differ from the identity by at most a dimension constant times \(u/\sigma\) on a further half-collar. They are mutual inverses on their common inner domain. Constants do not depend on \(r,b,Z,I^0\) or on the coefficients of the constant symplectic form after scaling.

**Proof.** Define \(\chi_0=0\) and \(\chi_k=f_k/(ik\cdot\omega)\) for \(k\ne0\). The divisor is constant in every phase variable. Thus the Fourier coefficients of \(X_\chi\) are precisely those of \(X_f\), for \(k\ne0\), divided by \(ik\cdot\omega\). Since
\[
 |k|_1^\tau e^{-\sigma s|k|_1/2}
       \le (2\tau/(e\sigma s))^\tau,
\]
equation (26) follows. The scalar series exists as well: for \(k\ne0\), some fast action component of \(X_f\) equals \(-ik_jf_k\), so its norm controls \(|f_k|\) after a fixed factor \(r\). The reality relation \(f_{-k}=\overline {f_k}\) gives the same relation for \(\chi\).

Here are detailed Lie and flow estimates. If a holomorphic field \(Y\) has norm \(u\) on a larger domain, repeated application of (25), dividing a total collar \(\eta\) into \(j\) equal parts, gives
\[
 {1\over j!}\|\operatorname{ad}_Y^jV\|_{\rho-\eta}
 \le {j^j\over j!}\left({2Du\over\eta}\right)^j\|V\|_\rho
 \le\left({2eDu\over\eta}\right)^j\|V\|_\rho.               \tag{28}
\]
The inequality \(j!\ge(j/e)^j\) follows by comparing \(\sum_{l=1}^j\log l\) with \(\int_1^j\log t\,dt\). Hence the Lie series converges when the last geometric ratio is less than one. It also represents the pullback by the actual flow: the flow solves the integral equation, its derivative solves the corresponding variational equation, and differentiating the pullback in time gives the commutator equation. Successive substitution gives the Lie series; (28), also on a slightly larger inner domain, bounds the remaining iterated integral by a geometric tail tending to zero.

There is no missing scalar convergence issue in this vector-field argument. In scaled coordinates the constant symplectic form has coefficients bounded by \(\max(rs,b^2)\), so a scalar bracket satisfies a bound of the form \(D\max(rs,b^2)\|X_F\|\|X_\chi\|\). Apply this once, then (28) to the remaining commutators. This proves convergence of the scalar series after its first bracket; angle-independent additive constants are unchanged. For identification with the time-one flow, trajectories from \(\mathcal D_{\rho-\sigma}\) move at most \(u\le\sigma/4\), so stay in \(\mathcal D_{\rho-3\sigma/4}\). Relative to the generator domain \(\mathcal D_{\rho-\sigma/2}\), a collar \(\sigma/4\) remains. When \(4eDu/\sigma\le1/4\), the integral Taylor remainders on these trajectories have geometric ratio at most \(8eDu/\sigma\le1/2\). They tend to zero, proving the exact scalar identity used below.

For completeness, the flow exists for both signs of time up to one. In a scaled ball about any starting point of the inner domain, Cauchy's estimate bounds \(DY\) by a dimension constant times \(u/\eta\). If \(u\) is a sufficiently small multiple of the collar, the integral map on continuous paths stays in that ball and is a contraction. Its iterates converge uniformly, including for complex initial values on smaller balls; this proves holomorphic dependence. Uniqueness gives the inverse, reality, and lattice equivariance. Integrating the field gives displacement \(\le u\); integrating the variational equation gives \(\|D\phi-1\|\le e^{C_Du/\eta}-1\le2C_Du/\eta\) when the exponent is at most one. The Hamiltonian field has \((DY)^T\Omega+\Omega DY=0\); differentiating \((D\phi^t)^T\Omega D\phi^t\) proves symplecticity. This argument works for any constant nondegenerate \(\Omega\), including the scaled form, without using a bound on \(\Omega^{-1}\).

With \(L_\chi F=\{F,\chi\}\), our sign convention gives \(L_\chi h_0=-(f-\langle f\rangle)=-f^{\rm osc}\). Therefore the exact remainder is
\[
 f_+=\sum_{j\ge1}{L_\chi^j(g+f)\over j!}
       -\sum_{j\ge1}{L_\chi^jf^{\rm osc}\over(j+1)!}.        \tag{29}
\]
For Hamiltonian vector fields each bracket here is a vector-field commutator, up to sign, so (28) applies directly. Use the remaining collar \(\eta=\sigma/2\). If \(v=4eDu/\sigma\le1/4\), the two sums have norm at most
\(v(1-v)^{-1}(G+2E)\le4v(G+E)\).
This proves (27), for example with \(B_D=16eD\), and with \(c_D>0\) decreased to satisfy the flow estimates as well. The term \(X_{h_0}\), which need not be small, has disappeared through the exact homological identity. This is essential. **Dependencies:** Lemma 9. **Status: proved here.**

### Lemma 11 — exponential normal form on the full slow set

**Statement.** In the setting of Lemmas 9–10 suppose
\(H=h_0+F\), \(\|X_F\|_3\le\epsilon\), and let \(N\ge1\) be an integer. There is a number \(q_D>0\), depending only on \(D\), such that
\[
 A\epsilon N^{\tau+1}\le q_D                              \tag{30}
\]
implies a real holomorphic symplectic map \(\Phi:\mathcal D_2\to\mathcal D_3\), with
\[
 H\circ\Phi=h_0+Z+R,\quad\partial_\theta Z=0,
 \quad\|X_R\|_2\le\epsilon2^{-N},\quad\|X_Z\|_2\le2\epsilon.         \tag{31}
\]
The scaled displacement of \(\Phi\) is at most \(1/16\). Its inverse exists on \(\mathcal D_{3/2}\), takes values in \(\mathcal D_2\), and has the same displacement bound. In particular the two action-coordinate errors are at most \(r/16\). These assertions hold on the entire tube around \(Z\), with no restriction on the slow dynamics.

**Proof.** Put \(\rho_j=3-j/N\), \(g_0=0\), \(f_0=F\). Apply Lemma 10 with loss \(\sigma=1/N\) at each step. If
\(E_j\le\epsilon2^{-j}\), \(G_j\le2\epsilon\), then
\[
 u_j\le A N^\tau\epsilon2^{-j},\qquad
 E_{j+1}\le3B_D A\epsilon N^{\tau+1}E_j.
\]
Choose
\[
 q_D=\min(c_D,\,1/(6B_D),\,1/64).
\]
Condition (30) validates the step and gives \(E_{j+1}\le E_j/2\). Since \(g_{j+1}=g_j+\langle f_j\rangle\), its norm is at most \(\sum_{l<j+1}E_l\le2\epsilon\); it remains angle independent. Induction proves all the estimates. Composition of the actual flow maps gives \(\Phi=\phi_0\circ\cdots\circ\phi_{N-1}\) and the exact identity (31), with \(Z=g_N,R=f_N\). The telescoped displacement is at most
\[
 \sum_{j<N}u_j\le2A\epsilon N^\tau\le2q_D/N\le1/32<1/16.
\]
Each factor is defined on its prescribed larger domain and maps its smaller domain into it; the displacement is smaller than its allocated collar. Thus the composition has the stated domain, is injective, and is symplectic. For an initial point in \(\mathcal D_{3/2}\), apply the negative-time flows in reverse composition order. Every intermediate point stays within scaled distance \(1/32\) of \(\mathcal D_{3/2}\), hence lies strictly in \(\mathcal D_2\), which is inside the domains of every factor and its negative-time flow. This constructs the inverse, with the same telescoped bound. The two compositions are identities by uniqueness of each flow. Cauchy's formula applied to the bounded holomorphic displacements gives \(\|D\Phi-1\|\le D/8\) on \(\mathcal D_{3/2}\), and \(\|D\Phi^{-1}-1\|\le D/4\) on \(\mathcal D_{5/4}\), in the induced maximum norm; these deliberately loose bounds are uniform. They are not used to infer invertibility, which was already proved by the negative-time flows. No claim about a trajectory staying near its initial slow point entered the argument. **Dependencies:** Lemmas 9–10. **Status: proved here.**

### Lemma 12 — planetary scaling, exponential time, and finite divisors

**Statement.** Suppose the uniform chart-domain statement of Lemma 8 holds, with \(m\) canonical slow pairs, and \(I^0\) satisfies (5). There are constants \(M_1,\kappa,\mu_1,c>0\), uniform in \(I^0\) and depending only on the fixed chart data and \((\gamma,\tau)\), with the following properties. For \(0<\mu\le\mu_1\), set
\[
 r=\sqrt\mu,\quad a={1\over2(\tau+1)},\quad
 N=\lfloor\kappa\mu^{-a}\rfloor\ge1,\quad
 \epsilon=M_1\sqrt\mu,
 \quad h_0=h(I^0)+\omega(I^0)\cdot(I-I^0).                   \tag{32}
\]
The normal form of Lemma 11 exists on the entire corresponding slow tube, with \(\epsilon,N\) as in (32), and it can be rewritten as
\[
 H_\mu\circ\Phi=h(J)+\mathcal Z(J,z)+R(J,\theta,z),\qquad
 \partial_\theta\mathcal Z=0,
 \quad |\dot J|_\infty\le r\epsilon2^{-N}.                  \tag{33}
\]
The last bound holds along every transformed solution in \(\mathcal D_2\). With \(T_\mu=\exp(c\mu^{-a})\), any portion of an original solution in \(\mathcal D_1\) of duration at most \(T_\mu\), starting at action \(I^0\), has
\[
 \|I(t)-I^0\|_\infty\le r/4.                               \tag{34}
\]
Furthermore, for every complex action \(\|I-I^0\|_\infty\le4r\) and every \(0<|k|_1\le N\),
\[
 |k\cdot\omega(I)|\ge(\gamma/2)N^{-\tau}.                  \tag{35}
\]

**Proof.** First decrease the fixed widths in Lemma 8 so that their \(\mathcal D_4\) closures have the uniform first-derivative bounds there. Restrict \(\mu_1\) so that \(4r<r_*\) and \(r\le1\). The scaled vector field of \(h-h_0\) has only angle components; they are \((\omega(I)-\omega(I^0))/s\), bounded by a constant times \(r\). The scaled components of \(X_{\mu f}\) are bounded by a constant times \(\mu/r+\mu/s+\mu/b\). These are at most a fixed constant times \(\sqrt\mu\). The supremum-to-Fourier estimate in Lemma 9, losing only the fixed strip between \(\mathcal D_4\) and \(\mathcal D_3\), gives \(\|X_{H_\mu-h_0}\|_3\le M_1\sqrt\mu\). This is where a fixed initial strip, rather than a strip shrinking with \(N\), avoids a dimension-dependent small-divisor exponent.

Choose \(\kappa>0\) so that
\[
 A M_1\kappa^{\tau+1}\le q_D/2,
 \qquad 4L_\omega\kappa^{\tau+1}\le\gamma/2,                 \tag{36}
\]
where \(L_\omega\) is a fixed complex Lipschitz bound for \(\omega\) on the action neighborhood. Such a bound follows also directly from \(\partial_{I_i}\omega_i=-3\nu_i^3/I_i^4\). If \(L_\omega=0\), omit the second restriction. Since \(a(\tau+1)=1/2\), equation (36) implies (30). Take \(\mu_1\) smaller so that \(\kappa\mu^{-a}\ge2\), hence \(N\ge\kappa\mu^{-a}/2\), and \(\epsilon\le1/8\).

Set \(c=(\log2)\kappa/4\). Then \(T_\mu\le2^{N/2}\). Define \(\mathcal Z=h_0-h+Z\) in (31). It is independent of \(\theta\), proving (33). For an original solution inside \(\mathcal D_1\), the inverse in Lemma 11 defines a transformed solution inside \(\mathcal D_2\); symplecticity proves that it solves the transformed Hamilton equations. Integrating (33), and including the forward error at time \(t\) and inverse error at time zero, gives
\[
 \|I(t)-I^0\|_\infty
 \le r/16+r\epsilon |t|2^{-N}+r/16
 \le r/8+r\epsilon2^{-N/2}\le r/4.
\]
This applies for both signs of \(t\). Finally
\[
 |k\cdot\omega(I)|\ge\gamma N^{-\tau}-4L_\omega Nr
                       \ge(\gamma/2)N^{-\tau}
\]
by (36), proving (35).

The averaging proof actually inverts only \(ik\cdot\omega(I^0)\), for all initial Fourier modes, and absorbs \(h-h_0\) in the small vector field. It never assumes an open set of all-orders Diophantine actions. Equation (35) supplies the finite-order tube statement explicitly; no all-orders arithmetic condition is asserted at later times. **Dependencies:** Lemmas 8–11, or their stated spatial version. **Status: proved here.**

### Lemma 13 — checked reuse of the repository's finite-cutoff engine

**Statement.** The analytic data in Lemma 8, with \(m=n\) planar or \(m=2n\) spatial, can also be fed to the repository's `KAM.Nekhoroshev.nonresonant`, using a full center-dependent slow ball, with radius \(r=D_0\sqrt\mu\), cutoff \(K\asymp\mu^{-a}\), and a fixed slow collar. Its stopped action estimate has the same exponent as Lemma 12. This is a checked specialization for formalization, not an additional hypothesis of either headline theorem.

**Proof and exact interface check.** The inspected declaration is `/root/code/KAM/KAM/Nekhoroshev/Partial/Nonresonant.lean:341`, `KAM.Nekhoroshev.nonresonant`, at commit `f5625f197c621ccc8045e8392a07e23fe0cb10fc`. Its normal-form input is `ExtNFHyp` in `Partial/Setting.lean`; the supplied normal-form theorem is `Partial/NormalForm.lean:604`, `KAM.Nekhoroshev.nf`, and its preimage proof is in `Partial/Preimage.lean`. The real slow set `S` in `PartialBlock` is arbitrary; take it to be the closed ball (21), not a neighborhood of the starting secular point.

The following conversion checks physical time and the slow bracket. Put \(\theta=\lambda/(2\pi)\), \(\ell=w/r\), \(\widetilde z=z/\ell\), and
\[
 \widehat H(\theta,I,\widetilde z)
    ={1\over2\pi}H(2\pi\theta,I,\ell\widetilde z).
\]
Use the repository's weighted slow bracket coefficient \(c_s=2\pi/\ell^2\). Then \(\dot\theta=H_I/(2\pi)\), \(\dot I=-H_\lambda\), and \(\dot{\widetilde z}=J H_z/\ell\), exactly the original equations in the new coordinates, with unchanged time. The unperturbed frequencies are \(\omega/(2\pi)\). The planar oscillator convention here is related to the repository's slow position/momentum by \((\xi,\eta)=(x,-y)\), and the spatial node pair by \((u,-v)\); these sign changes give the repository's standard slow bracket.

Choose fixed period-one strip \(s_1>0\) and physical slow width \(w>0\) within the complex neighborhood. The scalar Fourier bound is \(\varepsilon=M_2\mu\), uniformly: the contour estimate in Lemma 9 applies to \(f/(2\pi)\). Let \(L\) bound the complex frequency derivative of \(h/(2\pi)\), choose \(p=2\) and conjugate exponent \(q=2\), and put
\[
 \alpha={\gamma\over2\pi}K^{-\tau},\qquad
 K=\lfloor\kappa_1\mu^{-a}\rfloor,\qquad r=D_0\sqrt\mu.
\]
All non-geometric numeric hypotheses of `ExtNFHyp` and `nonresonant` are
\[
 KLr\le\alpha/2,\qquad
 \varepsilon\le{\alpha r\over256K},\qquad
 64\pi m s_1r\le w^2,\qquad 2\pi Ks_1\ge6.                 \tag{37}
\]
For any fixed \(D_0>0\), the first two follow on choosing
\[
 LD_0\kappa_1^{\tau+1}\le\gamma/(4\pi),\qquad
 M_2\kappa_1^{\tau+1}\le\gamma D_0/(512\pi).
\]
The last two follow by decreasing \(\mu_0\). Holomorphy, reality, periodicity, the weighted Fourier norm, positivity of widths and perturbation bound, and the dimension hypotheses follow from Lemma 8 and \(n\ge2,m\ge1\). The nonresonance module is exactly \(\{0\}\), which is symmetric. The rescaled complex slow tube has physical width \(w\) because \(\ell r=w\); it does not shrink with \(\mu\). The finite action tube lies inside (22) for small \(\mu\). The equations just computed verify the literal orbit-field equality in the theorem. The initial fast action is its center, as required.

The conclusion of `nonresonant` is drift \(\le r/2\) through
\[
 {s_1r\over5\varepsilon}\exp(2\pi Ks_1/6),                  \tag{38}
\]
provided physical slow coordinates belong to \(S\) only through the queried time. Since \(K\ge\kappa_1\mu^{-a}/2\) for small \(\mu\), (38) exceeds \(\exp(c_1\mu^{-a})\) for a fixed positive \(c_1\). Lemma 14 below discharges precisely that stopped membership. The exact normal-form statement also bounds slow displacement; its companion `nnf_disp_radius` gives physical slow displacement at most \(w/2^{10}\). Thus slow coordinates have not been omitted from the estimate or the inverse map. The independent paper proof is Lemmas 9–12; this specialization explains how to reuse the already available Lean theorem. **Dependencies:** Lemma 8, algebra (37), inspected repository declarations. **Status: proved specialization; repository use is read-only, without a fresh build or certificate audit.**

## 5. Planar first exit and the planar theorem

### Lemma 14 — first exit on the entire allowed secular ball

**Statement.** Fix the data of §1 and the uniform chart/domain construction (21)–(22). Suppose the exact real chart is an analytic symplectic diffeomorphism of the entire prograde negative-energy region, modulo the fast angle lattice, satisfies \(H_\mu=h+\mu f\), and, along the physical orbit in a fixed reference frame, has \(|z(t)|_2^2/2=C(t)\). Then the estimate of Lemma 12 proves existence, uniqueness, and (8)–(9) on (7). This is an internal assembly lemma; its chart conditions are proved in Lemma 7 for the plane and Lemmas 17–18 for space.

**Proof.** By the nonnegativity of AMD, every admissible center belongs to \(\mathcal L_\delta\); no assumption that \(B>\delta\) at every point of the originally supplied compact set is needed. Choose once and for all a compact neighborhood \(U\subset\mathcal Q\) of \(\mathcal L_\delta\). Decrease \(\mu_0\le\mu_1\) so that \(r=\sqrt\mu\) has its action tube in \(U\) and satisfies
\[
 nr+\Omega_B(r)\le\delta/4,\qquad\Omega_B(r)\le\delta/16.     \tag{39}
\]
All these choices precede the initial point and \(\mu\); the modulus is uniform on \(U\).

Take the maximal local Newtonian solution. On the connected interval containing zero where it is elliptic, its chart is defined, and
\[
 \|I(t)-I^0\|_\infty<r,\qquad C(t)<B(I(t))-\delta/2,         \tag{40}
\]
the identity for \(z\) gives
\[
 |z(t)|_2^2/2=C(t)<B(I^0)-\delta/2+\Omega_B(r)
                         \le B(I^0)-7\delta/16.
\]
Thus every such physical point lies in \(\mathcal D_1\), using the **whole** ball (21). This verification uses only the stopped conditions (40), not the desired exponential conclusion. Lemma 12 is consequently valid on any finite subinterval of this interval up to \(T_\mu\), and improves the action bound to \(r/4\). Equations (13), (17), and (39) improve the AMD margin to at least \(3\delta/4\).

Suppose the forward end of this interval were a time \(t_*\le T_\mu\). Lemma 5, with margin \(\delta/2\), bounds the entire preceding orbit in a compact nonsingular physical set. Its energies stay uniformly negative and its individual angular momenta have positive projections bounded away from zero. Lemma 6 extends the physical solution through a finite maximal endpoint; at any other endpoint ordinary continuity is enough. The chart remains valid at the limit because it is a chart of the entire prograde negative-energy region. The improved bounds \(r/4<r\) and \(3\delta/4>\delta/2\) persist on a small neighborhood of the limiting time. This contradicts the definition of \(t_*\). The backwards proof uses the same normal-form estimate with \(|t|\) and the backwards continuation argument. Hence the solution exists through both endpoints of (7), and all inequalities hold there by continuity.

The final separation constants are those of Lemma 5 with \(m=\delta/2\), including the explicit choice
\[
 d_\star={a_{\min}\delta^2\over8I_{\max}^2}.                 \tag{41}
\]
All adjacent and nonadjacent physical pairs are separated. The action-to-axis estimate follows directly from
\[
 |a_i(I)-a_i(I^0)|={|I_i-I_i^0|\,|I_i+I_i^0|\over\nu_i^2}
            \le {2I_{\max}\over\min_i\nu_i^2}\|I-I^0\|_\infty.
\]
Thus one can take \(A_I=1\), \(A_a=2I_{\max}/\min_i\nu_i^2\), and \(T_0=1\) with the choices in Lemma 12. Any enlargement of these constants is harmless. Using Lemma 13 instead replaces \(A_I\) by a fixed multiple of \(D_0\) and leaves the argument unchanged: its stopped slow-membership premise is exactly the membership proved before the improvement. **Dependencies:** Lemmas 3–6 and 12; specified chart identities. **Status: proved internal assembly lemma, with all its conditions discharged in the headline theorems.**

### Theorem 15 — planar nonresonant exponential safety

**Statement.** The conclusion of §1 holds in dimension two for precisely hypotheses (6).

**Proof.** Lemma 3 gives nonzero total angular momentum and individual angular momenta of its sign. Reverse the planar orientation if necessary, so that this sign is positive; the Hamiltonian and all constants are invariant under this orthogonal change applied simultaneously to position and momentum. The product of the charts in Lemma 7 covers every initial state and gives \(C=\sum_i\Gamma_i=|z|_2^2/2\) wherever the physical orbit remains in the prograde region. Exact conservation in Lemma 3 keeps the reference orientation fixed. Lemma 8 supplies the analytic domain and perturbation bounds, Lemmas 9–12 the full slow-domain normal form, and Lemma 14 closes the first exit and proves (7)–(9). Lemma 1 reconstructs the exact Newtonian motion, and Lemma 16 below gives the claimed osculating conclusion. There is no hypothesis on the behavior of the averaged Hamiltonian \(\mathcal Z\). This completes the planar proof before use of any spatial chart. **Dependencies:** Lemmas 1–14 and 16 for the osculating corollary. **Status: proved here.**

### Lemma 16 — actual-velocity osculating ellipses

**Statement.** On any of the fixed safe compact physical sets in Lemma 5, define
\[
 V_i=\dot q_i=p_i/\nu_i+\mu\sum_jp_j,\qquad k_i=1+\mu\nu_i,
\]
\[
 E_i^{\rm osc}=|V_i|^2/2-k_i/|q_i|,\quad
 a_i^{\rm osc}=-k_i/(2E_i^{\rm osc}),\quad
 \mathbf e_i^{\rm osc}={ (|V_i|^2-k_i/|q_i|)q_i-(q_i\cdot V_i)V_i\over k_i},
 \quad e_i^{\rm osc}=|\mathbf e_i^{\rm osc}|.                 \tag{42}
\]
For all sufficiently small \(\mu>0\), uniformly on that compact set, these are nondegenerate elliptic elements and
\[
 |a_i^{\rm osc}-a_i|+|\mathbf e_i^{\rm osc}-\mathbf e_i|\le A\mu,
 \qquad |a_i^{\rm osc}(1\pm e_i^{\rm osc})-a_i(1\pm e_i)|\le A_{\rm osc}\mu.  \tag{43}
\]
The constants depend only on that compact set and the fixed masses, in dimensions two and three. These ellipses pass through the current positions and are tangent to the actual heliocentric velocities.

**Proof.** If \(|p_i|\le P\), then \(|V_i-v_i|\le nP\mu\), and \(|k_i-1|\le\mu\). Direct expansion of the energy and eccentricity-vector expressions in (42), using the bounded positions and momenta and \(|q_i|\ge d_\star\), gives \(|E_i^{\rm osc}-E_i|+|\mathbf e_i^{\rm osc}-\mathbf e_i|\le A_0\mu\). Since \(E_i\le-1/(2a_{\max})\), choose \(\mu_0\) so that \(E_i^{\rm osc}\le-1/(4a_{\max})\). The identity for the difference of two reciprocals then proves the axis estimate. The triangle inequality gives \(|e_i^{\rm osc}-e_i|\le|\mathbf e_i^{\rm osc}-\mathbf e_i|\), including at circular orbits, so differentiability of the norm at zero is not assumed. Since \(e_i\le e_*<1\), decreasing \(\mu_0\) gives \(e_i^{\rm osc}<1\); expansion of the products gives the second estimate of (43). The two-body initial-value problem with position \(q_i\), velocity \(V_i\), and gravitational parameter \(k_i\) defines precisely the tangent ellipse with these invariants; the orbital identities in Lemma 2, with parameter \(k_i\), verify that it contains the position. Require finally
\(A_{\rm osc}\mu_0\le d_\star/2\) and \(2A_{\rm osc}\mu_0\le d_{\rm pair}/2\).
Subtracting the two endpoint errors proves the stated half-gaps. A convention with gravitational parameter one satisfies the same estimate, but is a separately named convention. **Dependencies:** Lemmas 1–2 and 5. **Status: proved here.**

## 6. Spatial chart and the spatial theorem

### Lemma 17 — regular spatial Poincaré coordinates on the prograde region

**Statement.** Fix a reference unit vector \(e_3\). For one mass \(\nu>0\), the following map is a real analytic symplectic diffeomorphism from
\[
 I>0,\quad\lambda\in\mathbb T,\quad (x,y,u,v)\in\mathbb R^4,
 \quad\Gamma=(x^2+y^2)/2,\quad Z=(u^2+v^2)/2,
 \quad\Gamma+Z<I                                                   \tag{44}
\]
onto the negative-energy spatial states with \((q\times p)\cdot e_3>0\). The symplectic form is \(dI\wedge d\lambda+dx\wedge dy+du\wedge dv\). Its energy, angular-momentum magnitude and projection are
\[
 -\nu^3/(2I^2),\qquad G=I-\Gamma,\qquad H=I-\Gamma-Z.         \tag{45}
\]
It is regular at circular and coplanar orbits. For \(n\) bodies its fixed-plane deficit is
\(C_{e_3}=\sum_iI_i-L\cdot e_3=\frac12\sum_i(x_i^2+y_i^2+u_i^2+v_i^2)\).

**Construction and proof.** Form the planar vectors \(Q,P\) in (19), embedded in the first two coordinate directions. With \(G=I-\Gamma>0\), put
\[
 t={ (u,-v,0)\over2\sqrt G},\quad c=\sqrt{1-|t|^2},\quad
 R=(1-2|t|^2)\operatorname{Id}+2tt^T+2c[t]_\times,\qquad
 q=RQ,\quad p=RP.                                           \tag{46}
\]
Here \([t]_\times w=t\times w\). Since \(|t|^2=Z/(2G)<1/2\), all square roots are positive and analytic. Direct use of \([t]_\times^2=tt^T-|t|^2\operatorname{Id}\) proves \(R^TR=\operatorname{Id}\), \(\det R=1\), and
\[
 Re_3=(-cv/\sqrt G,-cu/\sqrt G,1-Z/G).
\]
Thus \(q\times p=GRe_3\), proving (45). Formula (46), together with (18)–(19), is the definition even at \(\Gamma=0\) or \(Z=0\); no perihelion or node angle is needed there.

To prove symplecticity, work first where \(e>0\), \(Z>0\). Define the node longitude \(h_n\), inclination \(\iota\), and perihelion longitude \(\varpi\) by
\[
 (u,v)=\sqrt{2Z}(\cos h_n,-\sin h_n),\quad
 Z=G(1-\cos\iota),\quad
 (x,y)=\sqrt{2\Gamma}(\cos\varpi,-\sin\varpi).
\]
Then \(R=R_z(h_n)R_x(\iota)R_z(-h_n)\), and the orbital perihelion rotation is \(g=\varpi-h_n\). Under a varying rotation, the additional term in \(p\cdot dq\) is angular momentum dotted with the infinitesimal rotation vector. The \(g\)-rotation contributes \(G\,dg\), the \(h_n\)-rotation contributes \(H\,dh_n\), and the inclination rotation about the line of nodes contributes zero, as this line is perpendicular to the angular momentum. Explicitly these coefficients are \(p\cdot(a\times q)=a\cdot(q\times p)\) for the relevant unit rotation axis \(a\). The unrotated calculation in Lemma 7 therefore gives
\[
 p\cdot dq=I\,d\ell+G\,dg+H\,dh_n+d(2Ie\sin E)
 =I\,d\lambda+\Gamma\,d(-\varpi)+Z\,d(-h_n)+d(2Ie\sin E).
\]
Taking exterior derivatives gives the asserted form. The set where both eccentricity and inclination are nonzero is dense in (44); both sides are analytic, so equality extends to the circular and coplanar loci.

For the inverse let \(\widehat w=(q\times p)/G\), with \(\widehat w_3>0\). Recover \(I,G\) from energy and angular momentum and set
\[
 c=\sqrt{(1+\widehat w_3)/2},\quad
 u=-\sqrt G\,\widehat w_2/c,\quad v=-\sqrt G\,\widehat w_1/c.
\]
These reconstruct \(R\), and \(R^{-1}q,R^{-1}p\) are planar with positive angular momentum. Apply the explicit inverse in Lemma 7 to recover \(x,y,\lambda\). This proves onto, uniqueness modulo \(2\pi\), and analytic invertibility. It also verifies that the image carrier is exactly the stated prograde negative-energy region. Summing (45) gives the final deficit identity. **Dependencies:** Lemma 7 and the displayed rotation algebra. **Status: proved here.**

### Lemma 18 — spatial whole-sublevel complex domain

**Statement.** Lemma 8 holds spatially with \(m=2n\), the product chart of Lemma 17, and
\[
 \mathcal Z_0=\{z\in\mathbb R^{4n}:|z|_2^2/2\le B(I^0)-\delta/4\}.     \tag{47}
\]
The constants are independent of the choice of reference direction. The domain includes all states allowed by (6) after aligning \(e_3\) with the initial total angular momentum.

**Proof.** For every real point of (47) and the real action neighborhood used in Lemma 8,
\[
 \Gamma_i+Z_i\le B(I^0)-\delta/4\le B(I)-3\delta/16
                                           \le I_i-3\delta/16.
\]
Consequently \(G_i\ge3\delta/16\), \(H_i\ge3\delta/16\), and \(c_i^2=1-Z_i/(2G_i)>1/2\). All the new radicands and denominators in (46) have a fixed positive margin. The fixed-plane deficit equals \(|z|_2^2/2\); each \(I_i-H_i\ge I_i-|L_i|=I_iD(e_i)\). Hence Lemma 5 applies to every point of this whole ball, including points whose total angular momentum is not parallel to the reference direction. Alignment is not a hidden restriction on the analytic domain.

The family over compact \(\mathcal L_\delta\), the real action neighborhood and a full angle cell is compact. Formulas (18)–(19) and (46), with the positive margins just proved, give holomorphic local extensions. The gluing, uniform-width construction and complex-denominator estimate in the proof of Lemma 8 apply verbatim, now in \(6n\) coordinates: the proof there used only finitely many coordinates, the explicit positive margins, compactness, and periodicity. In particular every \((q_i-q_j)\cdot(q_i-q_j)\) still has positive real part on the chosen complex tube; spatial rotations do not replace this check. The exact scalar products and Newtonian potentials are invariant under a simultaneous real orthogonal rotation of all positions and momenta. Thus the domain bounds can be chosen using the same chart relative to an abstract orthonormal frame, independently of its orientation in physical space.

For an actual initial state, Lemma 3 gives \(L\ne0\), so select a fixed orientation-preserving orthogonal map taking \(L/|L|\) to \(e_3\). Applied to both \(q\) and \(p\) it is symplectic. It need not be selected continuously as a function of the initial state: all constants are rotation invariant and the argument uses one fixed rotation per solution. Conservation of \(L\) makes \(C_{e_3}=C\) along that exact solution. Lemma 3 also gives positive individual projections, so Lemma 17 covers it until the stopped boundary. This proves all domain and identity assertions. **Dependencies:** Lemmas 3–5, 8's proved extension argument, and 17. **Status: proved here.**

### Theorem 19 — spatial nonresonant exponential safety

**Statement.** The conclusion of §1 holds in dimension three for precisely hypotheses (6), including circular or coplanar initial orbits.

**Proof.** Use Lemma 18 to align the fixed frame and obtain the entire ball (47) and a uniform complex collar. The chart is symplectic by Lemma 17, and the Kepler energy and exact perturbation are (1), (4). There are \(n\) fast angles and \(2n\) slow canonical pairs. Lemmas 9–12 apply with exactly this pair count: it changes dimension constants in (25) and (30), not the Diophantine exponent or the power of \(\mu\). All small divisors are \(k\cdot\omega(I^0)\) for \(k\in\mathbb Z^n\); no secular divisors are inverted. Conservation of vector angular momentum gives \(|z(t)|_2^2/2=C(t)\) in the original physical chart. These facts discharge every condition of Lemma 14, which proves the exponential interval, the action and AMD bounds, moving-threshold safety, separation, and continuation. Lemma 16 proves the velocity-osculating conclusion in the same dimension, and Lemma 1 reconstructs the exact Newtonian solution. Applying the inverse fixed rotation returns to the original frame without changing any of the inequalities. **Dependencies:** Lemmas 1–6, 9–14, 16–18. **Status: proved here.**

## 7. Source pins, reuse boundaries, and self-refutation

The primary literature was checked by web search and the indicated full texts. The proof above uses no unverified external normal-form theorem. The following pins establish its interpretation and compare available analytic statements:

| Source | Exact verified location | Role and boundary |
|---|---|---|
| [Laskar–Petit, A&A 605, A72 (2017)](https://doi.org/10.1051/0004-6361/201630022) | Publisher text: §2.1–2.2, (2)–(11); §3–3.2, (26)–(39); §5.3 | Exact canonical/AMD and strong-threshold interpretation. The conjectural sentence is in §3. All geometry needed here is independently proved in Lemmas 2–5. |
| [Laskar–Petit, arXiv:1703.07125v2](https://arxiv.org/pdf/1703.07125v2) | §2.1–2.2, pp.1–2; §3, p.4; §3.2, p.5; §5.3, p.10 | Independently verified page pins used in this proof. Contrary to the wording in the initial brainstorm, the conjecture already appears in this March v2. The published-PDF fetch returned HTTP 403, so published page numbers are not asserted as independently checked here. |
| [Barbieri–Marco–Massetti, CMP 396 (2022), 349–381](https://link.springer.com/article/10.1007/s00220-022-04464-0) | Appendix B, Lemma B.1, p.380, (B.1)–(B.5) | Checked action-angle normal-form bounds. This statement alone has no slow pairs and is not used as a supplier for our full domain. |
| [Pinzari–Liu, arXiv:2302.00279v2](https://arxiv.org/pdf/2302.00279v2) | §3.4, Proposition 3.2, pp.30–31; Lemma 3.3, p.31; iteration pp.32–34 | Checked mixed Fourier–Taylor setting. No unverified specialization to zero secular frequencies is used here. |

The repository baseline was inspected at commit `f5625f197c621ccc8045e8392a07e23fe0cb10fc`. Its planar `planetaryExponentialSafety` uses `AMDBox.Admissible`; it does **not** already state the sharp-threshold theorem above. `partialConvex_nekhoroshev` retains a stopped slow-domain condition, so neither its name nor its sealing alone removes the need for Lemma 14. The independent nonresonant proof succeeds; therefore the brief's conditional request for a fallback proof using global Nekhoroshev is not triggered. The existing global route remains useful for a separate resonance-tolerant upgrade, with a different exponent; this document does not label that upgrade proved.

The parallel `RESEARCH/LITERATURE.md` ([A2](A2-literature.md)) and `RESEARCH/GAP-ANALYSIS.md` ([A3](A3-gap-analysis.md)) were consulted after they appeared. Their decisive finding, the arbitrary-slow-set theorem in `Partial/Nonresonant.lean`, was checked against the actual source and incorporated in Lemma 13. The later `RESEARCH/PROOF-PLAN.md` ([A4](A4-proof-plan.md)) and `RESEARCH/STATEMENTS.md` ([A5](A5-statements.md)) were also read: their full-ball, weighted-bracket and moving-threshold mechanisms agree with the construction here. Their spatial-chart risk is addressed explicitly by Lemma 17. Their proposed extra planar prograde premise is unnecessary for our statement because Lemma 3 derives it after orienting the plane. Research prose is not used as an analytic axiom.

**Self-refutation pass.** The following are attempts to break the proof, and the precise reasons they do not break the stated theorem.

| Test | Resolution |
|---|---|
| A planet approaches the star while total AMD remains below the pair threshold. | The theorem uses \(B_\star\) as well; (16) gives a uniform positive perihelion. The pair-only theorem is not claimed. |
| A minimizer uses a parabolic/radial endpoint, making the threshold definition noncompact or wrong. | The definition includes endpoints; (15) proves continuity. Lemma 4 proves the actual pair minimizer is interior. Radial star degeneration is separately included. |
| The compact architecture includes points with \(B(I)<\delta\), or \(B(I)=\delta\). | Only centers in \(\mathcal L_\delta\) can satisfy (6). Equality is allowed and still leaves the \(\delta/4\) enlarged-ball collar. There is no requirement \(\min_U B>\delta\). |
| Spatial total angular momentum vanishes, or one orbit is retrograde. | Lemma 3 excludes both from the strong sublevel; it supplies \(H_i\ge\delta\) initially. This is a consequence, not an extra hypothesis. |
| Classical angles are undefined on circular/coplanar states. | The chart is defined by (18), (19), (46), not by those angles. They are used only on a dense set to prove the symplectic identity. |
| Real separation fails to control complex isotropic vectors \(w\cdot w=0\). | Lemma 8 bounds the change in \(w\cdot w\) and keeps its real part at least \(d^2/2\), for every denominator. |
| A secular trajectory leaves a local chart before exponential time. | There is one global prograde Poincaré chart modulo fast angles, with a tube around the entire ball (21) or (47). No reference secular orbit is used. |
| The analytic spatial ball silently imposes the invariable-plane constraint on transformed points. | It does not: the fixed-plane deficit bounds eccentricity AMD for every point of the ball. Alignment is used only along the original physical solution. |
| The fast-action tube requires an open all-orders Diophantine set. | Only the fixed linear frequencies are inverted; (35) separately verifies the finite-cutoff persistence actually available on a tube. |
| Cauchy estimates cost two derivatives per averaging step and spoil the exponent. | Lemmas 9–10 use vector-field commutators, which cost one derivative. Constant divisors commute with every phase derivative. The iteration condition is exactly \(\epsilon N^{\tau+1}\le\text{constant}\), with \(\epsilon=O(\sqrt\mu)\). |
| Fourier summation adds \(n\) to the Diophantine exponent. | The fixed initial strip pays the supremum-to-coefficient sum once. Subsequent cohomology bounds are diagonal operator bounds in weighted \(\ell^1\), as in (26). |
| The large integrable field ruins the Lie remainder bound. | The exact identity \(L_\chi h_0=-f^{\rm osc}\) is inserted before estimates in (29). No smallness of \(X_{h_0}\) is assumed. |
| Slow derivatives or the singular rescaled symplectic matrix were forgotten. | Every slow coordinate participates in (25). Vector-field commutator and flow estimates contain no inverse-symplectic-matrix norm; physical scaling is already included in \(X_F\). |
| A near-identity map has no inverse on the actual physical states. | Lemma 11 explicitly composes negative-time flows on \(\mathcal D_{3/2}\), with a reserved collar. Both coordinate errors appear in (34). |
| The original threshold moves by more than the AMD drift. | Inequalities (17) and (39) control the sum of both errors. |
| First exit assumes the very confinement it proves. | The stopped region (40) is nonempty initially, permits the estimate, and is strictly improved. Compact continuation then excludes every finite endpoint. |
| Inclination chaos changes the reference plane. | The reference plane is defined by the exactly conserved total vector, not individual orbital planes. No estimate of secular divergence is used. |
| Canonical ellipses are being called velocity-osculating. | They are distinguished in (10), (42), and (43). The osculating gap pays two endpoint errors. |
| Constants depend on \(\mu\) through hidden eccentricity or separation cutoffs. | All real and complex collars are selected from \((n,\nu,\mathcal A,\delta)\) before \(\mu\). Only the deliberately local action radius and iteration count depend on \(\mu\). |

All these checks are mathematical self-review, not independent peer review or a Lean run. No numerical astronomical application or novelty determination has been performed.

## 8. Status and frozen-input record

| Item | Status |
|---|---|
| Exact normalization and Newtonian reconstruction | Proved, Lemma 1 |
| Sharp pair/strong threshold, continuity, uniform geometry | Proved, Lemmas 2–6 |
| Planar regular chart and whole-sublevel analytic domain | Proved, Lemmas 7–8 |
| Exponential normal form including slow motion, maps and inverses | Proved, Lemmas 9–12 |
| Finite-cutoff repository specialization | Checked, Lemma 13; no build run |
| Noncircular first-exit/continuation assembly | Proved, Lemma 14 |
| Planar Candidate B | Proved, Theorem 15 |
| Actual-velocity osculating conclusion | Proved, Lemma 16 |
| Spatial regular chart and whole-sublevel analytic domain | Proved, Lemmas 17–18 |
| Spatial Candidate B | Proved, Theorem 19 |
| New Lean formalization of either headline theorem | Not performed; roadmap supplied |
| Unresolved mathematical lemma in this proof | None |

Input SHA-256 values at the initial read:

```text
BRIEF-3.md                  968be616f5b7c021b152e780822b09aaf499b2734622eea16d6fc3e105ac2947
co-author message           04a2c8c4f0abe1db597e83416599eced31543fbec914d30bf5499d3db9c6cd25
BRAINSTORM-1.md             bed180842b0b85991a7668a13c0c0f08eec2309cddf6a4cd9a612cc2be1fa071
ORCHESTRATOR-ASSESSMENT.md  662e3f9ff089aa5e84d37b3b490ddd80710eca224b1c22fd5e0180e0f8a0b767
RESEARCH/LITERATURE.md     cb7f4bd00db26c25f13d119ad6e77f60534ea409375c78c2d42b702b896ac1b5
RESEARCH/GAP-ANALYSIS.md   e966db1d2f97fc333ac6e7105e0bf778995c04ce90a6fa109cd89583841c85d3
RESEARCH/PROOF-PLAN.md     b669a974c16c7a7b1fa5962277c49ff8f8bd0782455e417b21e93c0051b6134d
RESEARCH/STATEMENTS.md     94f98bff5bbc5b9c47e65c80bb432bbf827fff1a64b9c04f1b960fbeba6167ce
```

The research hashes are the later consulted snapshots, not claims about their earlier or subsequent contents. During this turn the live KAM HEAD advanced to `2235c896b35359358b04d2a9b94e315f06f6458f`. A read-only comparison against the initial commit found no changes in the inspected `Planetary/AMD`, `Exponential`, `Poincare`, `Newtonian`, `Kepler`, `Nekhoroshev/Partial`, or frozen Planetary/Nekhoroshev paths. The reuse locators remain pinned to the initial commit.

Only files under `PROOF/` were written. No repository edits, commits, builds, Lean/Lake invocations, process termination, or global filesystem searches were performed.

