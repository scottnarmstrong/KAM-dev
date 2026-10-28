# Global source-topology review of track P

Reviewer: **sol-global-P**, fresh global reviewer, independent of the writer, extractors and slice reviewers. Date: **2026-10-28**.

**Overall verdict: FAIL.** Two major missing direct external-input edges remain in slice **P-p8**. They affect P-PLANAR and P-FIXED. The seven frozen root statements and identities pass comparison; neither finding changes an author-approved statement. The other five root closures receive source-model PASS. This verdict neither certifies the mathematics nor claims any Lean proof closure: the graph already exposes 34 source gaps.

Only this report is written. No graph, packet, blueprint, manifest, implementation Lean, generated file or git state is changed. No Lean is run. The review follows AGENTS.md, PLAN.md, DECISIONS.md, GLOBAL-BRIEF.md and the binding SPEC, including its P-FIXED revision and writer rulings; the source-only dependency-graph skill supplies the review boundary. Earlier slice verdicts are not accepted as evidence of correctness.

## Snapshot and structural evidence

- `docs/graph/P/DEPGRAPH.md`: SHA256 `129206246957868a9416f571230c14c9fbf2d33e2c78bea13c8b8e5192f2969b`.
- `docs/graph/P/DEPGRAPH_COVERAGE.md`: SHA256 `53e89e4972024fe5c748aa82c98dcf1948d8a2c7c050e44e842f084493ff4a34`.
- `docs/graph/P/SPEC.md`: SHA256 `46c1cf323866edc519123794aae8b00a0c479619e3041fe9dec3d1de777b53bf`.
- `docs/graph/P/GLOBAL-BRIEF.md`: SHA256 `e15dd743a1821fb848d721d3b5a436df5d1d781c2a2198a26dc986f695dce425`.
- `manifest/frozen-anchors.json`: SHA256 `5d8d31f1cc70c3cc67375ab28562e4fd4280215c7455dd329004c4dcd7a2f6fa`.

The assembled graph has **1,363 nodes, 6,071 edges (including six route edges), 77 frozen anchors, 181 dependency leaves, 147 external leaves, no standing-assumption leaves, six alternative route nodes, and 34 explicit SOURCE_GAP records**. All 1,363 nodes feed a root. There are no dangling dependencies or cycles. The coverage inventory has **2,095 items: 1,398 NODE dispositions and 697 exclusions**; no graph node is uncovered. There are no pending node or coverage reviews according to the stored metadata. These are structural results, not independent evidence that a proof paragraph is correctly modelled.

All 25 entries of CORPUS.sha256 match (23 P files and the two P-owned I/N source files); all nine IMPORTS.sha256 entries match. All 77 anchor identity tuples (path, export, manifest ID, contract ID/version and ABI hash) match the manifest. Every root belongs to FROZEN_ANCHORS. Every non-anchor, including all imports and P-owned cross-track nodes, has all four FROZEN_* fields equal to `-`. Manifest state and implementation status are not used.

The required import command was run without `--add`:

```text
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_imports.py docs/graph/P/packets --slice P-imports --self-track P
P-imports: 81 imported nodes present, 81 referenced, 0 missing, 0 unreferenced
```

Each import names an extant owning-graph node. Its four statement fields agree with the owning graph except for six K imports whose hypothesis fields explicitly restore the positive-dimension/positive-strip standing conventions of blueprint/parts/p1-analysis.tex L37-L39; those additions are supported by that source. I/N ownership is confirmed against the now-published owner graphs, so the historical pending-publication wording in the header is not a current ownership gap. The ten P-xown nodes remain P-owned: the I scaling/means/circular components and their steps, and N iterative-special. They are not relabelled as imports.

The read-only checker command was:

```text
python3 scripts/proof_depgraph.py --db docs/graph/P/DEPGRAPH.md --manifest docs/graph/P/DEPGRAPH_COVERAGE.md --source-root . --require-reviewed --require-complete-coverage --require-initial-lean-status --require-all-reachable --report
```

It returned exit 1 with exactly these two diagnostics:

```text
docs/graph/P/DEPGRAPH.md:12: review gate: missing or placeholder GLOBAL_REVIEWER
docs/graph/P/DEPGRAPH.md:13: review gate: missing or placeholder GLOBAL_REVIEW_REF
```

The parser/analyzer was also invoked read-only to obtain the counts above; its diagnostic list contains only these two entries. These unset publication fields are expected before delivery of this review; they are not the reason for FAIL. No dashboard was written or certified current.

## Root-by-root statement reconstruction and closure verdicts

The four fields below are the normalized reconstruction checked against Part 0 (Part 14b for the secular-box roots), the indicated frozen declaration and the assembled node. They agree with the stored fields. For P-G, “connected” is the nonempty `IsConnected` convention of the frozen declaration. The root verdict also includes its dependency closure, so a statement-match PASS does not cancel a missing-edge FAIL.

### `bpP:p0:pg` — PASS

Source: `blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L333-L365`. Frozen declaration: `KAM/Frozen/Planetary/Theorems/ProperlyDegenerateKAM.lean`, `KAM.Planetary.properlyDegenerateKAM`. Manifest identity: `planetary.properlyDegenerateKAM.v1`, contract `planetary.properlyDegenerateKAM@1`, ABI `d347498b8bc8935acd3895d5fd5316822593add37c2eff43f9d7f66bfa63d001`. **Identity and statement comparison: PASS.** Original closure: 366 nodes, 18 exposed source-gap records (including gaps on retained alternative routes).

**SOURCE_HYPOTHESES:** a, b >= 1; V subset R^a open, connected, bounded; W subset R^a open with closure(V) subset W; boundary collar: there are A, d > 0 with meas{I: exists J in boundary V, ¦I-J¦_inf < t} <= A t for all 0 < t < d; r_0, mu_0, B > 0; H_0: R^a -> R, P: R x Ph_{a+b} -> R, P_0: R x R^a -> R, Omega: R x R^a -> R^b, beta: R x R^a -> R^{bxb}; (H1) (mu,z) -> P(mu,z) real analytic at every point of [0,mu_0] x closure(C(V,r_0)); (H2) P(mu, z + shift(k)) = P(mu,z) for mu in [0,mu_0], z in C(V,r_0), k in Z^a; (H3) HasFastDiffeo(H_0,W); (H4) HasBirkhoff(P,V,r_0,mu_0,P_0,Omega,beta); (H5) ¦det beta(mu,I)¦ >= B for mu in [0,mu_0], I in V; (H6) beta(mu,I) symmetric for mu in [0,mu_0], I in V

**SOURCE_QUANTIFIERS:** forall a, b (>= 1), V, W, (A,d collar), r_0, mu_0, B, H_0, P, P_0, Omega, beta (all data fixed first), hypotheses (H1)-(H6); exists r_*, C, c; forall r, mu with 0 < r < r_*, 0 < mu < mu_0, mu < r^6/(log(1/r))^c; exists S

**SOURCE_CONCLUSION:** there exist r_*, C, c with 0 < r_* < r_0, r_* < 1, C > 0, c > 0 such that for all r, mu with 0 < r < r_*, 0 < mu < mu_0, mu < r^6/(log(1/r))^c there is S subset Ph_{a+b} with IsCylKol(H_mu,V,r,mu,C,S) (H_mu = H_0 + mu P(mu,.)) and 0 < meas(S cap F(V,r)), ofReal(1 - C sqrt r) meas F(V,r) < meas(S cap F(V,r)) < meas F(V,r)

**CONSTANT_SCOPE:** r_*, C, c depend on all the data and hypotheses (a, b, V, W, A, d, r_0, mu_0, B, H_0, P, P_0, Omega, beta) and not on r or mu; C is simultaneously the frequency bound of IsCylKol and the measure constant; S depends on (r, mu)

Closure: p5:main, with the analytic extension/jet/uniform-remainder chain, Parts 2–3 averaging and two-scale iteration/limit, Part 4's actual direct slicing estimates, then Part 5's parameter choice, chart, tori, cell transfer, measure and strictness. Part 5 L317–328 supplies constants first, the three restrictions on (r,mu), one shared C for frequencies and measure, and both strict inequalities. The uniform O(radius^5) obligation is p5:uniform-remainder (L65–74), not an extra premise of P-G. Its unpaid analytic inputs remain explicit SOURCE_GAPs; strictness is p5:strictness (L297–313), not an unproved citation to CP11.

### `bpP:p0:planar` — FAIL

Source: `blueprint-P/parts/p0-conventions.tex#bpP:p0:planar@L367-L377`. Frozen declaration: `KAM/Frozen/Planetary/Theorems/PlanarTwoPlanetKAM.lean`, `KAM.Planetary.planarTwoPlanetKAM`. Manifest identity: `planetary.planarTwoPlanetKAM.v1`, contract `planetary.planarTwoPlanetKAM@1`, ABI `53360f66c8f0dfa90319b671830d07e0f10087b394eab73dce5a2bded2651fba`. **Identity and statement comparison: PASS.** Original closure: 781 nodes, 28 exposed source-gap records (including gaps on retained alternative routes).

**SOURCE_HYPOTHESES:** G, m_0 > 0; m, a: Fin 2 -> R with m_i > 0 and a_i > 0 for i = 0,1 and a_0 < a_1 (strictly ordered axes, no numerical separation); eta > 0

**SOURCE_QUANTIFIERS:** forall G, m_0, m, a, eta (data fixed first); exists mu_0, d, D; forall mu with 0 < mu < mu_0; exists S

**SOURCE_CONCLUSION:** there exist mu_0, d, D with 0 < mu_0 and 0 < d < D such that for every mu with 0 < mu < mu_0 there is S subset Ph_{2.2} with 0 < meas S < infinity and MovKol(G,m_0,m,a,mu,eta,d,D,S) (n = 2)

**CONSTANT_SCOPE:** mu_0, d, D depend on (G, m_0, m, a, eta) and not on mu; S depends on mu

Closure: p12:planar L159–171, applying the actual frozen p0:pg through p12:pg-hypotheses L113–129, with data/choice packages, Part 11b's torsion and Birkhoff form, Part 7's chart, and Part 6's reconstruction/geometry. The datum and (H1)–(H6) checks have separate supplying steps: sets/collar/positivity, joint analyticity on the closed cylinder, period, fast inverse, Birkhoff form, determinant and symmetry. Neither finite-order nonresonance nor torsion is inserted as a source premise of P-PLANAR. Positive finite physical measure uses the injective cell and Liouville, not injectivity of the full periodic chart. Both G1 and G2 below lie in this closure; hence FAIL despite the exact root statement.

### `bpP:p0:fixed` — FAIL

Source: `blueprint-P/parts/p0-conventions.tex#bpP:p0:fixed@L379-L388`. Frozen declaration: `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean`, `KAM.Planetary.fixedSunPlanetaryKAM`. Manifest identity: `planetary.fixedSunPlanetaryKAM.v1`, contract `planetary.fixedSunPlanetaryKAM@1`, ABI `a710d06469f0efa43a0eede7aa23e7e13216737ac0895ff11757e256903b2eec`. **Identity and statement comparison: PASS.** Original closure: 1127 nodes, 34 exposed source-gap records (including gaps on retained alternative routes).

**SOURCE_HYPOTHESES:** n >= 2; G, m_0 > 0; m, a: Fin n -> R with m_i > 0 and a_i > 0 for all i, and a_i < a_j whenever i < j (strictly ordered axes, no numerical separation); eta > 0

**SOURCE_QUANTIFIERS:** forall n, G, m_0, m, a, eta (data fixed first); exists eps_0, d, D; forall eps with 0 < eps < eps_0; exists S

**SOURCE_CONCLUSION:** there exist eps_0, d, D with 0 < eps_0 and 0 < d < D such that for every eps with 0 < eps < eps_0 there is S subset Ph_{n.2} with 0 < meas S < infinity and FixKol(G,m_0,m,a,eps,eta,d,D,S)

**CONSTANT_SCOPE:** eps_0, d, D depend on (n, G, m_0, m, a, eta) and not on eps; S depends on eps

Closure: p13:fixed L153–161 and its genuine dimension case split. The n=2 branch uses the frozen P-G with new constants for P_fix (p13:data, pg-hypotheses, n2), not the moving-Sun theorem's constants. The general branch uses p11:wrapper, whose kam-input is supplied by 11a-1 weak measure, 11a-2 cutoff/canonical step, 11a-3 iteration/selection, 11a-4 limit/family/displacement/evaluation and 11a-5 quantitative assembly/budget. The two cases are conjunctive case coverage, not alternative ROUTES of the n>=2 root. The zero-perturbation branch and the shared named gamma, admissible threshold and Delta in 11a-5 are retained. The fixedHamiltonian, IsFixedSolution and FixedKolmogorovSet anchors are reachable. The numerical budget lemmas do not assume an already chosen Hamiltonian. Both G1 and G2 below lie in this closure, including its physical chart preparation; hence FAIL.

### `bpP:p0:amd` — PASS

Source: `blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L499-L511`. Frozen declaration: `KAM/Frozen/Planetary/Theorems/AmdConfinement.lean`, `KAM.Planetary.amdConfinement`. Manifest identity: `planetary.d25.amdConfinement.v1`, contract `planetary.d25.amdConfinement@1`, ABI `a06de42f8f9b1500dacb7d6458a771df2ac692e555eb951cd1b7f779ec077122`. **Identity and statement comparison: PASS.** Original closure: 114 nodes, 0 exposed source-gap records (including gaps on retained alternative routes).

**SOURCE_HYPOTHESES:** n >= 2; B an admissible box; mu, T, delta > 0 with l_i + 2 delta < l^0_i and u^0_i + 2 delta < u_i for all i, and A_0 + 2 n delta < A_1; z_0 in LowAMD(m,l^0,u^0,A_0) with StoppedBound(B,mu,T,delta,z_0); G = m_0 = 1

**SOURCE_QUANTIFIERS:** forall n >= 2, B (admissible), mu, T, delta (hypotheses above), z_0 (with the stopped bound); exists z: R -> Ph_{2n}

**SOURCE_CONCLUSION:** there is z: R -> Ph_{2n} with z(0) = z_0 and (a) IsMovSolOn(m,mu,[-T,T],z) and MovUniqueOn(m,mu,[-T,T],z); (b) IsNewtonOn(mass_mu,[-T,T], t -> x(z(t)_1), t -> v(z(t)_2)) with the barycentric reconstructions for G = m_0 = 1; (c) for every t in [-T,T]: z(t) in LowAMD(m,l,u,A_1), J(z(t)) = J(z(0)), for all i: ¦e_i(z(t))¦ < e_*, d <= ¦q_i(t)¦ <= R, and PairBounds(d,2R; x(z(t)_1)); (d) for every t in [-T,T]: A(z(t)) <= A_0 + n delta and ¦Lambda_i(z(t)) - Lambda_i(z_0)¦ <= delta for all i

**CONSTANT_SCOPE:** order of choice: B, mu, T, delta, then z_0 with the stopped bound; z depends on all of them; no dynamical premise except the stopped bound; no constant is produced

Closure: p14:amd L129–153, the element/eccentricity/geometry/closure lemmas, smooth moving field, conservation of angular momentum, the stopped first-exit argument in both directions, compact continuation beyond both endpoints and Part 6 barycentric reconstruction. The stopped bound is the sole dynamical premise. The proof tests [0,s] and [-s,0], and continues strictly beyond +/-T to supply the frozen two-sided endpoint derivatives. No Nekhoroshev assumption is added to this helper.

### `bpP:p0:expsafe` — PASS

Source: `blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L513-L522`. Frozen declaration: `KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean`, `KAM.Planetary.planetaryExponentialSafety`. Manifest identity: `planetary.d25.planetaryExponentialSafety.v1`, contract `planetary.d25.planetaryExponentialSafety@1`, ABI `2e161e3b644712a64211734b4208c2425542c31bf0a43de3857c3cceb1a2a14a`. **Identity and statement comparison: PASS.** Original closure: 285 nodes, 1 exposed source-gap records (including gaps on retained alternative routes).

**SOURCE_HYPOTHESES:** n >= 2; B an admissible box; G = m_0 = 1

**SOURCE_QUANTIFIERS:** forall n >= 2, B (admissible); exists mu_*, c, C > 0; forall mu in (0,mu_*), forall z_0 in LowAMD(m,l^0,u^0,A_0); exists z: R -> Ph_{2n}

**SOURCE_CONCLUSION:** there are mu_*, c, C > 0 such that for every mu in (0,mu_*) and every z_0 in LowAMD(m,l^0,u^0,A_0) there is z: R -> Ph_{2n} with z(0) = z_0 such that, with T = exp(c mu^{-alpha_n}): (a) the clauses (a), (b), (c) of P-AMD-CONFINEMENT hold on [-T,T] (existence, uniqueness, Newton equations, outer region, conservation of J, eccentricity, radius, pair bounds); (b) ¦a_i(z(t)) - a_i(z_0)¦ <= C mu^{beta_n} for all ¦t¦ <= T and all i

**CONSTANT_SCOPE:** mu_*, c, C depend on (n, B) only (before mu and z_0); z depends on (mu, z_0); exponents alpha_n, beta_n of the D25 definition

Closure: p14:expsafe L295–311, p14:stopped and the AMD helper. The N-PARTIAL-CONVEX application at p14a L274–287 has suppliers for dimensions n and k=n, open convex enlarged action sets, open slow ball, closed-ball collar, complex C2/reality, the curried bilinear Hessian bound (a sum, not a matrix maximum), definite sign +/-h and frequency lower bound, normalized perturbation, the real Hamiltonian identity, solution lifting, and both fast/slow erosions. Coupling nu=B0 mu, time reversal through (-h,-P) and the exponents indexed by the planet count are explicit. Constants are chosen before mu,z0; p14a L302–310 translates the stopped action drift to the axis drift and T=exp(c mu^-alpha_n). The single inherited gap is p7:ho-hol, already exposed in the graph; it is not claimed discharged.

### `bpP:p14:sb-safety` — PASS

Source: `blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-safety@L72-L86`. Frozen declaration: `KAM/Frozen/Planetary/Theorems/SecularBoxSafety.lean`, `KAM.Planetary.secularBoxSafety`. Manifest identity: `planetary.d25.secularBoxSafety.v1`, contract `planetary.d25.secularBoxSafety@1`, ABI `960d1b58a1fd45c10d30e4632f8154000761c77ab20f9e86a576601bcb6d1f48`. **Identity and statement comparison: PASS.** Original closure: 108 nodes, 0 exposed source-gap records (including gaps on retained alternative routes).

**SOURCE_HYPOTHESES:** sigma in [29/100,31/100]; mu>0; w0 in Phase(2+2) with Box_sigma(w0); m=(1,sigma); H=H_sec^(m,mu)

**SOURCE_QUANTIFIERS:** sigma and mu in R; sigma in [29/100,31/100] and mu>0; w0 in Phase(2+2) with Box_sigma(w0); then exists w; then the universal U,v,t,F,i clauses in the stated order

**SOURCE_CONCLUSION:** exists w: R -> Phase(2+2) with (a) w(0)=w0 and IsHamiltonianSolutionOn H univ univ w; (b) for every open convex U in R with 0 in U and every v: R -> Phase(2+2) with v(0)=w0, IsHamiltonianSolutionOn H univ U v and Reg_{sigma,mu}(v(t)) for all t in U: v(t)=w(t) for all t in U; (c) for every t: Reg_{sigma,mu}(w(t)), fast((w(t))_2)=fast((w0)_2) (Lambda constant), AMD(w(t))=AMD(w0)<16373/2500000, ¦v_i(w(t))¦<3/20 for i=0,1, and for every F in R^2: 1751/400<=¦q_i(w(t);F_i)¦<=4439/400 (i=0,1); 399/200<=¦q_1(w(t);F_1)¦-¦q_0(w(t);F_0)¦; PairBounds(399/200,4439/200; barycentricPositions 1 m mu (z(w(t);F)_1))

**CONSTANT_SCOPE:** none: all numerical constants are literals; w depends on (sigma,mu,w0)

Closure: the explicit secular definitions and rational numerics, direct ellipse identities/covariance, S, smoothness and regularity, conservation of Lambda and AMD, bounded slow flow, explicit integration of the fast angles, global existence and regular-solution uniqueness, then steps sb-th-1 through sb-th-11. The rational radii and radial gap hold for every t and every F, and pair bounds use the bodyVector/ellipsePhase bridge, not an identification of coordinate orders by assertion. The proof never requires mu to be small. Part 7/8 comparisons declared as consistency checks are not input edges.

### `bpP:p14:sb-cited` — PASS

Source: `blueprint-P/parts/p14b-secular-box.tex#bpP:p14:sb-cited@L88-L92`. Frozen declaration: `KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean`, `KAM.Planetary.secularBoxAtCitedMasses`. Manifest identity: `planetary.d25.secularBoxAtCitedMasses.v1`, contract `planetary.d25.secularBoxAtCitedMasses@1`, ABI `a26520919c3c64c781c509be044346ee7ee4d428b76b1862aaa97ef59672a014`. **Identity and statement comparison: PASS.** Original closure: 110 nodes, 0 exposed source-gap records (including gaps on retained alternative routes).

**SOURCE_HYPOTHESES:** w0 in Phase(2+2) with Box_{476/1591}(w0)

**SOURCE_QUANTIFIERS:** forall w0 (hypothesis Box_{476/1591}(w0))

**SOURCE_CONCLUSION:** the conclusion of Theorem sb-safety with sigma=476/1591 and mu=4773/5000000 substituted everywhere: exists w ... (a),(b),(c) as in sb-safety for H=H_sec^((1,476/1591),4773/5000000)

**CONSTANT_SCOPE:** none: sigma and mu are the literals 476/1591 and 4773/5000000

Closure: sb-ci-1 L309–310 instantiates the preceding frozen root with sigma=476/1591 and mu=4773/5000000; the sigma interval and positivity are exact rational checks. The decimal-mass provenance at L311 is not used as a proof premise. All regularity, uniqueness, all-time and all-F clauses specialize together.

## Global findings — owning slice P-p8

### G1 — major: missing compact uniform-continuity input

Consumer: `stepP:p8:pa-unif`, packet P-p8.nodes.md L253 onward; assembled DEPGRAPH.md at the same NODE ID. Evidence: blueprint-P/parts/p8-secular-form.tex **L49**:

> “hence uniformly continuous on $[0,2\pi]^n\times\overline{\mathcal N(\rho_0/2)}$ (compact)”

This is the nontrivial uniformization that chooses one rho_* for every angle and pair of planets. The node's seven current prerequisites supply holomorphy, the circular lower bound, domains, and nonzero one-body positions. None supplies the stated compact uniform-continuity theorem. The admitted external `bpP:p12:f-unif` has precisely that contract (p12-planar-assembly.tex L25). Its use here is implicit but direct. A later-part locator is harmless: this is an external leaf, not an application of P-PLANAR, so adding it does not introduce a cycle. Do not turn uniform continuity into a new hypothesis and do not add a stronger root premise.

Add `bpP:p12:f-unif` to this consumer's DEPS and add:

```text
EDGE: bpP:p12:f-unif | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | Heine-Cantor on the compact angle cell times the closed complex polydisc supplies uniform continuity and one collision-free radius rho_* for all real angles and pairs
```

### G2 — major: missing fundamental-theorem-of-calculus input

Consumer: `stepP:p8:l64-b`, packet P-p8.nodes.md L676 onward. Evidence: blueprint-P/parts/p8-secular-form.tex **L102**:

> “$\int_0^{2\pi}\partial_{\lambda_i}q^{(i)}d\lambda_i=0$ (fundamental theorem of calculus)”

Its two current prerequisites give real analyticity/periodicity of q and the identity p=m nu partial_lambda q. Neither supplies the integral-of-a-derivative theorem used to conclude that the mean momentum vanishes. The admitted import `K:bp:p1:ext-integral` states exactly int_a^b phi'=phi(b)-phi(a), with its C1 hypothesis (blueprint/parts/p1-analysis.tex **L82–86**). Real analyticity on the compact interval supplies that hypothesis, and periodicity makes the boundary difference zero. This is a direct external input to the exact zero-average result, which then supplies the cross kinetic cancellation, the exact two-model secular identification and both planetary KAM closures. It must not be hidden in the earlier chart theorem or treated as a new hypothesis.

Add `K:bp:p1:ext-integral` to this consumer's DEPS and add:

```text
EDGE: K:bp:p1:ext-integral | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102 | the fundamental theorem of calculus integrates the C1 periodic position derivative to q(2 pi)-q(0)=0, giving zero mean momentum through p=m nu partial_lambda q
```

These EDGE lines are the exact proposed changes, each attached to its named consumer. Preserve every existing dependency and source field. They add two edges and no nodes or new external assumptions. The two modified nodes need independent delta review before their repaired records can be marked REVIEWED; this report does not silently apply or approve its own repairs. No other owning slice receives a requested record change.

## Global convention, package and application checks

The source/definition dictionary is consistent: phase positions precede momenta; fast blocks precede slow blocks; assemble(I,phi,p,q)=((phi,q),(I,p)); Poincare coordinates are ((lambda,xi),(Lambda,eta)). Max norms are analytic norms, while planeLength is the Euclidean planar length only in physical formulas. Part 1 performs the CP radian/period-one conversion, with the Hamiltonian/conformal factor as well as the frequency divided by 2 pi, and the Part 5 pipeline uses the unscaled period-one torus exactly once. Part 11's oscillator/polar/action rescalings preserve physical time through the conformal Hamiltonian identity. The existing period mismatch at Part 9 d-d is retained as a SOURCE_GAP, not silently corrected by these convention checks.

The weighted Fourier norm and geometric-width conversion in Parts 2–3 and 11 are recorded separately from sup-norm Cauchy estimates. The physical-to-chart statements preserve increasing axis order, general G,m0 in P-PLANAR/P-FIXED, and G=m0=1 in D25. Part 8's actual Q_h is half the pinned revised Fejer matrix; Parts 9, 10 and 11b use Omega=2 sigma with sigma the eigenvalues of this Q_h, and the quartic/torsion data use the frozen sqrt(2 Lambda) normalization. No graph repair is permitted to change those factors.

The package/#data records represent local data rather than global assumptions. In particular the Parts 2–3 averaging interface is downstream of Part 2's averaging theorem, not conversely; Part 5 supplies the numerical upper bounds before computing K and checks the two-scale theorem's hypotheses; Parts 12–13 split out P-G data/choice packages rather than a cycle through the full application. The Part 11a budget/threshold definitions distinguish numerical conditions from Hamiltonian assumptions, treat the positive-size iteration and zero case separately, and retain shared witnesses across (K1)–(K6). The N flow/Lie-transform imports retain their complex domains, small-field requirements and shrinkings. Known failures to discharge those requirements in Part 11b remain explicit gap nodes; a general real-flow theorem is not substituted for the imported small holomorphic flow statement.

Part 7's noncircular I inputs have separate circular and scaling components owned by P-xown; the circular alternatives are represented by two routes. The Part 6 collision/reconstruction requirements are supplied by the tube or low-AMD geometry where consumed, including arbitrary time sets in reconstruction. The fixed-Sun arbitrary-real-epsilon bridge remains exposed rather than extending the nonnegative section-data convention silently.

All six route nodes were checked as three genuine pairs: circular scaled/direct identities (Part 7), compact-root-continuity/local-analytic alternatives (Part 9), and physical assembly through orbit/reconstruction or the tube lemma (Part 12). They are in ROUTES of their own targets; their prerequisites are conjunctive inside each route. The Part 9 roots-continuity route retains its SOURCE_GAP; the supplied analytic alternative is separate. P-FIXED's dimension cases are not incorrectly encoded as alternatives.

## Pre-global cleanup and coverage/reachability

**Unreachable retained nodes: none. Uncovered retained nodes: none. New coverage omissions found: none.** G1–G2 concern missing proof-input edges of already represented steps, not missing source paragraphs. This does not certify proof closure.

The deleted physical-interface component at **11a-5 L116–135**, including its unused Picard-Lindelof uniqueness assertion, does not feed Part 11's wrapper: the wrapper consumes (K1)–(K6) of weak-kam-quantitative directly (p11 L249–252). Part 13's physical-interface mention at L200 is a forward-reference list, not an application. Deleting that unused component does not pay its old source gap, and does not remove the actually used limit/family/evaluation components.

The removed rank-compact/rc-reduce and chart-scaling components are not used to discharge the quantitative theorem: finite type/amount are its hypotheses, supplied in the planetary wrapper by Part 10 and the preparation/amount steps; no extra rank premise is smuggled into the frozen root. The consumers remark and divisor-wide requirement list are administrative; the retained finite-divisor/parameter-selection steps discharge the finite-stage invariant themselves. References to rank-compact inside the example parenthesis of D1, and the end-of-file consumer lists, do not constitute proof use.

`bpP:p7:same-chart` is cited only in the Deviations/provenance discussion (notably p14a L339); its actual shared-chart/splitting facts are supplied by product-chart and Part 6. `bpP:p4:beta-inverse` is not used as a real theorem at complex vectors: Part 5 L112 repeats the adjugate estimate for complex matrices and directly uses the admitted Cramer input. Part 4's N3 mentions it as an example of a supplier, while Part 5 supplies the actual L_beta used at the application. Neither exclusion conceals a missing real-to-complex application.

The seven removed K/N import leaves have no surviving consumer requiring their contracts. In particular the K quadratic iteration lemma is explicitly inapplicable to the geometric 11a recursion (p11a3 L58–66); references in external/provenance/consumer lists do not force restoration. The live import checker independently confirms zero unreferenced imports and zero missing referenced imports.

### Explicit verdict on the writer's new edge

**PASS:** `bpP:p14:sec-domain#chart-facts -> bpP:p7:d25` at **p14a L162**. This is an actual recall, not Part 14b's consistency-only comparison. Part 7's displayed d25 proposition is for n=2 (p7 L247–255), so it must not be substituted unconditionally at arbitrary n. The source explicitly states its componentwise extension (p7 L245), and p14a **L168** spells out the general-n proof: poincare(d),(e) in each product block. The consumer has direct product-chart, poincare, product-def, poincare-def, o-facts and element-definition dependencies, and its NOTE explicitly distinguishes this reduction from applying the n=2 theorem at arbitrary n. Thus the new d25 edge faithfully records the named recall while the already represented componentwise argument supplies the general-n contract. Keep this edge and its present use-site locator.

Part 14b's sb-ch-a comparison with d25(a), by contrast, remains correctly nondependent: p14b L43 expressly says those comparisons are consistency checks and the displayed algebra proves the identity directly. These two cross-part references have different uses and should not be normalized to the same edge policy.

## Existing SOURCE_GAP records

All 34 records below remain source-model obligations. Their presence is compatible with a topology PASS; their mathematical discharge is outside this review. None is converted to a source hypothesis, an external leaf or a proof-status claim here. The physical-interface uniqueness gap is absent because its entire unused component was excluded, not because uniqueness was proved.

| Node | Source locator |
|---|---|
| `bpP:p3:rem-norm` | `blueprint-P/parts/p3a-two-scale-iteration.tex#bpP:p3:rem-norm@L89-L93` |
| `bpP:p3:step` | `blueprint-P/parts/p3a-two-scale-iteration.tex#bpP:p3:step@L192-L226` |
| `bpP:p5:kam-cond#scales` | `blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L217` |
| `bpP:p6:reconstruction-fixed#real-eps` | `blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed#real-eps@L191-L191` |
| `bpP:p9:diagonalize` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L148-L153` |
| `stepP:p11:hc-mean` | `blueprint-P/parts/p11-cp09-preparation.tex#stepP:p11:hc-mean@L83-L83` |
| `stepP:p11:hc-rot` | `blueprint-P/parts/p11-cp09-preparation.tex#stepP:p11:hc-rot@L75-L75` |
| `stepP:p11a:cs-lip` | `blueprint-P/parts/p11a2-cutoff-step.tex#stepP:p11a:cs-lip@L287-L287` |
| `stepP:p11a:ps-lim` | `blueprint-P/parts/p11a3-iteration-selection.tex#stepP:p11a:ps-lim@L330-L330` |
| `stepP:p11a:rl-deriv` | `blueprint-P/parts/p11a2-cutoff-step.tex#stepP:p11a:rl-deriv@L239-L239` |
| `stepP:p11a:rl-global` | `blueprint-P/parts/p11a2-cutoff-step.tex#stepP:p11a:rl-global@L237-L237` |
| `stepP:p11b:bt-rot#lift` | `blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot#lift@L217-L217` |
| `stepP:p11b:fl-bd` | `blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-bd@L148-L148` |
| `stepP:p11b:li-tay` | `blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-tay@L161-L161` |
| `stepP:p11b:lm-prop` | `blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175` |
| `stepP:p1:hc-real-derivative` | `blueprint-P/parts/p1-hamiltonian-tools.tex#bpP:p1:hol-chart@L76-L76` |
| `stepP:p2:ob-der` | `blueprint-P/parts/p2-averaging.tex#stepP:p2:ob-der@L177-L177` |
| `stepP:p3:inv-conj` | `blueprint-P/parts/p3b-two-scale-limit.tex#stepP:p3:inv-conj@L132-L134` |
| `stepP:p3:inv-lim` | `blueprint-P/parts/p3b-two-scale-limit.tex#stepP:p3:inv-lim@L142-L143` |
| `stepP:p5:be-an` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-an@L59-L59` |
| `stepP:p5:be-coef` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-coef@L58-L58` |
| `stepP:p5:be-jet` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-jet@L60-L60` |
| `stepP:p5:bl-comp` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-comp@L93-L93` |
| `stepP:p5:bl-real` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-real@L92-L92` |
| `stepP:p5:ext-glue` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-glue@L34-L34` |
| `stepP:p5:ext-loc` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-loc@L33-L33` |
| `stepP:p5:fi-blk` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-blk@L128-L128` |
| `stepP:p5:fi-inv` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inv@L129-L129` |
| `stepP:p5:st-ivt` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311` |
| `stepP:p5:ur-schwarz` | `blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-schwarz@L73-L73` |
| `stepP:p7:ho-hol` | `blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173` |
| `stepP:p7:pc-share` | `blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207` |
| `stepP:p9:d-d` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152` |
| `stepP:p9:gs-c#roots-route` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183` |

The open inputs fall into explicit groups: the Part 2 target-width error; Part 3 monotonicity/domain/conjugation/real-limit assertions; the Part 5 unregistered complexification, integration, identity/Schwarz, compactness, block-inversion, growth and measure-continuity inputs; the fixed-Sun real-epsilon extension; Part 7 local derivative restriction/analyticity; Part 9 period conversion and one continuity-of-roots alternative; Part 11 reverse complexification/Schwarz; Part 11a nonlinear real-flow/variational, reality-guard and continuous-limit bridges; and Part 11b existence/uniform-data, real-vs-complex Lie/symplectic applicability and analytic eigenvector lifting. The graph distinguishes asserted bridges from actual applicable imported contracts.

## Suspected blueprint defects and source limitations

No new pinned-paper erratum is asserted: pinned papers are provenance outside this source-graph review. G1–G2 are graph omissions; the blueprint itself names the correct elementary arguments. The following already-exposed blueprint problems remain material to future proof work:

- **p2-averaging.tex L177:** the angular estimate uses `e(S_0-S)` although the displayed lemma assumes only `S-sigma<S_0`. That denominator need not be positive; the target-width bound used later is different. This is the existing ob-der gap.
- **p3a-two-scale-iteration.tex L91:** “decreasing” the slow bound is said to increase both rhohat and Ehat while L is unchanged. With Ehat=E L/rhohat^2, increasing rhohat decreases Ehat. The recorded gap preserves the defective sentence separately from the usable normalization.
- **p3a L184–185 / L202–204:** the larger-domain displacement assertion is written for Psi_+, while its definition is only the restriction to the smaller new domain; the argument establishes the estimate for Psi. The graph correctly exposes the domain/name mismatch.
- **p7-kepler-poincare.tex L207:** “the proof” of p6:domain is invoked for real analyticity, although that earlier statement/proof supplies smoothness through smooth square-root/reciprocal facts. The missing analytic regularity argument remains pc-share's gap.
- **p9-secular-spectrum.tex L143/L152:** the period-one torus transport is invoked with only the radian lattice calculation. The required conversion is not supplied there; both the parent and d-d record the same unpaid bridge.
- **p11a2-cutoff-step.tex L248/L287:** reality of R is optional in the canonical-step setting, but the real-flow Lipschitz clause/application lacks the necessary reality guard. The graph retains cs-lip's source gap rather than strengthening the theorem.
- **p11b-planar-torsion.tex L161/L175:** the cited N Lie/symplectic theorems have small holomorphic-flow hypotheses, which the real analytic compact-parameter construction does not supply. Those exact applicability gaps remain represented.

These observations do not authorize editing the blueprint or frozen files. The existing source-gap notes retain the exact additional local evidence and limitations.

## Report and proposed-repair validation

A read-only in-memory copy of the assembled database was given exactly the two proposed DEPS/EDGE additions. Running the same parser/analyzer gates on that string returned only the two original unset GLOBAL_REVIEWER/GLOBAL_REVIEW_REF diagnostics; there were no new shape, identity, locator, cycle, coverage, review or reachability diagnostics. The proposed graph has **6,073 edges** and no added nodes. This validates the shape of the proposed repair, not its independent delta approval; the on-disk graph was not changed.

Report checks passed: seven root verdicts; seven occurrences of each of the four reconstructed source fields; 34 source-gap table rows; two fenced EDGE additions; no control characters. `git diff --check -- docs/graph/P/reviews/GLOBAL-review.md` exited 0. The report is untracked, so that diff command alone does not inspect its contents; the explicit report checks cover its generated text. Final read-only git status shows the same two pre-existing untracked assembled graph files and the newly written GLOBAL-review.md, with no tracked-file changes.

## Unresolved questions and closeout

**Unresolved adjudication:** accept or reject the two P-p8 input-edge additions G1–G2, then obtain fresh delta review of the modified records and reassemble/recheck. No new mathematical premise, frozen-statement revision, external-boundary expansion or owner ruling is requested. The existing 34 mathematical/source-input obligations remain open as listed.

The writer must separately fill the global-review identity/reference and run the publication/dashboard gates after adjudication. Since this report is FAIL, it must not be recorded as global acceptance of the current graph. No lint_sources.sh, Lean build or #print axioms is run: this brief expressly forbids Lean and restricts the task to a Markdown source-graph review.
