# Writer spec for slice W-w1a (blueprint-W/parts/w1-sequences.tex L1-L590). Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w1-sequences.tex"

EXT = dict(H="none (Mathlib-level external fact)", Q="as stated in the item", S="none", deps=[])

NODES = {
    "bpW:w1:transport": dict(
        H="typing data: a, p in R; K in {R, C}; a >= 0 for l^{a,p}_K", Q="a, p, K",
        C="defines omega_{a,p}(j) = j^p e^{aj} > 0 (frozen ellWeight a p j), l^2_K = l^2(N_+;K), "
          "tau_{a,p} : l^{a,p}_K -> l^2_K, (tau w)_j = omega_{a,p}(j) w_j, kappa_{a,p} : l^2_K -> l^{a,p}_K, "
          "(kappa y)_j = y_j/omega_{a,p}(j); y represents w = kappa y (weighted coordinates); a map A : l^{a,p} -> "
          "l^{a',p'} is represented by hat A = tau_{a',p'} o A o kappa_{a,p}", S="none",
        deps=[("bpW:w0:ellap#ellWeight", "L31", "omega_{a,p}(j) is the frozen ellWeight a p j"),
              ("bpW:w0:ellap#coeff", "L33", "the spaces l^{a,p}_K of Definition bpW:w0:ellap; kappa_{1,1} is the "
               "frozen coeff (realization table L51)")]),
    "bpW:w1:ext-lp": dict(EXT, C="l^2(iota;K) is a Hilbert space for every index type (lp.instInnerProductSpace, "
        "lp.completeSpace) with <f,g> = sum conj(f_i) g_i; ¦f_i¦ <= ||f||; membership and norm bounds follow from bounds "
        "on finite partial sums; f = sum_i f_i e_i, e_i = lp.single 2 i 1"),
    "bpW:w1:ext-series": dict(EXT, C="sum_{k>=1} k^{-2} = pi^2/6; sum_{k>=1} k^{-sigma} < infinity for sigma > 1; "
        "Tonelli for nonnegative double series and Fubini for absolutely summable ones"),
    "bpW:w1:ext-analytic": dict(EXT, C="a continuous multilinear map is analytic (a continuous polynomial) everywhere; "
        "continuous linear and bilinear maps are analytic; compositions and pairs of analytic maps are analytic; a "
        "continuous bilinear map applied to two analytic maps is analytic; C-analytic maps are R-analytic; analytic "
        "maps are Frechet differentiable"),
    "bpW:w1:ext-onevar": dict(EXT, C="for a complete complex normed space F: the Cauchy estimate (phi continuous on "
        "the closed disc of radius R > 0, holomorphic inside, ||phi|| <= B on the circle implies ||phi'(c)|| <= B/R); "
        "the Cauchy integral formula (valid for complete F; K's bp:p1:ext-cauchy, provenance), in particular the "
        "formula for phi'(c); continuous linear maps commute with Bochner integrals; the norm is attained by norm-one "
        "functionals; holomorphic maps on open subsets of C are analytic; a locally uniform limit of holomorphic maps "
        "on an open subset of C is holomorphic"),
    "bpW:w1:ext-unifderiv": dict(EXT, C="if f_k -> f pointwise on an open set U of a normed space over K, each f_k is "
        "differentiable on U and Df_k -> g uniformly on U, then f is differentiable on U with Df = g; the mean value "
        "inequality on convex sets (K's bp:p1:ext-mvt, provenance)"),
    "bpW:w1:ext-integral": dict(EXT, C="Bochner integrals of continuous maps of a compact interval or box into a "
        "complete space; ||int F|| <= int ||F||; differentiation under the integral sign with a dominating bound on "
        "the derivative (a.e.-strongly measurable integrand and derivative, measurability from continuity); dominated "
        "convergence (K's bp:p1:ext-integral, provenance)"),
    "bpW:w1:ext-ode": dict(EXT, C="Picard-Lindelof existence and uniqueness for Lipschitz fields in a Banach space; "
        "Gronwall's inequality"),
    "bpW:w1:ext-fourier": dict(EXT, C="the characters e^{inx}, n in Z, form a Hilbert basis of L^2 of R/2piZ with "
        "normalized Haar measure, and e^{2 pi i k.x}, k in Z^n, one of L^2(R^n/Z^n); Parseval; continuous periodic "
        "functions with absolutely summable coefficients are the sums of their Fourier series (K's bp:p1:ext-fourier, "
        "provenance)"),
    "bpW:w1:space": dict(
        H="a >= 0, p in R, K in {R, C}", Q="for all a >= 0, p",
        C="(i) tau_{a,p}, kappa_{a,p} are mutually inverse K-linear bijections, ||tau w||_{l^2} = ||w||_{a,p}; l^{a,p}_K "
          "with <w,w'>_{a,p} = sum omega^2 conj(w_j) w'_j is a Hilbert space isometric to l^2_K, complete and separable; "
          "(ii) ¦(kappa y)_j¦ <= ||y||/omega_{a,p}(j) and y -> (kappa y)_j is the continuous linear functional "
          "omega^{-1} ev_j; (iii) ||y - P_N y|| -> 0 for the truncations P_N; (iv) for K = R, a = p = 1, kappa_{1,1} is "
          "the frozen coeff, and WaveSpace = l^2_R x l^2_R with its product (max) norm is isometric to E_{1,1} with "
          "||(q,p)||_E = max(||q||_{1,1}, ||p||_{1,1}) via kappa_{1,1} x kappa_{1,1}", S="none",
        deps=[("bpW:w1:transport", "L125", "tau, kappa and the weights"),
              ("stepW:w1:iso", "L139", "proof step"), ("stepW:w1:sep", "L144", "proof step"),
              ("stepW:w1:coord", "L148", "proof step"), ("stepW:w1:frozen", "L151", "proof step")]),
    "stepW:w1:iso": dict(
        H="a >= 0, p", Q="w in l^{a,p}_K", C="||tau w||^2 = ||w||_{a,p}^2; tau, kappa are mutually inverse; the inner "
        "product and completeness transport from l^2", S="none",
        deps=[("bpW:w1:transport", "L140", "tau, kappa, omega"),
              ("bpW:w0:ellap#ellWeight", "L140", "the norm of Definition bpW:w0:ellap"),
              ("bpW:w1:ext-lp", "L143", "inner product and completeness of l^2")]),
    "stepW:w1:sep": dict(
        H="(iii) of the lemma", Q="none", C="finitely supported sequences with rational (Gaussian rational) entries "
        "form a countable dense set, so l^{a,p}_K is separable (not consumed by later milestones)", S="none",
        deps=[("stepW:w1:coord", "L146", "density by the truncation statement (iii)")]),
    "stepW:w1:coord": dict(
        H="y in l^2_K", Q="j, N", C="(ii) ¦(kappa y)_j¦ <= ||y||/omega(j); (iii) ||y - P_N y||^2 = sum_{j>N} ¦y_j¦^2 -> 0",
        S="none", deps=[("bpW:w1:ext-lp", "L149", "¦y_j¦ <= ||y||"),
                        ("bpW:w1:transport", "L149", "kappa divides by omega(j)")]),
    "stepW:w1:frozen": dict(
        H="K = R, a = p = 1", Q="y, j", C="coeff y j = y_j/omega_{1,1}(j) by the frozen definition, and Mathlib's "
        "product norm is the max norm, giving (iv)", S="none",
        deps=[("bpW:w0:ellap#coeff", "L152", "unfolds the frozen coeff"),
              ("bpW:w0:ellap#WaveSpace", "L153", "the frozen WaveSpace with the product (max) norm")]),
    "bpW:w1:coordinatewise": dict(
        H="c : R -> l^2_K differentiable at t; weights (a,p), (a',p') with a >= a', p >= p'; iota the inclusion of "
          "Lemma bpW:w1:embed, represented by hat iota; v in l^2_K",
        Q="for all such c, t, v",
        C="(a) for every j, t -> (kappa_{a,p} c(t))_j has derivative (kappa_{a',p'} v)_j at t iff (b) hat iota c'(t) = "
          "v; in particular for differentiable K : R^2 -> WaveSpace and X^w of Proposition bpW:w1:hamfield(v), the "
          "frozen conclusion (4) of KAM.Wave.nlw2 at (I,theta) (the HasDerivAt of t -> coeff (K(theta + t nu)).i j at "
          "0) is equivalent to hat iota(DK(theta) nu) = X^w(K(theta)), hat iota representing E_{1,1} subset E_{1,0}",
        S="none",
        note="The statement speaks of the *form* of the frozen conclusion (4) of nlw2; that is not a use of the root "
             "(no edge to bpW:wh:nlw2, which would create a cycle once W8 is added).",
        deps=[("bpW:w1:embed", "L160", "the inclusion iota and its representative"),
              ("bpW:w1:hamfield", "L165", "the field X^w of (v)"),
              ("bpW:w0:ellap#coeff", "L165", "the coefficients coeff in the frozen conclusion (4)"),
              ("stepW:w1:coordder", "L171", "proof step"), ("stepW:w1:coordcomp", "L175", "proof step")]),
    "stepW:w1:coordder": dict(
        H="c differentiable at t", Q="j", C="the coordinate curve t -> (kappa_{a,p} c(t))_j has derivative "
        "(kappa_{a,p} c'(t))_j = (kappa_{a',p'} hat iota c'(t))_j", S="none",
        deps=[("bpW:w1:space", "L172", "(ii): the coordinate is a continuous linear functional"),
              ("bpW:w1:embed", "L174", "(iii): the inclusion does not change coefficients")]),
    "stepW:w1:coordcomp": dict(
        H="Step stepW:w1:coordder", Q="j", C="(a) iff (b) by injectivity of kappa_{a',p'}; for the frozen statement, "
        "c(t) = K(theta + t nu) componentwise at t = 0 with (a,p) = (1,1), (a',p') = (1,0), compared with "
        "Proposition bpW:w1:hamfield(v)", S="none",
        deps=[("stepW:w1:coordder", "L176", "the derivative of the coordinates"),
              ("bpW:w1:space", "L177", "injectivity of kappa ((i))"),
              ("bpW:w1:hamfield", "L179", "(v): the coordinates of X^w are the right sides of (4)")]),
    "bpW:w1:multiplier": dict(
        H="mu : N_+ -> K and M >= 0 with ¦mu_j¦ <= M for all j", Q="for all mu, M",
        C="D_mu y = (mu_j y_j) is bounded linear on l^2_K with ||D_mu|| <= M and ||D_mu|| >= ¦mu_j¦ for every j; a "
          "diagonal map w -> (m_j w_j) from l^{a,p}_K to l^{a',p'}_K has representative D_mu with mu_j = "
          "m_j omega_{a',p'}(j)/omega_{a,p}(j); it is bounded with norm <= M when ¦mu_j¦ <= M, and unbounded if (mu_j) "
          "is unbounded", S="none",
        deps=[("bpW:w1:ext-lp", "L193", "norm bounds from finite partial sums"),
              ("bpW:w1:transport", "L194", "the representative tau o (m .) o kappa")]),
    "bpW:w1:embed": dict(
        H="a >= a' >= 0, p, p' in R", Q="for all such weights; w",
        C="(i) if p >= p', l^{a,p}_K subset l^{a',p'}_K with ||w||_{a',p'} <= ||w||_{a,p}, representative D_mu, mu_j = "
          "j^{p'-p} e^{(a'-a)j} in (0,1]; (ii) if a > a' and sigma = p' - p > 0, ||w||_{a',p'} <= "
          "(sigma/(e(a-a')))^sigma ||w||_{a,p}; (iii) the inclusions do not change coefficients (kappa_{a',p'} D_mu = "
          "kappa_{a,p}), are injective and compose", S="none",
        deps=[("bpW:w1:multiplier", "L210", "m_j = 1, mu_j = omega_{a',p'}(j)/omega_{a,p}(j)"),
              ("bpW:w1:transport", "L213", "the identity mu_j/omega_{a',p'}(j) = 1/omega_{a,p}(j)")]),
    "bpW:w1:diag": dict(
        H="a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j)", Q="for all a, p, r; t, s in R",
        C="(i) lambda^r is bounded l^{a,p+r}_K -> l^{a,p}_K, norm (1+m)^{r/2} for r >= 0 (attained at j = 1), at most 1 "
          "for r < 0, representative D_mu with mu_j = (lambda_j/j)^r, an isomorphism with inverse lambda^{-r}; (ii) for "
          "r > 0 it is not bounded l^{a,p} -> l^{a,p}; (iii) R_t z = (e^{-i lambda_j t} z_j) is a linear isometry of "
          "l^{a,p}_C, R_{t+s} = R_t R_s, t -> R_t z continuous; (iv) the real linear flow L_t(q,p) = (cos(lambda t)q + "
          "sin(lambda t)p, -sin(lambda t)q + cos(lambda t)p) preserves ||q||^2 + ||p||^2, ||L_t(q,p)||_E <= sqrt2 "
          "||(q,p)||_E, L_{t+s} = L_t L_s, every coordinate solves dq_j = lambda_j p_j, dp_j = -lambda_j q_j, and in the "
          "coordinates z of Definition bpW:w0:z, L_t is R_t", S="none",
        deps=[("bpW:w0:basis#lam", "L218", "the multiplier lambda^r"),
              ("bpW:w0:z", "L230", "the complex coordinates z"),
              ("stepW:w1:ratio", "L235", "proof step"), ("stepW:w1:rot", "L240", "proof step"),
              ("stepW:w1:realflow", "L244", "proof step")]),
    "stepW:w1:ratio": dict(
        H="r in R", Q="j", C="mu_j = (lambda_j/j)^r with 1 < lambda_j/j <= sqrt(1+m), equality at j = 1; so ¦mu_j¦ <= "
        "(1+m)^{r/2} = mu_1 (r >= 0), ¦mu_j¦ <= 1 (r < 0); the inverse is the same with -r", S="none",
        deps=[("bpW:w1:multiplier", "L236", "the representative and its norm"),
              ("bpW:w0:basis#lambda-facts", "L237", "j < lambda_j"),
              ("bpW:w0:mass", "L237", "lambda_j^2 = j^2 + m <= (1+m) j^2")]),
    "stepW:w1:rot": dict(
        H="t, s in R; z in l^{a,p}_C", Q="t, s", C="(ii) lambda_j^r -> infinity; (iii) R_t = D_mu with ¦mu_j¦ = 1 is an "
        "isometry, group law coordinatewise, and t -> R_t z continuous by dominated convergence for series", S="none",
        deps=[("bpW:w1:multiplier", "L241", "R_t is a multiplier D_mu with ¦mu_j¦ = 1"),
              ("bpW:w1:ext-series", "L243", "dominated convergence for series (Tonelli/Fubini for series)")]),
    "stepW:w1:realflow": dict(
        H="(q,p) in E_{a,p}", Q="t", C="coordinatewise rotation: q_j(t)^2 + p_j(t)^2 = q_j^2 + p_j^2, hence the norm "
        "identity and max(||q(t)||,||p(t)||)^2 <= ||q||^2 + ||p||^2 <= 2||(q,p)||_E^2; derivatives and group law by "
        "trigonometry; z_j(t) = e^{-i lambda_j t} z_j", S="none",
        deps=[("bpW:w0:z", "L248", "z_j = (q_j + i p_j)/sqrt 2")]),
    "bpW:w1:linfty": dict(
        H="typing data: p in R; Pi subset R^2; L >= 0", Q="p, Pi, L",
        C="defines l^p_infty (real sequences with ¦w¦_p = sup_j ¦w_j¦ j^p < infinity, realized as lp infinity by "
          "w -> (j^p w_j)) and L-Lipschitz maps Pi -> l^p_infty (max norm on R^2); P96-K's Lipschitz semi-norm is the "
          "least such L", S="none", deps=[]),
    "bpW:w1:tails": dict(
        H="b = (1/lambda_1, 1/lambda_2); Omega_j(xi) = lambda_j + (3/(2 pi lambda_j))<b,xi> (j >= 3, xi in R^2); "
          "bar Omega_j = j; tilde Omega_j = Omega_j - bar Omega_j",
        Q="for all xi, zeta in R^2; i, j >= 3",
        C="¦tilde Omega(xi)¦_1 <= m/2 + (3/(2pi))¦<b,xi>¦ and ¦tilde Omega(xi) - tilde Omega(zeta)¦_1 <= (3/(2pi))"
          "(1/lambda_1 + 1/lambda_2)¦xi - zeta¦; so P96-K Assumption B holds with d = 1, delta = -1, and p - bar p <= "
          "delta holds with equality for bar p = p + 1; ¦Omega_i(xi) - Omega_j(xi) - (i-j)¦ <= (m + (3/pi)¦<b,xi>¦)/"
          "min(i,j)", S="none",
        deps=[("bpW:w0n:AB", "L266", "Omega = lambda_N + B xi with the corrected B"),
              ("bpW:w1:linfty", "L268", "the norm ¦.¦_1 of l^1_infty and the Lipschitz condition"),
              ("bpW:w0:basis#lambda-facts", "L276", "lambda_j - j = m/(lambda_j + j) in (0, m/(2j)]; lambda_j > j")]),
    "bpW:w1:twosided-transport": dict(
        H="typing data: a >= 0, s in R", Q="a, s",
        C="defines omega^b_{a,s}(l) = <l>^s e^{a¦l¦} and the realization of l^{a,s}_b as lp (Int -> C) 2 via "
          "c -> (omega^b(l) c_l) (an isometry as in Lemma bpW:w1:space); (c*d)_l = sum_i c_i d_{l-i} when "
          "sum_i ¦c_i¦¦d_{l-i}¦ < infinity for all l", S="none",
        deps=[("bpW:w0:twosided", "L290", "the space l^{a,s}_b and the convolution"),
              ("bpW:w1:space", "L291", "the isometry argument")]),
    "bpW:w1:twosided": dict(
        H="a >= 0, p in R", Q="for all a, p; q; X; z, zbar",
        C="(i) (E^+- q)_l = (+-1)^{[l<0]} q_¦l¦/sqrt(lambda_¦l¦) (l != 0), 0 at l = 0, is linear l^{a,p}_C -> "
          "l^{a,p+1/2}_b with norm <= sqrt2 ||q||_{a,p}, also for the majorant ¦E^+ q¦; the even x_l = ¦q_¦l¦¦/sqrt(¦l¦) "
          "has ||x||_{a,p+1/2}^2 = 2||q||_{a,p}^2; (ii) for X in l^{a,p+1/2}_b, (X_l/sqrt(lambda_l))_{l>=1} lies in "
          "l^{a,p+1}_C with norm <= (sum_{l>=1} l^{2p+1} e^{2al} ¦X_l¦^2)^{1/2} <= ||X||_{a,p+1/2}, and <= "
          "||X||/sqrt2 if ¦X¦ is even; (iii) J(z,zbar) (z on j >= 1, zbar on -j, 0 at 0) is a linear isometry from "
          "l^{a,p}_C x l^{a,p}_C with (||z||^2 + ||zbar||^2)^{1/2} onto {w in l^{a,p}_b : w_0 = 0}, "
          "||J(z,zbar)|| <= sqrt2 max(||z||,||zbar||)", S="none",
        deps=[("bpW:w1:twosided-transport", "L302", "the two-sided weights"),
              ("bpW:w0:basis#lam", "L300", "the factor 1/sqrt(lambda_¦l¦)"),
              ("stepW:w1:ext", "L316", "proof step"), ("stepW:w1:restr", "L320", "proof step"),
              ("stepW:w1:pair", "L323", "proof step")]),
    "stepW:w1:ext": dict(
        H="q in l^{a,p}_C", Q="q", C="||E^+- q||^2 = 2 sum j^{2p+1} e^{2aj} ¦q_j¦^2/lambda_j <= 2||q||^2; the majorant "
        "has the same norm; with sqrt(¦l¦) the factor j/lambda_j becomes 1", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L318", "j/lambda_j < 1"),
              ("stepW:w0n:majorant", "L319", "this is the majorant step of W0")]),
    "stepW:w1:restr": dict(
        H="X in l^{a,p+1/2}_b", Q="X", C="sum_{l>=1} l^{2p+2} e^{2al} ¦X_l¦^2/lambda_l <= sum_{l>=1} l^{2p+1} e^{2al} "
        "¦X_l¦^2; for even ¦X¦ at most half the full sum", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L321", "l/lambda_l < 1"),
              ("stepW:w0n:smoothing", "L322", "this is the smoothing step of W0")]),
    "stepW:w1:pair": dict(
        H="z, zbar in l^{a,p}_C", Q="z, zbar", C="||J(z,zbar)||^2 = sum_{j>=1} omega_{a,p}(j)^2 (¦z_j¦^2 + ¦zbar_j¦^2) "
        "since <+-j> = j", S="none",
        deps=[("bpW:w1:twosided-transport", "L324", "the two-sided weight <l>")]),
    "bpW:w1:young": dict(
        H="(i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in "
          "l^{0,s}_b with s > 1/2; complex c, d", Q="for all such sequences",
        C="(i) each sum_i ¦X_i¦¦Y_{l-i}¦ converges and ||X*Y||_{l^2} <= ||X||_{l^2} ||Y||_{l^1}; (ii) sum_l <l>^{-2s} = "
          "1 + 2 zeta(2s) < infinity and ||Y||_{l^1} <= (1+2zeta(2s))^{1/2} ||Y||_{0,s} <= (1+2zeta(2s))^{1/2} "
          "||Y||_{a,s}; (iii) convolution of nonnegative sequences is commutative, associative and monotone; ¦c*d¦ <= "
          "¦c¦*¦d¦ pointwise", S="none",
        deps=[("bpW:w1:twosided-transport", "L333", "the norms ||.||_{a,s} and the convolution"),
              ("stepW:w1:cs", "L342", "proof step"), ("stepW:w1:youngsum", "L346", "proof step"),
              ("stepW:w1:l1", "L349", "proof step"), ("stepW:w1:rules", "L353", "proof step")]),
    "stepW:w1:cs": dict(
        H="X in l^2, Y in l^1", Q="l", C="(sum_i ¦X_i¦¦Y_{l-i}¦)^2 <= ||Y||_1 sum_i ¦X_i¦^2 ¦Y_{l-i}¦, finite", S="none",
        deps=[]),
    "stepW:w1:youngsum": dict(
        H="Step stepW:w1:cs", Q="none", C="sum_l ¦(X*Y)_l¦^2 <= ||Y||_1^2 ||X||_2^2", S="none",
        deps=[("stepW:w1:cs", "L348", "sums the pointwise bound over l"),
              ("bpW:w1:ext-series", "L347", "exchange of the nonnegative double sum (Tonelli)")]),
    "stepW:w1:l1": dict(
        H="s > 1/2, a >= 0", Q="Y", C="sum_l <l>^{-2s} = 1 + 2 sum_{l>=1} l^{-2s} < infinity and ||Y||_1 <= "
        "(1+2zeta(2s))^{1/2} ||Y||_{0,s} <= (1+2zeta(2s))^{1/2} ||Y||_{a,s}", S="none",
        deps=[("bpW:w1:ext-series", "L350", "sum k^{-sigma} < infinity for sigma = 2s > 1")]),
    "stepW:w1:rules": dict(
        H="sequences in l^1 cap l^2 by (ii)", Q="X, Y, Z", C="absolute convergence of the double series allows "
        "rearrangement (associativity); commutativity by i -> l - i; monotonicity and ¦c*d¦ <= ¦c¦*¦d¦ termwise",
        S="none",
        deps=[("stepW:w1:l1", "L354", "(ii) puts the sequences in l^1 cap l^2"),
              ("bpW:w1:ext-series", "L355", "Fubini for absolutely summable double series")]),
    "bpW:w1:algebra": dict(
        H="a >= 0, s >= 1, c, d (, e) in l^{a,s}_b", Q="for all such a, s, c, d, e",
        C="||c*d||_{a,s} <= K_s ||c|| ||d|| with K_s = 2^s(1+2zeta(2s))^{1/2}, and ||c*d*e||_{a,s} <= K_s^2 ||c|| ||d|| ||e||",
        S="K_s depends only on s",
        deps=[("bpW:w0n:algebra", "L366", "the two-factor bound is Lemma bpW:w0n:algebra"),
              ("bpW:w1:young", "L367", "(iii): associativity for the three-factor form")]),
    "bpW:w1:selection": dict(
        H="a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps "
          "[l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\\0)^4 -> C with the same bound in "
          "¦ijkl¦, w, w', w'' in l^{a,p}_b",
        Q="for all such a, p, M, c and arguments",
        C="(a) T_c(q,q',q'')_l = sum c_ijkl q_i q'_j q''_k converge absolutely and ||T_c||_{a,p+1} <= 2 M K_s^2 prod "
          "||q||_{a,p}; (b) T_c(w,w',w'')_l (l != 0) converge absolutely, T_c(.)_0 = 0, ||T_c||_{a,p+1} <= 64 M K_s^2 "
          "prod ||w||_{a,p}; T_c is trilinear, symmetric if c is symmetric in its first three indices",
        S="the bounds depend only on M and s (through K_s)",
        deps=[("stepW:w1:maj1", "L403", "proof step"), ("stepW:w1:sel1", "L406", "proof step"),
              ("stepW:w1:smooth1", "L412", "proof step"), ("stepW:w1:maj2", "L415", "proof step"),
              ("stepW:w1:sel2", "L419", "proof step"), ("stepW:w1:smooth2", "L423", "proof step")]),
    "stepW:w1:maj1": dict(
        H="(a); x_i = ¦q_¦i¦¦/sqrt(¦i¦), x_0 = 0", Q="q, q', q''", C="x is even with ||x||_{a,s} = sqrt2 ||q||_{a,p}",
        S="none", deps=[("bpW:w1:twosided", "L405", "(i): the even sequence x")]),
    "stepW:w1:sel1": dict(
        H="(a); the majorants of Step stepW:w1:maj1", Q="l >= 1",
        C="sum_{i,j,k} ¦c_ijkl q_i q'_j q''_k¦ <= M l^{-1/2} X_l with X = x*x'*x'', finite and even", S="none",
        deps=[("stepW:w1:maj1", "L408", "the even majorants"),
              ("stepW:w0n:selection", "L410", "the injectivity argument of the W0 selection step"),
              ("bpW:w1:young", "L410", "X is finite (Young, l^1 control)"),
              ("bpW:w1:algebra", "L411", "X lies in l^{a,s}_b")]),
    "stepW:w1:smooth1": dict(
        H="(a); X of Step stepW:w1:sel1", Q="none", C="||T_c||_{a,p+1}^2 <= (M^2/2) ||X||_{a,s}^2 and ||X||_{a,s} <= "
        "K_s^2 ||x|| ||x'|| ||x''|| = 2^{3/2} K_s^2 prod ||q||; hence ||T_c|| <= 2 M K_s^2 prod ||q||", S="none",
        deps=[("stepW:w1:sel1", "L413", "the pointwise bound by M l^{-1/2} X_l"),
              ("bpW:w1:algebra", "L414", "three-factor algebra bound"),
              ("stepW:w1:maj1", "L414", "||x|| = sqrt2 ||q||")]),
    "stepW:w1:maj2": dict(
        H="(b); tilde x_i = (¦w_i¦ + ¦w_{-i}¦)/sqrt(¦i¦), tilde x_0 = 0", Q="w, w', w''",
        C="tilde x is even with ||tilde x||_{a,s}^2 <= 4 ||w||_{a,p}^2", S="none",
        deps=[("bpW:w1:twosided-transport", "L417", "the two-sided weights")]),
    "stepW:w1:sel2": dict(
        H="(b); the majorants of Step stepW:w1:maj2", Q="l != 0",
        C="each of the eight eps-terms is at most (tilde x*tilde x'*tilde x'')_l =: tilde X_l, so ¦T_c(w,w',w'')_l¦ <= "
          "8 M ¦l¦^{-1/2} tilde X_l", S="none",
        deps=[("stepW:w1:maj2", "L421", "¦w_i¦/sqrt(¦i¦) <= tilde x_{i'}")]),
    "stepW:w1:smooth2": dict(
        H="(b); tilde X of Step stepW:w1:sel2", Q="none", C="||T_c||_{a,p+1}^2 <= 64 M^2 ||tilde X||_{a,s}^2, "
        "||tilde X|| <= 8 K_s^2 prod ||w||, so ||T_c|| <= 64 M K_s^2 prod ||w||; trilinearity and symmetry termwise",
        S="none",
        deps=[("stepW:w1:sel2", "L424", "the pointwise bound"),
              ("bpW:w1:algebra", "L425", "three-factor algebra bound"),
              ("stepW:w1:maj2", "L425", "||tilde x|| <= 2 ||w||")]),
    "bpW:w1:trilinear": dict(
        H="a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) "
          "y in l^2_R, l >= 1 (and a > 0 for the general case)",
        Q="for all such a, p, K",
        C="(i) there is a unique continuous symmetric K-trilinear map T^{a,p}_K : (l^2_K)^3 -> l^2_K with "
          "kappa_{a,p+1} T^{a,p}_K(y,y',y'') = T(kappa y, kappa y', kappa y'') (T of Theorem bpW:w0n:cubic-bound) and "
          "||T^{a,p}_K|| <= C_*; (ii) T_C(iota y, ...) = iota T_R(y, ...) and conj(T_C(z,z',z'')) = T_C(conj z, ...); "
          "(iii) T^{a',p'}(hat iota y, ...) = hat iota' T^{a,p}(y, ...); (iv) cubicGrad m hm y l = "
          "T^{1,1}_R(y,y,y)_l/omega_{1,2}(l), i.e. G_q(kappa_{1,1} y) = kappa_{1,2} T^{1,1}_R(y,y,y); for a > 0, "
          "p >= 1/2 likewise G_q(kappa_{a,p} y) = kappa_{a,p+1} T^{a,p}_R(y,y,y)",
        S="C_* depends only on p",
        deps=[("bpW:w1:transport", "L437", "kappa, omega"),
              ("bpW:w1:complexification", "L439", "iota and conjugation"),
              ("bpW:w0:Gq#cubicGrad", "L446", "the frozen cubicGrad in (iv)"),
              ("stepW:w1:tricoord", "L453", "proof step"), ("stepW:w1:tricont", "L459", "proof step"),
              ("stepW:w1:trireal", "L463", "proof step"), ("stepW:w1:trifrozen", "L467", "proof step")]),
    "stepW:w1:tricoord": dict(
        H="y, y', y'' in l^2_K; q = kappa_{a,p} y etc.", Q="y, y', y''",
        C="each T(q,q',q'')_l is an absolutely convergent tsum over N_+^3, T(q,q',q'') in l^{a,p+1}_K with norm <= C_* "
          "prod ||y||; define T(y,y',y'') = tau_{a,p+1} T(q,q',q'')", S="C_* depends only on p",
        routes=[("stepW:w1:tricoord#via-cubic-bound", "L454", "first derivation: Theorem bpW:w0n:cubic-bound"),
                ("stepW:w1:tricoord#via-selection", "L455", "equivalent derivation: Lemma bpW:w1:selection(a)")],
        deps=[("bpW:w1:transport", "L458", "tau_{a,p+1} and the weighted coordinates")]),
    "stepW:w1:tricoord#via-cubic-bound": dict(
        new=True, kind="route", title="Coordinates of the trilinear map via Theorem bpW:w0n:cubic-bound",
        stmt=f"{F}#stepW:w1:tricoord@L454-L458", proof=f"{F}#stepW:w1:tricoord@L454-L454",
        route_for="stepW:w1:tricoord",
        H="as in Step stepW:w1:tricoord", Q="y, y', y''", C="the conclusion of Step stepW:w1:tricoord", S="C_* depends only on p",
        deps=[("bpW:w0n:cubic-bound", "L454", "absolute convergence and the bound C_*")]),
    "stepW:w1:tricoord#via-selection": dict(
        new=True, kind="route", title="Coordinates of the trilinear map via Lemma bpW:w1:selection(a)",
        stmt=f"{F}#stepW:w1:tricoord@L454-L458", proof=f"{F}#stepW:w1:tricoord@L455-L456",
        route_for="stepW:w1:tricoord",
        H="as in Step stepW:w1:tricoord", Q="y, y', y''", C="the conclusion of Step stepW:w1:tricoord", S="C_* depends only on p",
        note="\"equivalently Lemma bpW:w1:selection(a) with c_ijkl = g_ijkl (lambda lambda lambda lambda)^{-1/2}, "
             "M = 1/(2pi)\": the text offers it as a sufficient alternative to cubic-bound.",
        deps=[("bpW:w1:selection", "L455", "(a) with M = 1/(2pi)"),
              ("bpW:w0n:quartic-coeff", "L456", "the bound after (bpW:w0n:g-signed) gives the hypothesis on c"),
              ("bpW:w0:basis#lambda-facts", "L456", "lambda >= j gives the (ijkl)^{-1/2} decay")]),
    "stepW:w1:tricont": dict(
        H="Step stepW:w1:tricoord", Q="none", C="trilinear and symmetric termwise; continuous with norm <= C_* "
        "(MultilinearMap.mkContinuous); unique since kappa_{a,p+1} is injective", S="C_* depends only on p",
        deps=[("stepW:w1:tricoord", "L461", "the bound C_* prod ||y||"),
              ("bpW:w0n:quartic-coeff", "L460", "symmetry of g"),
              ("bpW:w1:space", "L462", "kappa is injective ((i))")]),
    "stepW:w1:trireal": dict(
        H="Step stepW:w1:tricoord", Q="none", C="(ii) real coefficients commute with iota and conjugation; (iii) both "
        "sides have coefficients T(q,q',q'')", S="none",
        deps=[("bpW:w1:complexification", "L465", "iota and conjugation"),
              ("bpW:w1:embed", "L466", "(iii): inclusions do not change coefficients")]),
    "stepW:w1:trifrozen": dict(
        H="y in l^2_R, a = p = 1 (or a > 0)", Q="y, l",
        C="reconU m hm y = U_m(kappa_{1,1} y) (absolutely convergent tsum), the interval integral is that of "
          "Definition bpW:w0:Gq, so cubicGrad m hm y l = G_q(kappa_{1,1} y)_l = T(q,q,q)_l", S="none",
        deps=[("bpW:w0:reconstruction#reconU", "L468", "unfolds the frozen reconU"),
              ("bpW:w0n:recon-bounded", "L469", "the tsum converges absolutely"),
              ("bpW:w0:Gq#cubicGrad", "L470", "unfolds the frozen cubicGrad"),
              ("bpW:w0n:gradient", "L471", "G_q(q)_l = T(q,q,q)_l for a > 0"),
              ("bpW:w0:ellap#coeff", "L468", "kappa_{1,1} = coeff")]),
    "bpW:w1:cubic-analytic": dict(
        H="a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y)", Q="for all y, y', h, k",
        C="(i) N is K-analytic on l^2_K, ||N(y)|| <= C_* ||y||^3; (ii) DN(y)h = 3T(y,y,h), D^2N(y)(h,k) = 6T(y,h,k), "
          "D^3N = 6T, ||DN(y)|| <= 3C_*||y||^2, ||D^2N(y)|| <= 6C_*||y||; (iii) ||N(y) - N(y')|| <= 3C_* ||y-y'|| "
          "max(||y||,||y'||)^2; (iv) G^w(y)_l = omega_{1,2}(l) cubicGrad m hm y l is N for (a,p) = (1,1), K = R, real "
          "analytic with ||G^w(y)|| <= C_m ||y||^3, C_m = 8(1+2zeta(3))/pi; G_q(kappa_{1,1} y) has weighted "
          "coordinates G^w(y) at (1,2), (l^{-1} G^w(y)_l) at (1,1), (l^{-2} G^w(y)_l) at (1,0)",
        S="C_* depends only on p; C_m independent of m",
        deps=[("bpW:w1:trilinear", "L476", "T and C_*"),
              ("bpW:w0:Gq#cubicGrad", "L484", "the frozen cubicGrad in (iv)"),
              ("stepW:w1:can", "L492", "proof step"), ("stepW:w1:cder", "L494", "proof step"),
              ("stepW:w1:clip", "L499", "proof step"), ("stepW:w1:cfrozen", "L502", "proof step")]),
    "stepW:w1:can": dict(
        H="T continuous trilinear", Q="none", C="N = T o Delta, Delta(y) = (y,y,y) continuous linear, is analytic",
        S="none", deps=[("bpW:w1:ext-analytic", "L493", "continuous multilinear maps and compositions are analytic")]),
    "stepW:w1:cder": dict(
        H="T symmetric trilinear with ||T|| <= C_*", Q="y, h", C="DN(y)h = 3T(y,y,h), the higher derivatives likewise, "
        "with the stated bounds", S="none",
        deps=[("bpW:w1:trilinear", "L496", "symmetry and the bound C_* ((i))")]),
    "stepW:w1:clip": dict(
        H="T trilinear", Q="y, y'", C="N(y) - N(y') = T(y-y',y,y) + T(y',y-y',y) + T(y',y',y-y'), so the Lipschitz bound "
        "3C_* ||y-y'|| max^2", S="none",
        deps=[("bpW:w1:trilinear", "L501", "the bound C_*")]),
    "stepW:w1:cfrozen": dict(
        H="(a,p) = (1,1), K = R", Q="y, l", C="(iv) from Theorem bpW:w1:trilinear(iv), omega_{1,1}/omega_{1,2} = l^{-1}, "
        "omega_{1,0}/omega_{1,2} = l^{-2}, and C_* = K_{3/2}^2/pi = C_m", S="C_m independent of m",
        deps=[("bpW:w1:trilinear", "L503", "(iv) frozen identification"),
              ("bpW:w0n:cubic-bound", "L504", "C_m = K_{3/2}^2/pi"),
              ("bpW:w1:transport", "L503", "the weight ratios")]),
    "bpW:w1:gradient-identity": dict(
        H="a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), "
          "absolutely convergent for u in l^{a,p+1}, v in l^{a,p}",
        Q="for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)",
        C="(i) G(q) = (1/4)<G_q(q),q>_0 = (1/4) Q(q,q,q,q), Q(q_1,..,q_4) = <T(q_1,q_2,q_3),q_4>_0 symmetric continuous "
          "4-linear with ¦Q¦ <= C_* prod ||q_i||; (ii) G is real analytic on l^{a,p} and DG(q)h = <G_q(q),h>_0; (iii) "
          "G_q(q) is not the Riesz gradient of G for l^{a,p} (that is (omega^{-2} G_q(q)_j)); in frozen coordinates, "
          "G^w(y) = G(kappa_{1,1} y), DG^w(y)h = sum_j cubicGrad m hm y j . coeff h j and nabla^{l^2} G^w(y) = "
          "(G^w(y)_j/(omega_{1,1}(j) omega_{1,2}(j)))_j", S="C_* depends only on p",
        deps=[("bpW:w0:H", "L510", "G(q) = (1/4) int U_m(q)^4"),
              ("bpW:w0n:cubic-bound", "L515", "the trilinear map T"),
              ("bpW:w0:Gq#cubicGrad", "L519", "frozen cubicGrad in (iii)"),
              ("bpW:w0:ellap#coeff", "L519", "frozen coeff in (iii)"),
              ("stepW:w1:quartic", "L525", "proof step"), ("stepW:w1:gradder", "L531", "proof step"),
              ("stepW:w1:gradw", "L535", "proof step")]),
    "stepW:w1:quartic": dict(
        H="q in l^{a,p}, a > 0", Q="q_1, ..., q_4", C="G(q) = (1/4) sum_l q_l T(q,q,q)_l; Q is well defined, symmetric, "
        "and ¦Q¦ <= C_* prod ||q_i||", S="C_* depends only on p",
        deps=[("bpW:w0n:gradient", "L526", "G as an absolutely convergent quartic sum"),
              ("bpW:w0n:quartic-coeff", "L528", "symmetry of g"),
              ("bpW:w1:embed", "L529", "||u||_{0,0} <= ||u||_{a,p+1}, ||v||_{0,0} <= ||v||_{a,p}"),
              ("bpW:w0n:cubic-bound", "L530", "the bound on T")]),
    "stepW:w1:gradder": dict(
        H="Step stepW:w1:quartic", Q="q, h", C="G = (1/4) Q o (q -> (q,q,q,q)) is analytic and DG(q)h = Q(q,q,q,h) = "
        "<T(q,q,q),h>_0 = <G_q(q),h>_0", S="none",
        deps=[("stepW:w1:quartic", "L532", "the quartic form Q"),
              ("bpW:w1:ext-analytic", "L532", "continuous multilinear maps are analytic"),
              ("bpW:w1:trilinear", "L534", "(iv): T(q,q,q) = G_q(q)")]),
    "stepW:w1:gradw": dict(
        H="Step stepW:w1:gradder", Q="y, h", C="the Riesz gradient is (omega^{-2} G_q(q)_j); in frozen coordinates "
        "DG^w(y)h and nabla^{l^2} G^w(y) as stated", S="none",
        deps=[("stepW:w1:gradder", "L536", "DG(q)h = <G_q(q),h>_0"),
              ("bpW:w1:cubic-analytic", "L538", "(iv): G^w and the weighted coordinates of G_q(kappa y)")]),
    "bpW:w1:hamfield": dict(
        H="a > 0, p >= 1/2", Q="for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j",
        C="(i) X_Lambda(q,p) = (lambda p, -lambda q) is bounded E_{a,p} -> E_{a,p-1} with norm <= sqrt(1+m), not bounded "
          "E_{a,p} -> E_{a,p}; (ii) X_G(q,p) = (0, -G_q(q)) is real analytic E_{a,p} -> E_{a,p+1}, ||X_G|| <= C_* "
          "||q||^3, with the bounds of Corollary bpW:w1:cubic-analytic; its complex extension is C-analytic "
          "E^C_{a,p} -> E^C_{a,p+1}; (iii) X_H = X_Lambda + X_G is real analytic E_{a,p} -> E_{a,p-1}; (iv) H = "
          "Lambda + G is real analytic on E_{a,p}, DH(q,p)(0,e_j) = lambda_j p_j, DH(q,p)(e_j,0) = lambda_j q_j + "
          "G_q(q)_j, i.e. X_H = (d_p H, -d_q H), the system (bpW:w0:coeffsys); (v) for a = p = 1, with D = D_mu, "
          "mu_j = lambda_j/j, S = D_{(1/j)}, X^w(y,y') = (D y', -D y - S^2 G^w(y)) on WaveSpace represents X_H : "
          "E_{1,1} -> E_{1,0}, is real analytic on WaveSpace, and has j-th coordinates omega_{1,0}(j)(lambda_j coeff y' "
          "j, -lambda_j coeff y j - cubicGrad m hm y j)", S="C_* depends only on p",
        deps=[("bpW:w0:H", "L553", "H = Lambda + G"),
              ("bpW:w0:eqmotion", "L555", "the system (bpW:w0:coeffsys)"),
              ("bpW:w1:cubic-analytic", "L550", "the bounds of the cubic gradient"),
              ("bpW:w0:ellap#WaveSpace", "L557", "X^w : WaveSpace -> WaveSpace"),
              ("bpW:w0:ellap#coeff", "L560", "the coordinates in terms of coeff"),
              ("bpW:w0:Gq#cubicGrad", "L560", "the coordinates in terms of cubicGrad"),
              ("stepW:w1:hlin", "L566", "proof step"), ("stepW:w1:hnonlin", "L568", "proof step"),
              ("stepW:w1:hsum", "L571", "proof step"), ("stepW:w1:hham", "L574", "proof step"),
              ("stepW:w1:hfrozen", "L581", "proof step")]),
    "stepW:w1:hlin": dict(
        H="a > 0, p", Q="none", C="(i) from Lemma bpW:w1:diag(i)-(ii) with r = 1 componentwise; the max norm is "
        "preserved under componentwise bounds", S="none",
        deps=[("bpW:w1:diag", "L567", "(i)-(ii) with r = 1")]),
    "stepW:w1:hnonlin": dict(
        H="a > 0, p >= 1/2", Q="none", C="(ii) from Corollary bpW:w1:cubic-analytic and Theorem bpW:w1:trilinear(iv) in "
        "the second component, composed with the projection (q,p) -> q; complex version from (ii) of the theorem",
        S="none",
        deps=[("bpW:w1:cubic-analytic", "L569", "analyticity and bounds of N"),
              ("bpW:w1:trilinear", "L569", "(iv) identification with G_q and (ii) complex version")]),
    "stepW:w1:hsum": dict(
        H="(i), (ii)", Q="none", C="X_G maps into E_{a,p+1} subset E_{a,p-1}; a bounded linear plus an analytic map is "
        "analytic, giving (iii)", S="none",
        deps=[("bpW:w1:embed", "L572", "E_{a,p+1} subset E_{a,p-1}"),
              ("stepW:w1:hlin", "L573", "X_Lambda bounded linear"),
              ("stepW:w1:hnonlin", "L573", "X_G analytic"),
              ("bpW:w1:ext-analytic", "L573", "sums of analytic maps")]),
    "stepW:w1:hham": dict(
        H="a > 0, p >= 1/2", Q="(q,p), j", C="Lambda is the diagonal of beta(q,q') = sum lambda_j q_j q'_j with "
        "¦beta¦ <= sqrt(1+m) ||q|| ||q'||, a bounded quadratic form on E_{a,p}; DLambda(q,p)(h,k) = <lambda q,h>_0 + "
        "<lambda p,k>_0; with Proposition bpW:w1:gradient-identity(ii), evaluation at (e_j,0), (0,e_j) gives (iv)",
        S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L576", "lambda_j <= sqrt(1+m) j"),
              ("bpW:w1:embed", "L577", "||q||_{0,1/2} <= ||q||_{a,p} for p >= 1/2"),
              ("bpW:w1:gradient-identity", "L579", "(ii): DG(q)h = <G_q(q),h>_0")]),
    "stepW:w1:hfrozen": dict(
        H="a = p = 1", Q="y, y', j", C="the coordinates of X_H(kappa y, kappa y') times omega_{1,0}(j) = e^j are "
        "(lambda_j/j) y'_j and -(lambda_j/j) y_j - j^{-2} G^w(y)_j; D, S bounded, so X^w is a polynomial map on "
        "WaveSpace, analytic", S="none",
        deps=[("bpW:w1:cubic-analytic", "L583", "(iv): e^j cubicGrad_j = j^{-2} G^w(y)_j"),
              ("bpW:w1:multiplier", "L584", "D and S are bounded"),
              ("bpW:w0:basis#lambda-facts", "L584", "lambda_j/j <= sqrt(1+m)"),
              ("bpW:w1:ext-analytic", "L585", "polynomial maps are analytic")]),
}

DELETE = ["bpW:w1:algebra-half"]

COV = {
    "bpW:w1:algebra-half": ("EXCLUDED", "administrative remark (the algebra for 1/2 < s < 1 is not part of the plan; "
                            "no later milestone needs it)"),
    "w1-sequences:prose-L3-L15": ("EXCLUDED", "introduction and outline (standing assumption pointer; what W1 "
                                  "supplies; pointer to Remark bpW:w1:operator-fourier)"),
    "w1-sequences:prose-L17-L26": ("EXCLUDED", "route paragraph (outline)"),
    "w1-sequences:prose-L43-L44": ("EXCLUDED", "realization table heading (notation)"),
    "w1-sequences:prose-L46-L58": ("EXCLUDED", "realization table of Lean carriers (notation); the facts used are "
                                   "stated in Definition bpW:w1:transport and Lemma bpW:w1:space"),
    "w1-sequences:prose-L60-L64": ("EXCLUDED", "Lean notation (non-frozen helper coeffW, distinct name)"),
    "w1-sequences:prose-L68-L71": ("EXCLUDED", "introduction of the external list; the track-K externals it names "
                                   "(bp:p1:ext-*) are cited inside W's own ext items as provenance (SPEC)"),
    "w1-sequences:prose-L117-L118": ("EXCLUDED", "layout"),
    "w1-sequences:prose-L381-L384": ("EXCLUDED", "pointer (motivation of Lemma bpW:w1:selection)"),
}

STEP_CONTEXT = True
SYMBOL_EDGES = True

COV["stepW:w1:tricoord"] = ("NODE stepW:w1:tricoord, stepW:w1:tricoord#via-cubic-bound, stepW:w1:tricoord#via-selection",
                            "the step and its two alternative derivations (route nodes)")
