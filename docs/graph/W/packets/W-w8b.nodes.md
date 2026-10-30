NODE: bpW:w8:patch
KIND: definition
TITLE: The patched family
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L413-L420
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:patch
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; the shell iteration and its parameter sets Gamma_n
SOURCE_QUANTIFIERS: I in R^2, theta in R^2
SOURCE_CONCLUSION: defines Gamma = union_n Gamma_n, n(I) = the unique n with I in R_n for I in (0,t_0)^2, nu(I) = nu^(n(I))_*(I) on Gamma and 0 otherwise, K_I(theta) = K^(n(I))_I(theta) on Gamma and 0 otherwise; with r_0, C, tau, eta of Definition bpW:w8:const these are the witnesses of nlw2
CONSTANT_SCOPE: depend on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-iter, bpW:w7:shell-geom, bpW:w8:Kshell, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L414-L414 | Gamma_n, nu^(n)_*
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L415-L415 | (i) unique n(I)
EDGE: bpW:w8:Kshell | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L417-L417 | K^(n)_I
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L418-L418 | r_0, C, tau, eta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:patch-local
KIND: lemma
TITLE: Locality of the patching
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L424-L428
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L429-L434
CONTRACT_ID: bpW:w8:patch-local
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the patched family (Definition bpW:w8:patch); O_n = Pi_n
SOURCE_QUANTIFIERS: n, I in Gamma_n
SOURCE_CONCLUSION: the O_n are open and pairwise disjoint, Gamma_n subset O_n and Gamma cap O_n = Gamma_n; for I in Gamma_n, n(I) = n, nu(I) = nu^(n)_*(I) and K_I = K^(n)_I; so nu = nu^(n)_* on Gamma cap O_n and K = K^(.) on (Gamma cap O_n) x R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch, stepW:w8:pl-dis, stepW:w8:pl-id
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L425-L425 | the patched family
EDGE: stepW:w8:pl-dis | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L430-L430 | proof step
EDGE: stepW:w8:pl-id | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L432-L432 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:pl-dis
KIND: step
TITLE: Disjointness
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L431
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L431
CONTRACT_ID: stepW:w8:pl-dis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:patch-local: the patched family (Definition bpW:w8:patch); O_n = Pi_n
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:patch-local (n, I in Gamma_n); within the step: n, n'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: O_n pairwise disjoint and Gamma_n subset O_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w7:shell-geom, bpW:w8:shell-iter
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L430 | (ii) O_n subset R_n
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L431-L431 | (i) disjoint shells
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L431-L431 | Pi_* subset Pi_{-1} = Pi_n minus Xi
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:pl-id
KIND: step
TITLE: Identification
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L432-L433
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L432-L433
CONTRACT_ID: stepW:w8:pl-id
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:patch-local: the patched family (Definition bpW:w8:patch); O_n = Pi_n
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:patch-local (n, I in Gamma_n); within the step: I; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Gamma cap O_n = Gamma_n and the definitions unfold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:pl-dis, bpW:w8:patch
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:pl-dis | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L432-L432 | disjointness
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L433-L433 | n(I), nu, K
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:patch-cont
KIND: lemma
TITLE: Regularity of the patched family
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L447-L450
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L451-L460
CONTRACT_ID: bpW:w8:patch-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the patched family
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Gamma is Borel, Gamma subset {I : (forall i, 0 < I_i) and r(I) < r_0}, nu is continuous on Gamma, and (I,theta) -> K_I(theta) is continuous on Gamma x R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch, bpW:w8#data, stepW:w8:pc-borel, stepW:w8:pc-incl, stepW:w8:pc-nu, stepW:w8:pc-K
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L448-L448 | Gamma, nu, K
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L448-L448 | r(I)
EDGE: stepW:w8:pc-borel | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L452-L452 | proof step
EDGE: stepW:w8:pc-incl | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L453-L453 | proof step
EDGE: stepW:w8:pc-nu | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L455-L455 | proof step
EDGE: stepW:w8:pc-K | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L457-L457 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:pc-borel
KIND: step
TITLE: Borel
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452
CONTRACT_ID: stepW:w8:pc-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:patch-cont: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:patch-cont (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Gamma is Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell, bpW:w7:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452 | (iv) Gamma_n Borel
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452 | countable unions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:pc-incl
KIND: step
TITLE: Inclusion
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L454
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L454
CONTRACT_ID: stepW:w8:pc-incl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:patch-cont: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:patch-cont (none); within the step: I; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the inclusion
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w8:shells, bpW:w8:const, stepW:w8:pl-dis
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L453 | (ii) Gamma_n subset (0,t_n)^2
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L453 | t_n <= t_0
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L453 | r_0^2 = 2 t_0
EDGE: stepW:w8:pl-dis | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L453 | Gamma_n subset Pi_n
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:pc-nu
KIND: step
TITLE: Continuity of $\nu$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L455-L456
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L455-L456
CONTRACT_ID: stepW:w8:pc-nu
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:patch-cont: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:patch-cont (none); within the step: I; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: nu continuous on Gamma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-local, bpW:w8:freq-shell, bpW:w8:ext-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L455-L455 | nu = nu^(n)_* on Gamma cap O_n
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L456-L456 | (iv)
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L456-L456 | local continuity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:pc-K
KIND: step
TITLE: Continuity of $K$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L457-L459
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L457-L459
CONTRACT_ID: stepW:w8:pc-K
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:patch-cont: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:patch-cont (none); within the step: I, theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K continuous on Gamma x R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-local, bpW:w8:shell-inv, bpW:w8:ext-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L458-L458 | K = K^(.) on (Gamma cap O_n) x R^2
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L459-L459 | (ii)
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L459-L459 | local continuity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:unique
KIND: lemma
TITLE: Uniqueness for the coefficient system
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L465-L467
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L468-L487
CONTRACT_ID: bpW:w8:unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Y, Y' : R -> WaveSpace analytic coefficient solutions (Definition bpW:w2:coeffsol) with Y(0) = Y'(0)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Y = Y'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, stepW:w8:u-raw, stepW:w8:u-reg, stepW:w8:u-energy, stepW:w8:u-ineq, stepW:w8:u-gron, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L466-L466 | analytic coefficient solutions
EDGE: stepW:w8:u-raw | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L470-L470 | proof step
EDGE: stepW:w8:u-reg | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L474-L474 | proof step
EDGE: stepW:w8:u-energy | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L475-L475 | proof step
EDGE: stepW:w8:u-ineq | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L481-L481 | proof step
EDGE: stepW:w8:u-gron | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L484-L484 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L473-L473 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L469-L469 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L466-L466 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:u-raw
KIND: step
TITLE: Raw equations
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L473
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L473
CONTRACT_ID: stepW:w8:u-raw
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:unique: Y, Y' : R -> WaveSpace analytic coefficient solutions (Definition bpW:w2:coeffsol) with Y(0) = Y'(0)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:unique (none); within the step: t, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: g(y)_j = omega_j cubicGrad m hm y j maps l^2_R to l^2_R with ¦¦g(y) - g(y')¦¦ <= 3 C_m ¦¦y - y'¦¦ max(¦¦y¦¦,¦¦y'¦¦)^2; Y_1, Y_2 differentiable into l^2_R with (Y_1')_j = lambda_j (Y_2)_j and (Y_2')_j = -lambda_j (Y_1)_j - g(Y_1)_j; likewise for Y'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cubic-analytic, bpW:w2:curve-deriv, bpW:w0:ellap#ellWeight, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L470 | (iii), (iv)
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L472-L472 | differentiability into l^2
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L469-L469 | omega_{1,1}(j) = ellWeight 1 1 j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L473-L473 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L470 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:u-reg
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474
CONTRACT_ID: stepW:w8:u-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:unique: Y, Y' : R -> WaveSpace analytic coefficient solutions (Definition bpW:w2:coeffsol) with Y(0) = Y'(0)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:unique (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (lambda_j (Y_2)_j), (lambda_j (Y_1)_j) in l^2_R, and for Y'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:u-raw, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:u-raw | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474 | the raw equations
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:u-energy
KIND: step
TITLE: Energy identity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L480
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L480
CONTRACT_ID: stepW:w8:u-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:unique: Y, Y' : R -> WaveSpace analytic coefficient solutions (Definition bpW:w2:coeffsol) with Y(0) = Y'(0)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:unique (none); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f = ¦¦D_1¦¦^2 + ¦¦D_2¦¦^2 is differentiable with f' = -2<D_2, g(Y_1) - g(Y_1')>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-inner, stepW:w8:u-raw, stepW:w8:u-reg, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-inner | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L475 | inner products along curves
EDGE: stepW:w8:u-raw | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L476-L476 | derivatives
EDGE: stepW:w8:u-reg | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L479-L479 | absolute convergence
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L477-L477 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:u-ineq
KIND: step
TITLE: Differential inequality
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L481-L483
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L481-L483
CONTRACT_ID: stepW:w8:u-ineq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:unique: Y, Y' : R -> WaveSpace analytic coefficient solutions (Definition bpW:w2:coeffsol) with Y(0) = Y'(0)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:unique (none); within the step: T > 0, t in [-T,T]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦f'¦ <= L f on [-T,T] with L = 3 C_m R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-compact, stepW:w8:u-energy, stepW:w8:u-raw, bpW:w8:ext-inner
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-compact | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L482-L482 | boundedness on compacts
EDGE: stepW:w8:u-energy | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L483-L483 | f'
EDGE: stepW:w8:u-raw | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L482-L482 | Lipschitz bound of g
EDGE: bpW:w8:ext-inner | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L482-L482 | Cauchy-Schwarz
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:u-gron
KIND: step
TITLE: Gronwall
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L484-L486
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L484-L486
CONTRACT_ID: stepW:w8:u-gron
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:unique: Y, Y' : R -> WaveSpace analytic coefficient solutions (Definition bpW:w2:coeffsol) with Y(0) = Y'(0)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:unique (none); within the step: T; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f = 0, hence Y = Y'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-mono, stepW:w8:u-ineq
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-mono | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L485-L485 | monotonicity from the sign of the derivative
EDGE: stepW:w8:u-ineq | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L484-L484 | the inequality
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:winding
KIND: lemma
TITLE: Winding
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L491-L494
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L495-L500
CONTRACT_ID: bpW:w8:winding
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, a' : R -> (0,infinity) and phi, phi' : R -> R continuous, nu_0, nu_0' in R, phi(t) - t nu_0 and phi'(t) - t nu_0' bounded, a(t) e^{-2 pi i phi(t)} = a'(t) e^{-2 pi i phi'(t)} for all t
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: nu_0 = nu_0'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:w-mod, stepW:w8:w-const, stepW:w8:w-rate
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:w-mod | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L496-L496 | proof step
EDGE: stepW:w8:w-const | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L498-L498 | proof step
EDGE: stepW:w8:w-rate | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L499-L499 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:w-mod
KIND: step
TITLE: Moduli and phases
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L496-L497
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L496-L497
CONTRACT_ID: stepW:w8:w-mod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:winding: a, a' : R -> (0,infinity) and phi, phi' : R -> R continuous, nu_0, nu_0' in R, phi(t) - t nu_0 and phi'(t) - t nu_0' bounded, a(t) e^{-2 pi i phi(t)} = a'(t) e^{-2 pi i phi'(t)} for all t
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:winding (none); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: a = a' and phi(t) - phi'(t) in Z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-exp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L497-L497 | e^z = 1 iff z in 2 pi i Z
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:w-const
KIND: step
TITLE: Constant
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498
CONTRACT_ID: stepW:w8:w-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:winding: a, a' : R -> (0,infinity) and phi, phi' : R -> R continuous, nu_0, nu_0' in R, phi(t) - t nu_0 and phi'(t) - t nu_0' bounded, a(t) e^{-2 pi i phi(t)} = a'(t) e^{-2 pi i phi'(t)} for all t
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:winding (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi - phi' is a constant c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-exp, stepW:w8:w-mod
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498 | continuous integer-valued functions
EDGE: stepW:w8:w-mod | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498 | integer valued
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:w-rate
KIND: step
TITLE: Rates
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499
CONTRACT_ID: stepW:w8:w-rate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:winding: a, a' : R -> (0,infinity) and phi, phi' : R -> R continuous, nu_0, nu_0' in R, phi(t) - t nu_0 and phi'(t) - t nu_0' bounded, a(t) e^{-2 pi i phi(t)} = a'(t) e^{-2 pi i phi'(t)} for all t
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:winding (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: nu_0 = nu_0'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-exp, stepW:w8:w-const
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499 | bounded t c forces c = 0
EDGE: stepW:w8:w-const | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499 | the constant c
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:nu-injective
KIND: lemma
TITLE: The frequency map is injective on $\Gamma$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L503-L505
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L506-L514
CONTRACT_ID: bpW:w8:nu-injective
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the patched family
SOURCE_QUANTIFIERS: I, I' in Gamma
SOURCE_CONCLUSION: nu(I) = nu(I') implies I = I'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch, bpW:w8:patch-local, stepW:w8:ni-same, stepW:w8:ni-diff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L504-L504 | Gamma, nu
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L507-L507 | 2 pi nu = omega^(n)_* on Gamma_n
EDGE: stepW:w8:ni-same | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L508-L508 | proof step
EDGE: stepW:w8:ni-diff | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L509-L509 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:ni-same
KIND: step
TITLE: Same shell
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508
CONTRACT_ID: stepW:w8:ni-same
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nu-injective: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nu-injective (I, I' in Gamma); within the step: n = n'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: I = I'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508 | (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:ni-diff
KIND: step
TITLE: Different shells
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513
CONTRACT_ID: stepW:w8:ni-diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nu-injective: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nu-injective (I, I' in Gamma); within the step: n != n'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: omega^(n)_*(I) != omega^(n')_*(I')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w7:freqcoords, bpW:w8:freq-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | (ii) separation
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | (iv)
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L511-L511 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:injective
KIND: proposition
TITLE: Family injectivity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L517-L520
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L521-L538
CONTRACT_ID: bpW:w8:injective
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the patched family
SOURCE_QUANTIFIERS: I, I' in Gamma, theta, theta' in R^2
SOURCE_CONCLUSION: K_I(theta) = K_{I'}(theta') implies I = I' and theta - theta' in Z^2 (clause (6) of nlw2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch, bpW:w8:torus-shape, stepW:w8:in-orbit, stepW:w8:in-birk, stepW:w8:in-freq, stepW:w8:in-act, stepW:w8:in-ang, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L518-L518 | Gamma, K
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L523-L523 | X, y
EDGE: stepW:w8:in-orbit | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L524-L524 | proof step
EDGE: stepW:w8:in-birk | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L528-L528 | proof step
EDGE: stepW:w8:in-freq | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L531-L531 | proof step
EDGE: stepW:w8:in-act | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L535-L535 | proof step
EDGE: stepW:w8:in-ang | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L536-L536 | proof step
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L536-L536 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:in-orbit
KIND: step
TITLE: Orbits
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L527
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L527
CONTRACT_ID: stepW:w8:in-orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y(t) = K_I(theta + t nu) and Y'(t) = K_{I'}(theta' + t nu') coincide
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-embedding, bpW:w8:shell-inv, bpW:w8:patch-local, bpW:w2:orbit, bpW:w8:unique
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L524 | analyticity
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | (i) invariance
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | K_I = K^(n)_I, nu = nu^(n)_*
EDGE: bpW:w2:orbit | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | orbits are coefficient solutions
EDGE: bpW:w8:unique | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L527-L527 | uniqueness
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:in-birk
KIND: step
TITLE: Birkhoff coordinates
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L530
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L530
CONTRACT_ID: stepW:w8:in-birk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Psi(theta + t nu) = Psi'(theta' + t nu') for all t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:in-orbit, bpW:w8#data, bpW:w8:torus-shape, bpW:w3:gamma-real, bpW:w3:coords, bpW:w8:Kshell
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:in-orbit | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L528 | Y = Y'
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | tau_E injective
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | (v)
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | (iii)
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L530-L530 | Z bijective
EDGE: bpW:w8:Kshell | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L528 | K^(n)_I
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:in-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L534
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L534
CONTRACT_ID: stepW:w8:in-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); within the step: i; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: nu(I) = nu(I')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:torus-shape, bpW:w8:winding, stepW:w8:in-birk
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L531 | (i), (ii)
EDGE: bpW:w8:winding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L533-L533 | winding
EDGE: stepW:w8:in-birk | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L531 | equal tori
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:in-act
KIND: step
TITLE: Actions
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535
CONTRACT_ID: stepW:w8:in-act
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: I = I'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:nu-injective, stepW:w8:in-freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:nu-injective | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535 | injectivity of nu
EDGE: stepW:w8:in-freq | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535 | nu(I) = nu(I')
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:in-ang
KIND: step
TITLE: Angles
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L537
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L537
CONTRACT_ID: stepW:w8:in-ang
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:injective: the patched family
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:injective (I, I' in Gamma, theta, theta' in R^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: theta - theta' in Z^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-embedding, stepW:w8:in-act, bpW:w8:patch-local, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L537-L537 | third conjunct
EDGE: stepW:w8:in-act | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L536 | I = I'
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L536 | K_I = K^(n)_I
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L536 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:nlw2-proof
KIND: theorem
TITLE: Proof of W-NLW2
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L547-L551
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L552-L599
CONTRACT_ID: bpW:w8:nlw2-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every m > 0
SOURCE_CONCLUSION: Theorem bpW:wh:nlw2 (KAM.Wave.nlw2) holds exactly as frozen: the witnesses r_0, C, tau, eta of Definition bpW:w8:const and Gamma, nu, K of Definition bpW:w8:patch, chosen in this order and depending on m only, satisfy every conjunct
CONSTANT_SCOPE: all witnesses depend on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:const, bpW:w8:patch, bpW:w8:shells, bpW:w8:shell-iter, stepW:w8:p-pos, stepW:w8:p-etapos, stepW:w8:p-etalim, stepW:w8:p-meas, stepW:w8:p-incl, stepW:w8:p-nucont, stepW:w8:p-Kcont, stepW:w8:p-dens, stepW:w8:p-dioph, stepW:w8:p-lim, stepW:w8:p-emb, stepW:w8:p-close, stepW:w8:p-size, stepW:w8:p-inv, stepW:w8:p-pde, stepW:w8:p-inj, stepW:w8:p-assembly, bpW:w0:periodone#linearTorus, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L549-L549 | r_0, C, tau, eta
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L549-L549 | Gamma, nu, K
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L554-L554 | the shell data
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L554-L554 | the shell iteration
EDGE: stepW:w8:p-pos | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L556-L556 | proof step
EDGE: stepW:w8:p-etapos | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L558-L558 | proof step
EDGE: stepW:w8:p-etalim | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L559-L559 | proof step
EDGE: stepW:w8:p-meas | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L560-L560 | proof step
EDGE: stepW:w8:p-incl | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L561-L561 | proof step
EDGE: stepW:w8:p-nucont | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L563-L563 | proof step
EDGE: stepW:w8:p-Kcont | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L564-L564 | proof step
EDGE: stepW:w8:p-dens | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L566-L566 | proof step
EDGE: stepW:w8:p-dioph | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L575-L575 | proof step
EDGE: stepW:w8:p-lim | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L579-L579 | proof step
EDGE: stepW:w8:p-emb | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L583-L583 | proof step
EDGE: stepW:w8:p-close | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L585-L585 | proof step
EDGE: stepW:w8:p-size | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L589-L589 | proof step
EDGE: stepW:w8:p-inv | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L591-L591 | proof step
EDGE: stepW:w8:p-pde | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L593-L593 | proof step
EDGE: stepW:w8:p-inj | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L596-L596 | proof step
EDGE: stepW:w8:p-assembly | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L597-L597 | proof step
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L585-L585 | the linear torus K^0_I occurs directly here (frozen linearTorus)
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L584-L584 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: [pre-extract: dropped reference to bpW:wh:nlw2, which part w8-assembly proves or sets up]

NODE: stepW:w8:p-pos
KIND: step
TITLE: Positivity of $r_0$, $C$; $\tau>1$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L556-L557
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L556-L557
CONTRACT_ID: stepW:w8:p-pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: 0 < r_0, 0 < C, 1 < tau
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:const, bpW:w2:clause5
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L556-L556 | t_0, r_0, C_3, C
EDGE: bpW:w2:clause5 | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L557-L557 | M_m
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-etapos
KIND: step
TITLE: $\eta\ge0$ on $(0,r_0)$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558
CONTRACT_ID: stepW:w8:p-etapos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: r in (0,r_0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: eta(r) >= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-rpow, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-rpow | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558 | real powers
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558 | eta, E_7
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-etalim
KIND: step
TITLE: $\eta\to0$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559
CONTRACT_ID: stepW:w8:p-etalim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: eta -> 0 along nhdsWithin 0 (Set.Ioi 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-rpow, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-rpow | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559 | continuity at 0
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559 | eta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-meas
KIND: step
TITLE: \Lean{MeasurableSet $\Gamma$}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560
CONTRACT_ID: stepW:w8:p-meas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: MeasurableSet Gamma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560 | via Step stepW:w8:pc-borel
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-incl
KIND: step
TITLE: $\Gamma\subseteq\{I\mid(\forall i,0<I_i)\wedge r(I)<r_0\}$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L562
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L562
CONTRACT_ID: stepW:w8:p-incl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Gamma subset {I ¦ (forall i, 0 < I_i) and r(I) < r_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L561 | via Step stepW:w8:pc-incl
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-nucont
KIND: step
TITLE: \Lean{ContinuousOn $\nu$ $\Gamma$}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563
CONTRACT_ID: stepW:w8:p-nucont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ContinuousOn nu Gamma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563 | via Step stepW:w8:pc-nu
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-Kcont
KIND: step
TITLE: \Lean{ContinuousOn (Function.uncurry K) ($\Gamma$ $\times^s$ Set.univ)}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L565
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L565
CONTRACT_ID: stepW:w8:p-Kcont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ContinuousOn (Function.uncurry K) (Gamma x^s Set.univ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L564 | via Step stepW:w8:pc-K
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-dens
KIND: step
TITLE: Clause (1): density one
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L574
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L574
CONTRACT_ID: stepW:w8:p-dens
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (1): the density-one Tendsto statement in [0,infinity] along nhdsWithin 0 (Set.Ioi 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shell-est, bpW:w8:shells, bpW:w8:shell-data, bpW:w8:w6-general, bpW:w6:freq-lip, bpW:w6:exclusion, bpW:w7:exponents, bpW:w7:density, bpW:w8:patch-cont, bpW:w8:patch
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shell-est | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L566 | shell estimate
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L567-L567 | q, t_n
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L567-L567 | (i), (ii)
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L569-L569 | admissible family, exclusion
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L569-L569 | via Lemma bpW:w8:w6-general
EDGE: bpW:w6:exclusion | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L570-L570 | via Lemma bpW:w8:w6-general
EDGE: bpW:w7:exponents | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L573-L573 | exponent arithmetic
EDGE: bpW:w7:density | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L573-L573 | density theorem
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L573-L573 | Gamma subset P Borel
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L570-L570 | Gamma_n subset Gamma
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-dioph
KIND: step
TITLE: Clause (2), Diophantine
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L578
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L578
CONTRACT_ID: stepW:w8:p-dioph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: I in Gamma; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (2): KAM.IsDiophantine gamma_I 24 (nu I) with gamma_I = check alpha_n/(8 pi) > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell, bpW:w7:dioph, bpW:w8:patch-local, bpW:w7:dioph-use
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L575 | (iii)
EDGE: bpW:w7:dioph | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L576-L576 | Diophantine conversion
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L577-L577 | nu(I) = omega^(n)_*(I)/(2 pi)
EDGE: bpW:w7:dioph-use | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L578-L578 | gamma chosen after I
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-lim
KIND: step
TITLE: Clause (2), frequency limit
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582
CONTRACT_ID: stepW:w8:p-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (2): Tendsto nu (nhdsWithin 0 Gamma) (nhds fun i => lam m hm (i : Nat).succPNat / (2 * pi))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:limit, bpW:w8:patch-local, bpW:w8:freq-shell, bpW:w8:etor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:limit | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L579 | frequency limit
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L580-L580 | omega_* = omega^(n)_* on Gamma_n
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | (iii) e_n <= alpha_n
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | eps^(n)_omega <= alpha_n
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-emb
KIND: step
TITLE: Clause (3), embedding
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L584
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L584
CONTRACT_ID: stepW:w8:p-emb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: I, hI, I in Gamma; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (3): IsAnalyticTorusEmbedding (K I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-local, bpW:w8:shell-embedding, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L583 | K_I = K^(n)_I
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L584-L584 | single shell
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L584-L584 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-close
KIND: step
TITLE: Clause (3), closeness
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L588
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L588
CONTRACT_ID: stepW:w8:p-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: I in Gamma, theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (3): ¦¦K_I(theta) - linearTorus I hI theta¦¦ <= eta(r(I)) r(I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-close, bpW:w8#data, bpW:w7:shell-geom, bpW:w8:ext-rpow, bpW:w8:const, bpW:w8:patch-local, bpW:w0:periodone#linearTorus
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-close | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L585 | closeness
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L586-L586 | linearTorus = tau_E o K^0_I
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L587-L587 | (iii) t_n <= 2 max_i I_i
EDGE: bpW:w8:ext-rpow | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L588-L588 | real powers
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L588-L588 | eta
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L586-L586 | K_I = K^(n)_I
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L585 | the linear torus K^0_I occurs directly here (frozen linearTorus)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-size
KIND: step
TITLE: Clause (3), size
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L590
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L590
CONTRACT_ID: stepW:w8:p-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: I in Gamma, theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (3): ¦¦K_I(theta)¦¦ <= C_3 r(I) <= C r(I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-close, bpW:w8:shells, bpW:w8:shell-data, bpW:w7:shell-geom, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-close | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | ¦¦K¦¦ <= 2 rho_n
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | rho_n
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | (i) rho_n^2 <= 2 c_A t_n
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L590-L590 | (iii)
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L590-L590 | C_3, C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-inv
KIND: step
TITLE: Clause (4), invariance
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L592
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L592
CONTRACT_ID: stepW:w8:p-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); within the step: I in Gamma, theta, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (4)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-inv, bpW:w8:patch-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L591 | (i)
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L592-L592 | K_I = K^(n)_I, nu = nu^(n)_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-pde
KIND: step
TITLE: Clause (5), PDE solutions
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L595
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L595
CONTRACT_ID: stepW:w8:p-pde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (5) verbatim with C = max(1,M_m) C_3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:clause5, stepW:w8:p-emb, stepW:w8:p-size, stepW:w8:p-inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:clause5 | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L593 | clause (5)
EDGE: stepW:w8:p-emb | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L594-L594 | hypothesis
EDGE: stepW:w8:p-size | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L594-L594 | hypothesis
EDGE: stepW:w8:p-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L594-L594 | hypothesis
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-inj
KIND: step
TITLE: Clause (6), family injectivity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596
CONTRACT_ID: stepW:w8:p-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (6)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:injective
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:injective | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596 | family injectivity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w8:p-assembly
KIND: step
TITLE: Assembly
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L598
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L598
CONTRACT_ID: stepW:w8:p-assembly
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the body of nlw2 for the chosen witnesses
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:p-pos, stepW:w8:p-inj, stepW:w8:p-etapos, stepW:w8:p-etalim, stepW:w8:p-meas, stepW:w8:p-incl, stepW:w8:p-nucont, stepW:w8:p-Kcont, stepW:w8:p-dens, stepW:w8:p-dioph, stepW:w8:p-lim, stepW:w8:p-emb, stepW:w8:p-close, stepW:w8:p-size, stepW:w8:p-inv, stepW:w8:p-pde
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:p-pos | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | first step
EDGE: stepW:w8:p-inj | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | last step
EDGE: stepW:w8:p-etapos | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-etalim | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-meas | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-incl | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-nucont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-Kcont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-dens | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-dioph | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-lim | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-emb | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-close | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-size | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
EDGE: stepW:w8:p-pde | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | conjunct
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
