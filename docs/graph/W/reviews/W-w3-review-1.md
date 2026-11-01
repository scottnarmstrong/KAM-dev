# W-w3 review

Reviewer: sol-review-W-w3

Verdict: FAIL. Raw w3-birkhoff.tex L1-L904 reread, with W0 gradient, algebra, quartic and action coefficients, W1 gradient-identity and multiplier inputs, and cross-slice packet records.

| Node | Verdict | Source spans / reason |
|---|---|---|
| bpW:w3:ext-multilinear | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-multilinear@L42-L48; - |
| bpW:w3:ext-series | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-series@L49-L59; - |
| bpW:w3:ext-tsum | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-tsum@L60-L68; - |
| bpW:w3:ext-mvt | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-mvt@L69-L72; - |
| bpW:w3:ext-integral | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-integral@L73-L82; - |
| bpW:w3:ext-neumann | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-neumann@L83-L86; - |
| bpW:w3:space | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L108-L116; - |
| bpW:w3:coords | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L119-L128; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L130-L136 |
| bpW:w3:omega | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L139-L145; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L147-L151 |
| bpW:w3:hamfield-def | FAIL | analytic maps are Frechet differentiable, hence holomorphic |
| bpW:w3:real-restrict | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L171-L177; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L179-L186 |
| bpW:w3:forms | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L189-L197; - |
| bpW:w3:Lambda | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L200-L206; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L208-L212 |
| bpW:w3:majorant | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L232-L239; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L241-L245 |
| bpW:w3:quartic | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L248-L259; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L261-L278 |
| stepW:w3:maj | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265 |
| stepW:w3:gradbound | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269 |
| stepW:w3:identify | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277 |
| bpW:w3:quartic-ident | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L282-L291; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L293-L312 |
| stepW:w3:Gz | FAIL | the integral identification via W0 gradient requires a > 0; at a=0 the blueprint declares a definition |
| stepW:w3:XG | FAIL | the a=0 field identification has an undisclosed conditional-premise gap; both cited gradient results assume a > 0; the a=0 Hamiltonian is the two-sided quartic series defined and bounded here |
| stepW:w3:Gnor | FAIL | the normal-only size and field bounds use the quartic result at the normal projection |
| stepW:w3:count | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L304-L308; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L304-L308 |
| stepW:w3:res | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L309-L311; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L309-L311 |
| bpW:w3:divisor | FAIL | the curvature or beta comparison from the proof preamble is directly used |
| stepW:w3:sel | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L329-L332; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L329-L332 |
| stepW:w3:signs | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L333-L336; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L333-L336 |
| stepW:w3:s0 | FAIL | the curvature or beta comparison from the proof preamble is directly used |
| stepW:w3:s1 | FAIL | the curvature or beta comparison from the proof preamble is directly used |
| stepW:w3:s23 | FAIL | the curvature or beta comparison from the proof preamble is directly used |
| stepW:w3:s1inner | FAIL | the double integral argument uses the fundamental theorem of calculus; the curvature or beta comparison from the proof preamble is directly used |
| stepW:w3:divconcl | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L360-L363; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L360-L363 |
| bpW:w3:Fdef | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L385-L391; - |
| bpW:w3:F | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L396-L403; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L405-L414 |
| stepW:w3:fcoef | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L406-L409; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L406-L409 |
| stepW:w3:Fconcl | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L410-L413; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L410-L413 |
| bpW:w3:homological | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L417-L422; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L424-L439 |
| stepW:w3:Xfcoord | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L425-L427; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L425-L427 |
| stepW:w3:euler | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L428-L433; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L428-L433 |
| stepW:w3:divide | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L434-L438; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L434-L438 |
| bpW:w3:lie-coeff | FAIL | S must be a continuous trilinear map to construct continuous Lie coefficients; slot insertion preserves continuous multilinearity |
| bpW:w3:leibniz | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L460-L470; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L472-L491 |
| stepW:w3:rec | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L473-L475; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L473-L475 |
| stepW:w3:norms | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L476-L480; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L476-L480 |
| stepW:w3:Phireal | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L481-L482; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L481-L482 |
| stepW:w3:leib | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L483-L486; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L483-L486 |
| stepW:w3:leibid | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L487-L490; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L487-L490 |
| bpW:w3:flow | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:conv | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:floweq | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:transport | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:est | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:Greal | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:var | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:inv | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| bpW:w3:symplectic | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L569-L576; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L578-L593 |
| stepW:w3:skew | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L579-L582; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L579-L582 |
| stepW:w3:constform | FAIL | continuity and bilinearity of the symplectic form are used to differentiate g |
| stepW:w3:gradtrans | FAIL | the defining Hamiltonian pairing of P is directly consumed |
| bpW:w3:Yseries | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L611-L619; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L621-L673 |
| stepW:w3:majcalc | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majflow | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majA | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majN | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majX | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majY | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majint | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majps | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:majreal | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| bpW:w3:main | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L677-L695; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L697-L746 |
| stepW:w3:Kanalytic | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:K1 | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:K2 | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8); integrating the derivative bound on h gives the K2 estimate; the derivative bound for Z prime requires its quartic smoothing bound |
| stepW:w3:XK1 | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8); the cubic field bound for X_G supplies the premise of the transport estimate |
| stepW:w3:XK2 | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:XKconcl | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8); reality of K from part (i) supplies the reality premise of the Hamiltonian-field argument |
| stepW:w3:iii | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| stepW:w3:conj | FAIL | the radius bound or identity K=K1+K2 is derived in the proof, not a source premise (rule 8) |
| bpW:w3:gamma-real | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L770-L784; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L786-L796 |
| bpW:w3:transport-tori | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L800-L807; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L809-L813 |
| bpW:w3#data | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3@L23-L27; - |
| bpW:w3:hamfield-def#hamilton | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167 |
| bpW:w3:quartic-sec#data | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L224-L230; - |
| bpW:w3:main-sec#data | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L598-L609; - |
| stepW:w3:divisor#curvature | FAIL | missing substantive quantitative preamble at L326-L328; add the node below |

| stepW:w3:XG#via-w0-gradient | FAIL | missing alternative route for the equivalently citation at L301; its a=0 applicability gap must remain visible |
| stepW:w3:XG#via-w1-gradient | FAIL | missing alternative route for the equivalently citation at L301; its a=0 applicability gap must remain visible |

Coverage:

| Item | Verdict | Reason |
|---|---|---|
| w3-birkhoff:prose-L326-L328 | FAIL | missing quantitative curvature / beta proof preamble; add the inventory item below |

all other coverage items PASS. All prose dispositions were checked. sourcegap-L366 maps the three printed-divisor-proof repairs to s1/s23/s1inner; sourcegap-L750 maps the remainder application to K2/XK2. The interface and constants tables are summaries and future-consumer instructions; their exclusion does not exclude a wave-1 result merely for unreachability.

The generating coefficients discharge the divisor premise through nonzero g, the selection rule and the tangential minimum <=2. The proof preserves the 1/16 prefactor and corrected A/B. The nonlinear remainder cancels D Lambda X_F before estimating its smoothing field; it does not assume an everywhere-defined X_Lambda. The power-series construction supplies analyticity on Banach domains without invoking the W1 general ODE flow theorem.

Replacement fragments:

```text
NODE: bpW:w3:flow
KIND: theorem
TITLE: The flow of $X_F$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L494-L517
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L519-L556
CONTRACT_ID: bpW:w3:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})
SOURCE_CONCLUSION: r <= 1/10; (i) the series converges absolutely, w -> Gamma_t(w) has the power series (t^k Phi_k) on B_{rho_0} and is analytic, Gamma_t - id is analytic B_{rho_0} -> W+, (t,w) -> Gamma_t(w) is C^1; (ii) Gamma_0 = id, d_t Gamma_t = X_F(Gamma_t) and d_t Gamma_t = D Gamma_t X_F; (iii) ¦¦Gamma_t(w)¦¦ <= (10/9)¦¦w¦¦, ¦¦Gamma_t(w) - w¦¦_+ <= 3¦t¦C_F¦¦w¦¦^3, ¦¦D Gamma_t(w) - I¦¦_{W -> W+} <= 10¦t¦C_F¦¦w¦¦^2 <= 1/2, D Gamma_t(w) maps W+ into itself, is invertible on W and W+ with inverses of norm <= 2 and ¦¦D Gamma_t^{-1} - I¦¦_{W -> W+} <= 20¦t¦C_F¦¦w¦¦^2; (iv) Gamma_t(rho w) = rho Gamma_t(w); (v) d_t D Gamma_t(w)v = DX_F(Gamma_t(w)) D Gamma_t(w)v, DX_F(y)xi = 3S(y,y,xi); (vi) Gamma_{-t}(Gamma_t(w)) = w, Gamma = Gamma_1 is injective on B_{rho_1}, Gamma(B_{rho_1}) subset B_{10 rho_1/9} and Gamma(B_{rho_1}) contains B_{9 rho_1/10}
CONSTANT_SCOPE: rho_0, rho_1 depend on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:lie-coeff, bpW:w3:F, stepW:w3:conv, stepW:w3:floweq, stepW:w3:transport, stepW:w3:est, stepW:w3:Greal, stepW:w3:var, stepW:w3:inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L497-L497 | phi_k
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L495-L495 | C_F
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L520-L520 | proof step
EDGE: stepW:w3:floweq | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L528-L528 | proof step
EDGE: stepW:w3:transport | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L532-L532 | proof step
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L535-L535 | proof step
EDGE: stepW:w3:Greal | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L542-L542 | proof step
EDGE: stepW:w3:var | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L544-L544 | proof step
EDGE: stepW:w3:inv | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L548-L548 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:conv
KIND: step
TITLE: Convergence and analyticity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L520-L527
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L520-L527
CONTRACT_ID: stepW:w3:conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦t¦^k ¦¦phi_k(w)¦¦ <= r^k ¦¦w¦¦, r <= 1/10; the formal series with coefficients t^k Phi_k gives analyticity in W and (k >= 1) in W+; termwise derivatives in (t,w) are summable, giving joint C^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-series, bpW:w3:ext-tsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L521-L521 | (ii) the coefficient bounds
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L524-L524 | power series give analyticity
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L527-L527 | termwise differentiation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:floweq
KIND: step
TITLE: Flow equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L528-L531
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L528-L531
CONTRACT_ID: stepW:w3:floweq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t Gamma_t = S(Gamma_t,Gamma_t,Gamma_t) = X_F(Gamma_t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-tsum, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L530-L530 | (iv)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L531-L531 | Cauchy product
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L529-L529 | termwise derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:transport
KIND: step
TITLE: Transport equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L532-L534
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L532-L534
CONTRACT_ID: stepW:w3:transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t Gamma_t = D Gamma_t X_F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L534-L534 | (i)
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L534-L534 | termwise derivatives
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:est
KIND: step
TITLE: Estimates
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L535-L541
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L535-L541
CONTRACT_ID: stepW:w3:est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the bounds of (iii) and the inverses
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-neumann, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L537-L537 | (ii)
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L540-L540 | Neumann series
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L536-L536 | r <= 1/10
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:Greal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L542-L543
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L542-L543
CONTRACT_ID: stepW:w3:Greal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t real; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) termwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L543-L543 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:var
KIND: step
TITLE: Variational equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L544-L547
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L544-L547
CONTRACT_ID: stepW:w3:var
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t D Gamma_t v = 3S(D Gamma_t v, Gamma_t, Gamma_t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-tsum, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L545-L545 | (iv)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L545-L545 | Cauchy product
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L546-L546 | termwise derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:inv
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L548-L555
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L548-L555
CONTRACT_ID: stepW:w3:inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: ¦t¦ <= 1, w in B_{rho_1}; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: psi(s) = Gamma_{-s}(Gamma_s(w)) is C^1 with derivative 0, so Gamma_{-t}(Gamma_t(w)) = w; injectivity and the image inclusions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:est, stepW:w3:conv, stepW:w3:transport, stepW:w3:floweq, bpW:w3:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L549-L549 | ¦¦Gamma_s(w)¦¦ <= (10/9)¦¦w¦¦
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L550-L550 | C^1
EDGE: stepW:w3:transport | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L552-L552 | transport equation
EDGE: stepW:w3:floweq | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L552-L552 | flow equation
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L553-L553 | zero derivative implies constant
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majcalc
KIND: step
TITLE: Majorant calculus
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L623-L634
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L623-L634
CONTRACT_ID: stepW:w3:majcalc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: (t,w)-series P^i, multilinear B; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: majorant calculus: composite series have mu_{B(P^1..P^n)} <= ¦¦B¦¦ prod mu_{P^i} and sum to B(P^1(t,w),..); sums add coefficientwise; graded series and shifts
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3:ext-tsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L630-L630 | norms of composites
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L631-L631 | regrouping
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majflow
KIND: step
TITLE: The flow
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L635-L637
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L635-L637
CONTRACT_ID: stepW:w3:majflow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: s, rho; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the series Gamma (shift 1) sums to Gamma_t(w) with mu_Gamma <= rho/(1-r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:leibniz, stepW:w3:majcalc
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L636-L636 | Gamma_t
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L637-L637 | (ii)
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L636-L636 | (t,w)-series
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majA
KIND: step
TITLE: The derivative
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L638-L644
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L638-L644
CONTRACT_ID: stepW:w3:majA
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: k >= 1; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: A_{k,2k} with ¦¦A_{k,2k}¦¦ <= (2k+1)(2C_F)^k, mu_A <= 5r <= 1/16, sums to D Gamma_t(w) - I on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, stepW:w3:est, bpW:w3:ext-multilinear, bpW:w3:flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L641-L641 | (ii)
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L643-L643 | sum (2k+1) r^k <= 5r
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L643-L643 | derivative of the diagonal
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L644-L644 | (i) termwise derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majN
KIND: step
TITLE: The inverse
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L645-L651
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L645-L651
CONTRACT_ID: stepW:w3:majN
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N = sum_n (-A)^n regrouped is a graded series (shift 0) with mu_N <= 16/15 summing to D Gamma_t(w)^{-1} on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majA, stepW:w3:majcalc, bpW:w3:ext-tsum, bpW:w3:ext-neumann
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majA | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L647-L647 | mu_A <= 1/16
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L647-L647 | composite series
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L649-L649 | regrouping
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L650-L650 | Neumann series
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majX
KIND: step
TITLE: The cubic field along the flow
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L652-L655
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L652-L655
CONTRACT_ID: stepW:w3:majX
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: 4 nabla frak z(Gamma,Gamma,Gamma) has majorant <= C_* rho^3 (1-r)^{-3}, sums to X_{Z'}(Gamma_t w), shift 3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, stepW:w3:majflow, stepW:w3:majcalc
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L653-L653 | 4 nabla frak z trilinear of norm <= C_*
EDGE: stepW:w3:majflow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L654-L654 | the series Gamma
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L654-L654 | composites
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majY
KIND: step
TITLE: The integrand
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661
CONTRACT_ID: stepW:w3:majY
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the composite series cal Y sums to Y(t,w), has shift 3 and mu_Y(1,rho_1) <= 4 C_* rho_1^3; Y_j = cal Y_{j,2j+3}
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majN, stepW:w3:majX, bpW:w3:main-sec#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majN | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L658-L658 | N
EDGE: stepW:w3:majX | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L658-L658 | the cubic field along the flow
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L659-L659 | Y(t,w)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majint
KIND: step
TITLE: Integrate in $t$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L662-L665
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L662-L665
CONTRACT_ID: stepW:w3:majint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: termwise integration in t: int_0^1 Y dt = sum Y_j(w,..,w)/(j+1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majY, bpW:w3:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L664-L664 | the bounds on Y_j
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L664-L664 | termwise integration
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majps
KIND: step
TITLE: Power series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668
CONTRACT_ID: stepW:w3:majps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum ¦¦q_n¦¦ rho_1^n < infinity, so the formal power series and analyticity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majY, bpW:w3:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L667-L667 | sum ¦¦Y_j¦¦ rho_1^{2j+3}
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L667-L667 | power series give analyticity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:majreal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L669-L672
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L669-L672
CONTRACT_ID: stepW:w3:majreal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: t real; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y(t, rho w) = rho Y(t,w) and rho commutes with the t-integral
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:hamfield-def, bpW:w3:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L670-L670 | (iv) reality of Gamma_t
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L671-L671 | X_{Z'} commutes with rho
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L672-L672 | continuous R-linear maps commute with the integral
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:Kanalytic
KIND: step
TITLE: Analyticity and reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L700-L703
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L700-L703
CONTRACT_ID: stepW:w3:Kanalytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K is analytic on B_{rho_1} and real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:ext-series, bpW:w3:Lambda, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L702-L702 | (i) Gamma analytic; (iv) reality
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L702-L702 | compositions
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L701-L701 | Lambda a continuous polynomial
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L701-L701 | G, bar G, G^nor polynomials
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:K1
KIND: step
TITLE: The bound for $K_1$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L704-L707
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L704-L707
CONTRACT_ID: stepW:w3:K1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦K_1(w)¦ = ¦G(Gamma w) - G(w)¦ <= 5 C_* C_F ¦¦w¦¦^6
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-mvt, bpW:w3:flow, bpW:w3:quartic, bpW:w3:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L706-L706 | mean value inequality on the segment
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L707-L707 | (iii) estimates
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L706-L706 | ¦¦X_G(y)¦¦_+ <= C_*¦¦y¦¦^3
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L706-L706 | DG(y)v = Omega(X_G(y),v)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:K2
KIND: step
TITLE: The bound for $K_2$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L708-L713
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L708-L713
CONTRACT_ID: stepW:w3:K2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: h(t) = Lambda(Gamma_t w) - Lambda(w) - t Z'(w) has h(0) = 0, h'(t) = Z'(Gamma_t w) - Z'(w), ¦h'(t)¦ <= 5 C_* C_F t ¦¦w¦¦^6, so ¦K_2(w)¦ <= 5 C_* C_F ¦¦w¦¦^6; with K_1, (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:homological, stepW:w3:K1, stepW:w3:Kanalytic, bpW:w3:ext-integral, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L710-L710 | (ii) flow equation
EDGE: bpW:w3:homological | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L710-L710 | DLambda . X_F = Z' at Gamma_t w
EDGE: stepW:w3:K1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L712-L712 | the same mean value argument
EDGE: stepW:w3:Kanalytic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L713-L713 | (i) analyticity part
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L713-L713 | integrating the derivative bound on h gives the K2 estimate
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L712-L712 | the derivative bound for Z prime requires its quartic smoothing bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:XK1
KIND: step
TITLE: The field of $K_1$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L714-L721
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L714-L721
CONTRACT_ID: stepW:w3:XK1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_{K_1}(w) = D Gamma^{-1} X_G(Gamma w) - X_G(w), ¦¦X_{K_1}(w)¦¦_+ <= 44 C_* C_F ¦¦w¦¦^5, analytic into W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:symplectic, bpW:w3:forms, bpW:w3:flow, bpW:w3:ext-series, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L715-L715 | gradient transport
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L717-L717 | Lipschitz bound d = 4
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L717-L717 | (iii)
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L720-L720 | analyticity of D(Gamma - id), inversion
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L718-L718 | the cubic field bound for X_G supplies the premise of the transport estimate
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:XK2
KIND: step
TITLE: The field of $K_2$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L722-L731
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L722-L731
CONTRACT_ID: stepW:w3:XK2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K_2(w) = int_0^1 (Z'(Gamma_t w) - Z'(w)) dt, X_{K_2}(w) = int_0^1 Y(t,w) dt with ¦¦X_{K_2}(w)¦¦_+ <= 22 C_* C_F ¦¦w¦¦^5, analytic B_{rho_1} -> W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-integral, stepW:w3:K2, bpW:w3:symplectic, bpW:w3:main-sec#data, stepW:w3:XK1, bpW:w3:Yseries
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L723-L723 | FTC and differentiation under the integral
EDGE: stepW:w3:K2 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L723-L723 | h'(t)
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L725-L725 | gradient transport
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L726-L726 | Y of (bpW:w3:Ydef)
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L726-L726 | the same bound
EDGE: bpW:w3:Yseries | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L727-L727 | D_w Y bounded; analyticity of the integral
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:XKconcl
KIND: step
TITLE: Conclusion of (ii)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L732-L736
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L732-L736
CONTRACT_ID: stepW:w3:XKconcl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): X_K = X_{K_1} + X_{K_2}, 44 + 22 = 66, analytic; reality; the real restriction and (d_p K^R, -d_q K^R)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:XK1, stepW:w3:XK2, bpW:w3:hamfield-def, bpW:w3:real-restrict, bpW:w3:hamfield-def#hamilton, bpW:w3:coords, stepW:w3:Kanalytic
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L733-L733 | X_{K_1}
EDGE: stepW:w3:XK2 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L733-L733 | X_{K_2}
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L734-L734 | reality of the field
EDGE: bpW:w3:real-restrict | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L734-L734 | real restriction
EDGE: bpW:w3:hamfield-def#hamilton | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L735-L735 | Z^{-1} X_K = (d_p K, -d_q K) on real points
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L736-L736 | ¦¦Zx¦¦ <= sqrt2 ¦¦x¦¦_E
EDGE: stepW:w3:Kanalytic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L734-L734 | reality of K from part (i) supplies the reality premise of the Hamiltonian-field argument
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:iii
KIND: step
TITLE: (iii)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L737-L738
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L737-L738
CONTRACT_ID: stepW:w3:iii
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) from Lemmas bpW:w3:quartic and bpW:w3:quartic-ident
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, bpW:w3:quartic-ident
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L738-L738 | forms and bounds
EDGE: bpW:w3:quartic-ident | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L738-L738 | bar G, G^nor
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745
CONTRACT_ID: stepW:w3:conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w in B_{rho_1} cap W+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): Gamma(w) in W+ and D Gamma(w)[X_Lambda + X_{bar G} + X_{G^nor} + X_K](w) = X_H(Gamma(w))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:Lambda, bpW:w3:symplectic, bpW:w3:omega, stepW:w3:XKconcl
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L740-L740 | Gamma - id into W+
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L741-L741 | DH(y)u = Omega(X_H(y),u) on W+
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L742-L742 | gradient transport
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L745-L745 | nondegeneracy
EDGE: stepW:w3:XKconcl | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L744-L744 | X_K
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:Gz
KIND: step
TITLE: The quartic
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
CONTRACT_ID: stepW:w3:Gz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: expanding prod(z+zbar) in (bpW:w0n:Gz) gives the two-sided (1/16) sum frak g_x w_x, absolutely convergent by bpW:w3:quartic; for a > 0 it equals the integral-defined G(q) by bpW:w0n:gradient; at a = 0 this series is the definition of G on E_{0,p}, as declared at L283-L284
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:birkhoff#data, bpW:w3:quartic, bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L295-L295 | the identity (bpW:w0n:Gz)
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L296-L296 | absolute convergence
EDGE: bpW:w0n:gradient | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L297-L297 | G(q) as the quartic sum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:XG
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301
CONTRACT_ID: stepW:w3:XG
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Z^{-1} X_G = (d_p G, -d_q G) with d_p G = 0 and d_{q_l} G = T(q,q,q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:hamfield-def#hamilton, bpW:w0n:cubic-bound, bpW:w3:quartic
ROUTES: stepW:w3:XG#via-w0-gradient, stepW:w3:XG#via-w1-gradient
ROUTE_FOR: -
EDGE: bpW:w3:hamfield-def#hamilton | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L299-L299 | on real points Z^{-1} X_P = (d_p P, -d_q P)
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 | the trilinear T
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L300-L300 | the a=0 Hamiltonian is the two-sided quartic series defined and bounded here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the displayed field formula is claimed for a >= 0, but L300-L301 cites bpW:w0n:gradient (a > 0) or bpW:w1:gradient-identity (a > 0). Neither is directly applicable at a=0. The blueprint does not separately give the derivative identification for the newly series-defined a=0 Hamiltonian. Do not insert a > 0 into the source premises or treat either conditional result as a proof of the full source claim. The two positively weighted gradient arguments are alternative routes, corresponding to the parenthetical equivalently at L301.
```

```text
NODE: stepW:w3:Gnor
KIND: step
TITLE: Normal part
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L302-L303
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L302-L303
CONTRACT_ID: stepW:w3:Gnor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: x in T^c; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: every x in T^c has all ¦x_t¦ >= 3, whence the normal-part claims
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L303-L303 | the set T
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L303-L303 | the normal-only size and field bounds use the quartic result at the normal projection
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w3:hamfield-def
KIND: definition
TITLE: Hamiltonian field; one-smoothing holomorphic class
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:hamfield-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; U subset W open, P : U -> C complex differentiable
SOURCE_QUANTIFIERS: U, P
SOURCE_CONCLUSION: defines X_P as the map with DP(w)v = Omega(X_P(w),v) for all w in U, v in W (unique, X_P(w)_l = -i sgn(l) DP(w) e_{-l}); P real iff P(rho w) = conj P(w) on U = rho U (then X_P o rho = rho o X_P); the class A(U) of real P analytic on U whose Hamiltonian field exists, takes values in W+, and is analytic U -> W+; analytic maps are holomorphic (Definition bpW:w1:holomorphic)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:omega, bpW:w3:coords, bpW:w1:holomorphic, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L157-L157 | uniqueness by nondegeneracy; the formula for X_P
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L158-L158 | the involution rho
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L161-L161 | holomorphic maps
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L161-L161 | analytic maps are Frechet differentiable, hence holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w3:lie-coeff
KIND: definition
TITLE: Lie coefficients
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L451-L456
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:lie-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: k >= 0
SOURCE_CONCLUSION: defines the continuous (2k+1)-linear Phi_k : W^{2k+1} -> W by Phi_0(w) = w and the recursion Phi_{k+1}(w^1..w^{2k+3}) = (1/(k+1)) sum_{i=1}^{2k+1} Phi_k(w^1,..,w^{i-1},S(w^i,w^{i+1},w^{i+2}),w^{i+3},..), phi_k(w) = Phi_k(w,..,w), and (LQ)(w) = DQ(w) X_F(w) for C^1 maps Q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Fdef, bpW:w3:F, bpW:w3:ext-multilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Fdef | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L453-L453 | S and X_F
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L453-L453 | S must be a continuous trilinear map to construct continuous Lie coefficients
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L453-L453 | slot insertion preserves continuous multilinearity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:gradtrans
KIND: step
TITLE: Gradient transport
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592
CONTRACT_ID: stepW:w3:gradtrans
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: w, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: D(P o Gamma_t)(w)v = Omega(D Gamma_t^{-1} X_P(Gamma_t w), v); values in W+ by invertibility on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, stepW:w3:constform, bpW:w3:hamfield-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L591-L591 | (iii) invertibility on W and W+
EDGE: stepW:w3:constform | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L592-L592 | constant form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L589-L589 | the defining Hamiltonian pairing of P is directly consumed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:constform
KIND: step
TITLE: Constant form
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L583-L587
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L583-L587
CONTRACT_ID: stepW:w3:constform
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: g(t) = Omega(D Gamma_t xi, D Gamma_t eta) has g' = 0 and g(0) = Omega(xi,eta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, stepW:w3:skew, bpW:w3:ext-mvt, bpW:w3:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L586-L586 | (v) variational equation; D Gamma_0 = I
EDGE: stepW:w3:skew | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L586-L586 | skewness
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L587-L587 | zero derivative
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L584-L584 | continuity and bilinearity of the symplectic form are used to differentiate g
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:s1inner
KIND: step
TITLE: Two minus signs, inner pair
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L349-L359
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L349-L359
CONTRACT_ID: stepW:w3:s1inner
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); within the step: cases (i), (ii); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_1 = lambda_a + lambda_d - lambda_b - lambda_c is paired iff a = b, c = d, and otherwise >= beta: (i) d = b+c-a via f'' >= m/(27 lambda_a^3); (ii) d = a+b+c via 2a f'(b) >= 2/sqrt(1+m) >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:sel, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, bpW:w3:ext-integral, stepW:w3:divisor#curvature
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L352-L352 | the two cases d = b+c-a, d = a+b+c
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L353-L353 | f' increasing, f'' = m/f^3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L350-L350 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L353-L353 | the double integral argument uses the fundamental theorem of calculus
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L354-L354 | the curvature or beta comparison from the proof preamble is directly used
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w3:divisor
KIND: lemma
TITLE: Divisor lower bound; P96-W Lemma~4
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L317-L323
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L325-L364
CONTRACT_ID: bpW:w3:divisor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦
SOURCE_QUANTIFIERS: for all such x
SOURCE_CONCLUSION: ¦delta_x¦ >= m/(27 (n^2+m)^{3/2}); consequently, if x in T, frak g_x != 0 and x is not paired, ¦delta_x¦ >= delta_*(m) := m/(27 (4+m)^{3/2})
CONSTANT_SCOPE: delta_* depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w0:basis#lambda-facts, stepW:w3:sel, stepW:w3:signs, stepW:w3:s0, stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner, stepW:w3:divconcl, bpW:w0:basis#lam, stepW:w3:divisor#curvature
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L318-L318 | delta_x, pairing, T
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L327 | f'(s) = s/f(s) increasing, f'' = m/f^3 > 0 decreasing
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L329-L329 | proof step
EDGE: stepW:w3:signs | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L333-L333 | proof step
EDGE: stepW:w3:s0 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L337 | proof step
EDGE: stepW:w3:s1 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L339-L339 | proof step
EDGE: stepW:w3:s23 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L344-L344 | proof step
EDGE: stepW:w3:s1inner | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L349-L349 | proof step
EDGE: stepW:w3:divconcl | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L360-L360 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L327 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L327 | the curvature or beta comparison from the proof preamble is directly used
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:s0
KIND: step
TITLE: No minus sign
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L337-L338
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L337-L338
CONTRACT_ID: stepW:w3:s0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with no minus sign delta >= 4 > beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w3:divisor#curvature
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L338-L338 | lambda_k > k >= 1
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L338-L338 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L338-L338 | the curvature or beta comparison from the proof preamble is directly used
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:s1
KIND: step
TITLE: One minus sign
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L339-L343
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L339-L343
CONTRACT_ID: stepW:w3:s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with one minus sign the divisor is >= m/(2 lambda_a) >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:sel, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w3:divisor#curvature
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L343-L343 | a + b + c >= d
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L340-L340 | f(k) - k = m/(f(k)+k); lambda_c + c <= lambda_d + d
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L340-L340 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L342-L342 | the curvature or beta comparison from the proof preamble is directly used
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:s23
KIND: step
TITLE: Two minus signs, outer pairs
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L344-L348
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L344-L348
CONTRACT_ID: stepW:w3:s23
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_3 = lambda_c + lambda_d - lambda_a - lambda_b and delta_2 = (lambda_b - lambda_a) + (lambda_d - lambda_c) vanish identically iff paired, and otherwise are >= a/lambda_a >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w3:divisor#curvature
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L346-L346 | lambda_{k+1} - lambda_k >= f'(k) >= f'(a)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L345-L345 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L347-L347 | the curvature or beta comparison from the proof preamble is directly used
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w3:divisor#curvature
KIND: step
TITLE: Curvature and comparison for the divisor bound
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L326-L328
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L326-L328
CONTRACT_ID: stepW:w3:divisor#curvature
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 fixed; x as in bpW:w3:divisor; A <= B <= C <= D are its sorted positive absolute indices (the source writes a,b,c,d); f(s)=sqrt(s^2+m), lambda_k=f(k); beta=m/(27 lambda_A^3)
SOURCE_QUANTIFIERS: for every such m,x and every s >= 0
SOURCE_CONCLUSION: f_prime(s)=s/f(s) is increasing; f_second(s)=m/f(s)^3 is positive and decreasing on s >= 0; m <= lambda_A^2 gives 0 < beta <= 1/(27 lambda_A)
CONSTANT_SCOPE: the numerical constant 1/27 is absolute; beta depends on m and A
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:mass, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L327 | positivity of the second derivative uses m > 0 itself
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L328 | f(k)=lambda_k and beta explicitly use the frozen frequencies
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L327 | the recalled monotonicity of f prime is the earlier frequency fact
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: This separates the quantitative preamble used by the sign cases; it is not an extra assumption. The symbol A here is the smallest mode, not the exponential weight a.
```

```text
ITEM: w3-birkhoff:prose-L326-L328
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L326-L328
DISPOSITION: NODE stepW:w3:divisor#curvature
REASON: quantitative second-derivative and beta bounds used by the sign cases, previously absent from the inventory
COVERAGE_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w3
REVIEWER: -
```

```text
NODE: stepW:w3:XG#via-w0-gradient
KIND: route
TITLE: Field identification via bpW:w0n:gradient
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301
CONTRACT_ID: stepW:w3:XG#via-w0-gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Z^{-1} X_G = (d_p G, -d_q G) with d_p G = 0 and d_{q_l} G = T(q,q,q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: stepW:w3:XG
EDGE: bpW:w0n:gradient | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 | this is the cited alternative gradient identification, applicable only when a > 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: this route is asserted in the enclosing a >= 0 context but the cited gradient result requires a > 0. It supplies the positive-a case only; no source argument for a=0 is provided by this application.
```

```text
NODE: stepW:w3:XG#via-w1-gradient
KIND: route
TITLE: Field identification via bpW:w1:gradient-identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301
CONTRACT_ID: stepW:w3:XG#via-w1-gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Z^{-1} X_G = (d_p G, -d_q G) with d_p G = 0 and d_{q_l} G = T(q,q,q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:gradient-identity
ROUTES: -
ROUTE_FOR: stepW:w3:XG
EDGE: bpW:w1:gradient-identity | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 | this is the cited alternative gradient identification, applicable only when a > 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: this route is asserted in the enclosing a >= 0 context but the cited gradient result requires a > 0. It supplies the positive-a case only; no source argument for a=0 is provided by this application.
```

Suspected defects of the blueprint:

- L300-L301, “partial_q G = T(q,q,q) by ... gradient (equivalently ... gradient-identity)”: both cited results assume a > 0, while L23-L27 and quartic-ident include a=0. L283 declares a new series definition at a=0, but the cited gradient results do not establish its derivative formula there. The existing XG record now exposes that missing application as SOURCE_GAP; no source premise is repaired.
- Existing pinned-paper defects at L366-L375: P96-W p.285 Case 1 asserts delta_prime >= 1/lambda_i, contradicted by the listed (1,10,10,19), m=1 example; the corrected half bound is used. P96-W p.286 reduces all two-minus cases to the inner pair, losing a positive lower bound when that inner pair is resonant; s23 handles the other patterns. The printed intermediate “>=2(lambda_{j+1}-lambda_j)” also needs the factor i.
- Existing omitted application at L750-L759: P96-W p.285 concludes smoothing of X_K from conditional transport/bracket facts without showing the cancellation of the unbounded linear field. W3 supplies K2/XK2 and the explicit Yseries construction.

Check: the permitted slice checker returned “W-w3: 84 nodes, 284 edges, 134 coverage items, 0 problems” for the input packet. This structural result does not discharge the findings above. No Lean or build commands were run.

Validation: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/W/packets W-w3` returned `W-w3: 84 nodes, 284 edges, 134 coverage items, 0 problems`. Report-only checks verified verdict coverage, complete replacement fields, matching DEPS/EDGE sets, valid locator ranges and whitespace. The checker ran on the unchanged input packet; it does not accept these proposed corrections. No git, Lean, lake or lint commands were run.
