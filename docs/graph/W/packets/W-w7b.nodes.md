NODE: bpW:w7:prep
KIND: proposition
TITLE: Preparatory zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L462-L464
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L465-L504
CONTRACT_ID: bpW:w7:prep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Xi is Borel and Leb(Xi) <= C_P rho_zeta D_A^{-1} hat alpha^{8/11}
CONSTANT_SCOPE: C_P depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zones, bpW:w7:constdef, bpW:w7:basic#data, bpW:w7:sep, stepW:w7:prep-0, stepW:w7:prep-plus, stepW:w7:prep-minus-group, stepW:w7:prep-j0, stepW:w7:prep-n, stepW:w7:prep-X, stepW:w7:prep-sum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zones | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L463-L463 | Xi
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L463-L463 | C_P
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L463-L463 | rho_zeta
EDGE: bpW:w7:sep | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L466-L466 | S_{0l} empty
EDGE: stepW:w7:prep-0 | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L467-L467 | proof step
EDGE: stepW:w7:prep-plus | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L469-L469 | proof step
EDGE: stepW:w7:prep-minus-group | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L474-L474 | proof step
EDGE: stepW:w7:prep-j0 | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L482-L482 | proof step
EDGE: stepW:w7:prep-n | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L494-L494 | proof step
EDGE: stepW:w7:prep-X | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L497-L497 | proof step
EDGE: stepW:w7:prep-sum | blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L500-L500 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:prep-0
KIND: step
TITLE: $l=0$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L467-L468
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L467-L468
CONTRACT_ID: stepW:w7:prep-0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); within the step: k != 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Leb(S_k0) <= 8 rho_zeta hat alpha/(¦k¦ A_k D_A)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zone
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zone | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L468-L468 | psi = 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:prep-plus
KIND: step
TITLE: $\Lambda^+$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L469-L473
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L469-L473
CONTRACT_ID: stepW:w7:prep-plus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); within the step: k != 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Lambda^+ zones not in X sum to <= 32 rho_zeta hat alpha ¦k¦^2/(vartheta^3 A_k D_A)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:dichotomy, bpW:w7:zone, bpW:w7:count
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:dichotomy | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L471-L471 | dichotomy
EDGE: bpW:w7:zone | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L470-L470 | zone estimate
EDGE: bpW:w7:count | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L472-L472 | (i)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:prep-minus-group
KIND: step
TITLE: $\Lambda^-$, grouping
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481
CONTRACT_ID: stepW:w7:prep-minus-group
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); within the step: k, n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: grouping of the Lambda^- zones by n = i - j and the inclusion S_{k,ij} subset Q_{knj} subset Q_{knj_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zone, bpW:w7:unpert-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zone | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L477-L477 | zone estimate
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L479-L479 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:prep-j0
KIND: step
TITLE: $\Lambda^-$, choice of $j_0$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L482-L493
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L482-L493
CONTRACT_ID: stepW:w7:prep-j0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); within the step: k, n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with j_0 = ceil((A_k/hat alpha)^{4/11}) the union is <= (8 rho_zeta n/(¦k¦ D_A))(3 + a_kappa)(hat alpha/A_k)^{8/11}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zone, bpW:w7:ext-ennreal, stepW:w7:prep-minus-group
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zone | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L484-L484 | psi = n
EDGE: bpW:w7:ext-ennreal | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L493-L493 | ceil(x) <= 2x and real powers
EDGE: stepW:w7:prep-minus-group | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L486-L486 | the grouping
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:prep-n
KIND: step
TITLE: $\Lambda^-$, sum over $n$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L494-L496
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L494-L496
CONTRACT_ID: stepW:w7:prep-n
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: summing over n and doubling
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:prep-j0
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:prep-j0 | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L496-L496 | per n
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:prep-X
KIND: step
TITLE: Exceptional zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L497-L499
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L497-L499
CONTRACT_ID: stepW:w7:prep-X
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the exceptional zones have total measure <= 4 N_X rho_zeta hat alpha K_*/(vartheta sigma_X D_A)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xzones
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xzones | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L498-L498 | a = hat alpha
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:prep-sum
KIND: step
TITLE: Sum over $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503
CONTRACT_ID: stepW:w7:prep-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:prep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:prep (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: summing over k gives the bound with C_P; Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:count, bpW:w7:measurable, stepW:w7:prep-0, stepW:w7:prep-plus, stepW:w7:prep-n, stepW:w7:prep-X
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:count | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L502-L502 | (iii)
EDGE: bpW:w7:measurable | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L503-L503 | Borel
EDGE: stepW:w7:prep-0 | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L501-L501 | l = 0
EDGE: stepW:w7:prep-plus | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L501-L501 | Lambda^+
EDGE: stepW:w7:prep-n | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L501-L501 | Lambda^-
EDGE: stepW:w7:prep-X | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L502-L502 | X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:iter
KIND: proposition
TITLE: Iteration zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L510-L514
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L515-L544
CONTRACT_ID: bpW:w7:iter
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: E_it = union over nu and (k,l) in Z with ¦k¦ > K_{nu-1} of R^nu_kl is Borel and Leb(E_it) <= rho_zeta D_A^{-1}(Z_3(8 + 32 vartheta^{-3} + 16(2 + a_kappa) vartheta^{-2}) check alpha^{2/3} + 32 Z_3 vartheta^{-1}(eps_1 + eps_2) + 4 N_X K_*^2 vartheta^{-1} sigma_X^{-1} check alpha)
CONSTANT_SCOPE: constants depend only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:basic#data, stepW:w7:it-plus, stepW:w7:it-group, stepW:w7:it-j0, stepW:w7:it-n, stepW:w7:it-sum, stepW:w7:it-X
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L511-L511 | R^nu_kl
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L512-L512 | rho_zeta
EDGE: stepW:w7:it-plus | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L518-L518 | proof step
EDGE: stepW:w7:it-group | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L521-L521 | proof step
EDGE: stepW:w7:it-j0 | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L527-L527 | proof step
EDGE: stepW:w7:it-n | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L533-L533 | proof step
EDGE: stepW:w7:it-sum | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L537-L537 | proof step
EDGE: stepW:w7:it-X | blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L541-L541 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:it-plus
KIND: step
TITLE: $l=0$ and $\Lambda^+$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L518-L520
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L518-L520
CONTRACT_ID: stepW:w7:it-plus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); within the step: nu, k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the l = 0 and Lambda^+ zones as in the preparatory case with check alpha
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:prep-0, stepW:w7:prep-plus
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:prep-0 | blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L519-L519 | as there
EDGE: stepW:w7:prep-plus | blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L519-L519 | as there
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:it-group
KIND: step
TITLE: $\Lambda^-$, grouping with drift
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526
CONTRACT_ID: stepW:w7:it-group
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); within the step: nu, k, n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: R^nu_{k,ij} subset Q_{knj}, decreasing in j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:unpert-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L522-L522 | (H2)
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L522-L522 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:it-j0
KIND: step
TITLE: $\Lambda^-$, choice of $j_0$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532
CONTRACT_ID: stepW:w7:it-j0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); within the step: nu, k, n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with j_0 = ceil((A_k/check alpha)^{1/3}) the bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zone, stepW:w7:it-group
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zone | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L528-L528 | zone estimate
EDGE: stepW:w7:it-group | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L529-L529 | the grouping
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:it-n
KIND: step
TITLE: $\Lambda^-$, sum over $n$ and sign
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L533-L536
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L533-L536
CONTRACT_ID: stepW:w7:it-n
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); within the step: nu, k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: summing over n and the sign
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:it-j0
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:it-j0 | blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L534-L534 | per n
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:it-sum
KIND: step
TITLE: Sum over $\nu$ and $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540
CONTRACT_ID: stepW:w7:it-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: summing over nu and k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:count, stepW:w7:it-n, stepW:w7:it-plus
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:count | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L538-L538 | (ii), (iii)
EDGE: stepW:w7:it-n | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L539-L539 | per k
EDGE: stepW:w7:it-plus | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L539-L539 | per k
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:it-X
KIND: step
TITLE: Exceptional zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543
CONTRACT_ID: stepW:w7:it-X
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:iter: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:iter (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the exceptional zones; Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xzones, bpW:w7:measurable
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xzones | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L542-L542 | a = check alpha
EDGE: bpW:w7:measurable | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L543-L543 | Borel
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:measurable
KIND: lemma
TITLE: Measurability
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L550-L553
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L554-L560
CONTRACT_ID: bpW:w7:measurable
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: every zone S_kl, R^nu_kl, Q_knj is Borel, and so are Xi, E_it, E and Pi minus E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zones, bpW:w7:family, stepW:w7:meas-cont, stepW:w7:meas-union
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zones | blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L551-L551 | the zones
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L551-L551 | E
EDGE: stepW:w7:meas-cont | blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L555-L555 | proof step
EDGE: stepW:w7:meas-union | blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L558-L558 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:meas-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L555-L557
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L555-L557
CONTRACT_ID: stepW:w7:meas-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:measurable: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:measurable (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each phi_kl is continuous on its Borel domain
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:omega0, bpW:w7:family
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L556-L556 | affine
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L556-L556 | (H1)-(H2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:meas-union
KIND: step
TITLE: Unions
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L558-L559
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L558-L559
CONTRACT_ID: stepW:w7:meas-union
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:measurable: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:measurable (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: countable unions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-borel, stepW:w7:meas-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L559-L559 | Borel sets
EDGE: stepW:w7:meas-cont | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L559-L559 | continuity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:measure
KIND: theorem
TITLE: Measure of the resonance set; P96-K Theorem~D for the wave equation
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L563-L570
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L571-L579
CONTRACT_ID: bpW:w7:measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 and the constants of Definition bpW:w7:constdef; Pi subset {¦xi¦_infty <= 1/2} Borel with rho = diam_infty Pi; 0 < alpha <= alpha_0; an admissible family (Definition bpW:w7:family)
SOURCE_QUANTIFIERS: for all such Pi, alpha, families
SOURCE_CONCLUSION: E is Borel and Leb(E) <= C_7 rho alpha^{32/47}; equivalently Leb(omega^0(E)) <= (C_P + C_I) N_A rho alpha^{32/47}
CONSTANT_SCOPE: C_7 depends on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:constdef, bpW:w7:family, bpW:w7:measurable, stepW:w7:assemble, stepW:w7:return
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L564-L564 | C_7
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L566-L566 | admissible families, E
EDGE: bpW:w7:measurable | blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L566-L566 | E Borel
EDGE: stepW:w7:assemble | blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L572-L572 | proof step
EDGE: stepW:w7:return | blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L577-L577 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:assemble
KIND: step
TITLE: Assemble
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L572-L576
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L572-L576
CONTRACT_ID: stepW:w7:assemble
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:measure: m > 0 and the constants of Definition bpW:w7:constdef; Pi subset {¦xi¦_infty <= 1/2} Borel with rho = diam_infty Pi; 0 < alpha <= alpha_0; an admissible family (Definition bpW:w7:family)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:measure (for all such Pi, alpha, families); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Leb(E) <= Leb(Xi) + Leb(E_it) and the exponent substitutions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-borel, bpW:w7:prep, bpW:w7:iter
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L573-L573 | subadditivity
EDGE: bpW:w7:prep | blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L574-L574 | preparatory zones
EDGE: bpW:w7:iter | blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L574-L574 | iteration zones
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:return
KIND: step
TITLE: Return to $\xi$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:return@L577-L578
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:return@L577-L578
CONTRACT_ID: stepW:w7:return
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:measure: m > 0 and the constants of Definition bpW:w7:constdef; Pi subset {¦xi¦_infty <= 1/2} Borel with rho = diam_infty Pi; 0 < alpha <= alpha_0; an admissible family (Definition bpW:w7:family)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:measure (for all such Pi, alpha, families); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: rho_zeta/D_A <= L_A rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:return@L578-L578 | (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:melnikov
KIND: corollary
TITLE: Melnikov conditions on the complement
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L585-L596
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L597-L599
CONTRACT_ID: bpW:w7:melnikov
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Theorem bpW:w7:measure
SOURCE_QUANTIFIERS: xi as stated
SOURCE_CONCLUSION: (i) for xi in Pi minus Xi and (k,l) in Z: ¦<k,omega^0> + <l,Omega^0>¦ >= hat alpha hat w(l)/A_k, in particular ¦<k,omega^0>¦ >= hat alpha/A_k for k != 0; (ii) for xi in D_nu minus the R^nu_kl (¦k¦ > K_{nu-1}): the bound with check alpha <l>/A_k; (iii) for every frequency pair and l in Lambda: ¦<l,Omega'>¦ >= 2 beta_* <l> >= hat alpha <l>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:measure, bpW:w7:zones, bpW:w7:sep
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:measure | blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L586-L586 | the setting
EDGE: bpW:w7:zones | blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L598-L598 | negation of the zone definitions
EDGE: bpW:w7:sep | blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L598-L598 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Inline proof (L598).

NODE: bpW:w7:shells
KIND: definition
TITLE: Shells
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shells@L608-L612
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:shells
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q in (0,1), t_0 in (0,1/2]
SOURCE_QUANTIFIERS: k; a > 0
SOURCE_CONCLUSION: defines t_k = q^k t_0, the shells R_k = (0,t_k)^2 minus (0,t_{k+1})^2 = {I in (0,t_k)^2 : max I_i >= t_{k+1}}, and U_{-a} R_k = {I in R_k : dist_infty(I, R^2 minus R_k) > a}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:shell-geom
KIND: lemma
TITLE: Shell geometry
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L616-L620
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L621-L632
CONTRACT_ID: bpW:w7:shell-geom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the shells of Definition bpW:w7:shells
SOURCE_QUANTIFIERS: k; 0 < a <= t_k
SOURCE_CONCLUSION: (i) the shells R_l, l >= k, are pairwise disjoint Borel with union (0,t_k)^2 and Leb(R_l) = (1-q^2) t_l^2; (ii) Leb(R_k minus U_{-a} R_k) <= 7 a t_k; (iii) R_k subset {¦I¦_infty >= t_{k+1}} and diam_infty R_k <= t_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shells, stepW:w7:partition, stepW:w7:layer, stepW:w7:shell-size
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shells | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L617-L617 | the shells
EDGE: stepW:w7:partition | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L622-L622 | proof step
EDGE: stepW:w7:layer | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L625-L625 | proof step
EDGE: stepW:w7:shell-size | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L630-L630 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:partition
KIND: step
TITLE: Partition
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:partition@L622-L624
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:partition@L622-L624
CONTRACT_ID: stepW:w7:partition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:shell-geom: the shells of Definition bpW:w7:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:shell-geom (k; 0 < a <= t_k); within the step: I; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-ball
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-ball | blueprint-W/parts/w7-measure.tex#stepW:w7:partition@L624-L624 | Leb of boxes
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:layer
KIND: step
TITLE: Boundary layer
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L625-L629
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L625-L629
CONTRACT_ID: stepW:w7:layer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:shell-geom: the shells of Definition bpW:w7:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:shell-geom (k; 0 < a <= t_k); within the step: I; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) the boundary layer bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:shell-size
KIND: step
TITLE: Size
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:shell-size@L630-L631
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:shell-size@L630-L631
CONTRACT_ID: stepW:w7:shell-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:shell-geom: the shells of Definition bpW:w7:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:shell-geom (k; 0 < a <= t_k); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:density
KIND: theorem
TITLE: Density one from shell estimates
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:density@L635-L642
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:density@L643-L657
CONTRACT_ID: bpW:w7:density
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0
SOURCE_QUANTIFIERS: for all such Gamma
SOURCE_CONCLUSION: lim_{h -> 0+} Leb(Gamma cap B_h)/Leb(P cap B_h) = 1 in [0,infinity] (volume on Fin 2 -> R, B_h = Metric.ball 0 h), clause (1) of KAM.Wave.nlw2; for t_{k+1} < h <= t_k the ratio lies in [1 - q^{-2} sup_{l>=k} eps_l, 1]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shells, bpW:w7:density-sec#data, stepW:w7:den, stepW:w7:upper, stepW:w7:lower, stepW:w7:limit
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shells | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L636-L636 | the shells
EDGE: bpW:w7:density-sec#data | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L636-L636 | P and B_h
EDGE: stepW:w7:den | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L644-L644 | proof step
EDGE: stepW:w7:upper | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L646-L646 | proof step
EDGE: stepW:w7:lower | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L648-L648 | proof step
EDGE: stepW:w7:limit | blueprint-W/parts/w7-measure.tex#bpW:w7:density@L654-L654 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:den
KIND: step
TITLE: Denominator
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:den@L644-L645
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:den@L644-L645
CONTRACT_ID: stepW:w7:den
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:density: q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:density (for all such Gamma); within the step: h > 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Leb(P cap B_h) = h^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-ball
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-ball | blueprint-W/parts/w7-measure.tex#stepW:w7:den@L645-L645 | balls
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:upper
KIND: step
TITLE: Upper bound
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L646-L647
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L646-L647
CONTRACT_ID: stepW:w7:upper
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:density: q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:density (for all such Gamma); within the step: h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the ratio is <= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:lower
KIND: step
TITLE: Lower bound
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L648-L653
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L648-L653
CONTRACT_ID: stepW:w7:lower
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:density: q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:density (for all such Gamma); within the step: h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Leb(Gamma cap B_h) >= h^2(1 - bar eps_k/q^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shell-geom
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L650-L650 | (i)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:limit
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L654-L656
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L654-L656
CONTRACT_ID: stepW:w7:limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:density: q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:density (for all such Gamma); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the limit is 1 (squeeze; ENNReal quotient, nhdsWithin 0 (Ioi 0))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-ennreal, stepW:w7:lower, stepW:w7:upper
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-ennreal | blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L655-L655 | squeeze
EDGE: stepW:w7:lower | blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L655-L655 | lower bound
EDGE: stepW:w7:upper | blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L655-L655 | upper bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:shell-est
KIND: corollary
TITLE: Shell estimate from Theorem~\ref{bpW:w7:measure}
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L661-L667
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L668-L673
CONTRACT_ID: bpW:w7:shell-est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the shells; for every k, alpha_k in (0,alpha_0] with alpha_k <= t_k, a Borel Pi_k with U_{-alpha_k} R_k subset Pi_k subset (0,t_k)^2, and an admissible family for (Pi_k,alpha_k) with excluded set E_k such that Gamma contains R_k cap (Pi_k minus E_k)
SOURCE_QUANTIFIERS: for every k
SOURCE_CONCLUSION: eps_k <= (7 alpha_k + C_7 alpha_k^{32/47})/((1-q^2) t_k) <= (7 + C_7) alpha_k^{32/47}/((1-q^2) t_k); hence eps_k -> 0 whenever alpha_k^{32/47}/t_k -> 0, and Theorem bpW:w7:density applies
CONSTANT_SCOPE: C_7 depends on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shell-geom, bpW:w7:measure, bpW:w7:density, bpW:w7:family
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L670-L670 | (ii), (iii)
EDGE: bpW:w7:measure | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L670-L670 | the measure bound
EDGE: bpW:w7:density | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L666-L666 | conclusion
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L663-L663 | admissible families
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Inline proof (L669-L672).

NODE: bpW:w7:exponents
KIND: claim
TITLE: Scaling with the action radius; admissible choices of $\alpha$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L676-L691
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L676-L691
CONTRACT_ID: bpW:w7:exponents
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the shells and Theorem bpW:w7:measure; KP96's smallness alpha >= c_1 t^{3/2}
SOURCE_QUANTIFIERS: t -> 0
SOURCE_CONCLUSION: the excluded fraction is <= C alpha^{32/47}/t; density needs alpha = o(t^{47/32}); the admissible window is t^{3/2} <~ alpha = o(t^{47/32}); the explicit choice alpha(t) = t^{95/64} gives alpha^{32/47}/t = t^{1/94} -> 0, t^{3/2}/alpha = t^{1/64} -> 0 and alpha(t) <= t for t <= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:measure, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:measure | blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L679-L679 | the exponent 32/47
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L678-L678 | N_A, D_A
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: W8 cites it (4x) for the choice alpha(t) = t^{95/64}.

NODE: bpW:w7:dioph
KIND: lemma
TITLE: From the $l=0$ condition to \Lean{KAM.IsDiophantine}
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L697-L701
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L702-L708
CONTRACT_ID: bpW:w7:dioph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c > 0, omega in R^2 with ¦<k,omega>¦ >= c/A_k for all k in Z^2 minus 0 (A_k = 1 + ¦k¦^24)
SOURCE_QUANTIFIERS: for all such c, omega
SOURCE_CONCLUSION: nu = omega/(2pi) satisfies KAM.IsDiophantine (c/(4 pi)) 24 nu, i.e. (c/(4pi))/(sum ¦k_i¦)^24 <= ¦sum k_i nu_i¦ for k != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:wh:dioph#IsDiophantine, bpW:w7:indexdef, stepW:w7:dioph-base, stepW:w7:dioph-scale
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:wh:dioph#IsDiophantine | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L699-L699 | the frozen KAM.IsDiophantine
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L698-L698 | A_k with tau = 24
EDGE: stepW:w7:dioph-base | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L703-L703 | proof step
EDGE: stepW:w7:dioph-scale | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L706-L706 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:dioph-base
KIND: step
TITLE: Base
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-base@L703-L705
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-base@L703-L705
CONTRACT_ID: stepW:w7:dioph-base
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dioph: c > 0, omega in R^2 with ¦<k,omega>¦ >= c/A_k for all k in Z^2 minus 0 (A_k = 1 + ¦k¦^24)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dioph (for all such c, omega); within the step: k != 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: A_k <= 2 S^24 with S = sum ¦k_i¦ >= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:dioph-scale
KIND: step
TITLE: Rescale
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-scale@L706-L707
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-scale@L706-L707
CONTRACT_ID: stepW:w7:dioph-scale
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dioph: c > 0, omega in R^2 with ¦<k,omega>¦ >= c/A_k for all k in Z^2 minus 0 (A_k = 1 + ¦k¦^24)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dioph (for all such c, omega); within the step: k != 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦sum k_i nu_i¦ >= c/(4 pi S^24)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:dioph-base
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:dioph-base | blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-scale@L707-L707 | A_k <= 2 S^24
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:dioph-use
KIND: claim
TITLE: Use in clause (2)
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L713-L718
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L713-L718
CONTRACT_ID: bpW:w7:dioph-use
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the final parameter set of a shell with ¦<k,omega_*>¦ >= check alpha/(2 A_k)
SOURCE_QUANTIFIERS: I in that shell's part of Gamma
SOURCE_CONCLUSION: gamma_I = check alpha_k/(8 pi) > 0 (check alpha_k = alpha_k^{48/47}) with the exponent tau = 24 > 1; gamma_I depends on the shell and tends to 0 as I -> 0
CONSTANT_SCOPE: gamma_I per shell
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:dioph
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:dioph | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L715-L715 | with c = check alpha/2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: W8 cites it for gamma_I in clause (2). Its pointer to bpW:w6:final-freq is a forward pointer (the premise is supplied by W8).

NODE: bpW:w7:limit
KIND: lemma
TITLE: Frequency limit
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L720-L725
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L726-L734
CONTRACT_ID: bpW:w7:limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Gamma subset union R_k; omega_* : Gamma -> R^2 with sup_{Gamma cap R_k} ¦omega_* - omega^0¦_infty <= e_k, e_k -> 0
SOURCE_QUANTIFIERS: for all such Gamma, omega_*
SOURCE_CONCLUSION: nu = omega_*/(2pi) satisfies nu(I) -> lambda_J/(2pi) as I -> 0 in Gamma, i.e. Tendsto nu (nhdsWithin 0 Gamma) (nhds fun i => lam m hm (i : Nat).succPNat/(2 pi))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shells, bpW:w7:omega0, stepW:w7:lim-index, stepW:w7:lim-est, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shells | blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L721-L721 | the shells
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L722-L722 | omega^0
EDGE: stepW:w7:lim-index | blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L727-L727 | proof step
EDGE: stepW:w7:lim-est | blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L730-L730 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L723-L723 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:lim-index
KIND: step
TITLE: Shell index
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lim-index@L727-L729
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lim-index@L727-L729
CONTRACT_ID: stepW:w7:lim-index
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:limit: Gamma subset union R_k; omega_* : Gamma -> R^2 with sup_{Gamma cap R_k} ¦omega_* - omega^0¦_infty <= e_k, e_k -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:limit (for all such Gamma, omega_*); within the step: I; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: small ¦I¦_infty forces a large shell index
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shell-geom
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-index@L729-L729 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:lim-est
KIND: step
TITLE: Estimate
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L730-L733
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L730-L733
CONTRACT_ID: stepW:w7:lim-est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:limit: Gamma subset union R_k; omega_* : Gamma -> R^2 with sup_{Gamma cap R_k} ¦omega_* - omega^0¦_infty <= e_k, e_k -> 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:limit (for all such Gamma, omega_*); within the step: eps > 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦nu(I) - lambda_J/(2pi)¦ <= (e_k + N_A ¦I¦_infty)/(2pi), whence the limit
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, stepW:w7:lim-index, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L731-L731 | N_A
EDGE: stepW:w7:lim-index | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L732-L732 | shell index
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L731-L731 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:density-sec#data
KIND: definition
TITLE: Positive quadrant and max-norm balls of clause (1)
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:density-sec@L604-L606
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:density-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: h > 0
SOURCE_CONCLUSION: clause (1) compares Gamma with P = (0,infinity)^2 in the max-norm ball B_h = (-h,h)^2; density is obtained on shrinking action shells (KP96 Step 5)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L604-L606 fixing P and B_h for Theorem bpW:w7:density. It restates the sets of clause (1) of the headline; no edge to the root (that would be circular once W8 proves the root).
