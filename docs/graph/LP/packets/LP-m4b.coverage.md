ITEM: lpM:L12
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L381-L427
DISPOSITION: NODE lpM:L12
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; scaling r = sqrt(mu), N, eps; drift (34); (35) unused (amendment N4); conditional on the L8/L18 domain statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq32
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L384-L389
DISPOSITION: NODE lpM:L12
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; display (32)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq33
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L391-L395
DISPOSITION: NODE lpM:L12
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; display (33)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq34
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L397-L399
DISPOSITION: NODE lpM:L12#drift
REASON: display (34), the stopped drift r/4
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq35
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L401-L403
DISPOSITION: EXCLUDED
REASON: Q5 (ruling root-b8) and amendment N4: (35) is a remark, not a formal dependency (the paper route inverts only k·ω(I^0)); omitted from Lemma 12's source fields
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L12#perturbation-size
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L405-L405
DISPOSITION: NODE lpM:L12#perturbation-size
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; |X_{H-h_0}|_3 <= M_1 sqrt(mu)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L12#kappa-choice
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L407-L412
DISPOSITION: NODE lpM:L12#kappa-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; (36) implies (30)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq36
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L408-L411
DISPOSITION: NODE lpM:L12#kappa-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; display (36)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L12#time-choice
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L414
DISPOSITION: NODE lpM:L12#time-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; c = kappa log2 / 4, T_mu <= 2^{N/2}
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L12#drift
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L420
DISPOSITION: NODE lpM:L12#normal-form, lpM:L12#drift
REASON: L414-L420: the rewrite (33) and the drift (34)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L12#finite-divisors
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L420-L425
DISPOSITION: EXCLUDED
REASON: Q5 (ruling root-b8) and amendment N4: the proof of (35) (L420-L425) serves only the remark (35), which has no consumer
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L12#remark
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L427-L427
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m4b; commentary on what is inverted; no new obligation
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L13
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L429-L464
DISPOSITION: NODE lpM:L13
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; checked specialization of the Track N finite-cutoff theorem; Lean route of LP1/LP2 (N7)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L13#interface
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L433
DISPOSITION: NODE lpM:L13#interface
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; interface check against named repository declarations; consumed through IMPORTED graph-N nodes, never by reading implementation Lean
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L13#cite-repository
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L433
DISPOSITION: NODE N:bpN:p11:nonresonant
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; KAM.Nekhoroshev.nonresonant / ExtNFHyp / nf / preimage at f5625f19: candidate IMPORT N:bpN:p11:nonresonant (plus N:bpN:p11:s-nf#data if the NF hypothesis package is consumed separately); confirm in LP-imports
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L13#period-one
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L435-L440
DISPOSITION: NODE lpM:L13#period-one
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; theta = lambda/(2pi), rescaled slow variables, weighted bracket c_s, sign conventions
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L13#numeric-hypotheses
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L442-L457
DISPOSITION: NODE lpM:L13#numeric-hypotheses
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; (37) and the choices of kappa_1, D_0; amendment N6 (widths)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq37
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L448-L452
DISPOSITION: NODE lpM:L13#numeric-hypotheses
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; display (37)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L13#structural-hypotheses
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L458-L458
DISPOSITION: NODE lpM:L13#structural-hypotheses
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; holomorphy, reality, periodicity, module {0}, slow tube width, from L8
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L13#conclusion
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L460-L464
DISPOSITION: NODE lpM:L13#conclusion
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; (38): drift <= r/2 through exp(c_1 mu^{-a}) under stopped membership; slow displacement (nnf_disp_radius)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq38
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L461-L463
DISPOSITION: NODE lpM:L13#conclusion
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; display (38)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
