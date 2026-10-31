NODE: bpW:w8:patch
KIND: definition
TITLE: The patched family
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L413-L420
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:patch
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-iter, bpW:w7:shell-geom, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L414-L414 | cited at this line (statement; \ref{bpW:w8:shell-iter})
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L415-L415 | cited at this line (statement; \ref{bpW:w7:shell-geom})
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L418-L418 | cited at this line (statement; \ref{bpW:w8:const})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:pl-dis, stepW:w8:pl-id
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:pl-dis | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L430-L430 | proof step of this result
EDGE: stepW:w8:pl-id | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L432-L432 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w7:shell-geom
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L430 | cited at this line (step; \ref{bpW:w8:shell-data})
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L431-L431 | cited at this line (step; \ref{bpW:w7:shell-geom})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:boundaries
KIND: claim
TITLE: Shell boundaries
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L438-L445
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L438-L445
CONTRACT_ID: bpW:w8:boundaries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w8:patch-cont, bpW:w7:shell-geom, bpW:w7:shell-est
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L441-L441 | cited at this line (statement; \ref{bpW:w8:shell-data})
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L442-L442 | cited at this line (statement; \ref{bpW:w8:patch-cont})
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L443-L443 | cited at this line (statement; \ref{bpW:w7:shell-geom})
EDGE: bpW:w7:shell-est | blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L444-L444 | cited at this line (statement; \ref{bpW:w7:shell-est})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w8:patch-cont
KIND: lemma
TITLE: Regularity of the patched family
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L447-L450
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L451-L460
CONTRACT_ID: bpW:w8:patch-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:pc-borel, stepW:w8:pc-incl, stepW:w8:pc-nu, stepW:w8:pc-K
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:pc-borel | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L452-L452 | proof step of this result
EDGE: stepW:w8:pc-incl | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L453-L453 | proof step of this result
EDGE: stepW:w8:pc-nu | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L455-L455 | proof step of this result
EDGE: stepW:w8:pc-K | blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L457-L457 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell, bpW:w7:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452 | cited at this line (step; \ref{bpW:w8:freq-shell})
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452 | cited at this line (step; \ref{bpW:w7:ext-borel})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell, bpW:w8:ext-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L456-L456 | cited at this line (step; \ref{bpW:w8:freq-shell})
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L456-L456 | cited at this line (step; \ref{bpW:w8:ext-local})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-inv, bpW:w8:ext-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L459-L459 | cited at this line (step; \ref{bpW:w8:shell-inv})
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L459-L459 | cited at this line (step; \ref{bpW:w8:ext-local})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:u-raw, stepW:w8:u-reg, stepW:w8:u-energy, stepW:w8:u-ineq, stepW:w8:u-gron, bpW:w2:coeffsol
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:u-raw | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L470-L470 | proof step of this result
EDGE: stepW:w8:u-reg | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L474-L474 | proof step of this result
EDGE: stepW:w8:u-energy | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L475-L475 | proof step of this result
EDGE: stepW:w8:u-ineq | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L481-L481 | proof step of this result
EDGE: stepW:w8:u-gron | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L484-L484 | proof step of this result
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L466-L466 | cited at this line (statement; \ref{bpW:w2:coeffsol})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cubic-analytic, bpW:w2:curve-deriv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L470 | cited at this line (step; \ref{bpW:w1:cubic-analytic})
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L472-L472 | cited at this line (step; \ref{bpW:w2:curve-deriv})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-inner, stepW:w8:u-reg
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-inner | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L475 | cited at this line (step; \ref{bpW:w8:ext-inner})
EDGE: stepW:w8:u-reg | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L479-L479 | cited at this line (step; \ref{stepW:w8:u-reg})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-compact | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L482-L482 | cited at this line (step; \ref{bpW:w8:ext-compact})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-mono
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-mono | blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L485-L485 | cited at this line (step; \ref{bpW:w8:ext-mono})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:w-mod, stepW:w8:w-const, stepW:w8:w-rate
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:w-mod | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L496-L496 | proof step of this result
EDGE: stepW:w8:w-const | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L498-L498 | proof step of this result
EDGE: stepW:w8:w-rate | blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L499-L499 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-exp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L497-L497 | cited at this line (step; \ref{bpW:w8:ext-exp})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-exp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498 | cited at this line (step; \ref{bpW:w8:ext-exp})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-exp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499 | cited at this line (step; \ref{bpW:w8:ext-exp})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:ni-same, stepW:w8:ni-diff, bpW:w8:patch-local
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:ni-same | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L508-L508 | proof step of this result
EDGE: stepW:w8:ni-diff | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L509-L509 | proof step of this result
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L507-L507 | cited at this line (proof; \ref{bpW:w8:patch-local})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508 | cited at this line (step; \ref{bpW:w8:freq-shell})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w7:freqcoords, bpW:w8:freq-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | cited at this line (step; \ref{bpW:w8:shell-data})
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | cited at this line (step; \ref{bpW:w7:freqcoords})
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L511-L511 | cited at this line (step; \ref{bpW:w8:freq-shell})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:in-orbit, stepW:w8:in-birk, stepW:w8:in-freq, stepW:w8:in-act, stepW:w8:in-ang, bpW:w8:torus-shape
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:in-orbit | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L524-L524 | proof step of this result
EDGE: stepW:w8:in-birk | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L528-L528 | proof step of this result
EDGE: stepW:w8:in-freq | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L531-L531 | proof step of this result
EDGE: stepW:w8:in-act | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L535-L535 | proof step of this result
EDGE: stepW:w8:in-ang | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L536-L536 | proof step of this result
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L523-L523 | cited at this line (proof; \ref{bpW:w8:torus-shape})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-embedding, bpW:w2:orbit, bpW:w8:shell-inv, bpW:w8:patch-local, bpW:w8:unique
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L524 | cited at this line (step; \ref{bpW:w8:shell-embedding})
EDGE: bpW:w2:orbit | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | cited at this line (step; \ref{bpW:w2:inv})
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | cited at this line (step; \ref{bpW:w8:shell-inv})
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L525-L525 | cited at this line (step; \ref{bpW:w8:patch-local})
EDGE: bpW:w8:unique | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L527-L527 | cited at this line (step; \ref{bpW:w8:unique})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:torus-shape, bpW:w3:gamma-real
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | cited at this line (step; \ref{bpW:w8:torus-shape})
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L529-L529 | cited at this line (step; \ref{bpW:w3:gamma-real})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:torus-shape, bpW:w8:winding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L531 | cited at this line (step; \ref{bpW:w8:torus-shape})
EDGE: bpW:w8:winding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L533-L533 | cited at this line (step; \ref{bpW:w8:winding})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:nu-injective
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:nu-injective | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535 | cited at this line (step; \ref{bpW:w8:nu-injective})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-embedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L537-L537 | cited at this line (step; \ref{bpW:w8:shell-embedding})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:p-pos, stepW:w8:p-etapos, stepW:w8:p-etalim, stepW:w8:p-meas, stepW:w8:p-incl, stepW:w8:p-nucont, stepW:w8:p-Kcont, stepW:w8:p-dens, stepW:w8:p-dioph, stepW:w8:p-lim, stepW:w8:p-emb, stepW:w8:p-close, stepW:w8:p-size, stepW:w8:p-inv, stepW:w8:p-pde, stepW:w8:p-inj, stepW:w8:p-assembly, bpW:w8:const, bpW:w8:patch, bpW:w8:shells, bpW:w8:shell-iter
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:p-pos | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L556-L556 | proof step of this result
EDGE: stepW:w8:p-etapos | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L558-L558 | proof step of this result
EDGE: stepW:w8:p-etalim | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L559-L559 | proof step of this result
EDGE: stepW:w8:p-meas | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L560-L560 | proof step of this result
EDGE: stepW:w8:p-incl | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L561-L561 | proof step of this result
EDGE: stepW:w8:p-nucont | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L563-L563 | proof step of this result
EDGE: stepW:w8:p-Kcont | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L564-L564 | proof step of this result
EDGE: stepW:w8:p-dens | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L566-L566 | proof step of this result
EDGE: stepW:w8:p-dioph | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L575-L575 | proof step of this result
EDGE: stepW:w8:p-lim | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L579-L579 | proof step of this result
EDGE: stepW:w8:p-emb | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L583-L583 | proof step of this result
EDGE: stepW:w8:p-close | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L585-L585 | proof step of this result
EDGE: stepW:w8:p-size | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L589-L589 | proof step of this result
EDGE: stepW:w8:p-inv | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L591-L591 | proof step of this result
EDGE: stepW:w8:p-pde | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L593-L593 | proof step of this result
EDGE: stepW:w8:p-inj | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L596-L596 | proof step of this result
EDGE: stepW:w8:p-assembly | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L597-L597 | proof step of this result
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L549-L549 | cited at this line (statement; \ref{bpW:w8:const})
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L549-L549 | cited at this line (statement; \ref{bpW:w8:patch})
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L554-L554 | cited at this line (proof; \ref{bpW:w8:shells})
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L554-L554 | cited at this line (proof; \ref{bpW:w8:shell-iter})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:clause5
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:clause5 | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L557-L557 | cited at this line (step; \ref{bpW:w2:clause5})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-rpow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-rpow | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558 | cited at this line (step; \ref{bpW:w8:ext-rpow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-rpow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-rpow | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559 | cited at this line (step; \ref{bpW:w8:ext-rpow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560 | cited at this line (step; \ref{bpW:w8:patch-cont})
EDGE: stepW:w8:pc-borel | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560 | cited at this line (step; \ref{stepW:w8:pc-borel})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-incl
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L561 | cited at this line (step; \ref{bpW:w8:patch-cont})
EDGE: stepW:w8:pc-incl | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L562-L562 | cited at this line (step; \ref{stepW:w8:pc-incl})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-nu
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563 | cited at this line (step; \ref{bpW:w8:patch-cont})
EDGE: stepW:w8:pc-nu | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563 | cited at this line (step; \ref{stepW:w8:pc-nu})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-cont, stepW:w8:pc-K
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L564 | cited at this line (step; \ref{bpW:w8:patch-cont})
EDGE: stepW:w8:pc-K | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L565-L565 | cited at this line (step; \ref{stepW:w8:pc-K})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:shell-est, bpW:w8:shells, bpW:w8:shell-data, bpW:w8:w6-general, bpW:w6:freq-lip, bpW:w6:exclusion, bpW:w7:exponents, bpW:w7:density, bpW:w8:patch-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:shell-est | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L566 | cited at this line (step; \ref{bpW:w7:shell-est})
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L567-L567 | cited at this line (step; \ref{bpW:w8:shells})
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L567-L567 | cited at this line (step; \ref{bpW:w8:shell-data})
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L569-L569 | cited at this line (step; \ref{bpW:w8:w6-general})
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L569-L569 | cited at this line (step; \ref{bpW:w6:freq-lip})
EDGE: bpW:w6:exclusion | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L570-L570 | cited at this line (step; \ref{bpW:w6:exclusion})
EDGE: bpW:w7:exponents | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L573-L573 | cited at this line (step; \ref{bpW:w7:exponents})
EDGE: bpW:w7:density | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L573-L573 | cited at this line (step; \ref{bpW:w7:density})
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L573-L573 | cited at this line (step; \ref{bpW:w8:patch-cont})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell, bpW:w7:dioph, bpW:w8:patch-local, bpW:w7:dioph-use
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L575 | cited at this line (step; \ref{bpW:w8:freq-shell})
EDGE: bpW:w7:dioph | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L576-L576 | cited at this line (step; \ref{bpW:w7:dioph})
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L577-L577 | cited at this line (step; \ref{bpW:w8:patch-local})
EDGE: bpW:w7:dioph-use | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L578-L578 | cited at this line (step; \ref{bpW:w7:dioph-use})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:limit, bpW:w8:freq-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:limit | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L579 | cited at this line (step; \ref{bpW:w7:limit})
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | cited at this line (step; \ref{bpW:w8:freq-shell})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:patch-local, bpW:w8:shell-embedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L583 | cited at this line (step; \ref{bpW:w8:patch-local})
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L584-L584 | cited at this line (step; \ref{bpW:w8:shell-embedding})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-close, bpW:w7:shell-geom, bpW:w8:ext-rpow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-close | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L585 | cited at this line (step; \ref{bpW:w8:shell-close})
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L587-L587 | cited at this line (step; \ref{bpW:w7:shell-geom})
EDGE: bpW:w8:ext-rpow | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L588-L588 | cited at this line (step; \ref{bpW:w8:ext-rpow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-close
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-close | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L589 | cited at this line (step; \ref{bpW:w8:shell-close})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-inv, bpW:w8:patch-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L591 | cited at this line (step; \ref{bpW:w8:shell-inv})
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L592-L592 | cited at this line (step; \ref{bpW:w8:patch-local})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:clause5, stepW:w8:p-emb, stepW:w8:p-size, stepW:w8:p-inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:clause5 | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L593 | cited at this line (step; \ref{bpW:w2:clause5})
EDGE: stepW:w8:p-emb | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L594-L594 | cited at this line (step; \ref{stepW:w8:p-emb})
EDGE: stepW:w8:p-size | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L594-L594 | cited at this line (step; \ref{stepW:w8:p-size})
EDGE: stepW:w8:p-inv | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L594-L594 | cited at this line (step; \ref{stepW:w8:p-inv})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:injective
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:injective | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596 | cited at this line (step; \ref{bpW:w8:injective})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
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
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:p-pos, stepW:w8:p-inj
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:p-pos | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | cited at this line (step; \ref{stepW:w8:p-pos})
EDGE: stepW:w8:p-inj | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L597 | cited at this line (step; \ref{stepW:w8:p-inj})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:deviations
KIND: claim
TITLE: Pages read and deviations
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L628-L650
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L628-L650
CONTRACT_ID: bpW:w8:deviations
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:wave-iteration, bpW:w6:to-w8, bpW:w6:prep-step, bpW:w8:shell-iter, bpW:w8:sharp-prep, bpW:w8:const, bpW:w8:shells, bpW:w8:Kshell, bpW:w8:patch, bpW:w8:shell-data, bpW:w8:w6-general, bpW:w8:etor, bpW:w8:freq-shell, bpW:w8:torus-shape, bpW:w8:shell-embedding, bpW:w8:shell-close, bpW:w8:shell-inv, bpW:w8:patch-local, bpW:w8:patch-cont, bpW:w8:unique, bpW:w8:winding, bpW:w8:nu-injective, bpW:w8:injective, bpW:w8:nlw2-proof, bpW:w8:boundaries, bpW:w8:ext-inner, bpW:w8:ext-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L632-L632 | cited at this line (statement; \ref{bpW:w6:wave-iteration})
EDGE: bpW:w6:to-w8 | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L633-L633 | cited at this line (statement; \ref{bpW:w6:to-w8})
EDGE: bpW:w6:prep-step | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L634-L634 | cited at this line (statement; \ref{bpW:w6:prep-step})
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L634-L634 | cited at this line (statement; \ref{bpW:w8:shell-iter})
EDGE: bpW:w8:sharp-prep | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L634-L634 | cited at this line (statement; \ref{bpW:w8:sharp-prep})
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L643-L643 | cited at this line (statement; \ref{bpW:w8:const})
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L643-L643 | cited at this line (statement; \ref{bpW:w8:shells})
EDGE: bpW:w8:Kshell | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L643-L643 | cited at this line (statement; \ref{bpW:w8:Kshell})
EDGE: bpW:w8:patch | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L644-L644 | cited at this line (statement; \ref{bpW:w8:patch})
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L644-L644 | cited at this line (statement; \ref{bpW:w8:shell-data})
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L644-L644 | cited at this line (statement; \ref{bpW:w8:w6-general})
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L644-L644 | cited at this line (statement; \ref{bpW:w8:etor})
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L645-L645 | cited at this line (statement; \ref{bpW:w8:freq-shell})
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L645-L645 | cited at this line (statement; \ref{bpW:w8:torus-shape})
EDGE: bpW:w8:shell-embedding | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L645-L645 | cited at this line (statement; \ref{bpW:w8:shell-embedding})
EDGE: bpW:w8:shell-close | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L645-L645 | cited at this line (statement; \ref{bpW:w8:shell-close})
EDGE: bpW:w8:shell-inv | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L645-L645 | cited at this line (statement; \ref{bpW:w8:shell-inv})
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L646-L646 | cited at this line (statement; \ref{bpW:w8:patch-local})
EDGE: bpW:w8:patch-cont | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L646-L646 | cited at this line (statement; \ref{bpW:w8:patch-cont})
EDGE: bpW:w8:unique | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L646-L646 | cited at this line (statement; \ref{bpW:w8:unique})
EDGE: bpW:w8:winding | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L646-L646 | cited at this line (statement; \ref{bpW:w8:winding})
EDGE: bpW:w8:nu-injective | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L646-L646 | cited at this line (statement; \ref{bpW:w8:nu-injective})
EDGE: bpW:w8:injective | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L647-L647 | cited at this line (statement; \ref{bpW:w8:injective})
EDGE: bpW:w8:nlw2-proof | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L647-L647 | cited at this line (statement; \ref{bpW:w8:nlw2-proof})
EDGE: bpW:w8:boundaries | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L647-L647 | cited at this line (statement; \ref{bpW:w8:boundaries})
EDGE: bpW:w8:ext-inner | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L648-L648 | cited at this line (statement; \ref{bpW:w8:ext-inner})
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L648-L648 | cited at this line (statement; \ref{bpW:w8:ext-local})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)
