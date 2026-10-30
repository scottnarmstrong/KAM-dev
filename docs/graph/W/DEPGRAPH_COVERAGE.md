# Proof-source coverage manifest

CORPUS: blueprint-W/parts/{w0-conventions,w0-normalization,w1-sequences,w2-reconstruction,w3-birkhoff,w-headline}.tex pinned by SHA-256 in docs/graph/W/CORPUS.sha256 (KAM-inp branch inp, fa002b43, 2026-10-30; wave 1 = accepted parts W0-W3 and the headline; W4-W8 pending)

## Inventory

ITEM: bpW:w0:mass
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:mass@L24-L27
DISPOSITION: NODE bpW:w0:mass
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:nlw#IsClassicalSolution
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:nlw@L29-L35
DISPOSITION: NODE bpW:w0:nlw#IsClassicalSolution
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:basis#lam
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L39-L42
DISPOSITION: NODE bpW:w0:basis#lam
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:basis#sineMode
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L39-L42
DISPOSITION: NODE bpW:w0:basis#sineMode
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:ellap#ellWeight
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
DISPOSITION: NODE bpW:w0:ellap#ellWeight
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:ellap#WaveSpace
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
DISPOSITION: NODE bpW:w0:ellap#WaveSpace, bpW:w0:ellap#spaces
REASON: includes the general spaces and product norm, as well as the frozen specialization
COVERAGE_STATUS: REVIEWED
EXTRACTOR: sol-review-W-w0c
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:ellap#coeff
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
DISPOSITION: NODE bpW:w0:ellap#coeff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:weights
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:weights@L60-L64
DISPOSITION: NODE bpW:w0:ellap#WaveSpace, bpW:w0:ellap#coeff
REASON: the convention a = p = 1 is realized by the frozen WaveSpace and coeff (weights ellWeight 1 1); its remark on lower exponents is an outline
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:twosided
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:twosided@L66-L71
DISPOSITION: NODE bpW:w0:twosided
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:reconstruction#reconU
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L75-L81
DISPOSITION: NODE bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#rescaling
REASON: reconstruction formula plus the inverse coefficient dictionary and symplectic rescaling
COVERAGE_STATUS: REVIEWED
EXTRACTOR: sol-review-W-w0c
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:reconstruction#reconV
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L75-L81
DISPOSITION: NODE bpW:w0:reconstruction#reconV
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:H
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L87-L92
DISPOSITION: NODE bpW:w0:H
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:Gq#cubicGrad
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L96-L101
DISPOSITION: NODE bpW:w0:Gq#cubicGrad
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:eqmotion
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L103-L112
DISPOSITION: NODE bpW:w0:eqmotion
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:z
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L118-L123
DISPOSITION: NODE bpW:w0:z
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:actions
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L127-L134
DISPOSITION: NODE bpW:w0:actions
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:periodone#linearTorus
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L136-L144
DISPOSITION: NODE bpW:w0:periodone#linearTorus
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:harmless
KIND: claim
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:harmless@L175-L180
DISPOSITION: EXCLUDED
REASON: administrative remark on the printed-convention disagreements (errata E-PDE-W-1/2); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:sources
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:sources@L8-L8
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:pde
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:pde@L22-L22
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:spaces
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:spaces@L49-L49
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:hamiltonian
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:hamiltonian@L73-L73
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:complex
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:complex@L116-L116
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:table
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:table@L146-L146
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L36
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L36-L36
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L43
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L43-L43
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L58
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L58-L58
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L82
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L82-L82
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L93
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L93-L93
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L113
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L113-L113
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L124
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L124-L124
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L3-L6
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L3-L6
DISPOSITION: EXCLUDED
REASON: introduction and pointer to the comparison table
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L10-L20
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L10-L20
DISPOSITION: EXCLUDED
REASON: list of pinned sources and locators (provenance)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L45-L47
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L45-L47
DISPOSITION: NODE bpW:w0:basis#lambda-facts
REASON: elementary facts about lambda consumed by later proofs
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L84-L85
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L84-L85
DISPOSITION: EXCLUDED
REASON: forward pointer to Lemma bpW:w0n:recon-bounded
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L148-L149
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L148-L149
DISPOSITION: EXCLUDED
REASON: introduction of the comparison table (provenance)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L151-L172
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L151-L172
DISPOSITION: EXCLUDED
REASON: comparison table with the printed conventions of P96-W/KP96 (provenance and errata E-PDE-W-1/2); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L174-L174
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L174-L174
DISPOSITION: EXCLUDED
REASON: layout line
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:eq
KIND: display
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:eq@L32-L34
DISPOSITION: NODE bpW:w0:nlw#IsClassicalSolution
REASON: equation label maps to its enclosing definition, per SPEC
COVERAGE_STATUS: REVIEWED
EXTRACTOR: sol-review-W-w0c
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:coeffsys
KIND: display
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:coeffsys@L106-L108
DISPOSITION: NODE bpW:w0:eqmotion
REASON: equation label maps to its enclosing definition, per SPEC
COVERAGE_STATUS: REVIEWED
EXTRACTOR: sol-review-W-w0c
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0n:recon-bounded
KIND: lemma
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L18-L27
DISPOSITION: NODE bpW:w0n:recon-bounded
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: bpW:w0n:quartic-coeff
KIND: lemma
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L40-L51
DISPOSITION: NODE bpW:w0n:quartic-coeff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:prod
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56
DISPOSITION: NODE stepW:w0n:prod
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:cos
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
DISPOSITION: NODE stepW:w0n:cos
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:signed
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
DISPOSITION: NODE stepW:w0n:signed
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:gradient
KIND: lemma
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L76-L82
DISPOSITION: NODE bpW:w0n:gradient
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:algebra
KIND: lemma
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L94-L98
DISPOSITION: NODE bpW:w0n:algebra
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:weight
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L102-L106
DISPOSITION: NODE stepW:w0n:weight
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:young
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L107-L112
DISPOSITION: NODE stepW:w0n:young
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:cubic-bound
KIND: theorem
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L118-L129
DISPOSITION: NODE bpW:w0n:cubic-bound
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:majorant
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L132-L135
DISPOSITION: NODE stepW:w0n:majorant
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:selection
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L136-L141
DISPOSITION: NODE stepW:w0n:selection
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:smoothing
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L142-L148
DISPOSITION: NODE stepW:w0n:smoothing
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:analytic
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L149-L154
DISPOSITION: NODE stepW:w0n:analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:pde-equiv
KIND: proposition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L165-L183
DISPOSITION: NODE bpW:w0n:pde-equiv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:force
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L186-L192
DISPOSITION: NODE stepW:w0n:force
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:time
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L193-L198
DISPOSITION: NODE stepW:w0n:time
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:ident
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L199-L201
DISPOSITION: NODE stepW:w0n:ident
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:converse
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L202-L208
DISPOSITION: NODE stepW:w0n:converse
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:nonres
KIND: lemma
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L220-L224
DISPOSITION: NODE bpW:w0n:nonres
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:31
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L229-L232
DISPOSITION: NODE stepW:w0n:31
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:22
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L233-L246
DISPOSITION: NODE stepW:w0n:22
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:nonres-remark
KIND: claim
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres-remark@L248-L254
DISPOSITION: EXCLUDED
REASON: administrative remark (qualitative versus quantitative nonresonance; pointer to W3's bpW:w3:divisor); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:Qdef
KIND: definition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L270-L273
DISPOSITION: NODE bpW:w0n:Qdef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: bpW:w0n:AB
KIND: theorem
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L275-L286
DISPOSITION: NODE bpW:w0n:AB
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:resavg
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L289-L294
DISPOSITION: NODE stepW:w0n:resavg
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:moments
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L295-L298
DISPOSITION: NODE stepW:w0n:moments
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:sum
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L299-L304
DISPOSITION: NODE stepW:w0n:sum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:formal-birkhoff
KIND: proposition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L307-L315
DISPOSITION: NODE bpW:w0n:formal-birkhoff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:compare
KIND: claim
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:compare@L330-L337
DISPOSITION: EXCLUDED
REASON: administrative remark (comparison with the printed P96-W coefficients, E-PDE-W-1); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:nondeg
KIND: theorem
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L346-L353
DISPOSITION: NODE bpW:w0n:nondeg
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:det
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L356-L359
DISPOSITION: NODE stepW:w0n:det
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w0n:A2
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L360-L362
DISPOSITION: NODE stepW:w0n:A2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w0n:A3red
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L363-L368
DISPOSITION: NODE stepW:w0n:A3red
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w0n:l1
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L369-L372
DISPOSITION: NODE stepW:w0n:l1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:l2
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L373-L376
DISPOSITION: NODE stepW:w0n:l2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:kappa
KIND: claim
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:kappa@L383-L387
DISPOSITION: EXCLUDED
REASON: administrative remark (P96-W's exponent kappa = 2 is unchanged by the correction); the spectral asymptotics used later are proved in bpW:w1:tails; no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:duffing
KIND: proposition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L391-L400
DISPOSITION: NODE bpW:w0n:duffing
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:recon
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon@L16-L16
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:coeff
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:coeff@L38-L38
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:gradient-sec
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient-sec@L74-L74
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:pde
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde@L163-L163
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:nonres-sec
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres-sec@L218-L218
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:birkhoff
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L256-L256
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:nondeg-sec
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L339-L339
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:duffing-sec
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing-sec@L389-L389
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:ledger
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:ledger@L415-L415
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:sourcegap-L159
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#sourcegap@L159-L161
DISPOSITION: NODE stepW:w0n:majorant
REASON: the printed P96-W p. 280 bound (constant 1) is wrong; the blueprint proves the corrected constant sqrt 2 in the majorant step (errata N-1); constants only, no open gap
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L36
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L36-L36
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L70
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L70-L70
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L114
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L114-L114
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L156
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L156-L156
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L210
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L210-L210
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L324
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L324-L324
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L378
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L378-L378
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L3-L14
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L3-L14
DISPOSITION: EXCLUDED
REASON: introduction and outline (standing assumption bpW:w0:mass pointer, list of results)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L211-L216
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L211-L216
DISPOSITION: EXCLUDED
REASON: provenance note (expansion of P96-W Lemma 1, errata N-4); the completeness of (phi_l) it mentions is the edge stepW:w0n:force -> bpW:w1:sine-completeness
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L258-L268
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L258-L268
DISPOSITION: NODE bpW:w0n:birkhoff#data
REASON: fixes the quartic part in z-coordinates (bpW:w0n:Gz), resonance and the split G^tan + G^nor
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L341-L344
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L341-L344
DISPOSITION: NODE bpW:w0n:nondeg-sec#data
REASON: defines (A1)-(A3)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L408-L413
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L408-L413
DISPOSITION: EXCLUDED
REASON: remark on a numerical check (scripts/wave/w0_checks.py); not a mathematical input
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L417-L429
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L417-L429
DISPOSITION: NODE bpW:w0n:ledger#ext-lindstedt
REASON: ledger: its only unlabelled external not provided elsewhere is the Lindstedt shift; the other external facts map to bpW:w1:sine-completeness, bpW:w1:ext-analytic, bpW:w1:young, bpW:w1:ext-series (SPEC); the rest is administrative
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w1:transport
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L30-L39
DISPOSITION: NODE bpW:w1:transport
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w1:ext-lp
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-lp@L72-L77
DISPOSITION: NODE bpW:w1:ext-lp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-series
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-series@L78-L80
DISPOSITION: NODE bpW:w1:ext-series
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-analytic
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-analytic@L81-L88
DISPOSITION: NODE bpW:w1:ext-analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-onevar
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-onevar@L89-L98
DISPOSITION: NODE bpW:w1:ext-onevar
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-unifderiv
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-unifderiv@L99-L102
DISPOSITION: NODE bpW:w1:ext-unifderiv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-integral
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-integral@L103-L108
DISPOSITION: NODE bpW:w1:ext-integral
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-ode
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-ode@L109-L111
DISPOSITION: NODE bpW:w1:ext-ode
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-fourier
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-fourier@L112-L116
DISPOSITION: NODE bpW:w1:ext-fourier
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:space
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L122-L136
DISPOSITION: NODE bpW:w1:space
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:iso
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L139-L143
DISPOSITION: NODE stepW:w1:iso
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:sep
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L144-L147
DISPOSITION: NODE stepW:w1:sep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:coord
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L148-L150
DISPOSITION: NODE stepW:w1:coord
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:frozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L151-L153
DISPOSITION: NODE stepW:w1:frozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:coordinatewise
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L158-L168
DISPOSITION: NODE bpW:w1:coordinatewise
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:coordder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L171-L174
DISPOSITION: NODE stepW:w1:coordder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:coordcomp
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L175-L179
DISPOSITION: NODE stepW:w1:coordcomp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:multiplier
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L183-L189
DISPOSITION: NODE bpW:w1:multiplier
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:embed
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L198-L207
DISPOSITION: NODE bpW:w1:embed
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:diag
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L217-L232
DISPOSITION: NODE bpW:w1:diag
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:ratio
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L235-L239
DISPOSITION: NODE stepW:w1:ratio
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:rot
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L240-L243
DISPOSITION: NODE stepW:w1:rot
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:realflow
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L244-L248
DISPOSITION: NODE stepW:w1:realflow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:linfty
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:linfty@L254-L261
DISPOSITION: NODE bpW:w1:linfty
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:tails
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L264-L273
DISPOSITION: NODE bpW:w1:tails
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:twosided-transport
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L288-L294
DISPOSITION: NODE bpW:w1:twosided-transport
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:twosided
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L297-L313
DISPOSITION: NODE bpW:w1:twosided
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:ext
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L316-L319
DISPOSITION: NODE stepW:w1:ext
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:restr
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L320-L322
DISPOSITION: NODE stepW:w1:restr
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:pair
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L323-L324
DISPOSITION: NODE stepW:w1:pair
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:young
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L329-L339
DISPOSITION: NODE bpW:w1:young
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:cs
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L342-L345
DISPOSITION: NODE stepW:w1:cs
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:youngsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L346-L348
DISPOSITION: NODE stepW:w1:youngsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:l1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L349-L352
DISPOSITION: NODE stepW:w1:l1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:rules
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L353-L356
DISPOSITION: NODE stepW:w1:rules
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w1:algebra
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L360-L363
DISPOSITION: NODE bpW:w1:algebra
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:algebra-half
KIND: claim
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra-half@L373-L377
DISPOSITION: EXCLUDED
REASON: administrative remark (the algebra for 1/2 < s < 1 is not part of the plan; no later milestone needs it)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:selection
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L386-L400
DISPOSITION: NODE bpW:w1:selection
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:maj1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L403-L405
DISPOSITION: NODE stepW:w1:maj1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:sel1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L406-L411
DISPOSITION: NODE stepW:w1:sel1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:smooth1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L412-L414
DISPOSITION: NODE stepW:w1:smooth1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:maj2
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L415-L418
DISPOSITION: NODE stepW:w1:maj2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:sel2
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L419-L422
DISPOSITION: NODE stepW:w1:sel2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:smooth2
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L423-L426
DISPOSITION: NODE stepW:w1:smooth2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:trilinear
KIND: theorem
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L431-L450
DISPOSITION: NODE bpW:w1:trilinear
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:tricoord
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L453-L458
DISPOSITION: NODE stepW:w1:tricoord, stepW:w1:tricoord#via-cubic-bound, stepW:w1:tricoord#via-selection
REASON: the step and its two alternative derivations (route nodes)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:tricont
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L459-L462
DISPOSITION: NODE stepW:w1:tricont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:trireal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L463-L466
DISPOSITION: NODE stepW:w1:trireal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:trifrozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L467-L471
DISPOSITION: NODE stepW:w1:trifrozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:cubic-analytic
KIND: corollary
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L475-L489
DISPOSITION: NODE bpW:w1:cubic-analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:can
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L492-L493
DISPOSITION: NODE stepW:w1:can
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:cder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L494-L498
DISPOSITION: NODE stepW:w1:cder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:clip
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L499-L501
DISPOSITION: NODE stepW:w1:clip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:cfrozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L502-L504
DISPOSITION: NODE stepW:w1:cfrozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:gradient-identity
KIND: proposition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L509-L522
DISPOSITION: NODE bpW:w1:gradient-identity
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:quartic
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L525-L530
DISPOSITION: NODE stepW:w1:quartic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:gradder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L531-L534
DISPOSITION: NODE stepW:w1:gradder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:gradw
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L535-L539
DISPOSITION: NODE stepW:w1:gradw
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:hamfield
KIND: proposition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L543-L563
DISPOSITION: NODE bpW:w1:hamfield
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:hlin
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L566-L567
DISPOSITION: NODE stepW:w1:hlin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:hnonlin
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L568-L570
DISPOSITION: NODE stepW:w1:hnonlin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:hsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L571-L573
DISPOSITION: NODE stepW:w1:hsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:hham
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L574-L580
DISPOSITION: NODE stepW:w1:hham
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:hfrozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L581-L585
DISPOSITION: NODE stepW:w1:hfrozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1:realization
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:realization@L28-L28
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1:ext
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext@L66-L66
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1:weighted
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:weighted@L120-L120
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1:twosided-sec
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-sec@L286-L286
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1:cubic
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic@L379-L379
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L40
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L40-L40
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L155
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L155-L155
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L181
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L181-L181
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L196
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L196-L196
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L215
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L215-L215
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L250
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L250-L250
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L262
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L262-L262
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L281
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L281-L281
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L295
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L295-L295
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L326
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L326-L326
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L358
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L358-L358
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L370
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L370-L370
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L428
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L428-L428
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L473
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L473-L473
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L506
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L506-L506
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L541
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L541-L541
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L587
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L587-L587
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L3-L15
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L3-L15
DISPOSITION: EXCLUDED
REASON: introduction and outline (standing assumption pointer; what W1 supplies; pointer to Remark bpW:w1:operator-fourier)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L17-L26
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L17-L26
DISPOSITION: EXCLUDED
REASON: route paragraph (outline)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L43-L44
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L43-L44
DISPOSITION: EXCLUDED
REASON: realization table heading (notation)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L46-L58
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L46-L58
DISPOSITION: EXCLUDED
REASON: realization table of Lean carriers (notation); the facts used are stated in Definition bpW:w1:transport and Lemma bpW:w1:space
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L60-L64
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L60-L64
DISPOSITION: EXCLUDED
REASON: Lean notation (non-frozen helper coeffW, distinct name)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L68-L71
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L68-L71
DISPOSITION: EXCLUDED
REASON: introduction of the external list; the track-K externals it names (bp:p1:ext-*) are cited inside W's own ext items as provenance (SPEC)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L117-L118
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L117-L118
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L381-L384
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L381-L384
DISPOSITION: EXCLUDED
REASON: pointer (motivation of Lemma bpW:w1:selection)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:sine-completeness
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L593-L596
DISPOSITION: NODE bpW:w1:sine-completeness
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:odd
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L599-L601
DISPOSITION: NODE stepW:w1:odd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:coeffs
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L602-L605
DISPOSITION: NODE stepW:w1:coeffs
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:basis
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L606-L609
DISPOSITION: NODE stepW:w1:basis
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:cont
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L610-L612
DISPOSITION: NODE stepW:w1:cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:sine-feature
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L617-L629
DISPOSITION: NODE bpW:w1:sine-feature
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:growth
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L632-L635
DISPOSITION: NODE stepW:w1:growth
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:normal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L636-L640
DISPOSITION: NODE stepW:w1:normal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:sinereal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L641-L644
DISPOSITION: NODE stepW:w1:sinereal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:recon-analytic
KIND: corollary
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L648-L670
DISPOSITION: NODE bpW:w1:recon-analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:bil
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L673-L676
DISPOSITION: NODE stepW:w1:bil
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:recanalytic
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682
DISPOSITION: NODE stepW:w1:recanalytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:recder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691
DISPOSITION: NODE stepW:w1:recder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w1:complexification
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification@L698-L703
DISPOSITION: NODE bpW:w1:complexification
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:complexification-lemma
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L707-L718
DISPOSITION: NODE bpW:w1:complexification-lemma
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:holomorphic
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holomorphic@L728-L734
DISPOSITION: NODE bpW:w1:holomorphic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:cauchy
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L737-L742
DISPOSITION: NODE bpW:w1:cauchy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:lines
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L745-L747
DISPOSITION: NODE stepW:w1:lines
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:onevar
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L748-L749
DISPOSITION: NODE stepW:w1:onevar
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:margins
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L750-L751
DISPOSITION: NODE stepW:w1:margins
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:deriv-continuous
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L755-L760
DISPOSITION: NODE bpW:w1:deriv-continuous
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:dcbound
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764
DISPOSITION: NODE stepW:w1:dcbound
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:dcintegral
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L765-L768
DISPOSITION: NODE stepW:w1:dcintegral
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:dclip
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L769-L774
DISPOSITION: NODE stepW:w1:dclip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:uniform-limit
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L778-L786
DISPOSITION: NODE bpW:w1:uniform-limit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:ulcauchy
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L789-L793
DISPOSITION: NODE stepW:w1:ulcauchy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:ullimit
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L794-L797
DISPOSITION: NODE stepW:w1:ullimit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:holo-analytic-fd
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L801-L811
DISPOSITION: NODE bpW:w1:holo-analytic-fd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:hamargin
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816
DISPOSITION: NODE stepW:w1:hamargin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:hacoef
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L817-L823
DISPOSITION: NODE stepW:w1:hacoef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:hagroup
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L824-L833
DISPOSITION: NODE stepW:w1:hagroup
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:hareal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L834-L835
DISPOSITION: NODE stepW:w1:hareal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:torus-analytic
KIND: corollary
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L839-L844
DISPOSITION: NODE bpW:w1:torus-analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:flow
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L852-L866
DISPOSITION: NODE bpW:w1:flow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:flowlip
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L869-L871
DISPOSITION: NODE stepW:w1:flowlip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:picard
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875
DISPOSITION: NODE stepW:w1:picard
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:picardholo
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888
DISPOSITION: NODE stepW:w1:picardholo
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:flowlim
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
DISPOSITION: NODE stepW:w1:flowlim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:flowreal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L895-L896
DISPOSITION: NODE stepW:w1:flowreal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:flowpar
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901
DISPOSITION: NODE stepW:w1:flowpar
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w1:kam-space
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-space@L916-L928
DISPOSITION: NODE bpW:w1:kam-space
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:kam-conventions
KIND: claim
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L931-L937
DISPOSITION: EXCLUDED
REASON: administrative remark (conventions to carry into W4-W6: P96-K's z is the conjugate of W0's; sum versus max norm); no wave-1 proof consumes it; re-examine when W4-W6 are added
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:kam-domain
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L939-L943
DISPOSITION: NODE bpW:w1:kam-domain
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:fourier-l2
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L955-L966
DISPOSITION: NODE bpW:w1:fourier-l2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:shift
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974
DISPOSITION: NODE stepW:w1:shift
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:parseval
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L975-L979
DISPOSITION: NODE stepW:w1:parseval
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:orthants
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983
DISPOSITION: NODE stepW:w1:orthants
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w1:fsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L984-L989
DISPOSITION: NODE stepW:w1:fsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:fourier-banach
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L996-L1012
DISPOSITION: NODE bpW:w1:fourier-banach
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbdual
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1015-L1018
DISPOSITION: NODE stepW:w1:fbdual
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbdecay
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1019-L1022
DISPOSITION: NODE stepW:w1:fbdecay
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1023-L1024
DISPOSITION: NODE stepW:w1:fbsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbconv
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1025-L1028
DISPOSITION: NODE stepW:w1:fbconv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:lattice
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1033-L1047
DISPOSITION: NODE bpW:w1:lattice
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latprod
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1050-L1053
DISPOSITION: NODE stepW:w1:latprod
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latcount
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1054-L1056
DISPOSITION: NODE stepW:w1:latcount
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latweight
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1057-L1061
DISPOSITION: NODE stepW:w1:latweight
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latdiv
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1062-L1064
DISPOSITION: NODE stepW:w1:latdiv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:operator-fourier
KIND: claim
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1068-L1104
DISPOSITION: EXCLUDED
REASON: administrative remark (counterexample to the operator-valued square-sum bound printed on P96-K p. 127 and what W4 must use instead); no wave-1 proof consumes it; re-examine when W4 is added
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:schur
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1110-L1121
DISPOSITION: NODE bpW:w1:schur
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:rows
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1124-L1127
DISPOSITION: NODE stepW:w1:rows
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:schurtest
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1128-L1130
DISPOSITION: NODE stepW:w1:schurtest
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:diagcomb
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1131-L1135
DISPOSITION: NODE stepW:w1:diagcomb
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:schurweights
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1136-L1137
DISPOSITION: NODE stepW:w1:schurweights
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:sines
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sines@L591-L591
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:analytic
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:analytic@L696-L696
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:kam
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam@L914-L914
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:ledger
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ledger@L1141-L1141
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:sourcegap-L906
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#sourcegap@L906-L912
DISPOSITION: NODE stepW:w1:flowpar
REASON: P96-K Lemma A.4's mean value step needs a segment in V; the blueprint repairs it by keeping both trajectories in the convex ball B(w,delta) (ball margin 2 delta, M < delta) in the parameter step
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:sourcegap-L1105
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#sourcegap@L1105-L1108
DISPOSITION: NODE bpW:w1:fourier-banach, bpW:w1:lattice
REASON: the false operator-valued square-sum bound of P96-K p. 127 is replaced by these lemmas; the homological estimate itself is W4's (later wave)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L614
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L614-L614
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L646
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L646-L646
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L693
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L693-L693
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L704
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L704-L704
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L726
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L726-L726
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L735
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L735-L735
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L753
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L753-L753
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L776
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L776-L776
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L799
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L799-L799
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L837
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L837-L837
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L850
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L850-L850
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L903
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L903-L903
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L929
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L929-L929
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L952
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L952-L952
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L991
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L991-L991
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L1030
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L1030-L1030
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L1066
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L1066-L1066
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L1139
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L1139-L1139
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:prose-L1143-L1152
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L1143-L1152
DISPOSITION: EXCLUDED
REASON: ledger: PLAN-node mapping (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:prose-L1154-L1162
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L1154-L1162
DISPOSITION: EXCLUDED
REASON: ledger: added nodes and their consumers (administrative pointers)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:prose-L1164-L1168
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L1164-L1168
DISPOSITION: EXCLUDED
REASON: ledger: source gaps and conventions (administrative; each gap is mapped at its \sourcegap item)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w2:ext-deriv
KIND: external
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-deriv@L40-L48
DISPOSITION: NODE bpW:w2:ext-deriv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:ext-an
KIND: external
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-an@L49-L54
DISPOSITION: NODE bpW:w2:ext-an
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:ext-sums
KIND: external
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-sums@L55-L60
DISPOSITION: NODE bpW:w2:ext-sums
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w2:ext-trig
KIND: external
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64
DISPOSITION: NODE bpW:w2:ext-trig
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w2:derived
KIND: definition
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L70-L76
DISPOSITION: NODE bpW:w2:derived
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:functionals
KIND: lemma
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L81-L92
DISPOSITION: NODE bpW:w2:functionals
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:features
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102
DISPOSITION: NODE stepW:w2:features
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:pairing
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107
DISPOSITION: NODE stepW:w2:pairing
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:norms
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113
DISPOSITION: NODE stepW:w2:norms
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:xder
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119
DISPOSITION: NODE stepW:w2:xder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:bdry
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123
DISPOSITION: NODE stepW:w2:bdry
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:force
KIND: lemma
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L128-L137
DISPOSITION: NODE bpW:w2:force
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:fsum
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
DISPOSITION: NODE stepW:w2:fsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:flin
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
DISPOSITION: NODE stepW:w2:flin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:fcub
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
DISPOSITION: NODE stepW:w2:fcub
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w2:coeffsol
KIND: definition
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L166-L174
DISPOSITION: NODE bpW:w2:coeffsol
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:orbit
KIND: lemma
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L178-L190
DISPOSITION: NODE bpW:w2:orbit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:oan
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195
DISPOSITION: NODE stepW:w2:oan
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:oshift
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201
DISPOSITION: NODE stepW:w2:oshift
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:curve-deriv
KIND: lemma
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L206-L210
DISPOSITION: NODE bpW:w2:curve-deriv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:cdiff
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
DISPOSITION: NODE stepW:w2:cdiff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:ccoord
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
DISPOSITION: NODE stepW:w2:ccoord
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w2:hidden
KIND: claim
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hidden@L223-L229
DISPOSITION: EXCLUDED
REASON: administrative remark (regularity hidden in the hypotheses; the proofs use only the coordinate form); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:curve
KIND: theorem
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L233-L249
DISPOSITION: NODE bpW:w2:curve
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:joint
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262
DISPOSITION: NODE stepW:w2:joint
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:t1
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
DISPOSITION: NODE stepW:w2:t1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:t2
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
DISPOSITION: NODE stepW:w2:t2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:x
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280
DISPOSITION: NODE stepW:w2:x
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:frozen
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289
DISPOSITION: NODE stepW:w2:frozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:bound
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295
DISPOSITION: NODE stepW:w2:bound
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:main
KIND: theorem
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L303-L321
DISPOSITION: NODE bpW:w2:main
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: stepW:w2:mred
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
DISPOSITION: NODE stepW:w2:mred
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w2:mconc
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331
DISPOSITION: NODE stepW:w2:mconc
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:hyp
KIND: claim
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hyp@L336-L345
DISPOSITION: EXCLUDED
REASON: administrative remark (how W8 supplies (H1)-(H3); Lean statement may weaken (H1)); re-examine when W8 is added
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:clause5
KIND: corollary
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L347-L353
DISPOSITION: NODE bpW:w2:clause5
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w2:constants
KIND: claim
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:constants@L363-L371
DISPOSITION: EXCLUDED
REASON: administrative remark (order of constants; the value of M_m); the constant choice is Corollary bpW:w2:clause5
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: heading:bpW:w2
KIND: heading
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: heading:bpW:w2:ext
KIND: heading
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext@L35-L35
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: heading:bpW:w2:functionals-sec
KIND: heading
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals-sec@L68-L68
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: heading:bpW:w2:orbit-sec
KIND: heading
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit-sec@L164-L164
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: heading:bpW:w2:curve-sec
KIND: heading
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-sec@L231-L231
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: heading:bpW:w2:main-sec
KIND: heading
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main-sec@L301-L301
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: heading:bpW:w2:summary
KIND: heading
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:summary@L373-L373
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L77
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L77-L77
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L125
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L125-L125
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L161
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L161-L161
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L175
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L175-L175
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L203
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L203-L203
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L221
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L221-L221
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L297
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L297-L297
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L333
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L333-L333
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:source-L361
KIND: citation
SOURCE: blueprint-W/parts/w2-reconstruction.tex#source@L361-L361
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L3-L12
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L3-L12
DISPOSITION: EXCLUDED
REASON: introduction and outline (what W2 delivers; pointer to Corollary bpW:w2:clause5)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L14-L23
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L14-L23
DISPOSITION: EXCLUDED
REASON: route paragraph (outline of the proof)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L25-L33
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L25-L33
DISPOSITION: NODE bpW:w2:functionals, bpW:w2:force, bpW:w2:coeffsol, bpW:w2:curve, bpW:w2:main
REASON: standing data: notation identifying lambda, phi, U_m, V_m, G, kappa with the frozen lam, sineMode, reconU, reconV, cubicGrad, coeff (each consumer has the anchor edge where it uses the symbol); max norm on WaveSpace is ext-sums (norm_fst_le, norm_snd_le)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L37-L39
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L37-L39
DISPOSITION: EXCLUDED
REASON: introduction of the external list (pointer to W1's externals)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L65-L66
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L65-L66
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L375-L381
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L375-L381
DISPOSITION: EXCLUDED
REASON: Lean totality notes (administrative; the summability facts they recall are proved in Lemmas bpW:w2:functionals, bpW:w2:force)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L383-L392
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L383-L392
DISPOSITION: EXCLUDED
REASON: comparison with the source (provenance; errata N-4 already in W0)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: w2-reconstruction:prose-L394-L403
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#prose@L394-L403
DISPOSITION: EXCLUDED
REASON: summary of results and inputs (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2

ITEM: bpW:w3:ext-multilinear
KIND: external
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-multilinear@L42-L48
DISPOSITION: NODE bpW:w3:ext-multilinear
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:ext-series
KIND: external
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-series@L49-L59
DISPOSITION: NODE bpW:w3:ext-series
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:ext-tsum
KIND: external
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-tsum@L60-L68
DISPOSITION: NODE bpW:w3:ext-tsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:ext-mvt
KIND: external
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-mvt@L69-L72
DISPOSITION: NODE bpW:w3:ext-mvt
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:ext-integral
KIND: external
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-integral@L73-L82
DISPOSITION: NODE bpW:w3:ext-integral
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:ext-neumann
KIND: external
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-neumann@L83-L86
DISPOSITION: NODE bpW:w3:ext-neumann
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:ext-flows
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-flows@L89-L103
DISPOSITION: EXCLUDED
REASON: remark stating what Mathlib does not provide and that W3 does not use Lemma bpW:w1:flow or ODE uniqueness; not an external input
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:space
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L108-L116
DISPOSITION: NODE bpW:w3:space
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:coords
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L119-L128
DISPOSITION: NODE bpW:w3:coords
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:omega
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L139-L145
DISPOSITION: NODE bpW:w3:omega
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:hamfield-def
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162
DISPOSITION: NODE bpW:w3:hamfield-def
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w3:real-restrict
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L171-L177
DISPOSITION: NODE bpW:w3:real-restrict
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:forms
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L189-L197
DISPOSITION: NODE bpW:w3:forms
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:Lambda
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L200-L206
DISPOSITION: NODE bpW:w3:Lambda
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:w1-requests
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:w1-requests@L215-L220
DISPOSITION: EXCLUDED
REASON: administrative remark (requests to W1)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:majorant
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L232-L239
DISPOSITION: NODE bpW:w3:majorant
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:quartic
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L248-L259
DISPOSITION: NODE bpW:w3:quartic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:maj
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265
DISPOSITION: NODE stepW:w3:maj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:gradbound
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269
DISPOSITION: NODE stepW:w3:gradbound
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:identify
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277
DISPOSITION: NODE stepW:w3:identify
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:quartic-ident
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L282-L291
DISPOSITION: NODE bpW:w3:quartic-ident
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Gz
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
DISPOSITION: NODE stepW:w3:Gz
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:XG
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301
DISPOSITION: NODE stepW:w3:XG, stepW:w3:XG#via-w0-gradient, stepW:w3:XG#via-w1-gradient
REASON: the step and its two alternative derivations (route nodes added by sol-review-W-w3)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:Gnor
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L302-L303
DISPOSITION: NODE stepW:w3:Gnor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:count
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L304-L308
DISPOSITION: NODE stepW:w3:count
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:res
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L309-L311
DISPOSITION: NODE stepW:w3:res
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:divisor
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L317-L323
DISPOSITION: NODE bpW:w3:divisor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:sel
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L329-L332
DISPOSITION: NODE stepW:w3:sel
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:signs
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L333-L336
DISPOSITION: NODE stepW:w3:signs
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:s0
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L337-L338
DISPOSITION: NODE stepW:w3:s0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:s1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L339-L343
DISPOSITION: NODE stepW:w3:s1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:s23
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L344-L348
DISPOSITION: NODE stepW:w3:s23
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:s1inner
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L349-L359
DISPOSITION: NODE stepW:w3:s1inner
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:divconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L360-L363
DISPOSITION: NODE stepW:w3:divconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:Fdef
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L385-L391
DISPOSITION: NODE bpW:w3:Fdef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:F
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L396-L403
DISPOSITION: NODE bpW:w3:F
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:fcoef
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L406-L409
DISPOSITION: NODE stepW:w3:fcoef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Fconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L410-L413
DISPOSITION: NODE stepW:w3:Fconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:homological
KIND: proposition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L417-L422
DISPOSITION: NODE bpW:w3:homological
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Xfcoord
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L425-L427
DISPOSITION: NODE stepW:w3:Xfcoord
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:euler
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L428-L433
DISPOSITION: NODE stepW:w3:euler
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:divide
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L434-L438
DISPOSITION: NODE stepW:w3:divide
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:lie-coeff
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L451-L456
DISPOSITION: NODE bpW:w3:lie-coeff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w3:leibniz
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L460-L470
DISPOSITION: NODE bpW:w3:leibniz
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:rec
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L473-L475
DISPOSITION: NODE stepW:w3:rec
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:norms
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L476-L480
DISPOSITION: NODE stepW:w3:norms
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Phireal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L481-L482
DISPOSITION: NODE stepW:w3:Phireal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:leib
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L483-L486
DISPOSITION: NODE stepW:w3:leib
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:leibid
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L487-L490
DISPOSITION: NODE stepW:w3:leibid
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:flow
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L494-L517
DISPOSITION: NODE bpW:w3:flow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:conv
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L520-L527
DISPOSITION: NODE stepW:w3:conv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:floweq
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L528-L531
DISPOSITION: NODE stepW:w3:floweq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:transport
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L532-L534
DISPOSITION: NODE stepW:w3:transport
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:est
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L535-L541
DISPOSITION: NODE stepW:w3:est
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:Greal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L542-L543
DISPOSITION: NODE stepW:w3:Greal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:var
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L544-L547
DISPOSITION: NODE stepW:w3:var
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:inv
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L548-L555
DISPOSITION: NODE stepW:w3:inv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w3:symplectic
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L569-L576
DISPOSITION: NODE bpW:w3:symplectic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:skew
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L579-L582
DISPOSITION: NODE stepW:w3:skew
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:constform
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L583-L587
DISPOSITION: NODE stepW:w3:constform
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:gradtrans
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592
DISPOSITION: NODE stepW:w3:gradtrans
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w3:Yseries
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L611-L619
DISPOSITION: NODE bpW:w3:Yseries
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:majcalc
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L623-L634
DISPOSITION: NODE stepW:w3:majcalc
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majflow
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L635-L637
DISPOSITION: NODE stepW:w3:majflow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majA
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L638-L644
DISPOSITION: NODE stepW:w3:majA
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majN
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L645-L651
DISPOSITION: NODE stepW:w3:majN
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majX
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L652-L655
DISPOSITION: NODE stepW:w3:majX
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majY
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661
DISPOSITION: NODE stepW:w3:majY
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majint
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L662-L665
DISPOSITION: NODE stepW:w3:majint
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majps
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668
DISPOSITION: NODE stepW:w3:majps
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:majreal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L669-L672
DISPOSITION: NODE stepW:w3:majreal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w3:main
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L677-L695
DISPOSITION: NODE bpW:w3:main
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Kanalytic
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L700-L703
DISPOSITION: NODE stepW:w3:Kanalytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:K1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L704-L707
DISPOSITION: NODE stepW:w3:K1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:K2
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L708-L713
DISPOSITION: NODE stepW:w3:K2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:XK1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L714-L721
DISPOSITION: NODE stepW:w3:XK1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:XK2
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L722-L731
DISPOSITION: NODE stepW:w3:XK2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:XKconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L732-L736
DISPOSITION: NODE stepW:w3:XKconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:iii
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L737-L738
DISPOSITION: NODE stepW:w3:iii
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: stepW:w3:conj
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745
DISPOSITION: NODE stepW:w3:conj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:w3:class-remark
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L761-L768
DISPOSITION: EXCLUDED
REASON: administrative remark (summary of the regularity class; the facts are proved in Theorems bpW:w3:flow, bpW:w3:main and Lemma bpW:w3:Yseries)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:gamma-real
KIND: corollary
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L770-L784
DISPOSITION: NODE bpW:w3:gamma-real
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:transport-tori
KIND: corollary
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L800-L807
DISPOSITION: NODE bpW:w3:transport-tori
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:interface
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:interface@L818-L861
DISPOSITION: EXCLUDED
REASON: administrative remark (what W3 supplies to W4-W6); no wave-1 proof consumes it; re-examine when W4-W6 are added
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:ext
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext@L35-L35
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:coords-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords-sec@L106-L106
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:quartic-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L222-L222
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:divisor-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor-sec@L315-L315
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:F-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F-sec@L383-L383
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:flow-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow-sec@L449-L449
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:main-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L596-L596
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:interface-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:interface-sec@L816-L816
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:constants
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:constants@L865-L865
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:status
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:status@L889-L889
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:sourcegap-L366
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#sourcegap@L366-L375
DISPOSITION: NODE stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner
REASON: two incorrect steps of P96-W Lemma 4's printed proof; the blueprint's own proof repairs them (constant 1/27)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:sourcegap-L750
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#sourcegap@L750-L759
DISPOSITION: NODE stepW:w3:K2, stepW:w3:XK2
REASON: P96-W leaves implicit the application of its conditional facts to the remainder; the blueprint gives it via the homological identity
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L117
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L117-L117
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L137
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L137-L137
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L152
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L152-L152
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L168
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L168-L168
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L187
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L187-L187
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L198
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L198-L198
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L213
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L213-L213
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L246
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L246-L246
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L279
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L279-L279
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L313
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L313-L313
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L365
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L365-L365
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L392
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L392-L392
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L415
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L415-L415
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L440
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L440-L440
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L457
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L457-L457
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L492
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L492-L492
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L557
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L557-L557
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L594
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L594-L594
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L674
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L674-L674
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L747
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L747-L747
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L797
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L797-L797
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L814
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L814-L814
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L862
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L862-L862
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L3-L13
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L3-L13
DISPOSITION: EXCLUDED
REASON: introduction and outline
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L15-L21
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L15-L21
DISPOSITION: EXCLUDED
REASON: route paragraph (outline)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L23-L27
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L23-L27
DISPOSITION: NODE bpW:w3#data
REASON: standing data of W3 (a >= 0, p >= 1/2, J)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L29-L33
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L29-L33
DISPOSITION: EXCLUDED
REASON: pointer to the W1 inputs (each use is an edge at its consumer)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L38-L39
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L38-L39
DISPOSITION: EXCLUDED
REASON: introduction of the external list
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L164-L167
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L164-L167
DISPOSITION: NODE bpW:w3:hamfield-def#hamilton
REASON: Hamilton's equations on real points and reality of X_P, consumed by Steps stepW:w3:XG, stepW:w3:XKconcl
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L224-L230
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L224-L230
DISPOSITION: NODE bpW:w3:quartic-sec#data
REASON: notation frak g, delta, pairing, T
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L377-L381
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L377-L381
DISPOSITION: EXCLUDED
REASON: unlabelled remark (sharpness and asymptotics of delta_*); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L443-L447
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L443-L447
DISPOSITION: EXCLUDED
REASON: unlabelled remark (why the identity is stated with DLambda); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L563-L567
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L563-L567
DISPOSITION: EXCLUDED
REASON: unlabelled remark (identification with the ODE solution, explicitly not used)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L598-L600
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L598-L600
DISPOSITION: NODE bpW:w3:main-sec#data
REASON: H = Lambda + G on W and X_H
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L602-L609
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L602-L609
DISPOSITION: NODE bpW:w3:main-sec#data
REASON: the integrand Y(t,w) (bpW:w3:Ydef)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L867-L887
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L867-L887
DISPOSITION: EXCLUDED
REASON: constants table and Lean totality notes (summary; each constant is defined and bounded in its result)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L891-L904
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L891-L904
DISPOSITION: EXCLUDED
REASON: status summary (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L326-L328
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L326-L328
DISPOSITION: NODE stepW:w3:divisor#curvature
REASON: quantitative second-derivative and beta bounds used by the sign cases, previously absent from the inventory
COVERAGE_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w3
REVIEWER: -

ITEM: bpW:wh:lintorus
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:lintorus@L18-L20
DISPOSITION: NODE bpW:w0:periodone#linearTorus
REASON: restates Convention bpW:w0:periodone; the frozen KAM.Wave.linearTorus is bound to that node
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:embedding#IsAnalyticTorusEmbedding
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:embedding@L22-L27
DISPOSITION: NODE bpW:wh:embedding#IsAnalyticTorusEmbedding
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:Dnu
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:Dnu@L29-L31
DISPOSITION: NODE bpW:wh:nlw2
REASON: notation D_nu K = DK nu used in (4); the frozen statement inlines it as a HasDerivAt along t -> theta + t nu at t = 0
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:dioph#IsDiophantine
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:dioph@L33-L37
DISPOSITION: NODE bpW:wh:dioph#IsDiophantine
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:nlw2
KIND: theorem
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L41-L65
DISPOSITION: NODE bpW:wh:nlw2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:reading
KIND: claim
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:reading@L67-L89
DISPOSITION: EXCLUDED
REASON: administrative remark (reading of the statement: quantifier order, recorded in the SOURCE_QUANTIFIERS and CONSTANT_SCOPE of bpW:wh:nlw2; pointers to W2/W8; deviations); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:weakenings
KIND: claim
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:weakenings@L91-L101
DISPOSITION: EXCLUDED
REASON: administrative remark (declared weakenings W-A2, D30 Q3); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: heading:bpW:wh
KIND: heading
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: heading:bpW:wh:defs
KIND: heading
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:defs@L11-L11
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: heading:bpW:wh:statement
KIND: heading
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:statement@L39-L39
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: w-headline:source-L102
KIND: citation
SOURCE: blueprint-W/parts/w-headline.tex#source@L102-L102
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: w-headline:prose-L3-L3
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L3-L3
DISPOSITION: EXCLUDED
REASON: status line (\proposed), superseded by the owner freeze D41
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: w-headline:prose-L5-L9
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L5-L9
DISPOSITION: EXCLUDED
REASON: introduction (provenance, D30)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: w-headline:prose-L13-L16
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L13-L16
DISPOSITION: NODE bpW:wh:nlw2
REASON: fixes the data of the statement (m, a = p = 1, E, U_m, V_m, G_q, P, r(I), B_h)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: K:bp:p1:decay
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay@L786-L789
DISPOSITION: NODE K:bp:p1:decay
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: K:bp:p1:fourier-basic
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L757-L768
DISPOSITION: NODE K:bp:p1:fourier-basic
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: K:bp:p1:holomorphic-analytic
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L296-L312
DISPOSITION: NODE K:bp:p1:holomorphic-analytic
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: K:bp:p1:strip-identity
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
DISPOSITION: NODE K:bp:p1:strip-identity
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: K:step:p1:dec-shift
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#step:p1:dec-shift@L800-L811
DISPOSITION: NODE K:step:p1:dec-shift
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
