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
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:twosided@L66-L75
DISPOSITION: NODE bpW:w0:twosided
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:reconstruction#reconU
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L79-L85
DISPOSITION: NODE bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#rescaling
REASON: reconstruction formula plus the inverse coefficient dictionary and symplectic rescaling
COVERAGE_STATUS: REVIEWED
EXTRACTOR: sol-review-W-w0c
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:reconstruction#reconV
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L79-L85
DISPOSITION: NODE bpW:w0:reconstruction#reconV
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c

ITEM: bpW:w0:H
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L91-L98
DISPOSITION: NODE bpW:w0:H
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:Gq#cubicGrad
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L102-L109
DISPOSITION: NODE bpW:w0:Gq#cubicGrad
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:eqmotion
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L111-L120
DISPOSITION: NODE bpW:w0:eqmotion
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:z
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L126-L131
DISPOSITION: NODE bpW:w0:z
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:actions
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L135-L142
DISPOSITION: NODE bpW:w0:actions
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:periodone#linearTorus
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L144-L152
DISPOSITION: NODE bpW:w0:periodone#linearTorus
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: bpW:w0:harmless
KIND: claim
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:harmless@L183-L188
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
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:hamiltonian@L77-L77
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:complex
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:complex@L124-L124
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: heading:bpW:w0:table
KIND: heading
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:table@L154-L154
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
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L86-L86
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L93
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L99-L99
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L113
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L121-L121
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:source-L124
KIND: citation
SOURCE: blueprint-W/parts/w0-conventions.tex#source@L132-L132
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
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L88-L89
DISPOSITION: EXCLUDED
REASON: forward pointer to Lemma bpW:w0n:recon-bounded
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L148-L149
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L156-L157
DISPOSITION: EXCLUDED
REASON: introduction of the comparison table (provenance)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L151-L172
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L159-L180
DISPOSITION: EXCLUDED
REASON: comparison table with the printed conventions of P96-W/KP96 (provenance and errata E-PDE-W-1/2); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0c

ITEM: w0-conventions:prose-L174-L174
KIND: proof-region
SOURCE: blueprint-W/parts/w0-conventions.tex#prose@L182-L182
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
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:coeffsys@L114-L116
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
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L76-L83
DISPOSITION: NODE bpW:w0n:gradient
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:algebra
KIND: lemma
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L95-L99
DISPOSITION: NODE bpW:w0n:algebra
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:weight
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L103-L107
DISPOSITION: NODE stepW:w0n:weight
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:young
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L108-L113
DISPOSITION: NODE stepW:w0n:young
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:cubic-bound
KIND: theorem
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L119-L131
DISPOSITION: NODE bpW:w0n:cubic-bound
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:majorant
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L134-L137
DISPOSITION: NODE stepW:w0n:majorant
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:selection
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L138-L143
DISPOSITION: NODE stepW:w0n:selection
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:smoothing
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L144-L150
DISPOSITION: NODE stepW:w0n:smoothing
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:analytic
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L151-L156
DISPOSITION: NODE stepW:w0n:analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:pde-equiv
KIND: proposition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L167-L185
DISPOSITION: NODE bpW:w0n:pde-equiv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:force
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L194
DISPOSITION: NODE stepW:w0n:force
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:time
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L195-L200
DISPOSITION: NODE stepW:w0n:time
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:ident
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L201-L203
DISPOSITION: NODE stepW:w0n:ident
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:converse
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L204-L210
DISPOSITION: NODE stepW:w0n:converse
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:nonres
KIND: lemma
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L222-L226
DISPOSITION: NODE bpW:w0n:nonres
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:31
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L234
DISPOSITION: NODE stepW:w0n:31
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:22
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L235-L248
DISPOSITION: NODE stepW:w0n:22
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:nonres-remark
KIND: claim
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres-remark@L250-L256
DISPOSITION: EXCLUDED
REASON: administrative remark (qualitative versus quantitative nonresonance; pointer to W3's bpW:w3:divisor); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:Qdef
KIND: definition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L272-L275
DISPOSITION: NODE bpW:w0n:Qdef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: bpW:w0n:AB
KIND: theorem
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L277-L288
DISPOSITION: NODE bpW:w0n:AB
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:resavg
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L291-L296
DISPOSITION: NODE stepW:w0n:resavg
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:moments
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L297-L300
DISPOSITION: NODE stepW:w0n:moments
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n

ITEM: stepW:w0n:sum
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L301-L306
DISPOSITION: NODE stepW:w0n:sum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:formal-birkhoff
KIND: proposition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L309-L317
DISPOSITION: NODE bpW:w0n:formal-birkhoff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:compare
KIND: claim
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:compare@L332-L339
DISPOSITION: EXCLUDED
REASON: administrative remark (comparison with the printed P96-W coefficients, E-PDE-W-1); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:nondeg
KIND: theorem
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L348-L355
DISPOSITION: NODE bpW:w0n:nondeg
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:det
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L358-L361
DISPOSITION: NODE stepW:w0n:det
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta2-W-w0n

ITEM: stepW:w0n:A2
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L362-L364
DISPOSITION: NODE stepW:w0n:A2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta2-W-w0n

ITEM: stepW:w0n:A3red
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L365-L370
DISPOSITION: NODE stepW:w0n:A3red
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta2-W-w0n

ITEM: stepW:w0n:l1
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L371-L374
DISPOSITION: NODE stepW:w0n:l1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: stepW:w0n:l2
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L375-L378
DISPOSITION: NODE stepW:w0n:l2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:kappa
KIND: claim
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:kappa@L385-L389
DISPOSITION: EXCLUDED
REASON: administrative remark (P96-W's exponent kappa = 2 is unchanged by the correction); the spectral asymptotics used later are proved in bpW:w1:tails; no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: bpW:w0n:duffing
KIND: proposition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L393-L402
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
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde@L165-L165
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:nonres-sec
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres-sec@L220-L220
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:birkhoff
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L258-L258
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:nondeg-sec
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L341-L341
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:duffing-sec
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing-sec@L391-L391
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: heading:bpW:w0n:ledger
KIND: heading
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:ledger@L417-L417
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:sourcegap-L159
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#sourcegap@L161-L163
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
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L115-L115
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L156
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L158-L158
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L210
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L212-L212
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L324
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L326-L326
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:source-L378
KIND: citation
SOURCE: blueprint-W/parts/w0-normalization.tex#source@L380-L380
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
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L213-L218
DISPOSITION: EXCLUDED
REASON: provenance note (expansion of P96-W Lemma 1, errata N-4); the completeness of (phi_l) it mentions is the edge stepW:w0n:force -> bpW:w1:sine-completeness
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L258-L268
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L260-L270
DISPOSITION: NODE bpW:w0n:birkhoff#data
REASON: fixes the quartic part in z-coordinates (bpW:w0n:Gz), resonance and the split G^tan + G^nor
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L341-L344
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L343-L346
DISPOSITION: NODE bpW:w0n:nondeg-sec#data
REASON: defines (A1)-(A3)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L408-L413
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L410-L415
DISPOSITION: EXCLUDED
REASON: remark on a numerical check (scripts/wave/w0_checks.py); not a mathematical input
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w0n

ITEM: w0-normalization:prose-L417-L429
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#prose@L419-L431
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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

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
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L131-L145
DISPOSITION: NODE bpW:w1:space
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:iso
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L148-L152
DISPOSITION: NODE stepW:w1:iso
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:sep
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L153-L156
DISPOSITION: NODE stepW:w1:sep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:coord
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L157-L159
DISPOSITION: NODE stepW:w1:coord
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:frozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L160-L162
DISPOSITION: NODE stepW:w1:frozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:coordinatewise
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L167-L177
DISPOSITION: NODE bpW:w1:coordinatewise
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:coordder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L180-L183
DISPOSITION: NODE stepW:w1:coordder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:coordcomp
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L184-L188
DISPOSITION: NODE stepW:w1:coordcomp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:multiplier
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L192-L198
DISPOSITION: NODE bpW:w1:multiplier
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:embed
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L207-L216
DISPOSITION: NODE bpW:w1:embed
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:diag
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L226-L241
DISPOSITION: NODE bpW:w1:diag
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:ratio
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L244-L248
DISPOSITION: NODE stepW:w1:ratio
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:rot
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L249-L252
DISPOSITION: NODE stepW:w1:rot
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:realflow
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L253-L257
DISPOSITION: NODE stepW:w1:realflow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:linfty
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:linfty@L263-L270
DISPOSITION: NODE bpW:w1:linfty
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:tails
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L273-L282
DISPOSITION: NODE bpW:w1:tails
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:twosided-transport
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L297-L303
DISPOSITION: NODE bpW:w1:twosided-transport
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:twosided
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L306-L322
DISPOSITION: NODE bpW:w1:twosided
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:ext
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L325-L329
DISPOSITION: NODE stepW:w1:ext
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:restr
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L330-L334
DISPOSITION: NODE stepW:w1:restr
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:pair
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L335-L336
DISPOSITION: NODE stepW:w1:pair
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:young
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L341-L351
DISPOSITION: NODE bpW:w1:young
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:cs
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L354-L357
DISPOSITION: NODE stepW:w1:cs
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:youngsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L358-L360
DISPOSITION: NODE stepW:w1:youngsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:l1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L361-L364
DISPOSITION: NODE stepW:w1:l1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:rules
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L365-L368
DISPOSITION: NODE stepW:w1:rules
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: bpW:w1:algebra
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L372-L375
DISPOSITION: NODE bpW:w1:algebra
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:algebra-half
KIND: claim
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra-half@L385-L389
DISPOSITION: EXCLUDED
REASON: administrative remark (the algebra for 1/2 < s < 1 is not part of the plan; no later milestone needs it)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:selection
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L398-L412
DISPOSITION: NODE bpW:w1:selection
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:maj1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L415-L417
DISPOSITION: NODE stepW:w1:maj1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:sel1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L418-L423
DISPOSITION: NODE stepW:w1:sel1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:smooth1
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L424-L426
DISPOSITION: NODE stepW:w1:smooth1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:maj2
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L427-L430
DISPOSITION: NODE stepW:w1:maj2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:sel2
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L431-L434
DISPOSITION: NODE stepW:w1:sel2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:smooth2
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L435-L438
DISPOSITION: NODE stepW:w1:smooth2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:trilinear
KIND: theorem
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L443-L462
DISPOSITION: NODE bpW:w1:trilinear
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:tricoord
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L465-L470
DISPOSITION: NODE stepW:w1:tricoord, stepW:w1:tricoord#via-cubic-bound, stepW:w1:tricoord#via-selection
REASON: the step and its two alternative derivations (route nodes)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:tricont
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L471-L474
DISPOSITION: NODE stepW:w1:tricont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:trireal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L475-L478
DISPOSITION: NODE stepW:w1:trireal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:trifrozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L479-L483
DISPOSITION: NODE stepW:w1:trifrozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:cubic-analytic
KIND: corollary
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L487-L501
DISPOSITION: NODE bpW:w1:cubic-analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:can
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L504-L505
DISPOSITION: NODE stepW:w1:can
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:cder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L506-L510
DISPOSITION: NODE stepW:w1:cder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:clip
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L511-L513
DISPOSITION: NODE stepW:w1:clip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:cfrozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L514-L516
DISPOSITION: NODE stepW:w1:cfrozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:gradient-identity
KIND: proposition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L521-L534
DISPOSITION: NODE bpW:w1:gradient-identity
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:quartic
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L537-L542
DISPOSITION: NODE stepW:w1:quartic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:gradder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L543-L546
DISPOSITION: NODE stepW:w1:gradder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:gradw
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L547-L551
DISPOSITION: NODE stepW:w1:gradw
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:hamfield
KIND: proposition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L555-L575
DISPOSITION: NODE bpW:w1:hamfield
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:hlin
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L578-L579
DISPOSITION: NODE stepW:w1:hlin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:hnonlin
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L580-L582
DISPOSITION: NODE stepW:w1:hnonlin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: stepW:w1:hsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L583-L585
DISPOSITION: NODE stepW:w1:hsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:hham
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L586-L592
DISPOSITION: NODE stepW:w1:hham
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1a

ITEM: stepW:w1:hfrozen
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L593-L597
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
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:weighted@L129-L129
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1:twosided-sec
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-sec@L295-L295
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: heading:bpW:w1:cubic
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic@L391-L391
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
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L164-L164
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L181
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L190-L190
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L196
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L205-L205
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L215
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L224-L224
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L250
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L259-L259
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L262
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L271-L271
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L281
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L290-L290
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L295
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L304-L304
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L326
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L338-L338
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L358
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L370-L370
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L370
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L382-L382
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L428
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L440-L440
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L473
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L485-L485
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L506
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L518-L518
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L541
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L553-L553
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:source-L587
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L599-L599
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
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L126-L127
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: w1-sequences:prose-L381-L384
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L393-L396
DISPOSITION: EXCLUDED
REASON: pointer (motivation of Lemma bpW:w1:selection)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a

ITEM: bpW:w1:ext-rect
KIND: external
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-rect@L117-L125
DISPOSITION: NODE bpW:w1:ext-rect
REASON: labelled external item (W1-E9)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: -

ITEM: bpW:w1:sine-completeness
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L605-L608
DISPOSITION: NODE bpW:w1:sine-completeness
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:odd
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L611-L613
DISPOSITION: NODE stepW:w1:odd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:coeffs
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L614-L617
DISPOSITION: NODE stepW:w1:coeffs
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:basis
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L618-L621
DISPOSITION: NODE stepW:w1:basis
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:cont
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L622-L624
DISPOSITION: NODE stepW:w1:cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:sine-feature
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L629-L641
DISPOSITION: NODE bpW:w1:sine-feature
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:growth
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L644-L647
DISPOSITION: NODE stepW:w1:growth
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:normal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L648-L652
DISPOSITION: NODE stepW:w1:normal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:sinereal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L653-L656
DISPOSITION: NODE stepW:w1:sinereal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:recon-analytic
KIND: corollary
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L660-L682
DISPOSITION: NODE bpW:w1:recon-analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:bil
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L685-L688
DISPOSITION: NODE stepW:w1:bil
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:recanalytic
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L689-L694
DISPOSITION: NODE stepW:w1:recanalytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:recder
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L695-L703
DISPOSITION: NODE stepW:w1:recder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: bpW:w1:complexification
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification@L710-L715
DISPOSITION: NODE bpW:w1:complexification
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:complexification-lemma
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L719-L730
DISPOSITION: NODE bpW:w1:complexification-lemma
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:holomorphic
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holomorphic@L740-L746
DISPOSITION: NODE bpW:w1:holomorphic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:cauchy
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L749-L754
DISPOSITION: NODE bpW:w1:cauchy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:lines
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L757-L759
DISPOSITION: NODE stepW:w1:lines
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:onevar
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L760-L761
DISPOSITION: NODE stepW:w1:onevar
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:margins
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L762-L763
DISPOSITION: NODE stepW:w1:margins
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:deriv-continuous
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L767-L772
DISPOSITION: NODE bpW:w1:deriv-continuous
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:dcbound
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L775-L776
DISPOSITION: NODE stepW:w1:dcbound
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:dcintegral
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L777-L780
DISPOSITION: NODE stepW:w1:dcintegral
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:dclip
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L781-L786
DISPOSITION: NODE stepW:w1:dclip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:uniform-limit
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L790-L798
DISPOSITION: NODE bpW:w1:uniform-limit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:ulcauchy
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L801-L805
DISPOSITION: NODE stepW:w1:ulcauchy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:ullimit
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L806-L809
DISPOSITION: NODE stepW:w1:ullimit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:holo-analytic-fd
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L813-L823
DISPOSITION: NODE bpW:w1:holo-analytic-fd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:hamargin
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L826-L828
DISPOSITION: NODE stepW:w1:hamargin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:hacoef
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L829-L835
DISPOSITION: NODE stepW:w1:hacoef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:hagroup
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L836-L845
DISPOSITION: NODE stepW:w1:hagroup
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:hareal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L846-L847
DISPOSITION: NODE stepW:w1:hareal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:torus-analytic
KIND: corollary
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L851-L856
DISPOSITION: NODE bpW:w1:torus-analytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:flow
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L864-L878
DISPOSITION: NODE bpW:w1:flow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:flowlip
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L881-L883
DISPOSITION: NODE stepW:w1:flowlip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:picard
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L884-L887
DISPOSITION: NODE stepW:w1:picard
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:picardholo
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L888-L900
DISPOSITION: NODE stepW:w1:picardholo
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:flowlim
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L901-L906
DISPOSITION: NODE stepW:w1:flowlim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:flowreal
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L907-L908
DISPOSITION: NODE stepW:w1:flowreal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:flowpar
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L909-L913
DISPOSITION: NODE stepW:w1:flowpar
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: bpW:w1:kam-space
KIND: definition
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-space@L928-L940
DISPOSITION: NODE bpW:w1:kam-space
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:kam-conventions
KIND: claim
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L943-L949
DISPOSITION: EXCLUDED
REASON: administrative remark (conventions to carry into W4-W6: P96-K's z is the conjugate of W0's; sum versus max norm); no wave-1 proof consumes it; re-examine when W4-W6 are added
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:kam-domain
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L951-L955
DISPOSITION: NODE bpW:w1:kam-domain
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:fourier-l2
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L1000-L1011
DISPOSITION: NODE bpW:w1:fourier-l2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:shift
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L1014-L1016
DISPOSITION: NODE stepW:w1:shift
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:parseval
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L1017-L1021
DISPOSITION: NODE stepW:w1:parseval
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:orthants
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L1022-L1025
DISPOSITION: NODE stepW:w1:orthants
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w1b

ITEM: stepW:w1:fsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L1026-L1031
DISPOSITION: NODE stepW:w1:fsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:fourier-banach
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1038-L1054
DISPOSITION: NODE bpW:w1:fourier-banach
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbdual
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1057-L1060
DISPOSITION: NODE stepW:w1:fbdual
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbdecay
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1061-L1064
DISPOSITION: NODE stepW:w1:fbdecay
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbsum
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1065-L1066
DISPOSITION: NODE stepW:w1:fbsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:fbconv
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1067-L1070
DISPOSITION: NODE stepW:w1:fbconv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:lattice
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1075-L1089
DISPOSITION: NODE bpW:w1:lattice
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latprod
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1092-L1095
DISPOSITION: NODE stepW:w1:latprod
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latcount
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1096-L1098
DISPOSITION: NODE stepW:w1:latcount
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latweight
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1099-L1103
DISPOSITION: NODE stepW:w1:latweight
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:latdiv
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1104-L1106
DISPOSITION: NODE stepW:w1:latdiv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:operator-fourier
KIND: claim
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1110-L1146
DISPOSITION: EXCLUDED
REASON: administrative remark (counterexample to the operator-valued square-sum bound printed on P96-K p. 127 and what W4 must use instead); no wave-1 proof consumes it; re-examine when W4 is added
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:schur
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1152-L1163
DISPOSITION: NODE bpW:w1:schur
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:rows
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1166-L1169
DISPOSITION: NODE stepW:w1:rows
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:schurtest
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1170-L1172
DISPOSITION: NODE stepW:w1:schurtest
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:diagcomb
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1173-L1177
DISPOSITION: NODE stepW:w1:diagcomb
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: stepW:w1:schurweights
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1178-L1179
DISPOSITION: NODE stepW:w1:schurweights
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:sines
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sines@L603-L603
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:analytic
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:analytic@L708-L708
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:kam
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam@L926-L926
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: heading:bpW:w1:ledger
KIND: heading
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ledger@L1183-L1183
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:sourcegap-L906
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#sourcegap@L918-L924
DISPOSITION: NODE stepW:w1:flowpar
REASON: P96-K Lemma A.4's mean value step needs a segment in V; the blueprint repairs it by keeping both trajectories in the convex ball B(w,delta) (ball margin 2 delta, M < delta) in the parameter step
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:sourcegap-L1105
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#sourcegap@L1147-L1150
DISPOSITION: NODE bpW:w1:fourier-banach, bpW:w1:lattice
REASON: the false operator-valued square-sum bound of P96-K p. 127 is replaced by these lemmas; the homological estimate itself is W4's (later wave)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L614
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L626-L626
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L646
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L658-L658
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L693
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L705-L705
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L704
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L716-L716
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L726
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L738-L738
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L735
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L747-L747
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L753
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L765-L765
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L776
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L788-L788
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L799
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L811-L811
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L837
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L849-L849
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L850
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L862-L862
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L903
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L915-L915
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L929
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L941-L941
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L952
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L964-L964
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L991
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L1033-L1033
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L1030
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L1072-L1072
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L1066
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L1108-L1108
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:source-L1139
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L1181-L1181
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:prose-L1143-L1152
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L1185-L1194
DISPOSITION: EXCLUDED
REASON: ledger: PLAN-node mapping (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:prose-L1154-L1162
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L1196-L1205
DISPOSITION: EXCLUDED
REASON: ledger: added nodes and their consumers (administrative pointers)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: w1-sequences:prose-L1164-L1168
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#prose@L1207-L1211
DISPOSITION: EXCLUDED
REASON: ledger: source gaps and conventions (administrative; each gap is mapped at its \sourcegap item)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1b

ITEM: bpW:w1:fourier-shift
KIND: lemma
SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-shift@L967-L973
DISPOSITION: NODE bpW:w1:fourier-shift
REASON: labelled unit added by the blueprint cleanup (inp 99afc128)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: -

ITEM: stepW:w1:fshift-one
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-one@L976-L981
DISPOSITION: NODE stepW:w1:fshift-one
REASON: labelled unit added by the blueprint cleanup (inp 99afc128)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: -

ITEM: stepW:w1:fshift-iter
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-iter@L982-L991
DISPOSITION: NODE stepW:w1:fshift-iter
REASON: labelled unit added by the blueprint cleanup (inp 99afc128)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: -

ITEM: stepW:w1:fshift-end
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-end@L992-L995
DISPOSITION: NODE stepW:w1:fshift-end
REASON: labelled unit added by the blueprint cleanup (inp 99afc128)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: -

ITEM: w1-sequences:source-L997
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L997-L998
DISPOSITION: EXCLUDED
REASON: provenance note (K's step:p1:dec-shift has the same argument for a particular shift); not an input
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: -

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

ITEM: bpW:w2:ext-trig
KIND: external
SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64
DISPOSITION: NODE bpW:w2:ext-trig
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

ITEM: stepW:w2:fsum
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
DISPOSITION: NODE stepW:w2:fsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

ITEM: stepW:w2:flin
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
DISPOSITION: NODE stepW:w2:flin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

ITEM: stepW:w2:fcub
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
DISPOSITION: NODE stepW:w2:fcub
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

ITEM: stepW:w2:cdiff
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
DISPOSITION: NODE stepW:w2:cdiff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

ITEM: stepW:w2:ccoord
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
DISPOSITION: NODE stepW:w2:ccoord
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

ITEM: stepW:w2:t2
KIND: proof-region
SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
DISPOSITION: NODE stepW:w2:t2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w2

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:XG
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311
DISPOSITION: NODE stepW:w3:XG
REASON: labelled proof step (route nodes removed after the blueprint cleanup)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+claude-suborch-W-r2
REVIEWER: -

ITEM: stepW:w3:Gnor
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L312-L313
DISPOSITION: NODE stepW:w3:Gnor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:count
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L314-L318
DISPOSITION: NODE stepW:w3:count
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:res
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L319-L321
DISPOSITION: NODE stepW:w3:res
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:divisor
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L333
DISPOSITION: NODE bpW:w3:divisor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:sel
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L339-L342
DISPOSITION: NODE stepW:w3:sel
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:signs
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L343-L346
DISPOSITION: NODE stepW:w3:signs
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:s0
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L347-L348
DISPOSITION: NODE stepW:w3:s0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:s1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L349-L353
DISPOSITION: NODE stepW:w3:s1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:s23
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L354-L358
DISPOSITION: NODE stepW:w3:s23
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:s1inner
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L359-L369
DISPOSITION: NODE stepW:w3:s1inner
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:divconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L370-L373
DISPOSITION: NODE stepW:w3:divconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:Fdef
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L395-L401
DISPOSITION: NODE bpW:w3:Fdef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:F
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L406-L413
DISPOSITION: NODE bpW:w3:F
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:fcoef
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L416-L419
DISPOSITION: NODE stepW:w3:fcoef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Fconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L420-L423
DISPOSITION: NODE stepW:w3:Fconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:homological
KIND: proposition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L427-L432
DISPOSITION: NODE bpW:w3:homological
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Xfcoord
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L435-L437
DISPOSITION: NODE stepW:w3:Xfcoord
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:euler
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L438-L443
DISPOSITION: NODE stepW:w3:euler
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:divide
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L444-L448
DISPOSITION: NODE stepW:w3:divide
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:lie-coeff
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L461-L466
DISPOSITION: NODE bpW:w3:lie-coeff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: bpW:w3:leibniz
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L470-L480
DISPOSITION: NODE bpW:w3:leibniz
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:rec
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L483-L485
DISPOSITION: NODE stepW:w3:rec
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:norms
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L486-L490
DISPOSITION: NODE stepW:w3:norms
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Phireal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L491-L492
DISPOSITION: NODE stepW:w3:Phireal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:leib
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L493-L496
DISPOSITION: NODE stepW:w3:leib
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:leibid
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L497-L500
DISPOSITION: NODE stepW:w3:leibid
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:flow
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L504-L527
DISPOSITION: NODE bpW:w3:flow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:conv
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L530-L537
DISPOSITION: NODE stepW:w3:conv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:floweq
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L538-L541
DISPOSITION: NODE stepW:w3:floweq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:transport
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L542-L544
DISPOSITION: NODE stepW:w3:transport
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:est
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L545-L551
DISPOSITION: NODE stepW:w3:est
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:Greal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L552-L553
DISPOSITION: NODE stepW:w3:Greal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:var
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L554-L557
DISPOSITION: NODE stepW:w3:var
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:inv
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L558-L565
DISPOSITION: NODE stepW:w3:inv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: bpW:w3:symplectic
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L579-L586
DISPOSITION: NODE bpW:w3:symplectic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:skew
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L589-L592
DISPOSITION: NODE stepW:w3:skew
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:constform
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L593-L597
DISPOSITION: NODE stepW:w3:constform
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:gradtrans
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L598-L602
DISPOSITION: NODE stepW:w3:gradtrans
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: bpW:w3:Yseries
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L621-L629
DISPOSITION: NODE bpW:w3:Yseries
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:majcalc
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L633-L644
DISPOSITION: NODE stepW:w3:majcalc
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majflow
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L645-L647
DISPOSITION: NODE stepW:w3:majflow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majA
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L648-L654
DISPOSITION: NODE stepW:w3:majA
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majN
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L655-L661
DISPOSITION: NODE stepW:w3:majN
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majX
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L662-L665
DISPOSITION: NODE stepW:w3:majX
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majY
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671
DISPOSITION: NODE stepW:w3:majY
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majint
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L672-L675
DISPOSITION: NODE stepW:w3:majint
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majps
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678
DISPOSITION: NODE stepW:w3:majps
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:majreal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L679-L682
DISPOSITION: NODE stepW:w3:majreal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: bpW:w3:main
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L687-L705
DISPOSITION: NODE bpW:w3:main
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: stepW:w3:Kanalytic
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L710-L713
DISPOSITION: NODE stepW:w3:Kanalytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:K1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L714-L717
DISPOSITION: NODE stepW:w3:K1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:K2
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L718-L723
DISPOSITION: NODE stepW:w3:K2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:XK1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L724-L731
DISPOSITION: NODE stepW:w3:XK1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:XK2
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L732-L741
DISPOSITION: NODE stepW:w3:XK2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:XKconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L742-L746
DISPOSITION: NODE stepW:w3:XKconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:iii
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L747-L748
DISPOSITION: NODE stepW:w3:iii
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: stepW:w3:conj
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755
DISPOSITION: NODE stepW:w3:conj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-w3

ITEM: bpW:w3:class-remark
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
DISPOSITION: EXCLUDED
REASON: administrative remark (summary of the regularity class; the facts are proved in Theorems bpW:w3:flow, bpW:w3:main and Lemma bpW:w3:Yseries)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:gamma-real
KIND: corollary
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L780-L794
DISPOSITION: NODE bpW:w3:gamma-real
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:transport-tori
KIND: corollary
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L810-L817
DISPOSITION: NODE bpW:w3:transport-tori
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: bpW:w3:interface
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:interface@L828-L872
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
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor-sec@L325-L325
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:F-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F-sec@L393-L393
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:flow-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow-sec@L459-L459
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:main-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L606-L606
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:interface-sec
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:interface-sec@L826-L826
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:constants
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:constants@L876-L876
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:status
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:status@L900-L900
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:sourcegap-L366
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#sourcegap@L376-L385
DISPOSITION: NODE stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner
REASON: two incorrect steps of P96-W Lemma 4's printed proof; the blueprint's own proof repairs them (constant 1/27)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:sourcegap-L750
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#sourcegap@L760-L769
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
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L323-L323
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L365
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L375-L375
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L392
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L402-L402
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L415
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L425-L425
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L440
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L450-L450
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L457
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L467-L467
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L492
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L502-L502
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L557
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L567-L567
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L594
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L604-L604
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L674
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L684-L684
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L747
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L757-L757
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L797
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L807-L807
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L814
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L824-L824
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:source-L862
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L873-L873
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
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L387-L391
DISPOSITION: EXCLUDED
REASON: unlabelled remark (sharpness and asymptotics of delta_*); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L443-L447
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L453-L457
DISPOSITION: EXCLUDED
REASON: unlabelled remark (why the identity is stated with DLambda); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L563-L567
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L573-L577
DISPOSITION: EXCLUDED
REASON: unlabelled remark (identification with the ODE solution, explicitly not used)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L598-L600
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L608-L610
DISPOSITION: NODE bpW:w3:main-sec#data
REASON: H = Lambda + G on W and X_H
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L602-L609
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L612-L619
DISPOSITION: NODE bpW:w3:main-sec#data
REASON: the integrand Y(t,w) (bpW:w3:Ydef)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L867-L887
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L878-L898
DISPOSITION: EXCLUDED
REASON: constants table and Lean totality notes (summary; each constant is defined and bounded in its result)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L891-L904
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L902-L915
DISPOSITION: EXCLUDED
REASON: status summary (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L326-L328
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L336-L338
DISPOSITION: NODE stepW:w3:divisor#curvature
REASON: quantitative second-derivative and beta bounds used by the sign cases, previously absent from the inventory
COVERAGE_STATUS: REVIEWED
EXTRACTOR: sol-review-W-w3
REVIEWER: sol-delta-W-w3

ITEM: bpW:wh:lintorus
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:lintorus@L24-L26
DISPOSITION: NODE bpW:w0:periodone#linearTorus
REASON: restates Convention bpW:w0:periodone; the frozen KAM.Wave.linearTorus is bound to that node
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:embedding#IsAnalyticTorusEmbedding
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:embedding@L28-L33
DISPOSITION: NODE bpW:wh:embedding#IsAnalyticTorusEmbedding
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:Dnu
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:Dnu@L35-L37
DISPOSITION: NODE bpW:wh:nlw2
REASON: notation D_nu K = DK nu used in (4); the frozen statement inlines it as a HasDerivAt along t -> theta + t nu at t = 0
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:dioph#IsDiophantine
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:dioph@L39-L43
DISPOSITION: NODE bpW:wh:dioph#IsDiophantine
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:nlw2
KIND: theorem
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L47-L71
DISPOSITION: NODE bpW:wh:nlw2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:reading
KIND: claim
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:reading@L73-L95
DISPOSITION: EXCLUDED
REASON: administrative remark (reading of the statement: quantifier order, recorded in the SOURCE_QUANTIFIERS and CONSTANT_SCOPE of bpW:wh:nlw2; pointers to W2/W8; deviations); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: bpW:wh:weakenings
KIND: claim
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:weakenings@L97-L107
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
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:defs@L17-L17
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: heading:bpW:wh:statement
KIND: heading
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:statement@L45-L45
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: w-headline:source-L102
KIND: citation
SOURCE: blueprint-W/parts/w-headline.tex#source@L108-L108
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh

ITEM: w-headline:prose-L3-L3
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L3-L4
DISPOSITION: EXCLUDED
REASON: status line (FROZEN, owner decision D41; nlw2 DRAFT_SORRY); administrative
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+claude-suborch-W-r2
REVIEWER: -

ITEM: w-headline:prose-L5-L9
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L6-L15
DISPOSITION: EXCLUDED
REASON: introduction (provenance D30, approval D41, list of the frozen declarations); administrative
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+claude-suborch-W-r2
REVIEWER: -

ITEM: w-headline:prose-L13-L16
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L19-L22
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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-imports

ITEM: K:bp:p1:fourier-basic
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L757-L768
DISPOSITION: NODE K:bp:p1:fourier-basic
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-imports

ITEM: K:bp:p1:holomorphic-analytic
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L296-L312
DISPOSITION: NODE K:bp:p1:holomorphic-analytic
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-imports

ITEM: K:bp:p1:strip-identity
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
DISPOSITION: NODE K:bp:p1:strip-identity
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-imports
