# Proof-source coverage manifest

CORPUS: blueprint-W/parts/{w0-conventions,w0-normalization,w1-sequences,w2-reconstruction,w3-birkhoff,w4-homological,w5-kamstep,w6-iteration,w7-measure,w8-assembly,w-headline}.tex pinned by SHA-256 in docs/graph/W/CORPUS.sha256 (KAM-inp branch inp plus inp-wbp 565c9040 W4-W6 gap repairs, accepted blueprint W0-W8, 2026-10-30; wave 2)

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
REVIEWER: sol-delta3-W-w0c

ITEM: bpW:w0:reconstruction#reconU
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L79-L85
DISPOSITION: NODE bpW:w0:reconstruction#reconU
REASON: reconstruction formula; the inverse coefficient dictionary and symplectic rescaling (L82-L84, formerly node bpW:w0:reconstruction#rescaling) are outside every root closure of track W (wave-2 all-reachable check): informational, used by no proof
COVERAGE_STATUS: REVIEWED
EXTRACTOR: sol-review-W-w0c+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0c

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
REVIEWER: sol-delta3-W-w0c

ITEM: bpW:w0:Gq#cubicGrad
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L102-L109
DISPOSITION: NODE bpW:w0:Gq#cubicGrad
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta3-W-w0c

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
REVIEWER: sol-delta3-W-w0n

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
REVIEWER: sol-delta3-W-w0n

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
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): no W proof uses the PDE equivalence; clause (5) comes from W2 (bpW:w2:clause5), which uses only Step stepW:w0n:force of this proof (kept as a node, cited by stepW:w2:fcub); the headline's citation is in the excluded reading remark bpW:wh:reading
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

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
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): step of the excluded Proposition bpW:w0n:pde-equiv; no other proof uses it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

ITEM: stepW:w0n:ident
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L201-L203
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): step of the excluded Proposition bpW:w0n:pde-equiv; no other proof uses it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

ITEM: stepW:w0n:converse
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L204-L210
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): step of the excluded Proposition bpW:w0n:pde-equiv; no other proof uses it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

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
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): the formal normal form is re-derived on all of the phase space in W3 (bpW:w3:F, bpW:w3:main); W3 cites it only in its source-provenance notes (w3-birkhoff.tex L404, L450)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

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
REASON: administrative remark (P96-W's exponent kappa = 2 is unchanged by the correction); the spectral asymptotics used later are proved in bpW:w1:tails; no proof consumes it. Re-checked in wave 2: W7 cites it in a source note (L207) and in its excluded interface remark (L783); the quantitative form is Lemma bpW:w7:unpert-bounds
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

ITEM: bpW:w0n:duffing
KIND: proposition
SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L393-L402
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): consistency check of the normal-form coefficients against the Duffing oscillator; no proof uses it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

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
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): W0 citation ledger (administrative); its one unlabelled external fact (Lindstedt, formerly bpW:w0n:ledger#ext-lindstedt) was used only by the excluded Duffing check
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w0n

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
REVIEWER: sol-delta3-W-w1a

ITEM: stepW:w1:restr
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L330-L334
DISPOSITION: NODE stepW:w1:restr
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta3-W-w1a

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: sol-delta3-W-w1a

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
REVIEWER: sol-delta9-W-W-w1b

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
REVIEWER: sol-delta4-W-w1b

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
DISPOSITION: NODE bpW:w1:kam-conventions
REASON: the coordinate-exchange claim is directly cited inside the statement of bpW:w4:index at L87; prose and source-note mentions remain provenance
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2+sol-delta5-W-w1b
REVIEWER: sol-delta6-W-W-w1b

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
REVIEWER: sol-delta3-W-w1b

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: sol-delta3-W-w1b

ITEM: stepW:w1:fshift-one
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-one@L976-L981
DISPOSITION: NODE stepW:w1:fshift-one
REASON: labelled unit added by the blueprint cleanup (inp 99afc128)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: sol-delta3-W-w1b

ITEM: stepW:w1:fshift-iter
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-iter@L982-L991
DISPOSITION: NODE stepW:w1:fshift-iter
REASON: labelled unit added by the blueprint cleanup (inp 99afc128)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: sol-delta3-W-w1b

ITEM: stepW:w1:fshift-end
KIND: proof-region
SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-end@L992-L995
DISPOSITION: NODE stepW:w1:fshift-end
REASON: labelled unit added by the blueprint cleanup (inp 99afc128)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: sol-delta3-W-w1b

ITEM: w1-sequences:source-L997
KIND: citation
SOURCE: blueprint-W/parts/w1-sequences.tex#source@L997-L998
DISPOSITION: EXCLUDED
REASON: provenance note (K's step:p1:dec-shift has the same argument for a particular shift); not an input
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: sol-delta3-W-w1b

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
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:omega
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L139-L145
DISPOSITION: NODE bpW:w3:omega
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:hamfield-def
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162
DISPOSITION: NODE bpW:w3:hamfield-def
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:real-restrict
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L171-L177
DISPOSITION: NODE bpW:w3:real-restrict
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:forms
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L189-L197
DISPOSITION: NODE bpW:w3:forms
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:Lambda
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L200-L206
DISPOSITION: NODE bpW:w3:Lambda
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

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
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:quartic
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L248-L259
DISPOSITION: NODE bpW:w3:quartic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:maj
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265
DISPOSITION: NODE stepW:w3:maj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:gradbound
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269
DISPOSITION: NODE stepW:w3:gradbound
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:identify
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277
DISPOSITION: NODE stepW:w3:identify
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:quartic-ident
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L282-L291
DISPOSITION: NODE bpW:w3:quartic-ident
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:Gz
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
DISPOSITION: NODE stepW:w3:Gz
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:XG
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311
DISPOSITION: NODE stepW:w3:XG
REASON: labelled proof step (route nodes removed after the blueprint cleanup)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-r2
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:Gnor
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L312-L313
DISPOSITION: NODE stepW:w3:Gnor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:count
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L314-L318
DISPOSITION: NODE stepW:w3:count
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:res
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L319-L321
DISPOSITION: NODE stepW:w3:res
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:divisor
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L333
DISPOSITION: NODE bpW:w3:divisor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:sel
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L339-L342
DISPOSITION: NODE stepW:w3:sel
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:signs
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L343-L346
DISPOSITION: NODE stepW:w3:signs
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:s0
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L347-L348
DISPOSITION: NODE stepW:w3:s0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:s1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L349-L353
DISPOSITION: NODE stepW:w3:s1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:s23
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L354-L358
DISPOSITION: NODE stepW:w3:s23
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:s1inner
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L359-L369
DISPOSITION: NODE stepW:w3:s1inner
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:divconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L370-L373
DISPOSITION: NODE stepW:w3:divconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:Fdef
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L395-L401
DISPOSITION: NODE bpW:w3:Fdef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:F
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L406-L413
DISPOSITION: NODE bpW:w3:F
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:fcoef
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L416-L419
DISPOSITION: NODE stepW:w3:fcoef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:Fconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L420-L423
DISPOSITION: NODE stepW:w3:Fconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:homological
KIND: proposition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L427-L432
DISPOSITION: NODE bpW:w3:homological
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:Xfcoord
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L435-L437
DISPOSITION: NODE stepW:w3:Xfcoord
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:euler
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L438-L443
DISPOSITION: NODE stepW:w3:euler
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:divide
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L444-L448
DISPOSITION: NODE stepW:w3:divide
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:lie-coeff
KIND: definition
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L461-L466
DISPOSITION: NODE bpW:w3:lie-coeff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:leibniz
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L470-L480
DISPOSITION: NODE bpW:w3:leibniz
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:rec
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L483-L485
DISPOSITION: NODE stepW:w3:rec
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:norms
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L486-L490
DISPOSITION: NODE stepW:w3:norms
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:Phireal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L491-L492
DISPOSITION: NODE stepW:w3:Phireal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:leib
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L493-L496
DISPOSITION: NODE stepW:w3:leib
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:leibid
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L497-L500
DISPOSITION: NODE stepW:w3:leibid
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:flow
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L504-L527
DISPOSITION: NODE bpW:w3:flow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:conv
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L530-L537
DISPOSITION: NODE stepW:w3:conv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:floweq
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L538-L541
DISPOSITION: NODE stepW:w3:floweq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:transport
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L542-L544
DISPOSITION: NODE stepW:w3:transport
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:est
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L545-L551
DISPOSITION: NODE stepW:w3:est
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:Greal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L552-L553
DISPOSITION: NODE stepW:w3:Greal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:var
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L554-L557
DISPOSITION: NODE stepW:w3:var
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:inv
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L558-L565
DISPOSITION: NODE stepW:w3:inv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:symplectic
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L579-L586
DISPOSITION: NODE bpW:w3:symplectic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:skew
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L589-L592
DISPOSITION: NODE stepW:w3:skew
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:constform
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L593-L597
DISPOSITION: NODE stepW:w3:constform
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:gradtrans
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L598-L602
DISPOSITION: NODE stepW:w3:gradtrans
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:Yseries
KIND: lemma
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L621-L629
DISPOSITION: NODE bpW:w3:Yseries
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majcalc
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L633-L644
DISPOSITION: NODE stepW:w3:majcalc
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majflow
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L645-L647
DISPOSITION: NODE stepW:w3:majflow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majA
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L648-L654
DISPOSITION: NODE stepW:w3:majA
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majN
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L655-L661
DISPOSITION: NODE stepW:w3:majN
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majX
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L662-L665
DISPOSITION: NODE stepW:w3:majX
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majY
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671
DISPOSITION: NODE stepW:w3:majY
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majint
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L672-L675
DISPOSITION: NODE stepW:w3:majint
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majps
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678
DISPOSITION: NODE stepW:w3:majps
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:majreal
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L679-L682
DISPOSITION: NODE stepW:w3:majreal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:main
KIND: theorem
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L687-L705
DISPOSITION: NODE bpW:w3:main
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:Kanalytic
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L710-L713
DISPOSITION: NODE stepW:w3:Kanalytic
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:K1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L714-L717
DISPOSITION: NODE stepW:w3:K1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:K2
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L718-L723
DISPOSITION: NODE stepW:w3:K2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:XK1
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L724-L731
DISPOSITION: NODE stepW:w3:XK1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:XK2
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L732-L741
DISPOSITION: NODE stepW:w3:XK2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:XKconcl
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L742-L746
DISPOSITION: NODE stepW:w3:XKconcl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:iii
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L747-L748
DISPOSITION: NODE stepW:w3:iii
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:conj
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755
DISPOSITION: NODE stepW:w3:conj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:class-remark
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
DISPOSITION: NODE bpW:w3:class-remark
REASON: the regularity claim is directly cited inside stepW:w6:t-an; retained with dependencies on its W3 suppliers
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2+sol-delta5-W-w3
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:gamma-real
KIND: corollary
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L780-L794
DISPOSITION: NODE bpW:w3:gamma-real
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:transport-tori
KIND: corollary
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L810-L817
DISPOSITION: NODE bpW:w3:transport-tori
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w3

ITEM: bpW:w3:interface
KIND: claim
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:interface@L872-L920
DISPOSITION: EXCLUDED
REASON: administrative remark (what W3 supplies to W4-W8). Re-checked in wave 2: the 15 citations in W4, W5, W7, W8 are in inputs prose, excluded remarks and source notes (W8 L353, L381, L409: provenance of the return trip and the closeness bound). Each supplied fact is a labelled result that the consumers cite directly: bpW:w3:main (normal form), bpW:w3:gamma-real (Gamma^R, closeness 6 sqrt2 C_F ¦¦x¦¦^3), bpW:w3:transport-tori-weak (return trip)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-w3

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
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:interface-sec@L870-L870
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:constants
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:constants@L924-L924
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: heading:bpW:w3:status
KIND: heading
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:status@L948-L948
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
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L921-L921
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
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L926-L946
DISPOSITION: EXCLUDED
REASON: constants table and Lean totality notes (summary; each constant is defined and bounded in its result)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3

ITEM: w3-birkhoff:prose-L891-L904
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L950-L963
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

ITEM: bpW:w3:transport-tori-weak
KIND: corollary
SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L831-L842
DISPOSITION: NODE bpW:w3:transport-tori-weak
REASON: labelled unit of the revised W3 (wave 2)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:wk-lin
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849
DISPOSITION: NODE stepW:w3:wk-lin
REASON: labelled unit of the revised W3 (wave 2)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:wk-reg
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858
DISPOSITION: NODE stepW:w3:wk-reg
REASON: labelled unit of the revised W3 (wave 2)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2
REVIEWER: sol-delta9-W-W-w3

ITEM: stepW:w3:wk-transport
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865
DISPOSITION: NODE stepW:w3:wk-transport
REASON: labelled unit of the revised W3 (wave 2)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2
REVIEWER: sol-delta9-W-W-w3

ITEM: w3-birkhoff:prose-L826-L829
KIND: proof-region
SOURCE: blueprint-W/parts/w3-birkhoff.tex#prose@L826-L829
DISPOSITION: EXCLUDED
REASON: motivation for Corollary bpW:w3:transport-tori-weak (pointer to Theorem bpW:w6:tori)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2
REVIEWER: sol-delta5-W-w3

ITEM: w3-birkhoff:source-L867
KIND: citation
SOURCE: blueprint-W/parts/w3-birkhoff.tex#source@L867-L868
DISPOSITION: EXCLUDED
REASON: provenance note (ours; pointer to the return-trip item of the excluded Remark bpW:w3:interface)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2
REVIEWER: sol-delta5-W-w3

ITEM: bpW:w4:ext-roots
KIND: external
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-roots@L43-L44
DISPOSITION: NODE bpW:w4:ext-roots
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:ext-parallelogram
KIND: external
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-parallelogram@L45-L46
DISPOSITION: NODE bpW:w4:ext-parallelogram
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:ext-exp
KIND: external
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-exp@L47-L49
DISPOSITION: NODE bpW:w4:ext-exp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:ext-intparts
KIND: external
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-intparts@L50-L52
DISPOSITION: NODE bpW:w4:ext-intparts
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:index
KIND: definition
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:index@L69-L113
DISPOSITION: NODE bpW:w4:index
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: bpW:w4:weights
KIND: claim
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:weights@L118-L125
DISPOSITION: EXCLUDED
REASON: administrative remark (why the wave weights are kept)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:ops
KIND: definition
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L127-L138
DISPOSITION: NODE bpW:w4:ops
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: bpW:w4:taylor
KIND: definition
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L142-L161
DISPOSITION: NODE bpW:w4:taylor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: bpW:w4:melnikov
KIND: definition
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:melnikov@L167-L188
DISPOSITION: NODE bpW:w4:melnikov
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:wave
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L194-L208
DISPOSITION: NODE bpW:w4:wave
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:waveLip
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L211-L215
DISPOSITION: NODE stepW:w4:waveLip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:waveTail
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L216-L219
DISPOSITION: NODE stepW:w4:waveTail
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:waveIdx
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveIdx@L220-L223
DISPOSITION: NODE stepW:w4:waveIdx
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:k0
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L229-L234
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): the k = 0 Melnikov conditions used downstream come from W7 Lemma bpW:w7:sep (perturbed frequencies, all l in Lambda); W4 cites this lemma only in the excluded Remark bpW:w4:melnikov-check
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:k0one
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:k0one@L238-L240
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): step of the excluded Lemma bpW:w4:k0
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:k0diff
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:k0diff@L241-L245
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (wave-2 all-reachable check): step of the excluded Lemma bpW:w4:k0
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:melnikov-check
KIND: claim
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:melnikov-check@L252-L261
DISPOSITION: EXCLUDED
REASON: administrative remark (summary of what is checked about the Melnikov conditions)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:counterexample
KIND: claim
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:counterexample@L265-L284
DISPOSITION: EXCLUDED
REASON: administrative remark (counterexample to P96-K p. 127's operator-valued square-sum bound; errata); no proof consumes it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:w1-requests
KIND: claim
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L286-L304
DISPOSITION: NODE bpW:w4:w1-requests
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:fourier-ops
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L306-L315
DISPOSITION: NODE bpW:w4:fourier-ops
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:linimg
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L318-L319
DISPOSITION: NODE stepW:w4:linimg
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:deriv
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L320-L325
DISPOSITION: NODE stepW:w4:deriv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:fpar
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L326-L327
DISPOSITION: NODE stepW:w4:fpar
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: bpW:w4:lattice
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L331-L346
DISPOSITION: NODE bpW:w4:lattice
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:count
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:count@L349-L351
DISPOSITION: NODE stepW:w4:count
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:coth
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L352-L354
DISPOSITION: NODE stepW:w4:coth
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:wsum
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L355-L357
DISPOSITION: NODE stepW:w4:wsum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:bw
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L358-L365
DISPOSITION: NODE stepW:w4:bw
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:divisors
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L372-L378
DISPOSITION: NODE bpW:w4:divisors
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:member
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:member@L381-L385
DISPOSITION: NODE stepW:w4:member
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:divlip
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L386-L390
DISPOSITION: NODE stepW:w4:divlip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: bpW:w4:schur
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L398-L413
DISPOSITION: NODE bpW:w4:schur
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:schurtr
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L416-L418
DISPOSITION: NODE stepW:w4:schurtr
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:schurrep
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L419-L435
DISPOSITION: NODE stepW:w4:schurrep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w4

ITEM: stepW:w4:schurdiag
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L436-L437
DISPOSITION: NODE stepW:w4:schurdiag
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:solve
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L443-L461
DISPOSITION: NODE bpW:w4:solve
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:solvecoef
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L464-L467
DISPOSITION: NODE stepW:w4:solvecoef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:solvediff
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L468-L473
DISPOSITION: NODE stepW:w4:solvediff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:solvecomm
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L474-L479
DISPOSITION: NODE stepW:w4:solvecomm
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:solvelin
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L480-L482
DISPOSITION: NODE stepW:w4:solvelin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: bpW:w4:lie
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L502-L530
DISPOSITION: NODE bpW:w4:lie
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:liebd
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L533-L537
DISPOSITION: NODE stepW:w4:liebd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:liebr
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebr@L538-L541
DISPOSITION: NODE stepW:w4:liebr
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:liecoef
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L542-L549
DISPOSITION: NODE stepW:w4:liecoef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:lieder
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L550-L558
DISPOSITION: NODE stepW:w4:lieder
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: bpW:w4:extract
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L569-L573
DISPOSITION: NODE bpW:w4:extract
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:components
KIND: lemma
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:components@L585-L595
DISPOSITION: NODE bpW:w4:components
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:testpts
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L598-L603
DISPOSITION: NODE stepW:w4:testpts
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:first
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:first@L604-L608
DISPOSITION: NODE stepW:w4:first
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:angle
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L609-L617
DISPOSITION: NODE stepW:w4:angle
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:polar
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L618-L622
DISPOSITION: NODE stepW:w4:polar
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:lemma1
KIND: theorem
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L630-L655
DISPOSITION: NODE bpW:w4:lemma1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:divops
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L658-L666
DISPOSITION: NODE stepW:w4:divops
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w4

ITEM: stepW:w4:class
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:class@L667-L671
DISPOSITION: NODE stepW:w4:class
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:equation
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L672-L681
DISPOSITION: NODE stepW:w4:equation
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:Fcomp
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L682-L695
DISPOSITION: NODE stepW:w4:Fcomp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:assembly
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L696-L708
DISPOSITION: NODE stepW:w4:assembly
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:lip
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L709-L714
DISPOSITION: NODE stepW:w4:lip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:Nhat
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L715-L721
DISPOSITION: NODE stepW:w4:Nhat
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: stepW:w4:real
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:real@L722-L729
DISPOSITION: NODE stepW:w4:real
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:lemma2
KIND: corollary
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L743-L751
DISPOSITION: NODE bpW:w4:lemma2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:compare
KIND: claim
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:compare@L762-L792
DISPOSITION: EXCLUDED
REASON: administrative remark (comparison of constants with P96-K)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:from-w3
KIND: claim
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L796-L815
DISPOSITION: NODE bpW:w4:from-w3
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w4

ITEM: bpW:w4:to-w5
KIND: claim
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:to-w5@L817-L831
DISPOSITION: EXCLUDED
REASON: administrative remark (what W5 receives and must supply); pointer
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:ext
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext@L38-L38
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:setting
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:setting@L67-L67
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:fourier-sec
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-sec@L263-L263
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:solve-sec
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:solve-sec@L370-L370
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:lie-sec
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L489-L489
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:extract-sec
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:extract-sec@L567-L567
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:main-sec
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:main-sec@L628-L628
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:compare-sec
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:compare-sec@L760-L760
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:interface-sec
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:interface-sec@L794-L794
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: heading:bpW:w4:ledger
KIND: heading
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ledger@L833-L833
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:sourcegap-L716
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#sourcegap@L738-L741
DISPOSITION: NODE stepW:w4:Fcomp, stepW:w4:assembly
REASON: P96-K p. 128 omits the bookkeeping of the other components and of the y-component; the blueprint supplies it
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L104
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L114-L114
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L129
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L139-L139
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L152
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L162-L162
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L179
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L189-L189
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L215
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L225-L225
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L237
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L247-L248
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L318
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L329-L329
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L356
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L367-L367
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L381
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L392-L392
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L417
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L439-L439
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L462
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L484-L484
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L538
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L560-L560
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L560
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L582-L582
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L602
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L624-L624
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L709
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L731-L731
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:source-L736
KIND: citation
SOURCE: blueprint-W/parts/w4-homological.tex#source@L758-L758
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L3-L7
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L3-L7
DISPOSITION: EXCLUDED
REASON: introduction
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L9-L21
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L9-L21
DISPOSITION: EXCLUDED
REASON: route paragraph (outline)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L23-L30
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L23-L30
DISPOSITION: EXCLUDED
REASON: inputs paragraph (pointers; each use is an edge at its consumer)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L32-L36
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L32-L36
DISPOSITION: EXCLUDED
REASON: regularity remark (outline)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L40-L42
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L40-L42
DISPOSITION: EXCLUDED
REASON: introduction of the external list
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L53-L55
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L63-L65
DISPOSITION: EXCLUDED
REASON: derivation note for an external item (W4-E3); layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L469-L478
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L491-L500
DISPOSITION: NODE bpW:w4:lie-sec#guard
REASON: the formal N and the guard (G)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L813-L819
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L835-L841
DISPOSITION: EXCLUDED
REASON: ledger (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L821-L824
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L843-L846
DISPOSITION: EXCLUDED
REASON: ledger (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: w4-homological:prose-L826-L831
KIND: proof-region
SOURCE: blueprint-W/parts/w4-homological.tex#prose@L848-L853
DISPOSITION: EXCLUDED
REASON: ledger of suspected P96-K errata (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4

ITEM: bpW:w4:ext-riesz
KIND: external
SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-riesz@L53-L62
DISPOSITION: NODE bpW:w4:ext-riesz
REASON: mechanical inventory of a labelled unit (new external of the gap repair)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w4

ITEM: bpW:w5:ext-taylor
KIND: external
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-taylor@L46-L53
DISPOSITION: NODE bpW:w5:ext-taylor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: bpW:w5:ext-ftc
KIND: external
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-ftc@L54-L56
DISPOSITION: NODE bpW:w5:ext-ftc
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: bpW:w5:setting
KIND: definition
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:setting@L76-L85
DISPOSITION: NODE bpW:w5:setting
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: bpW:w5:omega
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L89-L93
DISPOSITION: NODE bpW:w5:omega
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:ombd
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L95-L96
DISPOSITION: NODE stepW:w5:ombd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:omnd
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnd@L97-L99
DISPOSITION: NODE stepW:w5:omnd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:omnorm
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L100-L101
DISPOSITION: NODE stepW:w5:omnorm
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: bpW:w5:class
KIND: definition
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L105-L119
DISPOSITION: NODE bpW:w5:class
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: bpW:w5:lambda-product
KIND: claim
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:lambda-product@L123-L128
DISPOSITION: NODE bpW:w5:lambda-product
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: bpW:w5:w4-general
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L137-L147
DISPOSITION: NODE bpW:w5:w4-general
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: stepW:w5:g-pair
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L150-L152
DISPOSITION: NODE stepW:w5:g-pair
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: stepW:w5:g-tail
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L153-L154
DISPOSITION: NODE stepW:w5:g-tail
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:g-div
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L155-L157
DISPOSITION: NODE stepW:w5:g-div
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:g-diag
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L158-L160
DISPOSITION: NODE stepW:w5:g-diag
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:g-rest
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L161-L164
DISPOSITION: NODE stepW:w5:g-rest
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: bpW:w5:w4-modified
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L170-L191
DISPOSITION: NODE bpW:w5:w4-modified
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:m-sup
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L194-L198
DISPOSITION: NODE stepW:w5:m-sup
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:m-other
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L199-L200
DISPOSITION: NODE stepW:w5:m-other
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:m-lip
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L201-L204
DISPOSITION: NODE stepW:w5:m-lip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:m-act
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L205-L226
DISPOSITION: NODE stepW:w5:m-act
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:m-ass
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L227-L231
DISPOSITION: NODE stepW:w5:m-ass
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:m-const
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L232-L235
DISPOSITION: NODE stepW:w5:m-const
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: bpW:w5:prep-gap
KIND: claim
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:prep-gap@L254-L261
DISPOSITION: EXCLUDED
REASON: administrative remark (exponents adopted by W6-W7 after the sourcegap; their values are fixed in Definition bpW:w7:constdef and Lemma bpW:w6:prep-step)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: bpW:w5:taylor
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L265-L285
DISPOSITION: NODE bpW:w5:taylor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:t-scale
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-scale@L287-L290
DISPOSITION: NODE stepW:w5:t-scale
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:t-disc
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-disc@L291-L293
DISPOSITION: NODE stepW:w5:t-disc
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:t-poly
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-poly@L294-L298
DISPOSITION: NODE stepW:w5:t-poly
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:t-comp
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L299-L307
DISPOSITION: NODE stepW:w5:t-comp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:t-field
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L308-L313
DISPOSITION: NODE stepW:w5:t-field
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: stepW:w5:t-est
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L314-L320
DISPOSITION: NODE stepW:w5:t-est
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: bpW:w5:data
KIND: definition
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L328-L348
DISPOSITION: NODE bpW:w5:data
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w5a

ITEM: bpW:w5:solve
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L352-L363
DISPOSITION: NODE bpW:w5:solve
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: stepW:w5:s-in
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-in@L365-L366
DISPOSITION: NODE stepW:w5:s-in
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: stepW:w5:s-out
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L367-L372
DISPOSITION: NODE stepW:w5:s-out
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: stepW:w5:s-class
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L373-L376
DISPOSITION: NODE stepW:w5:s-class
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: bpW:w5:flow
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L380-L395
DISPOSITION: NODE bpW:w5:flow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: stepW:w5:f-margin
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-margin@L397-L399
DISPOSITION: NODE stepW:w5:f-margin
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: stepW:w5:f-flow
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L400-L403
DISPOSITION: NODE stepW:w5:f-flow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: stepW:w5:f-par
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L404-L409
DISPOSITION: NODE stepW:w5:f-par
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: stepW:w5:f-der
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L410-L413
DISPOSITION: NODE stepW:w5:f-der
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: stepW:w5:f-image
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L414-L415
DISPOSITION: NODE stepW:w5:f-image
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: stepW:w5:f-real
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L416-L419
DISPOSITION: NODE stepW:w5:f-real
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: bpW:w5:flow-calc
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L428-L441
DISPOSITION: NODE bpW:w5:flow-calc
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: stepW:w5:c-cont
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L443-L446
DISPOSITION: NODE stepW:w5:c-cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: stepW:w5:c-var
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L447-L449
DISPOSITION: NODE stepW:w5:c-var
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: stepW:w5:c-skew
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L450-L453
DISPOSITION: NODE stepW:w5:c-skew
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5a

ITEM: stepW:w5:c-symp
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L454-L455
DISPOSITION: NODE stepW:w5:c-symp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: stepW:w5:c-inv
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L456-L457
DISPOSITION: NODE stepW:w5:c-inv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: stepW:w5:c-trans
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L458-L461
DISPOSITION: NODE stepW:w5:c-trans
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5a

ITEM: stepW:w5:c-time
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-time@L462-L464
DISPOSITION: NODE stepW:w5:c-time
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: heading:bpW:w5
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: heading:bpW:w5:ext
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext@L41-L41
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: heading:bpW:w5:setting-sec
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:setting-sec@L74-L74
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: heading:bpW:w5:w4-sec
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-sec@L130-L130
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: heading:bpW:w5:taylor-sec
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor-sec@L263-L263
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: heading:bpW:w5:flow-sec
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-sec@L326-L326
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:sourcegap-L226
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#sourcegap@L240-L252
DISPOSITION: NODE bpW:w5:w4-modified, stepW:w5:m-lip, stepW:w5:m-act
REASON: P96-K p. 140's lambda-norm for the modified divisors needs 2 beta <= bar p - check p; the blueprint states (ii) under that hypothesis (Step stepW:w5:m-lip) and handles the action component separately (Step stepW:w5:m-act); W7 adopts beta = 1/4. Not an open gap of the blueprint
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L72
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L86-L86
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L89
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L103-L103
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L106
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L120-L120
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L152
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L166-L166
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L223
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L237-L237
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L307
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L322-L322
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L334
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L349-L349
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L362
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L378-L378
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L405
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L421-L421
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:source-L449
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L466-L466
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:prose-L7-L11
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L7-L11
DISPOSITION: EXCLUDED
REASON: introduction
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:prose-L13-L25
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L13-L25
DISPOSITION: EXCLUDED
REASON: route paragraph (outline)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:prose-L27-L33
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L27-L33
DISPOSITION: EXCLUDED
REASON: inputs paragraph (pointers; each use is an edge at its consumer)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:prose-L35-L39
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L35-L39
DISPOSITION: NODE bpW:w5#data
REASON: fixes a = p = 1 for W5
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:prose-L43-L45
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L43-L45
DISPOSITION: EXCLUDED
REASON: introduction of the external list and layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:prose-L57-L58
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L71-L72
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: w5-kamstep:prose-L118-L121
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L132-L135
DISPOSITION: EXCLUDED
REASON: motivation of Lemmas bpW:w5:w4-general and bpW:w5:w4-modified
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5a

ITEM: bpW:w5:ext-symm
KIND: external
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-symm@L57-L61
DISPOSITION: NODE bpW:w5:ext-symm
REASON: mechanical inventory of a labelled unit (new external of the gap repair)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w5a

ITEM: bpW:w5:ext-sqrt
KIND: external
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-sqrt@L62-L66
DISPOSITION: NODE bpW:w5:ext-sqrt
REASON: mechanical inventory of a labelled unit (new external of the gap repair)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w5a

ITEM: bpW:w5:ext-triangle
KIND: external
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-triangle@L67-L70
DISPOSITION: NODE bpW:w5:ext-triangle
REASON: mechanical inventory of a labelled unit (new external of the gap repair)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w5a

ITEM: bpW:w5:new-ham
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L474-L489
DISPOSITION: NODE bpW:w5:new-ham
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5b

ITEM: stepW:w5:n-exp
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L491-L498
DISPOSITION: NODE stepW:w5:n-exp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5b

ITEM: stepW:w5:n-br
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L499-L502
DISPOSITION: NODE stepW:w5:n-br
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:n-field
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L503-L505
DISPOSITION: NODE stepW:w5:n-field
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:n-conj
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L506-L510
DISPOSITION: NODE stepW:w5:n-conj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: bpW:w5:pullback
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L520-L524
DISPOSITION: NODE bpW:w5:pullback
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5b

ITEM: stepW:w5:p-inv
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L526-L533
DISPOSITION: NODE stepW:w5:p-inv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5b

ITEM: stepW:w5:p-dy
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L534-L536
DISPOSITION: NODE stepW:w5:p-dy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:p-ass
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L537-L543
DISPOSITION: NODE stepW:w5:p-ass
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5b

ITEM: bpW:w5:commutator
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L548-L551
DISPOSITION: NODE bpW:w5:commutator
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:k-cauchy
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L553-L555
DISPOSITION: NODE stepW:w5:k-cauchy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:k-bd
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L556-L559
DISPOSITION: NODE stepW:w5:k-bd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: bpW:w5:step
KIND: theorem
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L565-L588
DISPOSITION: NODE bpW:w5:step
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5b

ITEM: stepW:w5:st-con
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L590-L592
DISPOSITION: NODE stepW:w5:st-con
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5b

ITEM: stepW:w5:st-1
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L593-L594
DISPOSITION: NODE stepW:w5:st-1
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:st-2
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L595-L596
DISPOSITION: NODE stepW:w5:st-2
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:st-freq
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L597-L598
DISPOSITION: NODE stepW:w5:st-freq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:st-div
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L599-L601
DISPOSITION: NODE stepW:w5:st-div
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5b

ITEM: bpW:w5:notation
KIND: claim
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:notation@L607-L612
DISPOSITION: EXCLUDED
REASON: administrative remark (notation clash in P96-K)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: bpW:w5:action-angle
KIND: lemma
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L622-L660
DISPOSITION: NODE bpW:w5:action-angle
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:a-hol
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L662-L666
DISPOSITION: NODE stepW:w5:a-hol
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w5b

ITEM: stepW:w5:a-dom
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L667-L669
DISPOSITION: NODE stepW:w5:a-dom
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:a-der
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L670-L673
DISPOSITION: NODE stepW:w5:a-der
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:a-nf
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L674-L677
DISPOSITION: NODE stepW:w5:a-nf
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:a-field
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L678-L683
DISPOSITION: NODE stepW:w5:a-field
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5b

ITEM: stepW:w5:a-conj
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L684-L689
DISPOSITION: NODE stepW:w5:a-conj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: bpW:w5:initial
KIND: proposition
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L696-L705
DISPOSITION: NODE bpW:w5:initial
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w5b

ITEM: stepW:w5:i-q
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L707-L711
DISPOSITION: NODE stepW:w5:i-q
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:i-g
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L712-L714
DISPOSITION: NODE stepW:w5:i-g
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:i-k
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L715-L719
DISPOSITION: NODE stepW:w5:i-k
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:i-par
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L720-L724
DISPOSITION: NODE stepW:w5:i-par
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: stepW:w5:i-freq
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L725-L725
DISPOSITION: NODE stepW:w5:i-freq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: heading:bpW:w5:newham-sec
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:newham-sec@L469-L469
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: heading:bpW:w5:step-sec
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step-sec@L563-L563
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: heading:bpW:w5:aa-sec
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:aa-sec@L614-L614
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: heading:bpW:w5:ledger
KIND: heading
SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ledger@L732-L732
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:sourcegap-L498
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#sourcegap@L516-L518
DISPOSITION: NODE bpW:w5:new-ham, stepW:w5:n-exp
REASON: P96-K p. 130 asserts the new field without derivation; supplied in Lemma bpW:w5:new-ham
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:source-L494
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L512-L512
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:source-L523
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L545-L545
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:source-L539
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L561-L561
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:source-L581
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L603-L603
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:source-L668
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L691-L691
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:source-L704
KIND: citation
SOURCE: blueprint-W/parts/w5-kamstep.tex#source@L727-L727
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:prose-L454-L455
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L471-L472
DISPOSITION: NODE bpW:w5:newham-sec#bracket
REASON: notation {G,F} and [X_G,X_F]
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:prose-L594-L598
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L616-L620
DISPOSITION: NODE bpW:w5:action-angle
REASON: introduction of the action-angle subsection (W3's H' on B_{rho_1}, principal square root), recorded in the lemma's hypotheses
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:prose-L711-L718
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L734-L741
DISPOSITION: EXCLUDED
REASON: constants ledger (summary)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:prose-L720-L724
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L743-L747
DISPOSITION: EXCLUDED
REASON: ledger of results (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: w5-kamstep:prose-L726-L731
KIND: proof-region
SOURCE: blueprint-W/parts/w5-kamstep.tex#prose@L749-L754
DISPOSITION: EXCLUDED
REASON: ledger of source issues (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w5b

ITEM: bpW:w6:sequences
KIND: definition
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:sequences@L31-L41
DISPOSITION: NODE bpW:w6:sequences
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:iter-lemma
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L47-L67
DISPOSITION: NODE bpW:w6:iter-lemma
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:il-small
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L69-L71
DISPOSITION: NODE stepW:w6:il-small
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: stepW:w6:il-err
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L75
DISPOSITION: NODE stepW:w6:il-err
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:il-lip
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L78
DISPOSITION: NODE stepW:w6:il-lip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:il-div
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L79-L82
DISPOSITION: NODE stepW:w6:il-div
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:il-tr
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83
DISPOSITION: NODE stepW:w6:il-tr
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:k0
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L89-L93
DISPOSITION: NODE bpW:w6:k0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:convergence
KIND: proposition
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L103-L133
DISPOSITION: NODE bpW:w6:convergence
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:c-ind
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L136
DISPOSITION: NODE stepW:w6:c-ind
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:c-par
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L137-L138
DISPOSITION: NODE stepW:w6:c-par
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:c-freq
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L142
DISPOSITION: NODE stepW:w6:c-freq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:c-dom
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L146
DISPOSITION: NODE stepW:w6:c-dom
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:c-op
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L147-L150
DISPOSITION: NODE stepW:w6:c-op
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:c-cauchy
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L153
DISPOSITION: NODE stepW:w6:c-cauchy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: stepW:w6:c-lim
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L157
DISPOSITION: NODE stepW:w6:c-lim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:c-cont
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L160
DISPOSITION: NODE stepW:w6:c-cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: bpW:w6:strong
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L170-L175
DISPOSITION: NODE bpW:w6:strong
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:invariance
KIND: proposition
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L182-L187
DISPOSITION: NODE bpW:w6:invariance
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:i-weak
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L189-L196
DISPOSITION: NODE stepW:w6:i-weak
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:i-torus
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L197-L199
DISPOSITION: NODE stepW:w6:i-torus
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:i-lim
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L203
DISPOSITION: NODE stepW:w6:i-lim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:constants
KIND: definition
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L211-L218
DISPOSITION: NODE bpW:w6:constants
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:prep-step
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L245
DISPOSITION: NODE bpW:w6:prep-step
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta8-W-W-w6

ITEM: stepW:w6:p-data
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L247-L249
DISPOSITION: NODE stepW:w6:p-data
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:p-div
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L254
DISPOSITION: NODE stepW:w6:p-div
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w6

ITEM: stepW:w6:p-step
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L255-L259
DISPOSITION: NODE stepW:w6:p-step
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:p-lipp
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L263
DISPOSITION: NODE stepW:w6:p-lipp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta8-W-W-w6

ITEM: stepW:w6:p-size
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L264-L267
DISPOSITION: NODE stepW:w6:p-size
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:p-gap
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L268-L270
DISPOSITION: NODE stepW:w6:p-gap
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: bpW:w6:wave-iteration
KIND: definition
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L279-L286
DISPOSITION: NODE bpW:w6:wave-iteration
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:applicable
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L288-L290
DISPOSITION: NODE bpW:w6:applicable
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: bpW:w6:freq-lip
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L300-L310
DISPOSITION: NODE bpW:w6:freq-lip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w6

ITEM: stepW:w6:fl-size
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L312-L314
DISPOSITION: NODE stepW:w6:fl-size
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:fl-lip
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L315-L318
DISPOSITION: NODE stepW:w6:fl-lip
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:fl-borel
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L319-L322
DISPOSITION: NODE stepW:w6:fl-borel
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w6

ITEM: bpW:w6:exclusion
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L327-L330
DISPOSITION: NODE bpW:w6:exclusion
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: bpW:w6:final-freq
KIND: lemma
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L339-L342
DISPOSITION: NODE bpW:w6:final-freq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w6:tori
KIND: theorem
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L351-L370
DISPOSITION: NODE bpW:w6:tori
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:t-hol
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L372-L374
DISPOSITION: NODE stepW:w6:t-hol
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: stepW:w6:t-cont
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L375-L376
DISPOSITION: NODE stepW:w6:t-cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: stepW:w6:t-prep
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L377-L379
DISPOSITION: NODE stepW:w6:t-prep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:t-bk
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L380-L380
DISPOSITION: NODE stepW:w6:t-bk
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:t-close
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L381-L382
DISPOSITION: NODE stepW:w6:t-close
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: stepW:w6:t-an
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L383-L385
DISPOSITION: NODE stepW:w6:t-an
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w6

ITEM: bpW:w6:to-w8
KIND: claim
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L392-L422
DISPOSITION: NODE bpW:w6:to-w8
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w6

ITEM: heading:bpW:w6
KIND: heading
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: heading:bpW:w6:iter-sec
KIND: heading
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-sec@L29-L29
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: heading:bpW:w6:conv-sec
KIND: heading
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:conv-sec@L101-L101
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: heading:bpW:w6:inv-sec
KIND: heading
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:inv-sec@L168-L168
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: heading:bpW:w6:prep-sec
KIND: heading
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-sec@L209-L209
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: heading:bpW:w6:out-sec
KIND: heading
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:out-sec@L349-L349
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: heading:bpW:w6:ledger
KIND: heading
SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:ledger@L424-L424
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L42
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L42-L42
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L85
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L85-L85
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L99
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L99-L99
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L162
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L162-L162
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L180
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L180-L180
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L205
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L205-L205
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L268
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L272-L272
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L294
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L298-L298
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L315
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L324-L324
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L327
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L336-L336
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L338
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L347-L347
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:source-L378
KIND: citation
SOURCE: blueprint-W/parts/w6-iteration.tex#source@L387-L387
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:prose-L7-L12
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#prose@L7-L12
DISPOSITION: EXCLUDED
REASON: introduction
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:prose-L14-L20
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#prose@L14-L20
DISPOSITION: EXCLUDED
REASON: route paragraph (outline)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:prose-L22-L27
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#prose@L22-L27
DISPOSITION: NODE bpW:w6#data
REASON: fixed data and notation of W6
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:prose-L417-L421
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#prose@L426-L430
DISPOSITION: EXCLUDED
REASON: ledger (administrative)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: w6-iteration:prose-L423-L426
KIND: proof-region
SOURCE: blueprint-W/parts/w6-iteration.tex#prose@L432-L435
DISPOSITION: EXCLUDED
REASON: order of constants (summary; each constant is defined in Definition bpW:w6:constants or W5/W7)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6

ITEM: bpW:w7:ext-tonelli
KIND: external
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-tonelli@L47-L51
DISPOSITION: NODE bpW:w7:ext-tonelli
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:ext-diam
KIND: external
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-diam@L52-L54
DISPOSITION: NODE bpW:w7:ext-diam
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:ext-linear
KIND: external
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-linear@L55-L57
DISPOSITION: NODE bpW:w7:ext-linear
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:ext-borel
KIND: external
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-borel@L58-L65
DISPOSITION: NODE bpW:w7:ext-borel
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:ext-zeta
KIND: external
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-zeta@L66-L68
DISPOSITION: NODE bpW:w7:ext-zeta
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:ext-ball
KIND: external
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ball@L69-L71
DISPOSITION: NODE bpW:w7:ext-ball
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:ext-ennreal
KIND: external
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ennreal@L72-L76
DISPOSITION: NODE bpW:w7:ext-ennreal
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:indexdef
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:indexdef@L82-L98
DISPOSITION: NODE bpW:w7:indexdef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:reindex
KIND: claim
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:reindex@L103-L119
DISPOSITION: EXCLUDED
REASON: administrative remark (comparison of the Dirichlet labels and weights with P96-K's); W5-W6 use the Dirichlet weights directly
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:omega0
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L127-L131
DISPOSITION: NODE bpW:w7:omega0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:freqcoords
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L135-L150
DISPOSITION: NODE bpW:w7:freqcoords
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:inverse
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157
DISPOSITION: NODE stepW:w7:inverse
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:norms
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162
DISPOSITION: NODE stepW:w7:norms
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:Omegazeta
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165
DISPOSITION: NODE stepW:w7:Omegazeta
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:measure-affine
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167
DISPOSITION: NODE stepW:w7:measure-affine
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:unpert-bounds
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L172-L181
DISPOSITION: NODE bpW:w7:unpert-bounds
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:ssize
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185
DISPOSITION: NODE stepW:w7:ssize
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:plus
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189
DISPOSITION: NODE stepW:w7:plus
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:minus
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194
DISPOSITION: NODE stepW:w7:minus
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:kappa
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200
DISPOSITION: NODE stepW:w7:kappa
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:liplOmega
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203
DISPOSITION: NODE stepW:w7:liplOmega
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:constdef
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231
DISPOSITION: NODE bpW:w7:constdef, bpW:w7:constdef#base
REASON: the full constant definition, with (C1)-(C2) additionally represented separately to supply X's cutoffs before (C3)-(C6)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:choices
KIND: claim
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:choices@L235-L251
DISPOSITION: EXCLUDED
REASON: administrative remark (why tau = 24, varpi = 1/2, beta = 1/4); the values are fixed in Definitions bpW:w7:indexdef and bpW:w7:constdef
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:zones
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:zones@L255-L264
DISPOSITION: NODE bpW:w7:zones
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:family
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:family@L266-L280
DISPOSITION: NODE bpW:w7:family
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:w6-needs
KIND: claim
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:w6-needs@L286-L313
DISPOSITION: EXCLUDED
REASON: administrative remark (what W6 must supply; forward references)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:slab
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L317-L322
DISPOSITION: NODE bpW:w7:slab
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: stepW:w7:slab-borel
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-borel@L324-L325
DISPOSITION: NODE stepW:w7:slab-borel
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: stepW:w7:slab-line
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-line@L326-L329
DISPOSITION: NODE stepW:w7:slab-line
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: stepW:w7:slab-int
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L330-L333
DISPOSITION: NODE stepW:w7:slab-int
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:sep
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L345-L348
DISPOSITION: NODE bpW:w7:sep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: stepW:w7:sep-drift
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L350-L352
DISPOSITION: NODE stepW:w7:sep-drift
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:sep-concl
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355
DISPOSITION: NODE stepW:w7:sep-concl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:largek
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L359-L363
DISPOSITION: NODE bpW:w7:largek
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: stepW:w7:largek-tan
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367
DISPOSITION: NODE stepW:w7:largek-tan
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:largek-cmp
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370
DISPOSITION: NODE stepW:w7:largek-cmp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:zone
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L374-L380
DISPOSITION: NODE bpW:w7:zone
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: stepW:w7:zone-lower
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L382-L386
DISPOSITION: NODE stepW:w7:zone-lower
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:zone-slab
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L387-L389
DISPOSITION: NODE stepW:w7:zone-slab
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:zone-psi
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L390-L393
DISPOSITION: NODE stepW:w7:zone-psi
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:Xdef
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L398-L401
DISPOSITION: NODE bpW:w7:Xdef
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:dichotomy
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L403-L406
DISPOSITION: NODE bpW:w7:dichotomy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7a

ITEM: stepW:w7:Xfinite
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410
DISPOSITION: NODE stepW:w7:Xfinite
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:dich-large
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413
DISPOSITION: NODE stepW:w7:dich-large
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:dich-small
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416
DISPOSITION: NODE stepW:w7:dich-small
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:Xzones
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L421-L429
DISPOSITION: NODE bpW:w7:Xzones, bpW:w7:Xzones#consts
REASON: the lemma; its definitional part (sigma_X, c_X) is a separate definition node so that Definition bpW:w7:constdef (C3) does not depend on the lemma (cycle)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7a

ITEM: stepW:w7:X-A3
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435
DISPOSITION: NODE stepW:w7:X-A3
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:X-const
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438
DISPOSITION: NODE stepW:w7:X-const
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: stepW:w7:X-slope
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443
DISPOSITION: NODE stepW:w7:X-slope
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7a

ITEM: bpW:w7:count
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:count@L449-L452
DISPOSITION: NODE bpW:w7:count
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: heading:bpW:w7
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: heading:bpW:w7:ext
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext@L43-L43
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: heading:bpW:w7:indices
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:indices@L80-L80
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: heading:bpW:w7:unpert
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:unpert@L122-L122
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: heading:bpW:w7:constants
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:constants@L209-L209
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: heading:bpW:w7:interface-sec
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:interface-sec@L253-L253
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: heading:bpW:w7:basic
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:basic@L315-L315
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L99
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L99-L99
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L120
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L120-L120
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L132
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L132-L132
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L169
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L169-L169
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L205
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L205-L205
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L232
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L232-L232
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L281
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L281-L281
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L335
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L335-L335
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L357
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L357-L357
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L372
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L372-L372
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L395
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L395-L395
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L418
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L418-L418
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L445
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L445-L445
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:source-L458
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L458-L458
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L3-L8
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L3-L8
DISPOSITION: EXCLUDED
REASON: introduction
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L10-L21
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L10-L21
DISPOSITION: EXCLUDED
REASON: motivation (why the coarse estimate is not enough)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L23-L31
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L23-L31
DISPOSITION: EXCLUDED
REASON: route paragraph (outline)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L33-L41
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L33-L41
DISPOSITION: NODE bpW:w7#data
REASON: standing data of W7
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L45-L46
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L45-L46
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L77-L78
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L77-L78
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L124-L125
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L124-L125
DISPOSITION: NODE bpW:w7:omega0
REASON: notation lambda_J, b, A used in Definition bpW:w7:omega0
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: w7-measure:prose-L339-L343
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L339-L343
DISPOSITION: NODE bpW:w7:basic#data
REASON: fixed data of the zone lemmas
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a

ITEM: bpW:w7:prep
KIND: proposition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:prep@L462-L464
DISPOSITION: NODE bpW:w7:prep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:prep-0
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L467-L468
DISPOSITION: NODE stepW:w7:prep-0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:prep-plus
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L469-L473
DISPOSITION: NODE stepW:w7:prep-plus
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:prep-minus-group
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481
DISPOSITION: NODE stepW:w7:prep-minus-group
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:prep-j0
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L482-L493
DISPOSITION: NODE stepW:w7:prep-j0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:prep-n
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L494-L496
DISPOSITION: NODE stepW:w7:prep-n
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:prep-X
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L497-L499
DISPOSITION: NODE stepW:w7:prep-X
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:prep-sum
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503
DISPOSITION: NODE stepW:w7:prep-sum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: bpW:w7:iter
KIND: proposition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:iter@L510-L514
DISPOSITION: NODE bpW:w7:iter
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:it-plus
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L518-L520
DISPOSITION: NODE stepW:w7:it-plus
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:it-group
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526
DISPOSITION: NODE stepW:w7:it-group
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:it-j0
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532
DISPOSITION: NODE stepW:w7:it-j0
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:it-n
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L533-L536
DISPOSITION: NODE stepW:w7:it-n
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:it-sum
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540
DISPOSITION: NODE stepW:w7:it-sum
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:it-X
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543
DISPOSITION: NODE stepW:w7:it-X
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: bpW:w7:measurable
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L550-L553
DISPOSITION: NODE bpW:w7:measurable
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: stepW:w7:meas-cont
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L555-L557
DISPOSITION: NODE stepW:w7:meas-cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7b

ITEM: stepW:w7:meas-union
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L558-L559
DISPOSITION: NODE stepW:w7:meas-union
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w7b

ITEM: bpW:w7:measure
KIND: theorem
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:measure@L563-L570
DISPOSITION: NODE bpW:w7:measure
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:assemble
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:assemble@L572-L576
DISPOSITION: NODE stepW:w7:assemble
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:return
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:return@L577-L578
DISPOSITION: NODE stepW:w7:return
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:melnikov
KIND: corollary
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L585-L596
DISPOSITION: EXCLUDED
REASON: outside every root closure of track W (after the W4-W6 gap repair): its only consumer was Lemma bpW:w6:prep-step(i), which now argues directly from Definition bpW:w7:zones(i) (w6-iteration.tex L233, L250-L252); the remaining citations are in the excluded Remarks bpW:w7:w6-needs (L291) and bpW:w7:interface (L787); W6 cites Lemma bpW:w7:sep and Theorem bpW:w7:measure directly
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w7b

ITEM: bpW:w7:shells
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shells@L608-L612
DISPOSITION: NODE bpW:w7:shells
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:shell-geom
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shell-geom@L616-L620
DISPOSITION: NODE bpW:w7:shell-geom
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:partition
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:partition@L622-L624
DISPOSITION: NODE stepW:w7:partition
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:layer
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L625-L629
DISPOSITION: NODE stepW:w7:layer
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7b

ITEM: stepW:w7:shell-size
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:shell-size@L630-L631
DISPOSITION: NODE stepW:w7:shell-size
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:density
KIND: theorem
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:density@L635-L642
DISPOSITION: NODE bpW:w7:density
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:den
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:den@L644-L645
DISPOSITION: NODE stepW:w7:den
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:upper
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L646-L647
DISPOSITION: NODE stepW:w7:upper
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7b

ITEM: stepW:w7:lower
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L648-L653
DISPOSITION: NODE stepW:w7:lower
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7b

ITEM: stepW:w7:limit
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:limit@L654-L656
DISPOSITION: NODE stepW:w7:limit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:shell-est
KIND: corollary
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:shell-est@L661-L667
DISPOSITION: NODE bpW:w7:shell-est
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:exponents
KIND: claim
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L676-L691
DISPOSITION: NODE bpW:w7:exponents
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7b

ITEM: bpW:w7:dioph
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph@L697-L701
DISPOSITION: NODE bpW:w7:dioph
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:dioph-base
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-base@L703-L705
DISPOSITION: NODE stepW:w7:dioph-base
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:dioph-scale
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dioph-scale@L706-L707
DISPOSITION: NODE stepW:w7:dioph-scale
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:dioph-use
KIND: claim
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L713-L718
DISPOSITION: NODE bpW:w7:dioph-use
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w7b

ITEM: bpW:w7:limit
KIND: lemma
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:limit@L720-L725
DISPOSITION: NODE bpW:w7:limit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:lim-index
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lim-index@L727-L729
DISPOSITION: NODE stepW:w7:lim-index
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: stepW:w7:lim-est
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:lim-est@L730-L733
DISPOSITION: NODE stepW:w7:lim-est
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:errata
KIND: claim
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:errata@L739-L777
DISPOSITION: EXCLUDED
REASON: administrative remark (pages read, suspected P96-K errata, deviations)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w7:interface
KIND: claim
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:interface@L781-L791
DISPOSITION: EXCLUDED
REASON: administrative remark (consumed and supplied; pointers)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: heading:bpW:w7:prep-sec
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:prep-sec@L460-L460
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: heading:bpW:w7:iter-sec
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:iter-sec@L508-L508
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: heading:bpW:w7:main-sec
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:main-sec@L548-L548
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: heading:bpW:w7:density-sec
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:density-sec@L602-L602
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: heading:bpW:w7:dioph-sec
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-sec@L695-L695
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: heading:bpW:w7:check
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:check@L737-L737
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: heading:bpW:w7:summary
KIND: heading
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:summary@L779-L779
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L505
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L505-L505
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L545
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L545-L545
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L561
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L561-L561
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L580
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L580-L580
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L600
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L600-L600
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L613
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L613-L613
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L633
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L633-L633
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L658
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L658-L658
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L674
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L674-L674
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L692
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L692-L692
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L709
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L709-L709
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:source-L735
KIND: citation
SOURCE: blueprint-W/parts/w7-measure.tex#source@L735-L735
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: w7-measure:prose-L604-L606
KIND: proof-region
SOURCE: blueprint-W/parts/w7-measure.tex#prose@L604-L606
DISPOSITION: NODE bpW:w7:density-sec#data
REASON: P and B_h of clause (1)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7b

ITEM: bpW:w8:ext-inner
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-inner@L59-L64
DISPOSITION: NODE bpW:w8:ext-inner
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:ext-mono
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-mono@L65-L68
DISPOSITION: NODE bpW:w8:ext-mono
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:ext-compact
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-compact@L69-L71
DISPOSITION: NODE bpW:w8:ext-compact
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:ext-exp
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-exp@L72-L76
DISPOSITION: NODE bpW:w8:ext-exp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:ext-sqrt
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-sqrt@L77-L78
DISPOSITION: NODE bpW:w8:ext-sqrt
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:ext-dist
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-dist@L79-L81
DISPOSITION: NODE bpW:w8:ext-dist
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:ext-rpow
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-rpow@L82-L86
DISPOSITION: NODE bpW:w8:ext-rpow
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:ext-local
KIND: external
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-local@L87-L92
DISPOSITION: NODE bpW:w8:ext-local
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:const
KIND: definition
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:const@L100-L113
DISPOSITION: NODE bpW:w8:const
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:shells
KIND: definition
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L117-L128
DISPOSITION: NODE bpW:w8:shells
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta9-W-W-w8a

ITEM: bpW:w8:shell-data
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L132-L148
DISPOSITION: NODE bpW:w8:shell-data
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sd-size
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L150-L153
DISPOSITION: NODE stepW:w8:sd-size
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sd-trim
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L154-L159
DISPOSITION: NODE stepW:w8:sd-trim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sd-init
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L160-L167
DISPOSITION: NODE stepW:w8:sd-init
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sd-prep
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171
DISPOSITION: NODE stepW:w8:sd-prep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w8a

ITEM: bpW:w8:sharp-prep
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L178-L185
DISPOSITION: NODE bpW:w8:sharp-prep
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sp-step
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-step@L187-L188
DISPOSITION: NODE stepW:w8:sp-step
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sp-cmp
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L189-L193
DISPOSITION: NODE stepW:w8:sp-cmp
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:shell-iter
KIND: definition
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L198-L209
DISPOSITION: NODE bpW:w8:shell-iter
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:w6-general
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L212-L217
DISPOSITION: NODE bpW:w8:w6-general
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:g-app
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L221
DISPOSITION: NODE stepW:w8:g-app
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:g-freq
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-freq@L222-L223
DISPOSITION: NODE stepW:w8:g-freq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:g-excl
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224
DISPOSITION: NODE stepW:w8:g-excl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:g-tori
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-tori@L225-L226
DISPOSITION: NODE stepW:w8:g-tori
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:etor
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L231-L234
DISPOSITION: NODE bpW:w8:etor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:e-tor
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L239
DISPOSITION: NODE stepW:w8:e-tor
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:e-om
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L243
DISPOSITION: NODE stepW:w8:e-om
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: bpW:w8:freq-shell
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L248-L257
DISPOSITION: NODE bpW:w8:freq-shell
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:fs-lim
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L259-L261
DISPOSITION: NODE stepW:w8:fs-lim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:fs-low
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L262-L263
DISPOSITION: NODE stepW:w8:fs-low
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:fs-size
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L265
DISPOSITION: NODE stepW:w8:fs-size
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:fs-reg
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L268
DISPOSITION: NODE stepW:w8:fs-reg
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:torus-shape
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L275-L289
DISPOSITION: NODE bpW:w8:torus-shape
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:ts-bd
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L293
DISPOSITION: NODE stepW:w8:ts-bd
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:ts-real
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L299
DISPOSITION: NODE stepW:w8:ts-real
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:ts-per
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L302
DISPOSITION: NODE stepW:w8:ts-per
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:ts-cauchy
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L303-L306
DISPOSITION: NODE stepW:w8:ts-cauchy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:ts-ball
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L307-L309
DISPOSITION: NODE stepW:w8:ts-ball
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:Kshell
KIND: definition
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L314-L319
DISPOSITION: NODE bpW:w8:Kshell
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:shell-embedding
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L323-L325
DISPOSITION: NODE bpW:w8:shell-embedding
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:se-per
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-per@L328-L328
DISPOSITION: NODE stepW:w8:se-per
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:se-an
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L330
DISPOSITION: NODE stepW:w8:se-an
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:se-inj
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L331-L337
DISPOSITION: NODE stepW:w8:se-inj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:se-der
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L338-L349
DISPOSITION: NODE stepW:w8:se-der
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: bpW:w8:shell-close
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L355-L358
DISPOSITION: NODE bpW:w8:shell-close
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sc-tan
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L362-L365
DISPOSITION: NODE stepW:w8:sc-tan
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sc-dist
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L366-L369
DISPOSITION: NODE stepW:w8:sc-dist
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:sc-gamma
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L372
DISPOSITION: NODE stepW:w8:sc-gamma
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:sc-close
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L375
DISPOSITION: NODE stepW:w8:sc-close
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:sc-size
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377
DISPOSITION: NODE stepW:w8:sc-size
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: bpW:w8:shell-inv
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L383-L392
DISPOSITION: NODE bpW:w8:shell-inv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:si-weak
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L397
DISPOSITION: NODE stepW:w8:si-weak
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:si-tr
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L399
DISPOSITION: NODE stepW:w8:si-tr
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: stepW:w8:si-frozen
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L403
DISPOSITION: NODE stepW:w8:si-frozen
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: stepW:w8:si-cont
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L406
DISPOSITION: NODE stepW:w8:si-cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8a

ITEM: heading:bpW:w8
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: heading:bpW:w8:ext
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext@L55-L55
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: heading:bpW:w8:shell-sec
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-sec@L96-L96
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: heading:bpW:w8:iter-sec
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:iter-sec@L176-L176
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: heading:bpW:w8:tori-sec
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:tori-sec@L273-L273
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L114
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L114-L114
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L129
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L129-L129
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L173
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L173-L173
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L195
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L195-L195
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L210
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L210-L210
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L228
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L228-L228
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L245
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L245-L245
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L270
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L270-L270
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L311
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L311-L311
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L320
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L320-L320
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L351
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L351-L351
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L379
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L379-L379
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:source-L408
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L408-L408
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:prose-L5-L11
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#prose@L5-L11
DISPOSITION: EXCLUDED
REASON: introduction
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:prose-L13-L34
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#prose@L13-L34
DISPOSITION: EXCLUDED
REASON: outline of what W8 adds (pointers to the lemmas that carry it)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:prose-L36-L53
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#prose@L36-L53
DISPOSITION: NODE bpW:w8#data
REASON: standing data and notation of W8
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:prose-L57-L58
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#prose@L57-L58
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:prose-L93-L94
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#prose@L93-L94
DISPOSITION: EXCLUDED
REASON: layout
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: w8-assembly:prose-L98-L98
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#prose@L98-L98
DISPOSITION: NODE bpW:w8:const
REASON: all numbers are fixed after m and depend on m only (recorded in the CONSTANT_SCOPE of Definition bpW:w8:const)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a

ITEM: bpW:w8:patch
KIND: definition
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch@L413-L420
DISPOSITION: NODE bpW:w8:patch
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: bpW:w8:patch-local
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-local@L424-L428
DISPOSITION: NODE bpW:w8:patch-local
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:pl-dis
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-dis@L430-L431
DISPOSITION: NODE stepW:w8:pl-dis
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:pl-id
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pl-id@L432-L433
DISPOSITION: NODE stepW:w8:pl-id
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: bpW:w8:boundaries
KIND: claim
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:boundaries@L438-L445
DISPOSITION: EXCLUDED
REASON: explanatory remark (no cross-shell consistency is needed); its content is carried by Lemmas bpW:w8:patch-local and bpW:w8:patch-cont and Corollary bpW:w7:shell-est
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: bpW:w8:patch-cont
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-cont@L447-L450
DISPOSITION: NODE bpW:w8:patch-cont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:pc-borel
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-borel@L452-L452
DISPOSITION: NODE stepW:w8:pc-borel
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:pc-incl
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-incl@L453-L454
DISPOSITION: NODE stepW:w8:pc-incl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:pc-nu
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-nu@L455-L456
DISPOSITION: NODE stepW:w8:pc-nu
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:pc-K
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:pc-K@L457-L459
DISPOSITION: NODE stepW:w8:pc-K
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: bpW:w8:unique
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:unique@L465-L467
DISPOSITION: NODE bpW:w8:unique
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:u-raw
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-raw@L470-L473
DISPOSITION: NODE stepW:w8:u-raw
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:u-reg
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-reg@L474-L474
DISPOSITION: NODE stepW:w8:u-reg
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:u-energy
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-energy@L475-L480
DISPOSITION: NODE stepW:w8:u-energy
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:u-ineq
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-ineq@L481-L483
DISPOSITION: NODE stepW:w8:u-ineq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:u-gron
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:u-gron@L484-L486
DISPOSITION: NODE stepW:w8:u-gron
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: bpW:w8:winding
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:winding@L491-L494
DISPOSITION: NODE bpW:w8:winding
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:w-mod
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-mod@L496-L497
DISPOSITION: NODE stepW:w8:w-mod
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:w-const
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-const@L498-L498
DISPOSITION: NODE stepW:w8:w-const
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:w-rate
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:w-rate@L499-L499
DISPOSITION: NODE stepW:w8:w-rate
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: bpW:w8:nu-injective
KIND: lemma
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L503-L505
DISPOSITION: NODE bpW:w8:nu-injective
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:ni-same
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508
DISPOSITION: NODE stepW:w8:ni-same
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w8b

ITEM: stepW:w8:ni-diff
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513
DISPOSITION: NODE stepW:w8:ni-diff
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w8b

ITEM: bpW:w8:injective
KIND: proposition
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:injective@L517-L520
DISPOSITION: NODE bpW:w8:injective
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:in-orbit
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L527
DISPOSITION: NODE stepW:w8:in-orbit
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:in-birk
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L530
DISPOSITION: NODE stepW:w8:in-birk
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:in-freq
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L534
DISPOSITION: NODE stepW:w8:in-freq
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:in-act
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535
DISPOSITION: NODE stepW:w8:in-act
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:in-ang
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L537
DISPOSITION: NODE stepW:w8:in-ang
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: bpW:w8:nlw2-proof
KIND: theorem
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L547-L551
DISPOSITION: NODE bpW:w8:nlw2-proof
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:p-pos
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pos@L556-L557
DISPOSITION: NODE stepW:w8:p-pos
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-etapos
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etapos@L558-L558
DISPOSITION: NODE stepW:w8:p-etapos
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-etalim
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-etalim@L559-L559
DISPOSITION: NODE stepW:w8:p-etalim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-meas
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560
DISPOSITION: NODE stepW:w8:p-meas
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:p-incl
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L562
DISPOSITION: NODE stepW:w8:p-incl
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:p-nucont
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563
DISPOSITION: NODE stepW:w8:p-nucont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:p-Kcont
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L565
DISPOSITION: NODE stepW:w8:p-Kcont
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:p-dens
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dens@L566-L574
DISPOSITION: NODE stepW:w8:p-dens
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-dioph
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L578
DISPOSITION: NODE stepW:w8:p-dioph
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:p-lim
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582
DISPOSITION: NODE stepW:w8:p-lim
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta7-W-w8b

ITEM: stepW:w8:p-emb
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-emb@L583-L584
DISPOSITION: NODE stepW:w8:p-emb
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-close
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-close@L585-L588
DISPOSITION: NODE stepW:w8:p-close
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-size
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L590
DISPOSITION: NODE stepW:w8:p-size
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta6-W-W-w8b

ITEM: stepW:w8:p-inv
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inv@L591-L592
DISPOSITION: NODE stepW:w8:p-inv
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-pde
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-pde@L593-L595
DISPOSITION: NODE stepW:w8:p-pde
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-inj
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-inj@L596-L596
DISPOSITION: NODE stepW:w8:p-inj
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: stepW:w8:p-assembly
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-assembly@L597-L598
DISPOSITION: NODE stepW:w8:p-assembly
REASON: mechanical inventory of a labelled unit
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: bpW:w8:deviations
KIND: claim
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:deviations@L628-L650
DISPOSITION: EXCLUDED
REASON: administrative remark (pages read, deviations, list of results)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: heading:bpW:w8:patch-sec
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:patch-sec@L411-L411
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: heading:bpW:w8:inj-sec
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:inj-sec@L463-L463
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: heading:bpW:w8:proof-sec
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:proof-sec@L545-L545
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: heading:bpW:w8:check
KIND: heading
SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:check@L626-L626
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L421
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L421-L421
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L435
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L435-L435
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L461
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L461-L461
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L488
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L488-L488
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L501
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L501-L501
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L515
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L515-L515
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L539
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L539-L539
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:source-L600
KIND: citation
SOURCE: blueprint-W/parts/w8-assembly.tex#source@L600-L600
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

ITEM: w8-assembly:prose-L603-L624
KIND: proof-region
SOURCE: blueprint-W/parts/w8-assembly.tex#prose@L603-L624
DISPOSITION: EXCLUDED
REASON: summary table of the conjuncts and consumed results; each step's uses are recorded on its node
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8b

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
REVIEWER: sol-delta5-W-wh

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
REASON: administrative remark (declared weakenings W-A2, D30 Q3); no proof consumes it. Re-checked in wave 2: W6 L165 and W8 L601 cite it in source notes and W8 L34 in the excluded outline; the weakened clauses are the frozen statement itself
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: sol-delta5-W-wh

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
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-r2
REVIEWER: sol-delta3-W-wh

ITEM: w-headline:prose-L5-L9
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L6-L15
DISPOSITION: EXCLUDED
REASON: introduction (provenance D30, approval D41, list of the frozen declarations); administrative
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+claude-suborch-W-r2
REVIEWER: sol-delta3-W-wh

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
DISPOSITION: EXCLUDED
REASON: proof provenance only under SPEC import policy: stepW:w1:hacoef owns the Banach-target adaptation of K's finite-dimensional Cauchy argument, with W external suppliers ext-onevar and ext-integral; no W node applies the K theorem with its literal finite-dimensional target premise
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-imports

ITEM: K:bp:p1:strip-identity
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
DISPOSITION: NODE K:bp:p1:strip-identity
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-imports
