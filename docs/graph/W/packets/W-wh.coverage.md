ITEM: bpW:wh:lintorus
KIND: definition
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:lintorus@L18-L20
DISPOSITION: NODE bpW:w0:periodone#linearTorus
REASON: restates Convention bpW:w0:periodone; the frozen KAM.Wave.linearTorus is bound to that node
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

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
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

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
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: bpW:wh:weakenings
KIND: claim
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:weakenings@L91-L101
DISPOSITION: EXCLUDED
REASON: administrative remark (declared weakenings W-A2, D30 Q3); no proof consumes it
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: heading:bpW:wh
KIND: heading
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh@L1-L1
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: heading:bpW:wh:defs
KIND: heading
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:defs@L11-L11
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: heading:bpW:wh:statement
KIND: heading
SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:statement@L39-L39
DISPOSITION: EXCLUDED
REASON: section heading; its results are inventoried separately
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: w-headline:source-L102
KIND: citation
SOURCE: blueprint-W/parts/w-headline.tex#source@L102-L102
DISPOSITION: EXCLUDED
REASON: provenance note for a result proved in the blueprint (confirm; an unproved cited input must instead become an external node)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: w-headline:prose-L3-L3
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L3-L3
DISPOSITION: EXCLUDED
REASON: status line (\proposed), superseded by the owner freeze D41
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: w-headline:prose-L5-L9
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L5-L9
DISPOSITION: EXCLUDED
REASON: introduction (provenance, D30)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -

ITEM: w-headline:prose-L13-L16
KIND: proof-region
SOURCE: blueprint-W/parts/w-headline.tex#prose@L13-L16
DISPOSITION: NODE bpW:wh:nlw2
REASON: fixes the data of the statement (m, a = p = 1, E, U_m, V_m, G_q, P, r(I), B_h)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
