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
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: -

ITEM: K:bp:p1:strip-identity
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
DISPOSITION: NODE K:bp:p1:strip-identity
REASON: imported node (track K): its statement is proved, or is an external input, in the track-K graph; not extracted here
COVERAGE_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-delta-W-imports
