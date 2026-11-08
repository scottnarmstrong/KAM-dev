import json,sys
P='docs/explorations/program-b-plan.md'
rev=json.load(open(sys.argv[2])) if len(sys.argv)>2 else {}
items=[
('b:2.1#conventions','heading',f'{P}#b:2.1@L66-L99','NODE b:defs#hamiltonianVectorField, b:defs#symplecticForm, b:defs#bracket, b:brief2#uniqueness, b:2.2#B1-T, b:2.3#B1-E','field, form and bracket conventions are definition nodes; the solution-quantifier conventions L90-L99 are realized in the two roots and the uniqueness step'),
('b:2.2#statement','theorem',f'{P}#b:2.2@L100-L136','NODE b:2.2#B1-T','the B1-T statement'),
('b:2.2#isotropic','corollary',f'{P}#b:2.2@L138-L141','EXCLUDED','isotropic specialization and all-time remark; not used by either root'),
('b:2.2#transfer','corollary',f'{P}#b:2.2@L143-L155','NODE b:2.3#transfer, b:4#inverse-chart','B1-T observable transfer (proof source of b:2.3#transfer) and the inverse-chart requirement L153-L155'),
('b:2.2#source-and-proof','proof-region',f'{P}#b:2.2-source-and-proof@L157-L163','NODE b:2.2#action-derivative, b:2.2#first-exit, b:2.2#periodic-reduction, b:brief2#stopped-drift','proof sketch of B1-T: stopped drift, first exit, periodic continuation'),
('b:2.2#gls17','citation',f'{P}#b:2.2-source-and-proof@L157-L163','NODE b:2.2#B1-T','GLS17 §4.3 is provenance of the derivation reproduced in the plan'),
('b:2.3#oscillatorAction','definition',f'{P}#b:2.3@L167-L173','NODE b:defs#oscillatorAction','frozen oscillator action reused'),
('b:2.3#statement','theorem',f'{P}#b:2.3@L175-L193','NODE b:2.3#B1-E','the B1-E statement'),
('b:2.3#continuation','proof-region',f'{P}#b:2.3-continuation@L195-L199','NODE b:2.3#first-exit, b:2.3#normal-form-commutes, b:2.3#compact-continuation','no exit through I_j=0, compact continuation set, algebraic lemma'),
('b:2.3#transfer','corollary',f'{P}#b:2.3@L201-L201','NODE b:2.3#transfer','oscillator observable transfer, used by the HH physical bounds'),
('b:2.3#cl20','citation',f'{P}#b:2.3-continuation@L202-L205','NODE b:2.3#B1-E','CL20 §4.1 provenance of the action-bracket estimate'),
('b:2.4#approval','heading',f'{P}#b:2.4@L207-L226','EXCLUDED','approval-surface policy, no mathematics'),
('b:brief2#proof-sequence','proof-region',f'{P}#b:brief2-proof-sequence@L847-L855','NODE b:brief2#chart-transport, b:brief2#stopped-drift, b:brief2#uniqueness, b:2.2#action-derivative, b:2.2#first-exit, b:2.2#periodic-reduction, b:2.3#action-bracket, b:2.3#normal-form-commutes, b:2.3#first-exit, b:2.3#compact-continuation, ext:ode#local','proof sequence for both roots; edge cases (T=0, eta=0, zero actions) recorded in the first-exit/continuation NOTEs; the observable estimate (L853-L854) is the excluded transfer corollary'),
('ext:continuation','external',f'{P}#b:brief2-proof-sequence@L851-L851','NODE ext:ode#compact-continuation','"the existing continuation theorem"'),
('ext:picard','external',f'{P}#b:brief2-proof-sequence@L854-L854','NODE ext:ode#local','"Handle T=0 by local existence" and local uniqueness'),
('b:brief2#objective-scope','proof-region',f'{P}#b:brief2@L833-L846','EXCLUDED','task scope and policy; its mathematical constraint (no Diophantine or nondegeneracy premise) is reflected in the roots hypotheses'),
('b:brief2#outputs-checks','proof-region',f'{P}#b:brief2@L857-L870','EXCLUDED','process and handoff rules; the reviewer rule L863-L864 (first exit must not assume the existence interval) is enforced in the first-exit nodes quantifiers'),
('freeze#B1-T','theorem','docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L24-L54','NODE b:2.2#B1-T','exact frozen text of torus_confinement (statement source of the root)'),
('freeze#B1-E','theorem','docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L57-L95','NODE b:2.3#B1-E','exact frozen text of oscillator_confinement (statement source of the root)'),
('freeze#deviations','heading','docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-6@L161-L166','NODE b:2.2#B1-T, b:2.3#B1-E','owner-approved deviations from the plan statement, recorded in the roots NOTE'),
('freeze#scaffold-open','heading','docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L17-L23','EXCLUDED','section heading, code fence, open Set and namespace line; no mathematics'),
('freeze#scaffold-close','heading','docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L96-L99','EXCLUDED','proof placeholder, end namespace and code fence; no mathematics'),
('b:3.1#certificate-table','proof-region',f'{P}#b:3.1@L300-L323','NODE b:3.1#checker-soundness, b:4#model-identification, b:3.2#chart-composition, b:3.2#oscillator-drift','certificate contents and checked meanings (L304-L310 model, L317-L318 domains and flows, L319-L322 bounds)'),
('b:3.1#soundness','claim',f'{P}#b:3.1@L324-L340','NODE b:3.1#checker-soundness, b:4#certificate-accepted','soundness shape, no-extra-premise rule, kernel replay of producer data (L338-L340)'),
('b:4#model','display',f'{P}#b:4-first-instance@L529-L537','NODE b:4#model-identification, b:4#HH','the HH model (Appendix B of CL20)'),
('b:4#target','theorem',f'{P}#b:4-first-instance@L539-L543','NODE b:4#HH','the proposed application theorem, frozen as D73'),
('b:4#certificate','display',f'{P}#b:4-first-instance@L545-L553','NODE b:4#certificate-accepted, b:4#inverse-chart','literals of the sufficient certificate, forward and inverse displacement'),
('b:4#inequalities','proof-region',f'{P}#b:4-first-instance@L554-L557','NODE b:4#initial-inclusion, b:4#physical-bounds','the three transparent inequalities and the outer bound'),
('b:4#commentary','heading',f'{P}#b:4-first-instance@L558-L559','EXCLUDED','remark on volume and indefinite energy; no proof obligation'),
('freeze-hh#header','heading','docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L1-L14','EXCLUDED','approval record and placement; provenance of the root'),
('freeze-hh#docstring','heading','docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L15-L19','EXCLUDED','freeze-time docstring (commentary)'),
('freeze-hh#statement','theorem','docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L20-L36','NODE b:4#HH','exact frozen text of henonHeiles_confinement'),
('freeze-hh#provenance','heading','docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L37-L41','EXCLUDED','code fence and literal provenance (E1, OD-B18)'),
('b:3.2#lie','display',f'{P}#b:3.2@L341-L356','NODE b:3.2#lie-identity, b:3.2#chart-composition','Lie identity, remainder bound, canonical composition'),
('b:3.2#fourier','display',f'{P}#b:3.2@L358-L371','EXCLUDED','torus Fourier-Taylor norms; no oscillator root uses them'),
('b:3.2#oscillator','proof-region',f'{P}#b:3.2@L373-L385','NODE b:3.2#oscillator-drift','oscillator bracket bounds and Cartesian Cauchy tails'),
('b:3.2#tail','proof-region',f'{P}#b:3.2@L387-L397','EXCLUDED','CL-style infinite-majorant (Tail) formula, not used by the finite-order HH route'),
('b:3.2#propagation','proof-region',f'{P}#b:3.2@L398-L402','NODE b:3.2#oscillator-drift, b:3.2#chart-composition','eta decomposition and propagation through charts'),
('ext:cauchy','external',f'{P}#b:3.2@L382-L384','NODE ext:analysis#cauchy','Cauchy estimate behind the Cartesian tail contribution'),
('b:3.2#provenance','citation',f'{P}#b:3.2@L404-L406','NODE b:3.2#oscillator-drift','CL20 provenance of the majorant strategy'),
('b:3.3#divisors','heading',f'{P}#b:3.3@L408-L416','EXCLUDED','divisor witnesses are producer-side: an arbitrary generator is allowed (L317) and a bad one fails the checked inequality (L337); OD-B12'),
('b:3.3#units','heading',f'{P}#b:3.3@L418-L424','EXCLUDED','unit and time rescalings; HH uses no rescaling (b:4#certificate-accepted)'),
('b:4#cl20-computation','citation',f'{P}#b:4-first-instance@L560-L566','EXCLUDED','CL20 reported computation: motivation of the literals, explicitly not a certificate (L564-L565)'),
]
out=['# Proof-source coverage manifest — track B','','CORPUS: docs/explorations/program-b-plan.md (§2.1–2.3 L66–L206, §3.1 L300–L340, §3.2–3.3 L341–L424, §4 first instance L529–L566, Brief 2 L833–L870), docs/tracks/B/FREEZE-PROPOSAL.md (§2 L17–L99, §6 L161–L166) and docs/tracks/B/FREEZE-PROPOSAL-HH.md (L1–L41), pinned by SHA-256 in docs/graph/B/CORPUS.sha256 (main 95387f9b0, 2026-11-03)','','## Inventory','']
for i,k,s,d,r in items:
    v=rev.get(i,{})
    out+=[f'ITEM: {i}',f'KIND: {k}',f'SOURCE: {s}',f'DISPOSITION: {d}',f'REASON: {r}',f"COVERAGE_STATUS: {v.get('status','PROPOSED')}",'EXTRACTOR: kam-b1',f"REVIEWER: {v.get('reviewer','-')}",'']
open(sys.argv[1],'w').write('\n'.join(out))
