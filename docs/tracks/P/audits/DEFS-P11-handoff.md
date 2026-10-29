# DEFS-P11: definitions audit for three Part 11 / 11b definition nodes (main orchestrator; no new Lean)

This is NOT a package audit of new code: the worktree is a clean copy of inp. It is a DEFINITIONS audit under the
orchestrator's definition-node policy (OVERNIGHT 02:30, for owner review): a pure definition node closes by naming
the Lean definitions that ARE the source's objects, plus a definitions-audit row classifying each one.

Nodes (read each NODE record in docs/graph/P/DEPGRAPH.md, its STATEMENT_SOURCE lines and LEAN_NOTE):
1. bpP:p11:sec-conv#data (blueprint-P/parts/p11-cp09-preparation.tex L10-L12): the weighted norm wn, T_sigma, the
   polydisc D(c,r) and the 1-chart.
2. bpP:p11:sec-D#data (p11-cp09-preparation.tex L145-L153): Pi / the polar shell, G-hat, alpha_(i), r_*, sigma_3.
3. bpP:p11b:sec-set#data (blueprint-P/parts/p11b-planar-torsion.tex L14-L16): the Laplace coefficients, sigma_i,
   rho, Phi_4, NR_4, beta_0/beta_1, the complex notation and the slow variables (T1-audit-1.md already classifies
   PlanarData, axes/actions, hat functions and the secular average).

AUDIT FOCUS: for EVERY source object listed, locate the landed Lean definition(s) that implement it (search
KAM/Planetary/**, KAM/Frozen/**, the P11A/P11B/P11C design docs' node tables in docs/tracks/P/design/, and the audits
in docs/tracks/P/audits/), and give one row per object: source object | Lean declaration (file:line) | verdict
FAITHFUL / FAITHFUL-WITH-NOTE / NOT FAITHFUL / MISSING | reason (body equals the source formula on the whole public
carrier; no fallback branch, no arbitrary witness, no off-source behaviour; signed definitions follow the signature
files in /root/code/KAM-inp/.drafts/design/*Signatures.lean). Then a per-node verdict: CLOSABLE (every object
FAITHFUL, list the LEAN_REF) or NOT CLOSABLE (list exactly what is missing or unfaithful). Do not edit any file
other than your report. Write the report to docs/tracks/P/audits/DEFS-P11-audit-1.md.
