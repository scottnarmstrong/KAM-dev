# DEFS-P3: definitions audit for bpP:p11:sec-E#data and bpP:p5:rstar#Cgamma (main orchestrator; no new Lean)

Not a package audit of new code: the worktree is a clean copy of inp (which now contains the Part 11 preparation
chain: Preparation/PreparedData, PreparedBasic, Prepared, Amount, Datum, Wrapper*; and Part 5 PGAssembly).
Definition-node policy (OVERNIGHT 02:30, owner to review): a pure definition node closes by naming the Lean
definitions that ARE the source's objects, plus a definitions-audit row classifying each one; a property the node
asserts needs a named lemma.

Node records (from docs/graph/P/DEPGRAPH.md):

### bpP:p11:sec-E#data
STATEMENT_SOURCE: blueprint-P/parts/p11-cp09-preparation.tex#bpP:p11:sec-E#data@L189-L194
SOURCE_CONCLUSION: defines: rho tilde_0 = (2 pi eps, ..., 2 pi eps), the eps-chart A_eps(theta, r, zeta, rho prime) = (theta, J_0 + eps r, zeta, eps(2 pi 1 + rho prime)) with A_eps^*(dJ^dtheta + d rho tilde^dzeta) = eps(dr^dtheta + d rho prime^dzeta), mapping {¦r¦ < 2, ¦rho prime¦ < pi/2} into V_2/2 iff 2 eps <= s_2/2; E = {¦Im(theta, zeta)¦ < sigma_3/6, ¦r¦ < 2, ¦rho prime¦ < pi/2}; N_eps = (h_0 + g_2) o A_eps/eps, P_eps = f_3 o A_eps/eps, H hat_eps = H_2 o A_eps/eps = N_eps + P_eps with H_2 = H o Phi^1_eps o Theta hat o Psi_2; the KAM datum entries K_eps = [-1/2, 1/2]^{2n}, theta = 1/4, eps^* = 1/2, s = s_* = sigma_3/6 = sigma_F/72, N = 2n, mu = mu bar, tau_D = max{n mu bar, 2n}; the domain table; hat omega_eps = (omega hat^(1), eps omega hat^(2)) with omega hat^(1) = omega + eps d_J G hat_0 + d_J g_2, omega hat^(2) = Omega tilde + d_rho Z hat + eps^{-1} d_rho g_2
LEAN_NOTE: P11A-P7 gives only p11Rescale/p11PreparedBox; A_eps, N_eps, P_eps, KAM datum, domain table not covered; partial

### bpP:p5:rstar#Cgamma
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L152-L152
SOURCE_CONCLUSION: C_gamma := G(30/s_*)^(tau+1)
LEAN_NOTE: -

AUDIT FOCUS: for EVERY source object of each node (read the STATEMENT_SOURCE blueprint lines; for sec-E#data these
include A_eps, N_eps, P_eps, the KAM datum and the domain table), locate the landed Lean definition(s) (search
KAM/Planetary/Preparation/**, KAM/Planetary/PGAssembly/**, the design docs' node tables in docs/tracks/P/design/,
the signature files /root/code/KAM-inp/.drafts/design/*Signatures.lean, and the audits in docs/tracks/P/audits/),
and give one row per object: source object | Lean declaration (file:line) | FAITHFUL / FAITHFUL-WITH-NOTE /
NOT FAITHFUL / MISSING | reason (body equals the source formula on the whole public carrier; no fallback branch, no
arbitrary witness, no off-source behaviour; signed definitions follow the signature files). Then a per-node
verdict: CLOSABLE (list the LEAN_REF) or NOT CLOSABLE (exactly what is missing or unfaithful). Do not edit any file
other than your report docs/tracks/P/audits/DEFS-P3-audit-1.md.
