# Track LP, slice LP-imports (writer-owned): IMPORTED nodes from other tracks' graphs (SPEC §3). KIND external,
# LEAN_STATUS EXTERNAL, PROOF_SOURCE -, DEPS -, source fields copied verbatim from docs/graph/N/DEPGRAPH.md.
# Wave 2: Lemma 13 consumes KAM.Nekhoroshev.nonresonant (graph N node bpN:p11:nonresonant). The candidates
# N:bpN:p11:s-nf#data (its hypotheses are restated in the nonresonant record), N:bpN:p0:partial and the P imports
# (LP3 only) are not used by any extracted proof and are not rendered.

NODES = {
    "N:bpN:p11:nonresonant": dict(
        kind="external", title="[N] Nonresonant stability in the extended phase space (KAM.Nekhoroshev.nonresonant)",
        stmt="blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L68", proof="-",
        H="r,s,K_a,alpha>0, L>=0, p>1, q=p/(p-1), kappa=2 pi K_a s>=6; r=r_B; h holomorphic on V_r(I_c), real on real "
          "points; ¦k.omega(I_c)¦>=alpha for 0<¦k¦_1<=K_a (cond-nr, Lambda={0}), cond-L with L, K_a L r<=alpha/p; (SL); "
          "f in O(r,s)^{e,R}, ¦f¦<=eps with eps>0, eps<=alpha r/(2^7 q K_a); H=h+f; T_nr=(s r/(5 eps))e^{kappa/6}",
        Q="r,s,K_a,alpha,L,p; h; f; eps; F; J; y; t_1",
        C="for every F with F=X^c_{H^R} on W^e_r, J containing 0, y with y'=F(y) on J, y(0)=(theta_0,I_c,x-tilde_0), "
          "x-tilde_0 in S-tilde, and t_1 in J with ¦t_1¦<=T_nr and x-tilde(u) in S-tilde between 0 and t_1: "
          "¦I(u)-I_c¦<=r/2 between 0 and t_1",
        S="none",
        note="IMPORTED: proved in the track-N graph, node bpN:p11:nonresonant (there KIND proposition, contract "
             "bpN:p11:nonresonant v1); Lean theorem KAM.Nekhoroshev.nonresonant cited by MAIN L433 (never read here)"),
}
NEWCOV = [
    ("N:bpN:p11:nonresonant", "citation", "blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L68",
     "NODE N:bpN:p11:nonresonant", "imported node consumed by Lemma 13 (MAIN L433, L460); the MAIN citation item "
     "lpM:L13#cite-repository maps to it as well"),
]
