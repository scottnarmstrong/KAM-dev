# N10-5 prover handoff (branch inp-n105, 8af71688; contains N10-4 and N10-3 (both in audit; N10-3 in a re-scope audit per the 18:47 ruling), N10-1/2 on inp; offloaded package run by the main orchestrator; PROVIDER package for the frozen DRAFT_SORRY anchor KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound)


Files: KAM/Nekhoroshev/Assembly/Headline.lean (new, ~55 lines): `KAM.Nekhoroshev.head`, statement VERBATIM
from N10Signatures.lean. KAM/Provider/Nekhoroshev/QuasiConvexNekhoroshevComplexBound.lean (stub filled):
`KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound`, telescope verbatim from the signature file.

Approach: `head` = `HeadHyp` from H1-H5, `existence` for z, `hypotheses_check` (.1) for `Data`, then
`uniqueness` (initial value converted via hz0). Provider: p := HeadParams.mk R s M m Mcomplex ωmin,
hp := Pos.mk ..., witnesses p.C p.T p.c p.eps0, `choice_props` first five conjuncts, rest is `head hn p hp`
(tau/rho/expo unfold definitionally). Provider imports only Assembly.Headline.

Checks: gate build of both modules: success (3340 jobs), no warnings in my files (only pre-existing
unused-variable warnings in Existence/Stability). `#print axioms` of provider and head:
[propext, Classical.choice, Quot.sound]. scripts/lint_sources.sh: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK,
ABI HASHES OK; it also reports "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module
Headline; KAM.lean not edited per rules, integrator regenerates). No line > 100 columns.

Uncertainties/errata/deviations: none. No heartbeat issues. Frozen anchor and manifest untouched (sealing left to integrator).

AUDIT FOCUS (design docs/tracks/N/design/N10-LEAN-DESIGN.md: row N10-5, the 'Frozen binder/result | Assembly' table, Appendix A; its design audit; signatures /root/code/KAM-inp/.drafts/design/N10Signatures.lean lines ~203 (head) and ~226 (provider); manifest/frozen-anchors.json entry for the anchor and its frozen file): this is a SEAL-KEY audit. (1) head = signature file EXACTLY; (2) KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound has EXACTLY the frozen anchor's type: compile an exact-type probe (example : type_of% @<frozen> := @<provider>) and a prospective seal (copy the frozen declaration under a fresh name with body 'by exact <provider application>'); the provider file imports only Assembly/Headline; (3) the assembly follows the design's binder/result table (HeadParams.mk/Pos.mk, witnesses p.C, p.T, p.c, p.eps0 before all data, choice_props, head via existence and uniqueness, the drift and uniqueness clauses, EqOn including L=0) with no added premise and no hard step as a hypothesis; (4) the full chain N10-1..N10-5 is consistent: in particular the deliberately narrowed signed cf_branch (|t| <= 2T) suffices for the frozen time horizon; (5) quarantine: no module other than the anchor will import the provider; no DRAFT_SORRY import; #print axioms of the provider is [propext, Classical.choice, Quot.sound]; kernel replay; (6) hygiene: no EuclideanSpace, no reused public HELPER short name, lines <= 100. Audit KAM/Nekhoroshev/Assembly/Headline.lean and KAM/Provider/Nekhoroshev/QuasiConvexNekhoroshevComplexBound.lean (read Confinement/Existence as needed).
