# GAP-DEF prover handoff (branch inp-gdef, 7123b457; off inp; package run by the main orchestrator)


Files (new, append-only): `KAM/Planetary/TwoScale/LimitMapDefs.lean` (~105 lines),
`KAM/Planetary/Preparation/SecEDefs.lean` (~100 lines). No existing file touched; KAM.lean not regenerated
(lint reports "KAM.lean is out of date" only because of the two new modules; orchestrator regenerates).

## bpP:p3:limitmap#data (blueprint-P/parts/p3b-two-scale-limit.tex:43)
| Source object | Lean |
|---|---|
| S, S^-1, \|.\|_* (pre-existing) | `sc`, `unsc`, `limitmap_data` (TwoScale/LimitMapScale.lean:42,37,30) |
| Gcheck = S G S^-1, arbitrary G, any RCLike 𝕜 | `limitmapCheck` (LimitMapDefs.lean:32); `limitmapCheck_apply` :36 (rfl); `limitmapCheck_comp` :40; `limitmapCheck_id` :46; `limitmapCheck_sc` :51 (Ǧ(Sw)=S(Gw)); `limitmapCheck_sub_id` :57 ((G-id)ˇ = Ǧ-id). Round trips need R≠0, s≠0. |
| L_* (Lipschitz constant in \|.\|_*) | `LipStar R s L S G` (:71) = ∀ x y ∈ S, \|Gx-Gy\|_* ≤ L\|x-y\|_*; set-indexed (source: on D_k×R^n), no ∀-on-whole-space version since that would be false for psi; `lipStar_iff_check` :75 (equivalent to max-norm Lipschitz bound of Ǧ on S(S)); `LipStar.mono` :82 |
| source use | `PsiSteps.psi_lipStar` :97: LipStar for G = psiR(Ψ_{j+1}) - id on phaseTube(D_{j+1}, ρ_{j+1}/2) with constant 192 n c^j Ê_j (instance of `psi_lip_step`) |

Note: LipStar is a predicate "L is a Lipschitz constant", not a chosen infimum constant (no choice/sup).

## bpP:p11:sec-E#data, F1 and F2 (p11-cp09-preparation.tex:189)
| Source object | Lean |
|---|---|
| polydisc {\|r\|<2, \|ρ'\|<π/2} | `p11SecEPolydisc n := p11Box 0 2 (π/2)` (SecEDefs.lean:25) |
| E = strip(σ_F/72) × polydisc (F1) | `p11SecE C` (:28); `mem_p11SecE` (:31) coordinate characterization |
| mapping iff (F2) | `p11Rescale_polydisc_iff` (:39): (∀ z, z.2 ∈ polydisc → (A_ε z).2 ∈ p11Box (p11SlowCenter C ε) (s₂/2) (πε/2)) ↔ 2ε ≤ s₂/2, premises 0<n, 0<ε only; `p11Rescale_secE_iff` (:89): same over z ∈ E (extra 0<σ_F) |
Not touched: signed `p11PreparedData` (F3), other sec-E pieces (H₂ identity, domain table, frequency map).

## Checks
- Gate build `KAM.Planetary.TwoScale.LimitMapDefs`, `KAM.Planetary.Preparation.SecEDefs`: success, no sorry, no new warnings from my files.
- `#print axioms` of psi_lipStar, lipStar_iff_check, p11Rescale_polydisc_iff, p11Rescale_secE_iff: propext, Classical.choice, Quot.sound.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; only message: KAM.lean out of date (expected).
- No heartbeat options, no EuclideanSpace, lines ≤ 100.

Uncertainties: LipStar domain choice (set-indexed) follows source's "on D_k×R^n". p11SecE uses `p11Box 0 2 (π/2)` (strict norms on complex actions) with the strip on z.1 — matches blueprint line 189's E (σ_3/6 = σ_F/72).
Errata/deviations: none.

ORCHESTRATOR RULING (OVERNIGHT 06:55; definition-node policy 02:30, owner to review): new UNSIGNED definitions for missing source objects of two definition nodes, each with characterization lemmas. This is both a package audit and a DEFINITIONS AUDIT.

AUDIT FOCUS: (1) bpP:p3:limitmap#data (blueprint-P/parts/p3b-two-scale-limit.tex:43; previous rows in docs/tracks/P/audits/DEFS-P2-audit-1.md ~96-102): one definitions-audit row per source object (S, S^-1, |.|_*, Gcheck, L_*, calD_j): Lean declaration | FAITHFUL / FAITHFUL-WITH-NOTE / NOT FAITHFUL / MISSING | reason (whole public carrier, no fallback, no arbitrary witness). Judge LipStar as a predicate 'L is a Lipschitz constant on S' against the source's 'L_* the Lipschitz constants in |.|_*'. Per-node verdict CLOSABLE (with LEAN_REF) or not. (2) bpP:p11:sec-E#data, gaps F1 and F2 of docs/tracks/P/audits/DEFS-P3-audit-1.md (blueprint p11-cp09-preparation.tex:189): is p11SecE the literal E (strip sigma_F/72 x polydisc radius (2, pi/2))? Does p11Rescale_polydisc_iff state the literal mapping iff (2 eps <= s2/2) under only 0 < n, 0 < eps? State whether F1 and F2 are resolved; F3 (signed p11PreparedData selector) is an owner question, out of scope. Audit KAM/Planetary/TwoScale/LimitMapDefs.lean and KAM/Planetary/Preparation/SecEDefs.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
