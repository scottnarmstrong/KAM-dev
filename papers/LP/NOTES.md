# LP paper: plan, notation, claims ledger

Editor: kam-paper (paper sub-orchestrator). Started 2026-11-01 09:02 UTC. Branch `paper-lp`, directory `papers/LP/`.

## 0. Authorities

| Role | Source |
|---|---|
| Mathematics (ground truth) | `/root/code/KAM/docs/tracks/LP/source/MAIN.md` (cite `MAIN L<k>`; MAIN lines are those of the pinned file) as amended by `source/AMENDMENTS.md` (N1–N12, normative), audit `PROOF-AUDIT-1.md` |
| LP3 mathematics | `/root/code/KAM/docs/tracks/LP/lp3/LP3-PLAN.md` (+ `LP3-PLAN-REVIEW-1.md`); Lean on branch `inp-lp-lp3src` |
| Statements as formalized | Lean on `main` @ `a994efdf` (LP0–LP2); branch `inp-lp-lp3src` @ `402de5f7` (LP3); `docs/tracks/LP/FREEZE-PROPOSAL.md` (draft 6), `freeze/STATEMENT-REVIEW-*.md` |
| Literature | `docs/explorations/amd-crossing/A2-literature.md` (page pins), PDFs under `/root/code/KAM/sources/` and `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/RESEARCH/_sources/` |
| Practicality | `docs/explorations/amd-crossing/A7-practical.md` |
| Style | `latex-math-writing` skill, HCP-final exemplar; preamble in `main.tex` |

Rules: brief `/root/code/KAM-inp/.drafts/briefs/offload-main/paper-LP.md` (honesty rules binding).

## 1. Outline and page budget (hard cap 25 pages total; target ≤ 23)

| § | File | Writer | Content | Budget (pp) |
|---|---|---|---|---|
| — | `sections/abstract.tex` | A | abstract (≤ 180 words) | 0.3 |
| 1 | `sections/intro.tex` | A | AMD; Laskar–Petit AMD-stability and the conjecture (quoted, LP17 §3); chaos vs. collision safety; informal statement of results; mechanism (AM confinement + exponentially slow drift of fast actions); prior art (Nekhoroshev 1977, Pöschel 1993, Niederman 1996, Barbieri–Niederman, Pinzari; others from A2 only if pinned); honest scope (asymptotic, not practical; no Solar System claim; novelty unverified); formal verification in one paragraph; organization | 3.5 |
| 2 | `sections/results.tex` | A | the model (Hamiltonian (1), elements (2), chamber, thresholds (3), frequencies (4), Diophantine (5)); Theorem A = LP0 (barrier); Theorem B = LP1 (planar); Theorem C = LP2 (spatial); Corollary D = τ = n − 1/2; Theorem E = LP3; remarks on quantifier order, constants, what is not claimed | 3 |
| 3 | `sections/barrier.tex` | B | MAIN L1 (normalization, brief), L2 (orbital identities), L3 (AM conservation and AMD identity), L4 (thresholds attained, continuous, sharp; identification with LP17), L5 (uniform barrier = proof of Thm A), L6 (moving threshold + continuation) | 3 |
| 4 | `sections/planar.tex` | B | L7 (regular planar Poincaré chart), L8 (whole-sublevel analytic domain), L9–L11 (Fourier/commutator estimates, Lie step, exponential normal form on full slow set — presented as standard, Pöschel-type, not new), L12 (scaling, √μ, exponential time; L13 remark: Lean route uses the repository's finite-cutoff normal form), L14 (first exit), proof of Thm B, L16 (osculating) | 5.5 |
| 5 | `sections/spatial.tex` | C | L17 (regular spatial Poincaré chart), L18 (spatial domain, alignment with L), proof of Thm C and Cor D | 1.5 |
| 6 | `sections/resonant.tex` | C | LP3: partial Nekhoroshev theorem (Nek77 Thm 4.4 p.30, convex specialization), finite cover of the sharp sublevel by cells, cellwise forward/backward application, μ₀ minimum, drift radius μ^{b_n}, first exit unchanged; proof of Thm E; comparison table | 2 |
| 7 | `sections/outlook.tex` | C | limitations (asymptotic, non-explicit constants; A7 real masses out of reach), open questions | 1 |
| App. A | `sections/formal.tex` | C | formalization: what is verified, what is not (faithfulness of definitions by review), table paper result ↔ Lean declaration (file, name, commit), axioms; status (LP0–LP2 on main, audited; LP3 on branch, audits in progress; freeze pending) | 2.5 |
| — | bibliography | all | `refs.bib` (editor) + `refs-A/B/C.bib` (writer-owned) | 1 |

"Over the allowance = not done."

## 2. Labels (fixed; every writer uses exactly these)

Theorems (lettered): `thm:barrier` (A, LP0), `thm:planar` (B, LP1), `thm:spatial` (C, LP2), `cor:half` (D), `thm:resonant` (E, LP3).
Displays in §2 (writer A): `eq:H` (Hamiltonian), `eq:elements` (elements, AMD), `eq:chamber`, `eq:thresholds` (B_ij, B_cross, B_⋆, B), `eq:freq` (h, ω), `eq:dioph`, `eq:hyp` (initial hypotheses), `eq:time` (T_μ).
Lemmas: §3 `lem:normalization` (L1), `lem:orbital` (L2), `lem:amd` (L3), `lem:threshold` (L4), `lem:uniform` (L5), `lem:moving` (L6); §4 `lem:chart` (L7), `lem:domain` (L8), `lem:fourier` (L9), `lem:lie` (L10), `lem:nf` (L11), `lem:scaling` (L12, with L13 as a remark `rem:engine`), `lem:exit` (L14), `lem:osc` (L16); §5 `lem:spchart` (L17), `lem:spdomain` (L18); §6 `thm:partialnek` (the partial Nekhoroshev theorem used as input, stated as a Theorem/Proposition with citation), `lem:cover`.
Sections: `sec:intro`, `sec:results`, `sec:barrier`, `sec:planar`, `sec:spatial`, `sec:resonant`, `sec:outlook`, `app:formal`.

## 3. Notation (MAIN's conventions; macros in `macros.tex`)

| Symbol | Meaning | Source |
|---|---|---|
| n ≥ 2, d ∈ {2,3} | number of planets, space dimension | MAIN §1 |
| m_i = μν_i, ν_i > 0 | planet masses; star mass 1, G = 1. MAIN normalizes max ν_i = 1; the Lean general theorems drop this (μ is then a mass scale) | MAIN §1, OD-3 |
| q_i, p_i | heliocentric positions, scaled canonical momenta (physical momentum μp_i); form Σ dp_i∧dq_i | MAIN (1) |
| H_μ = Σ(|p_i|²/2ν_i − ν_i/|q_i|) + μ f, f = ½|Σp_i|² − Σ_{i<j} ν_iν_j/|q_i−q_j| | exact Hamiltonian, physical time | MAIN (1) = `eq:H` |
| v_i = p_i/ν_i, E_i, **e**_i | canonical velocity, specific energy, eccentricity vector | MAIN §1 |
| a_i = −1/(2E_i), Λ_i = ν_i√a_i, e_i = |**e**_i| | semi-major axis, Delaunay action, eccentricity. **Use Λ (not I) in the paper**; MAIN writes I = Λ | MAIN (2) |
| L_i = q_i×p_i, L = ΣL_i, C = ΣΛ_i − |L| | angular momenta and the (normalized) AMD; physical AMD is μC | MAIN (2) |
| D(u) = 1 − √(1−u²) | eccentricity deficit function | MAIN §1 |
| 𝒬 = {Λ: Λ_i > 0, (Λ_1/ν_1)² < … < (Λ_n/ν_n)²} | action chamber (ordered axes) | MAIN §1 |
| B_ij(Λ), B_cross, B_⋆ = min Λ_i, B = min(B_cross, B_⋆) | pair threshold (min over contact), strong threshold | MAIN (3) |
| h(Λ) = −Σν_i³/(2Λ_i²), ω_i = ν_i³/Λ_i³ | Kepler Hamiltonian, mean motions | MAIN (4) |
| |k·ω(Λ⁰)| ≥ γ|k|₁^{−τ}, k ∈ ℤⁿ∖0 | Diophantine condition (|k|₁ = Σ|k_i|) | MAIN (5) |
| 𝒜 ⊂ {0 < a_1 < … < a_n} compact; δ > 0 | axes window; normalized AMD margin | MAIN §1 |
| T_μ = T₀ exp(c μ^{−1/(2(τ+1))}) | stability time | MAIN (7) |
| d_⋆, d_pair, A_Λ, A_a, A_osc, A_el | separation and drift constants (A_el = Lean `Aelem`) | MAIN (8)–(9), Lean |
| a_n = 2/(6n²−3n+14), b_n = 3/(6n²−3n+14) | LP3 time and drift exponents | `planetaryTimeExponent`, `planetaryDriftExponent` |
| (Λ, λ, x, y) / (Λ, λ, x, y, u, v) | regular Poincaré variables, Γ = (x²+y²)/2, Z = (u²+v²)/2 | MAIN L7, L17 |
| ‖·‖_∞ | max norm on action vectors | MAIN §1 |

Avoid: campaign jargon (anchor, freeze, OD, codex, wave, package, provider, track, LP0/LP1… as names in the text — use Theorem A–E; "LP" in the paper means Laskar–Petit only).

## 4. Claims ledger

Status column: ☐ open, ☑ checked by editor against source/Lean, ✓A checked by fidelity audit.

### 4a. Theorems (paper ↔ Lean)

Lean commit (paper pin): main `74d77b43` for all of Theorems A–E (LP3 landed 09:50 UTC); line numbers identical to the earlier a994efdf/402de5f7 pins. Axioms [propext, Classical.choice, Quot.sound] for all 15 headline declarations, run by root-b8 on main's build (Lean files of these declarations unchanged through 01d36418).

| Paper | Content (exact contract) | MAIN | Lean (file:line @commit) | Status |
|---|---|---|---|---|
| Thm A (barrier) | ∀ n≥2, ν>0, compact U ⊂ 𝒬, m>0 ∃ d_⋆, d_pair > 0: (a) ∀ Λ∈U, e∈[0,1]ⁿ with ΣΛ_iD(e_i) ≤ B(Λ)−m: a_i(Λ)(1−e_i) ≥ d_⋆ and a_{i+1}(1−e_{i+1}) − a_i(1+e_i) ≥ d_pair; (b) ∃ compact K of collision-free negative-energy states such that every state with q_i ≠ 0, E_i<0, Λ∈U, C ≤ B(Λ)−m satisfies the perihelion and gap bounds, |q_i| ≥ d_⋆, |q_i−q_j| ≥ d_pair (i≠j), lies in K, and (planar) |L_i| ≥ m with L_i of the sign of L. Lean statement is planar. Spatial counterpart (H_i ≥ m) is MAIN L5 / used inside LP2 — writer C locate Lean name or say "planar only" | L5 (164–169), with L3, L4 | `KAM/Planetary/StrongAMD/PlanarSafety/Main.lean:255` `KAM.Planetary.StrongAMD.lp0_planar_barrier` @a994efdf | ✓A |
| Thm B (planar) | ∀ n≥2, ν>0, compact 𝒜 ⊂ ordered positive axes, δ,γ>0, τ>n−1 ∃ μ₀,c,T₀,A_Λ,A_a,d_⋆,d_pair,A_osc,A_el > 0 with A_oscμ₀ ≤ d_⋆/2, 2A_oscμ₀ ≤ d_pair/2, ∀ 0<μ≤μ₀ ∀ initial state with q_i≠0, E_i<0, a(0)∈𝒜, Diophantine (γ,τ) at ω(Λ(0)), [Λ(0)∈𝒬 — automatic from a(0)∈𝒜; Lean binder], C(0) ≤ B(Λ(0))−δ; T := T₀exp(cμ^{−1/(2(τ+1))}): ∃ solution of (1) on [−T,T] with that initial value, unique on [−T,T]; its barycentric reconstruction solves Newton's equations with masses (1, μν_1…μν_n); ∀|t|≤T: q_i≠0, E_i<0; Λ(t)∈𝒬 and C(t) ≤ B(Λ(t))−δ/2; ‖Λ(t)−Λ(0)‖∞ ≤ A_Λ√μ; ‖a(t)−a(0)‖∞ ≤ A_a√μ; |C(t)−C(0)| ≤ nA_Λ√μ; a_i(1−e_i) ≥ d_⋆; adjacent gaps ≥ d_pair; |q_i| ≥ d_⋆; |q_i−q_j| ≥ d_pair (all i≠j); osculating: E^osc_i<0, a^osc_i>0, e^osc_i<1, a^osc(1−e^osc) ≤ |q_i| ≤ a^osc(1+e^osc), |a^osc−a|+|**e**^osc−**e**| ≤ A_elμ, |peri^osc−peri|,|apo^osc−apo| ≤ A_oscμ, peri^osc ≥ d_⋆/2, adjacent osc gaps ≥ d_pair/2. No normalization max ν = 1 needed (general version); normalized version is the corollary `_normalized` | T15 (502–506), L14, L16, (6)–(9) | `PlanarSafety/Main.lean:44` `lp1_planar_strongAMD_safety`; `:137` `_normalized`; source-carrier forms `PlanarSafety/Source.lean:38,132` @a994efdf | ✓A |
| Thm C (spatial) | Thm B verbatim for d=3 (Euclidean |L|, 3-vectors); no prograde / inclination / alignment premise; includes circular and coplanar orbits | T19 (599–603), L17, L18 | `KAM/Planetary/Spatial/SpatialSafety/Main.lean:43` `KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety`; `:153` `_normalized`; `Source.lean:42,145` @a994efdf | ✓A |
| Cor D | Thm B and C with τ = n−1/2: T = T₀exp(cμ^{−1/(2n+1)}); Diophantine exponent n−1/2 | §1 (line 77) | `PlanarSafety/Main.lean:190` `lp1_planar_strongAMD_safety_halfInteger`; `SpatialSafety/Main.lean:210` `lp2_spatial_strongAMD_safety_halfInteger` | ✓A |
| Thm E (resonance-tolerant) | Thm B/C with: no γ, τ, no Diophantine premise; T = T₀exp(cμ^{−a_n}); drift lines A_Λμ^{b_n}, A_aμ^{b_n}, nA_Λμ^{b_n}; all else identical (margin δ/2, separations, osculating, uniqueness, reconstruction); constants depend on (n,ν,𝒜,δ). Planar and spatial | LP3-PLAN §1.2–1.3 | branch `inp-lp-lp3src` @402de5f7: `KAM/Planetary/StrongAMD/Nek/PlanarSafety/Main.lean:42` `lp3_planar_strongAMD_safety` (+`:135` normalized, `Source.lean:37,130`); `KAM/Planetary/Spatial/Nek/SpatialSafety/Main.lean:40` `lp3_spatial_strongAMD_safety` (+`:150`, `Source.lean:40,139`) | ✓A (Lean on main 74d77b43) |
| Input to Thm E | partial (convex) Nekhoroshev theorem: n≥2 fast, k≥1 slow pairs, open convex G ⊂ G′, open D, h fixed (holomorphic, definite Hessian, |ω|≥g), μ₀ chosen before P, C, solution; drift ≤ μ^{b_n}/2 up to min(C, μ⁻¹exp(μ^{−a_n})) while slow variables stay in innerCore D(μ^{b_n}) | Nek77 Thm 4.4 p.30 (+ Rem. 4.5.A–B) | `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:48` `KAM.Nekhoroshev.partialConvex_nekhoroshev` (proved in the repository on main) | ✓A |

Axioms: main results report `propext, Classical.choice, Quot.sound` (PROGRESS 03:39 and 05:49 entries for LP1/LP0; 06:44 for LP2, orchestrator re-check; landing checks "standard axioms"). The editor did not run `#print axioms` (docs-only brief). LP3: to confirm from the LP3 handoffs (writer C reads `docs/tracks/LP/packages/` handoffs).

### 4b. Lemmas (paper ↔ MAIN)

| Paper | MAIN | Amendments | Notes |
|---|---|---|---|
| lem:normalization | L1 (§2) | — | brief |
| lem:orbital | L2 | — | (11), (12) incl. e = 1 |
| lem:amd | L3 | N8 (|L| convention ruled: C = ΣΛ − |L|) | conservation of L, C ≥ 0, C < B_⋆ ⇒ L ≠ 0, H_i ≥ m, (13) |
| lem:threshold | L4 | N9 (interior-minimizer paragraph not used downstream) | attained, continuous, B_ij < Λ_j, B = min(B_cross, Λ_1); identification with LP17 relative critical AMD (LP17 §3.2 (35)–(39)) |
| lem:uniform | L5 | N11 (define d_⋆ := a_min m²/(2I_max²) first) | proof of Thm A |
| lem:moving | L6 | N2 (one shared compact U, 4r_g tube) | (17) and continuation |
| lem:chart | L7 | N1 (fixed in place) | regular planar Poincaré chart |
| lem:domain | L8 | N2, N3 | whole-sublevel complex domain; the key "entire ball" point |
| lem:fourier | L9 | — | standard |
| lem:lie | L10 | N5 | standard Lie step; do not present as new |
| lem:nf | L11 | — | normal form on full slow tube |
| lem:scaling | L12 | N4 ((35) is a remark), N7 (L12 and L13 alternative suppliers; Lean uses L13) | r = √μ, N ≍ μ^{−a}, time |
| rem:engine | L13 | N6 (widths; r = D₀√μ, improvement to r/2) | Lean route: Pöschel-type finite-cutoff normal form `KAM.Nekhoroshev.nonresonant` |
| lem:exit | L14 | N6 | first exit / bootstrap |
| lem:osc | L16 | N10 (μ₀ ordering; in Lean as A_oscμ₀ ≤ d_⋆/2 etc.) | velocity-osculating elements |
| lem:spchart | L17 | N12 (engineering only) | spatial chart |
| lem:spdomain | L18 | — | |
| lem:cover | LP3-PLAN §2.2 (F4–F5) | review-1 C1–C5 | finite cover, cells, local level B(c_j) − 5δ/16 |

### 4c. Quotations and literature pins (to be checked against PDFs by writer A, then by the literature audit)

| Item | Pin | PDF | Status |
|---|---|---|---|
| LP17 conjecture sentence | published §3, A72 p.3; arXiv v2 §3 p.4 | `sources/incoming-zohar2/r2-amd17.pdf`; `_sources/LP17-arxiv-v2.pdf` | ✓A |
| AMD definition, invariable plane | LP17 §2.2 (9)–(11) | same | ✓A |
| critical AMD C_c(α,γ) | LP17 §3.2 (35)–(39) | same | ✓A |
| strong/weak AMD-stability | LP17 §5.3 | same | ✓A |
| Nekhoroshev 1977 | Thm 4.4 p.30 (partial), exponents | `sources/incoming-round3/nek77-eng.pdf` | ✓A |
| Pöschel 1993 | Normal Form Lemma p.192 | `sources/incoming-N/poschel1993_gdz.pdf` | ✓A |
| Niederman 1996 | NOT inspected (A2 §2) — cite only as "studied exponential stability in the planetary problem", via secondary descriptions (CFG23 §1.3 p.5; BN18 intro p.2) | — | ✓A |
| Barbieri–Niederman | arXiv:1810.05987 | `sources/pdf/arxiv_1810.05987v1_BN_planetary.pdf` | ✓A |
| Pinzari | per A2 (Pinzari 2016 v4; Pinzari–Liu 2023) | `_sources/Pinzari2016-v4.pdf`, `PL23-v2.pdf` | ✓A |
| Nek77 Thm 12.3 (planetary, exponents = Thm E) | §12.2–12.3 pp.55–56 | nek77-eng.pdf | ✓A |
| Practicality | A7 | `_sources/target_margins.*` | ✓A |

## 5. Detail standard (binding for writers)

Reader: a mathematician in Hamiltonian dynamics / celestial mechanics, checking each step with pen and paper.
- **Full statement:** Theorems A–E (exact contracts per ledger), and each lemma's statement.
- **Written out (short):** Lemmas 2–6 (elementary; full short proofs), the whole-sublevel point of L8 (why the *entire* ball is one analytic domain), the scaling arithmetic of L12 (why √μ and μ^{−1/(2(τ+1))}), the first-exit bootstrap L14, the cover argument for Thm E.
- **Sketch + citation:** L7, L17 (charts; key formulas and the symplectic identity), L9–L11 (standard normal form; cite Pöschel 1993 and point to MAIN for the full proof), L16, complex-extension details of L8/L18.
- **Never:** Lean scaffolding, internal names in the text (Lean names only in the appendix table), campaign history, hedging-by-volume.
- Point to "the audited full proof" as a supplementary document: cite as the project's proof notes (writer C/editor will add a bib entry `KAMrepo` for the repository + docs path). Do not use MAIN line numbers in the paper.

## 6. Open questions

1. Spatial Thm A: Lean LP0 is planar only. Paper Thm A is stated for d = 2 with a remark that the spatial counterpart is proved inside Thm C's proof (MAIN L5 is dimension-free) — writer C to confirm the Lean spatial barrier declaration name for the appendix.
2. LP3 axioms record — writer C to find in handoffs; else "not yet recorded".
3. RESOLVED (root-b8 09:1x): main is public at https://github.com/scottnarmstrong/KAM-dev; cite proof notes as \cite{KAMnotes} and Lean as \cite{KAMrepo} at a994efdf; LP3 "in preparation in the same repository". Do not cite README campaign material.

## 7. FOR OWNER

- **Authorship line** "Scott Armstrong and Zohar Komargodski" (D15) is a draft line; confirm.
- **Acknowledgment of AI and formal tools** (who/what drafted the proofs, the Lean formalization, the paper text): draft in `sections/formal.tex` §A.4; owner to confirm wording.
- Where the audited proof notes will be public (citation target).
- Title.

## 8. Audit log

(to be filled: fidelity, literature, exposition audits; findings → repairs)

## 9. Progress log (UTC, from `date -u`)

- 09:02 plan started; sources read (MAIN, AMENDMENTS, OWNER-DECISIONS, Lean LP0–LP2 on main, LP3 plan and Lean on branch, A2 head).
- 09:2x writer A done (abstract 177 w, §1 3.0 pp, §2 3.0 pp). KEY FINDING: Nek77 §12.2–12.3 Thm 12.3 pp.55–56 already proves planetary no-collision for exp time with the SAME exponents a = 2/(6s²−3s+14), b = 3a/2 on boxes of axes with |N| ≥ γ above the collision value. Theorem E's difference: pointwise sharp strong threshold C(0) ≤ B(Λ(0)) − δ, ordered annuli, osculating. Ledger row added (4c). The LP17 "published A72 p.3" pin is unverified (r2-amd17.pdf = arXiv v2, identical md5); paper cites §3 only. Erratum in repository metadata: docs/sources.json treats r2-amd17.pdf as the published LP17.
- 09:20 writer B done (§3 ≈2.8 pp, §4 ≈5.5 pp). Deviations: L3 C ≥ ΣΛD(e) stated on whole negative-energy region (stronger, proved); L6 absorbs N2 (r_g, U, Ω_B(4r_g) ≤ δ/16); L9 tail estimate and L10/L11 derivative bounds dropped (unused); L12 (35) omitted (N4); N6 widths summarized; renamings ϑ, n_s, 𝖣, S, Y, A_γ, β, ϱ, M, ψ. No MAIN errata.
- 09:48 root-b8: every writer/auditor brief must say: never `rm -f $S/*`; use `rm -f "${S:?}"/*` or a fresh `mktemp -d` dir (avoids blocking confirmation).
- 09:56 writer C done. Draft 1 assembled: 23 pp, 0 overfull, 0 undefined. Editor renamed Nekhoroshev exponents a_n,b_n → \aE,\bE (𝔞_n, 𝔟_n) to avoid clash with semi-major axis a_n. C notes: Lean partial-Nek μ₀ also depends on g, m, Hessian bound (paper states full list); spatial barrier Lean = spatialStrongBarrier_physical (Spatial/Geometry.lean:83) + exists_spatialBarrierCompact (:252); Theorem E axioms per audits/LP3-*-handoff.md; LP3 branch not descended from a994efdf; PROGRESS.md has future-stamped entries (11:3x at 09:08) — report to root-b8; B_ij = C_c identification and Lemmas 4.3–4.6 not formalized (appendix says so).
- 09:57 root-b8: LP3 landing on main (commit to follow; table says 'landing' until then); PROGRESS stamps re-stamped upstream, not used in paper; LP17: cite published pages only where A2 checked them, else arXiv v2 pages labelled as such.
- 09:59 root-b8: LP3 on main 74d77b43. Editor verified: all theorem lines unchanged between a994efdf and 74d77b43 (LP3 at Nek/…/Main.lean:42/:40, Source :37,:130/:40,:139); no sorry. FIX ROUND: re-pin appendix, KAMrepo, KAMnotes to 74d77b43; drop 'in preparation'; freeze pending.

## 8. Audit round 1 (bound to cda28701) — summary
- FIDELITY-1: FAIL (2 blockers: false explanatory sentences barrier.tex:4, resonant.tex:100–101) + 10 minor. Theorems A–E, Cor D, Prop 6.1 match Lean exactly; appendix locators correct.
- LITERATURE-1: PASS WITH NOTES. F1 MAJOR: Nek77 Thm 12.3 (γ₀ includes collisions with O = star) via a finite box cover appears to give Thm E's hypothesis up to δ; Thm E's additions are the identification with LP's threshold, annulus/osculating conclusions, the formal proof. F2–F10 minor.
- EXPOSITION-1: FAIL. B1 (priority sentence vs uninspected Nie96) — editor ruling: keep the brief's prescribed "to our knowledge" phrasing but state plainly that Nie96 could not be consulted and its description is second-hand. B2 (L4.3–4.6 sketched) — editor ruling: per brief, sketches + precise citation of the public proof notes (KAM-dev at 74d77b43); say these are standard. M1–M9, 14 minor.
- Editor: refs.bib re-pinned to 74d77b43; tocdepth 2.
- Global symbol rulings (fix round 1): planet masses written μν_i (no m_i), so m is free as the barrier margin; Prop 6.1 time horizon C → T_1; LP17 mass ratio γ → write ν_i/ν_j; cover radius η → r_c; momentum bound P → \bar p; distance lower bound d (Lemma 4.2) → d_0; dimension d stays.
- 10:12 root-b8 confirmed #print axioms = [propext, Classical.choice, Quot.sound] for all 15 headline decls (lp0; lp1/lp2 + _normalized/_halfInteger/_source; lp3 planar/spatial + _normalized/_source) at 74d77b43 (Lean files unchanged through 01d36418; kernel replay at landings). Forwarded to C. Thm E framing (close to Nek77 Thm 12.3) confirmed.
- 10:17 fix round 1 done (A, B, C). 23 pp, clean (only bibtex 'missing pages in Pin18', a Memoir). B: lem:exit has explicit stopped-drift hypothesis (SD), eq:stopped; rem:engine deleted; lem:osc moved before Thm B proof; A_a = Λ_max/min ν_i² (r/2 drift). C: Las97 title from memory (unverified) — re-audit to check. Editor ruling: optional renames H_i, (k,l), 𝖣 not applied (standard notation, local).
- 10:20 LIT round 2 PASS WITH NOTES; editor fixed R2-1 (Las97 → @misc without title), R2-2 (arXiv-version notes restored), R2-3 (intro B–D differences restricted to √μ drift and exponent). R2-4 declined: proofs are verified; only the statement texts' approval is pending — not inconsistent.
- 10:21 round 2: FID FAIL (2 one-phrase blockers barrier.tex:4, :88) + 4 minor; EXPO PASS WITH NOTES (R2-1 'complete proofs' overclaim; R2-2 approval sentence kept per brief/root-b8; R2-7 §6 opening now refers to §1; R2-9 ζ removed; R2-10 table cell). Editor applied all fixes directly; 23 pp clean; pages viewed.
- 10:22 FID round 3 PASS WITH NOTES; R3-1 applied (spatial constants wording).

## 10. Final state

- Audits (fresh Opus 5.5, refute-first; reports in `audits/`):
  - FIDELITY-1: r1 FAIL (2 blockers) → r2 FAIL (2 new one-phrase blockers) → r3 PASS WITH NOTES (R3-1 applied).
  - LITERATURE-1: r1 PASS WITH NOTES (F1 major: Nek77 Thm 12.3 comparison) → r2 PASS WITH NOTES (R2-1..3 applied; R2-4 declined, see above).
  - EXPOSITION-1: r1 FAIL → r2 PASS WITH NOTES → r3 PASS WITH NOTES (R3-1, R3-2 applied; §A.3 spacing fixed with a list; KAMnotes title "proof notes").
- Final compile: 23 pages, no overfull/underfull boxes, no undefined references; every page viewed rendered.
- Errata/deviations to record: (1) `docs/sources.json` LP17 record (fixed on main b6241e69); (2) MAIN deviations in the paper: L3 inequality stated on the whole negative-energy region; L14 restated with an explicit stopped-drift hypothesis (drift r/2, A_a = Λ_max/min ν_i²); L9–L11 auxiliary bounds unused and omitted; (35) omitted (N4). (3) Las97 title unverifiable → cited without title.

## 11. FOR OWNER (final)
- Authorship line (D15 draft) and title.
- §A.4 "Use of AI and formal tools" wording.
- Closeness of Theorem E to Nekhoroshev 1977 Thm 12.3 is stated plainly; novelty limited to Theorems B–D "to our knowledge", with the caveat that Niederman 1996 could not be consulted. Obtaining Nie96 would settle it.
- Corollary D kept as a separate statement (the brief asks for it; house style would fold it).
- Once the statement texts are approved, delete the last sentence of §A.3.
- 10:23 EXPO round 3 PASS WITH NOTES; all notes applied; final build 23 pp clean.
- 10:30 root-b8: landed on main as 82e22386 (owner: 'Land on main now'). Standing by for owner edits on paper-lp; on statement freeze: delete last sentence of §A.3 and re-pin.
