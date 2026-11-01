# FIDELITY-1: mathematical fidelity audit of papers/LP (refute-first)

Target: branch `paper-lp`, commit `cda28701b2eca380d945c67f26013bf1dac53179`, files `papers/LP/main.tex`,
`papers/LP/sections/*.tex` (rendered `main.pdf`, 23 pp). Auditor wrote none of the text. Docs-only; no Lean
was edited and no lake command was run.

```
sha256sum papers/LP/sections/*.tex
f3ff73e5d17bc33caf1b7b2208ff88bd9cb03afc1804b23ba9a6fe81cf7018f7  papers/LP/sections/abstract.tex
ada83f3d7164acae9789f09af5b1f7f12c14c89976fa433fd8d809971660e9b6  papers/LP/sections/barrier.tex
a181b6562a9f7227abbf3108d53db74e5f23fd7fbf3e07c8acfd13c473f2da8e  papers/LP/sections/formal.tex
80434fbe44a19b4cbc64237446be9a3302097858d31365048a2e7d3260f3726a  papers/LP/sections/intro.tex
5959168e64b3799604c8f027d25f618d884e4b770ee7df2548d474a8a7c1e3c5  papers/LP/sections/outlook.tex
b2ac9581303d74a1e4b2e1b7378c02e68ddd75795445bbdcaa1c5dbcea1295f9  papers/LP/sections/planar.tex
971762711fd9c61e45f1358b2ddaeef31e343aaaf91d97717bf20daf93091736  papers/LP/sections/resonant.tex
be293bf790dea4e255f293b3afb4d54d4d0ac283c490ec066eac4314c313d347  papers/LP/sections/results.tex
fcadf891d3ac3ae65c274041ab3c30be77c98ecce7726aff1b89a3d10e4698a3  papers/LP/sections/spatial.tex
```

Authorities read: `/root/code/KAM/docs/tracks/LP/source/MAIN.md` + `AMENDMENTS.md` (N1–N12),
`lp3/LP3-PLAN.md` + `LP3-PLAN-REVIEW-1.md`; Lean text at `a994efdf` (planar/spatial `Main.lean`, all
definitions they use: `keplerEnergy/Axis/Action/EccVector`, `strongAMD`, `spatialStrongAMD`,
`chamber`, `pairThreshold`, `orderedStrongThreshold`, `osc*`, `keplerPeri/Apo`, `IsMovingSolutionOn`,
`MovingUniqueOn`, `NoCollision`, `movingHamiltonian`, `actualMasses`, `spatialMasses`,
`barycentric*`, `IsNewtonSolutionOn`, `modeSize`), Theorem E at `inp-lp-lp3src` (`402de5f7`), the
exponent definitions, and `PartialConvexNekhoroshev.lean:48` with all its Defs (`HasDefiniteFastPart`,
`IsPartialPerturbation`, `partialComplexDomain`, `innerCore`, `actionNbhd`, `fastShift`,
`partial{Time,Drift}Exponent`, `IsSolutionOn`, `degenerateHamiltonian`, `frequencyMap`). Nek77 §1.18
and (4.1) were spot-checked in `sources/incoming-round3/nek77-eng.pdf`.

## Verdict: **FAIL** (two BLOCKERs, both one-sentence repairs; otherwise PASS WITH NOTES)

Both blockers are false *explanatory* sentences. The brief counts any such sentence as a blocker. No theorem
statement is stronger than its Lean counterpart. No proof step fails. All appendix locators are correct.

## What was checked and found faithful (no finding)

* **Thm A ↔ `lp0_planar_barrier` (Main.lean:255).** Same data `(n≥2, ν>0, compact U⊆𝒬, m>0)` and order
  `∃ d⋆ dpair, (i) deficit-list barrier ∧ ∃ K compact, K ⊆ {NoCollision ∧ E_i<0} ∧ ∀ state…`. The
  conclusions are the same: perihelia, adjacent gaps, `|q_i|`, `|q_i−q_j|`, `z∈K`, `|L_i|≥m`, `L_i L>0`.
  `NoCollision` is `q_i≠0 ∧ q_i≠q_j`, which matches the paper.
* **Thm B ↔ `lp1_planar_strongAMD_safety` (:44).** The quantifier order is the same: the nine constants
  and both `A_osc μ0` relations, then `μ`, then `z₀`. The hypotheses are the same. Diophantine uses
  `modeSize = |k|_1`, `ω_i = ν_i³/Λ_i³` and `γ|k|_1^{−τ}`. `T = T0 exp(c μ^{−1/(2(τ+1))})`. Uniqueness
  (`MovingUniqueOn`: open convex `U∋0`, i.e. an open interval) and Newton reconstruction with
  `actualMasses 1 ν μ = (1, μν_i)` match. Every conclusion in (ii)–(v) matches, including the sup norm on
  `Λ`, `a` and the `n A_Λ √μ` AMD drift. `strongAMD = ΣΛ − |L|`. `keplerEnergy = ν_i E_i` has the sign
  of the paper's specific `E_i`, and `keplerAxis = −ν/(2ν E) = −1/(2E)`. `movingHamiltonian 1 1 ν μ`
  expands to (2.1).
  The one Lean-only binder `hch` (chamber membership) follows from `a(0)∈𝒜`, as the paper notes at
  results.tex:42.
* **Thm C ↔ `lp2_spatial_strongAMD_safety` (:43).** It is the same statement with Euclidean `|L|`,
  `spatialMasses = (1, μν)` and no orientation premise.
* **Cor D ↔ `…_halfInteger` (:190, :210).** These have `τ = n−1/2` and time exponent `1/(2n+1)`.
* **Thm E ↔ `lp3_{planar,spatial}_strongAMD_safety`** (`inp-lp-lp3src`, :42 and :40). They drop `γ, τ`
  and the Diophantine premise. The time is `T0 exp(c μ^{−𝔞_n})`, and the three drift lines are
  `μ^{𝔟_n}`. The frozen defs give `𝔞_n = 2/(6n²−3n+14)` and `𝔟_n = 3𝔞_n/2 = 3/(6n²−3n+14)`. Everything
  else is identical.
* **Prop 6.1 ↔ `partialConvex_nekhoroshev` (:48).** `μ0` comes after `(G,G′,D,ρ,h,g,m,Mc)` and before
  `P, C, z`. The collar is a closed sup ball. Both `σ = ±1` are allowed, with `‖∇h‖_∞ ≥ g`. `P` is
  holomorphic and real on `partialComplexDomain` (Re fast action ∈ G′, Re slow ∈ D, |Im| < ρ), with
  `|P| ≤ 1` and `2π` periodicity (`fastShift`). `innerCore` is the closed sup-norm erosion. The horizon is
  `min(C, ε^{−1}exp(ε^{−𝔞}))` and the conclusion is `≤ ε^{𝔟}/2` in the sup norm. The paper's
  "slightly weaker form" remarks are correct. Nek77 (4.1) with all `α = 1` gives `ζ = n(n−1)/2`, and
  `12ζ + 3n + 14 = 6n² − 3n + 14`.
* **Scaling arithmetic (planar.tex:146–171) is correct.** `A_γ ε N^{τ+1} ≤ A_γ M_1 κ^{τ+1} ≤ q_D/2`.
  `N ≥ κμ^{−ϑ}/2`. `c = (log 2)κ/4` gives `T_μ ≤ 2^{N/2}`. Then
  `r/16 + rε|t|2^{−N} + r/16 ≤ r/8 + rε2^{−N/2} ≤ r/4` because `ε ≤ 1/8`.
  The Lemma `lem:nf` iteration is also correct: `E_{j+1} ≤ 3B_D A_γ ε N^{τ+1} E_j ≤ E_j/2`,
  `G ≤ 2ε` and `Σu_j ≤ 2q_D/N ≤ 1/32`.
* **First exit (planar.tex:187–208) is correct.** `J` is open and nonempty, with `7δ/16 ⇒ z ∈ Z_0 ⇒ D_1`.
  The improvement to `r/4` gives `3δ/4`. Finite-endpoint exclusion uses Lemma `lem:moving` with
  `nr + Ω_B ≤ δ/2`, and continuity at `t*` uses `E_i ≤ −c_U` and `H_i ≥ 3δ/4`. The paper's constants
  match: `A_a = 2Λ_max/min ν²` and `d⋆ = a_min δ²/(8Λ_max²)`.
* **Section 6 (resonant.tex) matches LP3-PLAN §2.2–2.4 and Prop 6.1's hypotheses.**
  * Widths: `w = min{r_*, 4s, 4b}`, `η = w/4`, `ρ* = w/8`. Then `2η + ρ* = 5w/8 < w`, the collar is
    `η + ρ* < 2η`, `ρ* < 4s, 4b`, and `η/2 ≤ r_g`.
  * Thresholds: `B(Λ) ≤ B(c_j) + 2Ω_B(4r_g) ≤ B(c_j) + δ/8`, so the stopped state has
    `C < B(c_j) − 3δ/8`. `ε_D` is correct, with `|z′| ≤ |z| + √(2n_s) r`.
  * Constants: `ε = B0 μ ≤ ε0/2 < μ_j^±` (strict, as the Lean statement needs). `r = ε^{𝔟} < ε_D`,
    `r ≤ η/4, r_1, r_g`. `T = exp(ε^{−𝔞}) ≤ ε^{−1}exp(ε^{−𝔞})`, `c = B0^{−𝔞}`, `T0 = 1`.
  * Time reversal uses `(−h, −P)` with `σ` flipped. `A_Λ = B0^{𝔟}/2`. The `μ0` list includes Lemma
    `lem:osc` (review C5).
* **Lemmas `lem:normalization`, `lem:orbital`, `lem:amd`, `lem:threshold`, `lem:uniform` and
  `lem:moving` match MAIN L1–L6 as amended (N2, N11).** Each identity and inequality was rechecked,
  including the barycentric inverse (`ẋ0 = −μΣp`, `ẋ_i = p_i/ν_i`), the contact parametrisation, the
  `M`-rescaling remark (results.tex:95) and the Thm B/E exponent comparison (`1/5` vs `1/16` at `n = 2`).
* **Charts.** `k² + l² = 1 − β²`, `Γ d(−ϖ) = ½(x dy − y dx)`, `|t|² = Z/(2(Λ−Γ)) < ½` and
  `(q×p)·N = Λ − Γ − Z` all match MAIN L7/L17. Lemma `lem:spdomain` matches L18.
* **The writers' renamings change no meaning.** These are `ϑ`, `n_s`, `𝖣`, `S`, `Y`, `A_γ`, `β`, `ϱ`,
  bold `M`, `ψ`, `𝔞_n` and `𝔟_n`.
* **"Kepler Hamiltonian is convex [§1.18]" (resonant.tex:5) is faithful to Nek77's usage.** §1.18 reads:
  "If, moreover, these second derivatives have the same sign, then H₀ is convex". This is not a finding.
* **Appendix A.** Every declaration name and every `file:line` in Tables `tab:lean-main` and
  `tab:lean-lemmas` was checked at `a994efdf` (19 locators), and all are correct. The namespaces are
  correct, and the toolchain is `v4.35.0`. There is no `sorry` in `KAM/Nekhoroshev` or
  `KAM/Provider/Nekhoroshev`. The anchor's proof body is `by exact KAM.Provider…`. The LP3 handoffs
  (`LP3-PS`, `LP3-SP-SAFE`, `LP3-SRC` on `inp-lp-lp3src`) report `[propext, Classical.choice,
  Quot.sound]`. This audit did not re-run `#print axioms`.

## Findings

### F1 — BLOCKER (false explanatory sentence)

* **Location:** barrier.tex:4: "We show that exact conservation of the total angular momentum turns the
  strong condition $C\le B(\Lambda)-m$ into a bound on the eccentricities that keeps every perihelion
  and every pair of adjacent radial annuli uniformly apart".
* **Evidence:** The eccentricity bound uses no conservation. It comes from the pointwise triangle
  inequality `|L| ≤ Σ|L_i| = ΣΛ_i√(1−e_i²)` (barrier.tex:45, proof of Lemma `lem:amd`;
  `MAIN.md:139`). Lemma `lem:uniform` and Thm A are static, and the paper says so itself at intro.tex:19
  ("No secular or dynamical information enters") and barrier.tex:4 ("contains no small parameter").
  Conservation enters only through Lemma `lem:moving` (17).
* **Repair:** "We show that the inequality $C\ge\sum_i\Lambda_iD(e_i)$ turns the strong condition …
  uniformly apart, and that exact conservation of $L$ makes $C$ move only with the actions (Lemma
  `lem:moving`)."

### F2 — BLOCKER (false explanatory sentence)

* **Location:** resonant.tex:100–101: "the bound $C<B(\Lambda^0)-\delta/4$ of Lemma~\ref{lem:exit}
  would leave no room for this erosion."
* **Evidence:** Lemma `lem:exit` does not use `−δ/4` as its bound. It displays
  `½|z|² < B(Λ⁰) − 7δ/16` (planar.tex:201). Combined with `B(Λ⁰) ≤ B(c_j) + Ω_B(η/2) ≤ B(c_j) + δ/16`,
  that bound gives exactly `C < B(c_j) − 3δ/8 = A_j′`, which is the bound needed. So Lemma `lem:exit`'s
  bound does leave room. The sentence was inherited from LP3-PLAN §2.4 step 4 (lines 285–287). It refers
  there to the Lean lemma `strongAMD_le_of_stopped` (`ChartLift/Stopped.lean:98`), not to the paper's
  lemma.
* **Repair:** Delete the clause. Alternatively write: "the membership $z\in\mathcal Z_0(\Lambda^0)$ alone
  (½|z|² ≤ B(Λ⁰) − δ/4) would leave no room; the sharper bound is needed."

### F3 — MINOR (wrong constant in an inequality)

* **Location:** planar.tex:72, with planar.tex:44 ("distances are in the maximum norm"):
  `\abs{w\cdot w-\abs{w_0}^2}\le2Q\eta+\eta^2`.
* **Evidence:** With sup-norm distance `η` in `ℝ^d` (or `ℂ^d`), `|2w0·Δ| ≤ 2Q√d η` and `|Δ·Δ| ≤ dη²`.
  For example, with `w0 = (Q/√2, Q/√2)` and `Δ = (η, η)`, `2w0·Δ = 2√2 Qη`. MAIN.md:267–269 uses
  Euclidean distance `η_q`. The conclusion is unaffected because `η` is then taken small.
* **Repair:** Write "within Euclidean distance η", or replace the bound by `2\sqrt d\,Q\eta+d\eta^2`.

### F4 — MINOR

* **Location:** planar.tex:58: "Every denominator $\abs{q_i}$, $\abs{q_i-q_j}$ of $f$".
* **Evidence:** `f` (results.tex:7) has only the denominators `|q_i−q_j|`. The star term `ν_i/|q_i|`
  belongs to `h`. MAIN.md:255 says "Every Newtonian denominator".
* **Repair:** Write "Every Newtonian denominator $\abs{q_i}$, $\abs{q_i-q_j}$".

### F5 — MINOR (symbol clash that changes the reading)

* **Location:** resonant.tex:98 and resonant.tex:104. Line 98 has `\tfrac12\abs{z(u)}^2=C(u)<…` (AMD),
  and line 104 reads "Proposition~\ref{thm:partialnek} with $C=t$" (duration).
* **Evidence:** Prop 6.1 (resonant.tex:27) names the time horizon `C`, which collides with the AMD `C`
  four lines earlier. Two smaller clashes exist: `η` is a slow momentum in Prop 6.1 (resonant.tex:12) but
  the cover radius in resonant.tex:50, and `P` is the perturbation but also the momentum bound
  (planar.tex:227).
* **Repair:** Rename the horizon in Prop 6.1 (for example `T_1`), and the cover radius (for example
  `\varsigma`).

### F6 — MINOR

* **Location:** resonant.tex:54–70 (Lemma `lem:cover` and the constants at :83–86).
* **Evidence:** If `𝓛_δ = ∅`, then `J = 0` and `min_j μ_j^±` and `ε_D` are undefined. LP3-PLAN (F4)
  and review N3 treat this case. Lemma `lem:domain` does assume it away (planar.tex:62).
* **Repair:** Add "We may assume $\Lset_\delta\ne\emptyset$; otherwise no initial state is admissible."

### F7 — MINOR (Appendix accuracy)

* **Location:** formal.tex:13–14: "the thresholds … defined as minima over the action chamber".
* **Evidence:** `pairThreshold` is a literal `sInf` (`Threshold/Defs.lean:49–50`) and
  `orderedStrongThreshold` is a `⨅` on the carrier (:88–89). That these values are attained is a theorem
  (`exists_pairThreshold_attained`), not part of the definition.
* **Repair:** Write "defined as infima over the action chamber (proved attained)".

### F8 — MINOR (Appendix accuracy)

* **Location:** formal.tex:35–36: "The file containing that proof, at commit a994efdf, contains no
  sorry".
* **Evidence:** The proof is spread over the provider tree. The anchor file holds only
  `by exact KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev`. A file-level grep is the wrong
  certificate.
* **Repair:** Write "`partialConvex_nekhoroshev` depends only on the standard axioms (as reported by
  `#print axioms` of the Theorem E declarations, which use it)", or report its own `#print axioms`.

### F9 — MINOR (Appendix accuracy)

* **Location:** formal.tex:53: the "spatial" row, `exists_spatialBarrierCompact`.
* **Evidence:** In Spatial/Geometry.lean:254, `K ⊆ {SpatialNoCollision}` carries no `E_i < 0` clause,
  unlike planar `lp0` (Main.lean:265). The spatial angular-momentum conclusion is
  `m ≤ L_i·L̂` (:96–97), which agrees with results.tex:103.
* **Repair:** Add "(the spatial compact set is stated collision-free; negative energy is given separately
  by `spatialStrongBarrier_physical`)".

### F10 — MINOR (exactness of the correspondence claim)

* **Location:** intro.tex:34: "with the hypotheses, quantifier order and conclusions stated in
  Section~\ref{sec:results}".
* **Evidence:** The Lean statements carry the extra binder `hch : Λ(z₀) ∈ chamber ν`
  (Main.lean:58), which the paper does not list. It is implied by `a(0) ∈ 𝒜` (results.tex:42).
* **Repair:** Mention it in Appendix A ("the chamber membership of Λ(0), implied by a(0)∈𝒜, appears as a
  typing binder").

### F11 — MINOR (wording)

* **Location:** intro.tex:24: "the constants depend only on the mass ratios, $\Aset$, $\delta$"; also
  intro.tex:17 and abstract.tex:2 ("Fix the mass ratios").
* **Evidence:** The constants depend on `ν = (ν_1, …, ν_n)` (Thm B: "depending only on
  `(n,ν,𝒜,δ,γ,τ)`"), not only on the ratios `ν_i/ν_j`. The rescaling at results.tex:95 changes `δ` and
  `μ`.
* **Repair:** Write "the normalized masses $\nu$".

### F12 — MINOR (consistency)

* **Location:** intro.tex:34 and formal.tex:5 say "A formal proof of Theorem E is in preparation".
  formal.tex:108 says "Theorem E is proved on a development version".
* **Repair:** Use one phrasing, for example "proved on a development branch, not yet on the reviewed
  commit; review in progress".

## Not checked / out of scope

* Literature quotations and pins (LP17 §§2–5, Nek77 §12, BN20, CFG24, Pin18) are in the literature
  audit.
* The axioms of the Lean declarations were not re-run (docs-only).
* The sharpness paragraph (barrier.tex:69) is stated without proof. Its content is correct per MAIN
  L4:158, and it is off the critical path (N9).

## Suspected errata in pinned sources

None that bears on the paper. F2 originates in LP3-PLAN §2.4 step 4. That wording is correct there,
where it refers to the Lean `strongAMD_le_of_stopped`, but it was transcribed into the paper without
that referent.

---

# Round 2 (re-audit of commit `b6d1cca3`, Lean at `74d77b43`)

Target: `git diff cda28701 b6d1cca3 -- papers/LP/sections` (9 files changed, +251/−259). Lean statements were read
as text at `/root/code/KAM` commit `74d77b43486d`. Docs only: no `.tex` was edited, no lake command was run.

```
sha256 of papers/LP/sections/*.tex at b6d1cca3 (git show | sha256sum)
0b565f28b54772e4c97fdf9eba2211bedc4aadad4aa17bb2223ae48dd920f0b3  abstract.tex
fab6d6dd33aa0b69d791b0e3a72f666db3c9632a385490522bdd34cecb7f7c27  barrier.tex
bebe76929beb2540005cbfda8446a3ca76b964a145e7751ceed78061da09b1c0  formal.tex
9d4cdd88d301afd3f51ad94f146bd8e524bc6a6760982d41a42b539a0f4e5502  intro.tex
bb295fbc845e0807abb888bbf7fec42e515f9f459c10655b48ccd940f4213729  outlook.tex
d50bb6d0e29dc8cbf3c9896d1031f350b5ac9f3f94d30d8e0c7f56ce2540a859  planar.tex
0383ced534cd829d986153f0bdde13527043d9b3f212e102b5547b9844b5ee96  resonant.tex
fc1177df942b90dae4898bc278e8e9ff89c6d9d03e7d5c54e617f491f79a7d36  results.tex
157cc18f687ac912c69154c5b115a64d70366bbb10b55684bef385fa5601c0dc  spatial.tex
```

## Verdict: **FAIL** (two BLOCKERs, both one-phrase repairs; otherwise PASS WITH NOTES)

Both blockers are new false explanatory sentences in barrier.tex, introduced by the fix for F1. All
mathematical changes are correct:

* the new stopped-drift Lemma `lem:exit`;
* its verification in Theorem B and in §6.3;
* the moved Lemma `lem:osc`;
* the constants `A_Λ = 1` and `A_a = Λ_max/min ν_i²`;
* the generalized Lemma `lem:orbital`;
* the re-pinned Appendix table.

## Status of the round-1 findings

| # | Status | Evidence at `b6d1cca3` |
|---|---|---|
| F1 | Fixed, but the new sentence has a new error (R2-1) | The barrier.tex:4 conservation claim is gone. |
| F2 | Fixed | The resonant.tex clause is deleted. |
| F3 | Fixed | planar.tex:70: "within Euclidean distance $\eta$". |
| F4 | Fixed | planar.tex:58: "Every Newtonian denominator". |
| F5 | Fixed | Horizon `T_1` (resonant.tex:30), cover radius `r_c`, slow set `W`/`W_j`, threshold `ε_*`, momentum bound `\bar p`. |
| F6 | Fixed | resonant.tex:45–46: "We may assume $\Lset_\delta\ne\emptyset$". |
| F7 | Fixed | formal.tex:13: "defined as infima … and proved to be attained". |
| F8 | Fixed | The file-level "no sorry" sentence is replaced by the `#print axioms` statement (formal.tex:100–106). |
| F9 | Fixed | formal.tex:54: "negative energy is in the first". |
| F10 | Fixed | intro.tex:36 and formal.tex:16–17 name the chamber binder. |
| F11 | Fixed | intro.tex:17 and :24, abstract: "normalized masses". |
| F12 | Fixed | All of Thm E is now "proved" at `74d77b43` (intro.tex:36, formal.tex:3). |

## Changed material checked and found correct

* **Lemma `lem:exit` with (SD)** (planar.tex:196–229) was checked line by line.
  * The interval `J ∋ 0` is open and nonempty: at `t = 0`, `0 < r`, `C(0) ≤ B − δ < B − δ/2`, and the
    state is prograde by Lemma `lem:amd`.
  * For `t ∈ J ∩ [−T, T]`, the antecedent of (SD) holds on `[0, t]`. The improvement to `r/2` together
    with (17) and (eq:stop) gives `C ≤ B − δ + nr/2 + Ω_B(r/2) ≤ B − 3δ/4`, with `r/2 ≤ 4r_g`.
  * Exit: at a finite maximal endpoint, Lemma `lem:moving` applies with `nr + Ω_B(r) ≤ δ/4 < δ/2`.
    Otherwise `E_i = −ν_i²/(2Λ_i²)` is uniformly negative on `U`, and at `t*` we have `≤ r/2 < r`,
    `C ≤ B − 3δ/4 < B − δ/2`, and `H_i ≥ Λ_i − C ≥ 3δ/4`. This contradicts `t* = sup J ≤ T`.
  * Conclusions:
    * `|a_i − a_i^0| ≤ (r/2)(2Λ_max)/ν_i² = Λ_max r/ν_i²`;
    * `|ΔC| ≤ nr/2` by (eq:amd);
    * the separations follow from Lemma `lem:uniform` with `m = δ/2` on `U`, because `Λ(t)` is within
      `r/2 ≤ r_g` of `Λ⁰ ∈ 𝓛_δ`;
    * `d⋆ = a_min δ²/(8Λ_max²)`.
  * The paper's (SD) puts "prograde" in the antecedent. This makes it weaker to verify than Lean's
    `hstop` (`Confinement.lean:177–182`), which has no prograde clause and quantifies over all solutions.
    The paper's Lemma `lem:exit` is a stand-alone conditional helper with a distinct name, so this is
    acceptable.
* **(SD) in the proof of Theorem B** (planar.tex:234–242).
  * The constants `μ0 ≤ min(μ_1, μ_2)`, `r = √μ ≤ r_g`, (eq:stop), `Ω_B(r) ≤ δ/16` and the two `A_osc`
    relations all precede `μ` and the initial state.
  * Given the antecedent, `½|z|² < B(Λ⁰) − 7δ/16`, so `z ∈ 𝒵_0(Λ⁰)` and the orbit lies in `𝒟_1`. Then
    Lemma `lem:scaling` gives `r/4 ≤ r/2` for `|t| ≤ T_μ`, with `T_0 = 1`.
  * `A_Λ = 1` works because the drift is `≤ r/2 = √μ/2`. `A_a = Λ_max/min ν_i²` works because
    `Λ_max r/ν² = A_a √μ`. The AMD drift is `nr/2 ≤ nA_Λ√μ`.
  * Uniqueness follows from analyticity, as stated.
* **(SD) in §6.3** (resonant.tex:102–127).
  * `ε = B_0μ ≤ ε_0/2 < ε_j^±` (strict, as Lean needs).
  * `r = ε^𝔟 < ε_0^𝔟 ≤ min{r_c/4, r_1, r_g}` and `r < ε_1`.
  * `T = exp(ε^{−𝔞}) ≤ ε^{−1}exp(ε^{−𝔞})`, using `ε ≤ 1`.
  * Cell `j` with `‖Λ⁰ − Λ̄_j‖ < r_c/2`. Then `I(0) ∈ G_j ⊖ r` because `r_c/2 + r_c/4 < r_c`.
  * By Lemma `lem:cover`(ii), `C < B(Λ̄_j) − 3δ/8`. By (iii), `z ∈ W_j ⊖ r`.
  * Prop 6.1 with `T_1 = t` gives drift `≤ r/2`. Time reversal uses `(−h, −P)` with `ε_j^-`.
  * `A_Λ = B_0^𝔟/2`.
  * Lemma `lem:cover` arithmetic: `2r_c + ρ* = 5w/8 < w`, `r_c + ρ* < 2r_c`, `r_c/2 ≤ r_g`, and
    `2Ω_B(4r_g) ≤ δ/8`. The definition of `ε_1` is correct.
* **Lemma `lem:osc`** (planar.tex:177–192, moved). The data `(n, ν, U, m)`, the estimates and the half-gap
  conclusion are unchanged in substance. It now uses Lemma `lem:orbital` with `k = k_i`, `v = V_i`.
* **Lemma `lem:orbital`, generalized to parameter `k`** (barrier.tex). The following identities were
  checked:
  * `k²e² = k² + 2E|q×v|²`;
  * `2E = −k/a`, so `e² = 1 − |q×v|²/(ka)`;
  * `(q·v)² = 2kr − kr²/a − |q×v|² ≥ 0`, which gives `(r − a)² ≤ a²e²`;
  * `|v|² = k(2/|q| − 1/a)`;
  * `|q×p| = Λ√(1 − e²)` at `k = 1`.
* **Lemma `lem:normalization`**: `x_0 = −μΣν_i q_i/(1 + μΣν_i)` is unchanged in substance.
* **Lemma `lem:moving` proof**: `ρ` replaces `r_0`. It is correct.
* **Statements in results.tex.** Theorems A–E have the same content as round 1. The index rewording
  "inequalities involving $i+1$ required for $i<n$" matches Lean `AdjIdx`.
* **Lean pins at `74d77b43`.** All 34 file:line locators in Tables `tab:lean-main` and `tab:lean-lemmas`
  resolve to the named declarations:
  * the `_source` forms are `…_source_general` at the first line and `…_source` at the second, in each
    `Source.lean`;
  * Theorem E is at `Nek/PlanarSafety/Main.lean:42, 135`, `Source.lean:37, 130`,
    `Spatial/Nek/SpatialSafety/Main.lean:40, 150` and `Source.lean:40, 139`;
  * Prop 6.1 is at `PartialConvexNekhoroshev.lean:48`.

  Both Theorem E `Main.lean` files are byte-identical to the round-1 branch `inp-lp-lp3src`, so the round-1
  statement check of Theorem E carries over.

  The coordinator's note that "a994efdf→74d77b43 only adds files" is not exact. Nine files are modified, but
  they are only the generated roots `KAM/Root/{Planetary,Wave}.lean`, the README and docs. No declaration
  file changed.
* **Axiom text.** The axiom text is consistent with the project records. `docs/tracks/LP/PROGRESS.md`
  records the lander's standard-axiom reports for LP0/LP1 (05:49), LP2 (06:44), and W5A/W5B/W5C (LP3,
  "no sorryAx through the sealed anchor"). This audit did not re-run `#print axioms`.
* **New explanatory sentences classified true.**
  * intro.tex:3 ("at the threshold, two orbits, or an orbit and the star, can touch").
  * intro.tex:30, the Nekhoroshev comparison. It is hedged ("appears to give"). It is correct that a
    small-box cover plus continuity of `B` turns a uniform `|N| ≥ γ` condition into the pointwise
    `C ≤ B − δ` up to the margin. Adjacent-pair contact also covers non-adjacent collisions, because ordered
    axes force an adjacent overlap.
  * resonant.tex:3–9, the same comparison.
  * planar.tex:44 (meaning of `r_g`, `U`), :175, :194.
  * results.tex:95–99.
  * spatial.tex sketch ("q×p determines u, v, hence R").
  * barrier.tex:69 (sharpness paragraph).
  * Literature numbers (BN20 tables, Las97, LP17 §5) are left to the literature audit.

## Round-2 findings

### R2-1 — BLOCKER (false explanatory sentence)

* **Location:** barrier.tex:4: "…uniformly apart, and $B$ is the least deficit at which two annuli can
  touch."
* **Evidence:** `B = min(B_cross, Λ_1)` (results.tex (2.5), barrier.tex (eq:Bsharp)). When
  `Λ_1 < B_cross`, `B` is the deficit of a radial innermost orbit (planet–star contact), not of annulus
  contact. This case occurs, for example when `ν_1/ν_2` is small, since `Λ_1/Λ_2 = (ν_1/ν_2)√α` while
  `B_12 ≥` a positive multiple of `Λ_2`. The round-1 text said, correctly, "the least deficit at which this
  fails" (perihelion or annuli).
* **Repair:** "…and $B$ is the least deficit at which two adjacent annuli can touch or a planet can reach
  the star."

### R2-2 — BLOCKER (false explanatory sentence)

* **Location:** barrier.tex:88: "The next lemma, the only place where conservation of $L$ enters, converts
  action drift into margin drift."
* **Evidence:** Conservation of `L` also enters in four other places:
  * the identity (eq:amd) `C(t) − C(0) = Σ(Λ_i(t) − Λ_i(0))`, which Lemma `lem:exit` invokes directly
    (planar.tex:228);
  * the orientation step of Theorem B ("we may assume $L>0$, which is conserved", planar.tex:232);
  * the spatial alignment ("Along the solution $L$ is conserved, so $C_{\mathbf N}=C$", spatial.tex
    Lemma `lem:spdomain` proof);
  * the identification `½|z|² = C` along the solution in Theorems B, C and E.
* **Repair:** Restore the round-1 wording "It is the only place where the drift of the actions is compared
  with the threshold", or drop the clause "the only place where conservation of $L$ enters".

### R2-3 — MINOR

* **Location:** resonant.tex:125: "Lemma~\ref{lem:exit} now gives existence and uniqueness on $[-T,T]$".
* **Evidence:** The new Lemma `lem:exit` (planar.tex:212) concludes existence only. The proof of Theorem B
  adds "uniqueness holds because (H) is analytic" (planar.tex:242). Lean's
  `strongFirstExit_of_stopped_drift` does give `MovingUniqueOn`, but the paper's lemma does not state it.
* **Repair:** "…gives existence on $[-T,T]$ (uniqueness as in Theorem B)…"

### R2-4 — MINOR

* **Location:** spatial.tex, proof of Theorem C: "Lemmas~\ref{lem:exit}, \ref{lem:uniform}
  (dimension-free), \ref{lem:osc} and~\ref{lem:normalization} give all conclusions".
* **Evidence:** Lemma `lem:exit` now needs (SD) as an explicit hypothesis. The spatial proof never says
  where (SD) is verified, and it does not fix the constants `μ0`, `r`, `T`. The planar verification
  (planar.tex:234–240) carries over verbatim with the ball (eq:spball), but the proof should say so.
* **Repair:** Add "The constants and the verification of (SD) are those of the proof of
  Theorem~\ref{thm:planar}, with \eqref{eq:spball} in place of \eqref{eq:ball}."

### R2-5 — MINOR

* **Location:** planar.tex:203: "Consider a solution of \eqref{eq:H} with admissible initial state … and
  assume the stopped drift estimate".
* **Evidence:** The proof applies (SD) on the maximal solution's interval `J` (planar.tex:222–226). If "a
  solution" is a restriction to a short interval, (SD) says nothing beyond that interval.
* **Repair:** "Consider the maximal solution of \eqref{eq:H} with admissible initial state…"

### R2-6 — MINOR (Appendix accuracy)

* **Location:** formal.tex:105: "the Lean files are unchanged through commit \texttt{01d36418}".
* **Evidence:** `git diff --name-status 74d77b43 01d36418 -- '*.lean'` shows 34 added files (`KAM/Wave/…`)
  and the modified generated root `KAM/Root/Wave.lean`. No file of the LP declarations or their imports
  changed.
* **Repair:** "the files of these declarations and their imports are unchanged through commit
  \texttt{01d36418}".

## Suspected errata in pinned sources

None.

---

# Round 3 (final narrow check of commit `05ad2cbe14b3`)

Target: `git diff b6d1cca3 05ad2cbe -- papers/LP/sections` (barrier, formal, intro, planar, resonant, spatial).
Docs only: no `.tex` edited, no lake.

```
0b565f28b54772e4c97fdf9eba2211bedc4aadad4aa17bb2223ae48dd920f0b3  abstract.tex
9750a5c33b4e36c45f9bc1685d7891c1c8ab40de60a36665e5a2cbdea66096e0  barrier.tex
88d8549265fcf2e97a4b2072921a9aca54849594f5fee82d312e78111f2d8474  formal.tex
5835916c965ff3a6d1e6e38695ddc64b75d9249ed530821c2b83420b401e8755  intro.tex
bb295fbc845e0807abb888bbf7fec42e515f9f459c10655b48ccd940f4213729  outlook.tex
22c8477a68f497148d9d78bc8a0b1b9ab42fef4540be9aea880e0bc8c844e724  planar.tex
cf3c7f8402a1db88a582585d397fb53cd35fa07e6f1ef6374ae4c98642f2718c  resonant.tex
fc1177df942b90dae4898bc278e8e9ff89c6d9d03e7d5c54e617f491f79a7d36  results.tex
46b48ebd3c541d54d88463b24202e84ff18cf3ebf0c417f553a3a5631e5e520e  spatial.tex
```

## Verdict: **PASS WITH NOTES**

All six round-2 findings are resolved. No changed sentence is false. One wording note remains (R3-1), which is
not blocking.

## Round-2 findings

| # | Status | Evidence at `05ad2cbe` |
|---|---|---|
| R2-1 | Fixed | barrier.tex:4: "$B$ is the least deficit at which two adjacent annuli can touch or a planet can reach the star". This is true because `B = min(B_cross, Λ_1)`. |
| R2-2 | Fixed | barrier.tex:88: "the only place where the drift of the actions is compared with the threshold". This is true: the moving-threshold estimate (17) is the only comparison, and Lemma `lem:exit` and §6.3 use it via (17). |
| R2-3 | Fixed | resonant.tex: "gives existence on $[-T,T]$ (uniqueness as in Theorem~\ref{thm:planar})". |
| R2-4 | Fixed | spatial.tex, proof of Theorem C: (SD) is "verified as in the proof of Theorem~\ref{thm:planar} … with the ball~\eqref{eq:spball} in place of the planar one". Checked: the spatial stopped state gives `½|z|² = C_N = C < B(Λ⁰) − 7δ/16`, so `z ∈` (eq:spball) and the orbit lies in `𝒟_1` of Lemma `lem:spdomain`. Lemma `lem:scaling` with `n_s = 2n` then gives `r/4`. See R3-1 for one wording point. |
| R2-5 | Fixed | planar.tex: "Consider the maximal solution". |
| R2-6 | Fixed | See the next section. |

## Claim in formal.tex: no relevant Lean file changed through `01d36418`

The claim reads: "no file defining these declarations or imported by them changed through commit
\texttt{01d36418}". I checked it in `/root/code/KAM` as follows.

* `git diff --name-status 74d77b43 01d36418 -- KAM/Planetary KAM/Nekhoroshev KAM/Frozen KAM/Provider KAM/Fourier
  KAM/Iso KAM/Kepler KAM/Defs lakefile.lean lean-toolchain lake-manifest.json` is empty.
* Over all `*.lean`, the only changes are 34 added files under `KAM/Wave/Iteration/` and the modified
  generated root `KAM/Root/Wave.lean`.
* No file under `KAM/Planetary`, `KAM/Nekhoroshev`, `KAM/Frozen`, `KAM/Provider` or `KAM/Fourier` imports
  `KAM.Wave` or `KAM.Root` (`git grep` is empty). No module imports a root (AGENTS rule 10).
* Newly added files cannot enter an unchanged file's import closure.

The claim is **true**.

The table row for the spatial barrier lost its parenthesis "negative energy is in the first". That leaves the row
with no claim, so nothing in it is false. The F9 nuance, that `exists_spatialBarrierCompact` has no `E_i<0`
clause, is now simply unstated. This is acceptable.

## Other changed sentences

* **True:** planar.tex: "More detailed proofs, with constants, are in the supplementary proof notes~\cite{KAMnotes}
  (Lemmas~9--11 there), where the standard flow estimates of the Lie step are also only sketched."
  * MAIN Lemmas 9, 10 and 11 are the Fourier/commutator estimates, the Lie step and the normal form.
  * AMENDMENTS N5 records "Flow existence, Lie-series identification and `c_D` are sketched".
  * This assumes `\cite{KAMnotes}` resolves to MAIN, whose numbering this is.
* **True:** intro.tex, Formal verification: "More detailed proofs are written out in~\cite{KAMnotes}." This replaces
  "Complete proofs", which was an overclaim given N5.
* **True:** intro.tex: the shortened paragraph comparing Theorems B–D with earlier work now states only the
  drift and exponent comparison.
* **True:** resonant.tex opening: "As explained in Section~\ref{sec:intro}, Theorem~\ref{thm:resonant} is close to
  Nekhoroshev's planetary theorem~\cite[Theorem~12.3]{Nek77}." This is consistent with intro.tex:30.
* **True and harmless:** resonant.tex, removal of "$\zeta=n(n-1)/2$". The sentence still says that (4.1), (4.4) and
  (4.5) give the exponents.

## R3-1 — MINOR (wording, not blocking)

* **Location:** spatial.tex, proof of Theorem C: "with the same choice of $\mu_0$, $r=\sqrt\mu$ and $T$".
* **Evidence:** In space, `μ_1`, `c` and `M_1` come from Lemma `lem:scaling` with `n_s = 2n`. The domain
  constants come from Lemma `lem:spdomain`, and `A_osc` comes from Lemma `lem:osc` with `d = 3`. So `μ_0` and
  `T = exp(cμ^{−ϑ})` are chosen *by the same rule*, but they are not numerically the same as in the planar case.
  The sentence can be misread as "the same constants".
* **Repair:** Write "with $\mu_0$, $r=\sqrt\mu$ and $T$ chosen in the same way from the spatial constants".
