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
