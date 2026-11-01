# PROOF-AUDIT-1: refute-first audit of PROOF/MAIN.md

Auditor: independent Claude agent (Opus 5.5), 2026-11-01. Read-only everywhere except this file.
No Lean/Lake process was run. Repository claims are checked at the source level only.

Audited inputs (SHA-256):

```text
PROOF/MAIN.md          309e9eb38e3f12b24961c60e0aa84e580e4117c6998c69ffbfdfea665580e6ea
PROOF/LEAN-ROADMAP.md  bb52b50e5ba27914c81f2a65e9a207eebe1507ea92a1efdce30acb666717ca0f
PROOF/OPEN.md          af5d8a21858f42808c9bcc17012b77bcc2fd6ab3b071dbd4a05f13f410470541   ("None")
```

Repository: `/root/code/KAM`. HEAD is now `0084e98bfd733daa663d708c525bd76689f2f4c4`, not the pinned
`f5625f1…`. `git diff --stat f5625f1 HEAD` over `KAM/Nekhoroshev/Partial`, `KAM/Planetary`, `KAM/Kepler`,
`KAM/Frozen/Planetary` and `KAM/Frozen/Nekhoroshev` is **empty**, so every pin in MAIN still holds at HEAD.

## 0. Overall verdict

**PASS WITH NOTES.**

I attacked every point in the brief and the five coordinator points (§7). I re-derived the identities,
the threshold geometry, the chart algebra (planar and spatial), the scaled-vector-field normal-form
iteration, the exponent and drift, the first-exit bootstrap, and the repository interface.

- No genuine gap or error was found. No item is blocking.
- The architecture is sound and non-circular:
  - linear averaging about the frequency of the Diophantine centre;
  - a normal form valid on the **whole** slow AMD ball plus a fixed collar;
  - the exact identity C(t) − C(0) = Σ(I(t) − I⁰);
  - a moving threshold with a continuity modulus;
  - a stopped first exit with compact continuation.
- The exponent a = 1/(2(τ+1)) and the drift O(√μ) are correct. The drift bound is a valid upper bound, not
  sharp; see §3.
- The Lean shortest route goes through `KAM.Nekhoroshev.nonresonant` (MAIN Lemma 13). Its hypotheses and
  conclusion match the Lean source literally; see §4.

The notes in §2 are presentational or local. Each needs a one-line fix before statements are frozen.
None changes a theorem statement.

**What "PASS" does not cover.** This is a paper-level audit of correctness and completeness. The following
were not checked:

- Novelty, which RESEARCH/LITERATURE.md already flags as unverified (Niederman 1996, Pinzari 2013).
- Numerical constants: everything is existential, by compactness.
- Kernel or axiom status of the cited Lean declarations. I could not build. I did grep: no `sorry` outside
  `KAM/Frozen/`, and `KAM/Root/Nekhoroshev.lean:95` imports `KAM.Nekhoroshev.Partial.Nonresonant`.

## 1. Per-lemma table

| Item | Verdict | One-line reason |
|---|---|---|
| Lemma 1 (normalization, reconstruction) | PASS | Kinetic (Σ\|P_i\|²/(2μν_i) + \|ΣP_i\|²/2) and potential both scale by μ under P = μp. Inverse (x₀ = −μΣν_iq_i/M, ẋ₀ = −μΣp_i, ẋ_i = p_i/ν_i) gives (10). Agrees with frozen `movingHamiltonian` at G = m0 = 1, m = ν (`KAM/Frozen/Planetary/Defs/MovingHamiltonian.lean:44`). |
| Lemma 2 (orbital identities) | PASS | Checked e² = 1 + 2E\|q×v\|², (q·v)² = 2r − r²/a − \|ℓ\|² ⇒ (r−a)² ≤ a²e², and vis-viva. |
| Lemma 3 (L conserved, AMD identity, prograde) | PASS | Recoil term μ(Σp)×(Σp) = 0 and the pair torques cancel. L = 0 ⇒ C = ΣI ≥ B_⋆, contradiction. H_i ≥ I_i − C ≥ m. L ≠ 0 and prograde are derived, not assumed (§7.2). |
| Lemma 4 (attained, continuous, sharp thresholds) | PASS | Feasible→contact scaling t = (1−α)/(αu+v) ≤ 1. Contact parameterization (15) covers exactly u ∈ [0, m(α)]. B(I) = min(B_cross, I₁) holds because B_{j−1,j} < I_j. Matches LP17 v2 (26)–(29) (checked in `RESEARCH/_sources/LP17-arxiv-v2.txt`). The interior-minimizer paragraph is unused (N9). |
| Lemma 5 (uniform strong barrier) | PASS | K_m is compact and every gap on it is positive. (16): I_i√(1−e²) ≥ m, a(1−e) ≥ a_min m²/(2I_max²). Minor ordering issue: d_⋆ is used before it is named (N11). |
| Lemma 6 (moving threshold, continuation) | NOTE | Correct. U and Ω_B must be one fixed set shared with Lemmas 8 and 14 (N2). |
| Lemma 7 (planar regular chart) | NOTE | Correct. I re-derived p·dq = 2e sinE dI + I(1+e cosE)dE + I sinE de = I dℓ + d(2Ie sinE), and the Ac(F) = s c + (v·c)v/(1+s) eigenstructure. It agrees with the repository chart under (ξ,η) = (x,−y) (`Chart.lean:37-38`, `Kepler/Equation.lean:38`). Typo at MAIN.md:238 (N1). |
| Lemma 8 (whole-sublevel planar complex domain) | NOTE | Correct. One compact real set (projection over I⁰ ∈ L_δ) and one uniform tube. Gluing, bilinear-versus-Hermitian denominator bound and Newton map all check. The constraint r_* ≤ 4r_g is implicit (N3). The constants are qualitative. |
| Lemma 9 (Fourier, Cauchy, commutator) | PASS | Weighted-ℓ¹ algebra, Cauchy 1/σ in scaled I/z, s\|k_j\|e^{−σs\|k\|} ≤ 1/(eσ), so ‖[V,W]‖ ≤ (2D/σ)‖V‖‖W‖. Sup-to-Fourier constant ((1+e^{−s})/(1−e^{−s}))ⁿ is paid once. |
| Lemma 10 (cohomology, Lie step) | NOTE | Estimates (26)–(29) check: Σ v^j(G+E) + Σ v^j E/(j+1) ≤ (8/3)v(G+E) ≤ 4v(G+E), with B_D = 16eD. Flow existence and the Lie-series/flow identification are sketched and c_D is implicit (N5). |
| Lemma 11 (exponential normal form, full slow set) | PASS | E_{j+1} ≤ 3B_D·AεN^{τ+1}·E_j ≤ E_j/2. Σu_j ≤ 2q_D/N ≤ 1/32. Domain bookkeeping: input to φ_j lies in D_{2+Σ_{l>j}u_l} ⊂ D_{ρ_{j+1}} because each u_l ≤ 1/(4N). Inverse built on D_{3/2} by reversed negative-time flows. |
| Lemma 12 (scaling, exponent, divisors) | PASS | ε = M₁√μ from 4L_ω r/s + μM(1/r+1/s+1/b). Floor/power arithmetic correct (§7.5). Drift r/16 + r/16 + rε2^{−N/2} ≤ r/4. (35) is correct but unused (N4). |
| Lemma 13 (repository finite-cutoff reuse) | PASS | Every field of `ExtNFHyp`, `hsmall`, `ht`, `hstop` and `nnf_disp_radius` matches the Lean source (§4). Implicit width choices should be stated (N6). |
| Lemma 14 (first exit) | NOTE | Non-circular. The 7δ/16 ball membership, the r/4 improvement and the 3δ/4 improvement all check. U consistency (N2). Under the Lemma 13 variant, (39) must use r = D₀√μ and the improvement is r/2. The text says "unchanged"; it is correct but terse (N6). |
| Theorem 15 (planar) | PASS | Quantifiers: constants before μ and before initial data, uniform over phases and secular data. A planar reflection is symplectic and leaves H invariant. The dependency list should say "Lemma 12 **or** 13" (N7). |
| Lemma 16 (velocity-osculating) | PASS | V_i − v_i = μΣp_j and k_i − 1 = μν_i, so O(μ) on a compact set with E ≤ −1/(2a_max) and e ≤ e_* < 1. Using \|e^osc − e\| ≤ \|𝐞^osc − 𝐞\| avoids differentiating the norm at e = 0. |
| Lemma 17 (spatial regular chart) | PASS | Re-derived: R is the quaternion rotation by ι about the node line, \|t\|² = Z/(2G) = sin²(ι/2), Re₃ = (−cv/√G, −cu/√G, 1 − Z/G). Rotation term L·Ω = H dh + G dg gives p·dq = I dλ − Γdϖ − Z dh_n + exact. Inverse: Z = G(1 − ŵ₃), so Re₃ = ŵ. Domain H > 0 is exactly Γ + Z < I. |
| Lemma 18 (spatial whole-sublevel domain) | PASS | Γ_i + Z_i ≤ I_i − 3δ/16 ⇒ G_i, H_i ≥ 3δ/16 and c_i² > 1/2. Σ I_iD(e_i) = ΣΓ_i ≤ \|z\|²/2, so the whole fixed-frame ball is collision-safe even off the invariable plane. Alignment is used only along the true orbit. |
| Theorem 19 (spatial) | PASS | Same assembly with m = 2n slow pairs and the same n fast divisors k·ω(I⁰). C_{e₃} = C exactly after alignment. |

There is no GAP or ERROR entry. The NOTE items are listed in §2.

## 2. Notes (non-blocking; fix before freezing statements)

None of these is a GAP or an ERROR. Each gives its location, the problem, and the fix.

- **N1. Typo.** MAIN.md:238 reads "Γ d(−ϖ) = (x,dy-y,dx)/2". It should read (x dy − y dx)/2. The derivation
  is otherwise correct.
- **N2. Three different "U".**
  - The three sets: Lemma 6 (MAIN:179, U ⊃ L), Lemma 8 (MAIN:257, U ⊃ the 4r_g-tube about L_δ, with
    Ω_B(4r_g) ≤ δ/16) and Lemma 14 (MAIN:472, U ⊃ L_δ, with (39)).
  - Why it matters: Ω_B depends on U, and (17), (39) and Lemma 8's inequality are chained.
  - Fix: choose one compact U ⊂ Q that contains the closed 4r_g-tube about L_δ, use its Ω_B everywhere, and
    require r ≤ r_g.
  - Mathematically harmless: any larger compact U gives a larger modulus that still tends to 0.
- **N3. Lemma 8: r_* ≤ 4r_g is implicit (MAIN:271).**
  - Why it matters: complex actions in (22) must have real parts in the real tube where Lemma 5 was applied.
  - Fix: state it explicitly.
  - With this, every point of (22) lies within sup-distance max(r_*, 4s, 4b) of the single compact set
    K′ = {(I, z, λ)}. K′ is the projection over I⁰ ∈ L_δ of the closed set in MAIN:261.
  - This is exactly what `KAM.Planetary.tube` needs (`ComplexTube.lean:154-175`). The repository's
    `complexTube` is a sup-distance tube around the periodic orbit set of K, so the packaging works.
- **N4. Lemma 12, (35) is unused.** The paper route inverts only k·ω(I⁰). Keep (35) as a remark. Do not
  make it a formal dependency.
- **N5. Lemma 10 is sketched.** Flow existence, the Lie-series/flow identification and the constant c_D are
  sketched, not written out.
  - They are standard: Picard iteration and the Taylor remainder along trajectories. The claimed bounds are
    consistent; I checked v ≤ 1/24 under q_D ≤ 1/(6B_D).
  - This matters only if the optional packages 9–11 are formalized. The roadmap's shortest route does not
    use them.
- **N6. Lemma 13 leaves width choices implicit (MAIN:442).** It should state:
  - 2πs₁ < 4s (radian strip), with a margin so that the weighted Fourier sum e^{2πs₁\|k\|₁} converges;
  - w < 4b and D₀√μ < r_*;
  - J := the stopped interval of Lemma 14, F := `realWfield b.c (realHamiltonianExt b b.rB (liftFast h + f))`.
    This is legitimate because `realDom` is open, so the indicator Hamiltonian has the true derivative there.
  - Under this route the stopped radius is r = D₀√μ and the improvement is to r/2 (not r/4). (39) still
    gives C ≤ B(I(t)) − δ + nr/2 + Ω_B(r/2) ≤ B(I(t)) − 3δ/4.
- **N7. Theorem 15 dependencies.** "Lemmas 1–14" lists both Lemma 12 and Lemma 13. They are alternative
  suppliers of the stopped drift. List exactly one per proof route, as the roadmap DAG already does
  (LEAN-ROADMAP §4).
- **N8. AMD convention in the frozen headline.**
  - MAIN defines C = ΣI − \|L\| (orientation-free). The repository's planar `physicalAMD` is the signed
    Σ keplerAction − totalMomentum.
  - With the signed version, the hypothesis physicalAMD ≤ B − δ forces L > 0. If L < 0, it equals
    ΣI + \|L\| > I₁ > B.
  - So the signed form gives an equivalent theorem only after the reflection reduction (MAIN Theorem 15
    proof). Freeze one convention and prove the bridge.
- **N9. Lemma 4, optional paragraph.** The "minimizers are interior" and geometric-realization paragraph
  (MAIN:158) is not used downstream. Do not put it on the formal critical path.
- **N10. Lemma 16, constant ordering.** The final μ₀ must also satisfy A_oscμ₀ ≤ d_⋆/2 and
  2A_oscμ₀ ≤ d_pair/2. MAIN states this at the end of the proof; the headline constant list should record it.
- **N11. Lemma 5, ordering.** |p_i| ≤ ν_i√(2/d_⋆) uses d_⋆ before it is defined. Define
  d_⋆ := a_min m²/(2I_max²) first.
- **N12. Spatial reuse of `tube` (roadmap).** `ComplexTube.tube` is typed on `Phase (n+n)`, with n fast
  angles and an equal block size. The spatial chart has n fast and 2n slow pairs. Its gluing proof must be
  re-typed, as LEAN-ROADMAP:211 and PROOF-PLAN:220 already say. This is engineering, not mathematics.

## 3. My own derivation of the exponent and drift (point 6)

Take an action tube of radius r about I⁰ and fixed widths s (angles) and b (slow). Use scaled field
components X̂ = (X_I/r, X_θ/s, X_z/b). On D₄:

- X_{h−h₀}: θ-component |ω(I) − ω(I⁰)|/s ≤ 4L_ω r/s.
- X_{μf}: I-component μ|∂_θ f|/r ≤ Mμ/r; θ-component Mμ/s; z-component Mμ/b.

Hence ε ≍ r + μ/r. A Lie step with loss σ = 1/N:

- generator u ≍ A N^τ E;
- new error ≍ (u/σ)(G+E) ≍ A N^{τ+1} ε E.

The iteration contracts if A N^{τ+1}(r + μ/r) ≲ 1. Minimizing over r gives r = √μ and ε ≍ 2√μ, so
N^{τ+1} ≍ μ^{−1/2} and N ≍ μ^{−1/(2(τ+1))}. The two classical conditions are the two halves of this one
inequality:

- **Divisor persistence:** r N^{τ+1} ≲ γ, from the [X_{h−h₀}, X_χ] term. With r = √μ and N = κμ^{−a},
  this is κ^{τ+1} ≲ γ. This is MAIN (36), second inequality.
- **Averaging smallness:** μ N^{τ+1}/(γ r) ≲ 1, from the [X_{μf}, X_χ] term. It becomes κ^{τ+1} ≲ γ/M.
  This is MAIN (36), first inequality.

**Time.** The remainder satisfies ‖X_R‖ ≤ ε2^{−N}, so |J̇| ≤ rε2^{−N}. Therefore the time is
T ≍ 2^{N/2} = exp((log 2)N/2) ≥ exp(c μ^{−1/(2(τ+1))}), with c = (log 2)κ/4. **The exponent
a = 1/(2(τ+1)) is right.** For τ = n − ½ it equals 1/(2n+1). As τ ↓ n−1 it approaches 1/(2n), but never
reaches it.

**Drift.** ‖I(t) − I⁰‖ ≤ |Φ⁻¹ disp| + |Φ disp| + rε|t|2^{−N}. The displacements are
Σu_j·r ≲ AεN^τ r ≍ μN^τ = μ^{(τ+2)/(2(τ+1))} = o(√μ). So the true drift is O(μ^{(τ+2)/(2τ+2)}) plus an
exponentially small term. MAIN's A_I√μ, with A_I = 1, is a correct non-sharp upper bound. The AMD budget
needs only nr + Ω_B(r) ≤ δ/4, which holds for r = √μ small. The repository route (Lemma 13) gives the same
two conditions in the scalar norm: KLr ≤ α/2 and ε = M₂μ ≤ αr/(256K) with α = (γ/2π)K^{−τ}. Hence the same
exponent, with drift ≤ D₀√μ/2.

## 4. Repository-citation checks (Lemma 13 and point 9), with file:line evidence

All paths are relative to `/root/code/KAM`. Each claim in MAIN is listed with what the Lean source says.

- **`KAM.Nekhoroshev.nonresonant` at `Partial/Nonresonant.lean:341`.** Confirmed at line 341.
  - Premises: `ExtNFHyp b s K α L p ε {0} h f`; `hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K)`; the orbit ODE `hy`
    on an `OrdConnected` J ∋ 0; `hinit : fastAction (y 0) = b.Ic`; `hx`;
    `ht : |t1| ≤ s*b.rB/(5*ε)*exp(2πKs/6)`; `hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S`.
  - Conclusion: ‖fastAction(y u) − Ic‖ ≤ rB/2. This is MAIN (37)/(38) exactly.
- **`nf` at `Partial/NormalForm.lean:604`.** Confirmed at lines 604–631. The conclusion includes slow
  displacement ≤ qKε/(8α), canonicity for the weighted bracket, reality and periodicity.
- **`nnf_disp_radius` gives physical slow displacement ≤ w/2¹⁰.** Confirmed at `NormalForm.lean:635-654`:
  qKε/(8α) ≤ rB/2¹⁰ and lam·rB/2¹⁰ = w/2¹⁰.
- **S is arbitrary; slow scale ℓ = w/r; bracket coefficient 2π/ℓ².** Confirmed at `Partial/Setting.lean:72-85`:
  `PartialBlock.S : Set (Phase k)`, `lam = w/rB`, `c = 2π/lam²`, and `base` = {(Ic, x/lam) : x ∈ S}.
- **The four numeric hypotheses (37).** Confirmed at `Setting.lean:123-127`:
  - `divisor_size : K*L*rB ≤ α/p`. With p = 2 this is KLr ≤ α/2.
  - `SL : 64πk·s·rB ≤ w²` (`Setting.lean:85`).
  - `cutoff : 6 ≤ 2πKs`.
  - `hsmall` with conjExp 2 = 2 gives ε ≤ αr/(256K).
- **Nonresonance only at the centre; ℓ¹ cutoff.** Confirmed at `Setting.lean:121`:
  `nr : IsNonresonant {realInclusion Ic} K α Λ h`.
  - `NormalForm/Setting.lean:46-49`: IsNonresonant requires α ≤ \|k·freq h I\| for I ∈ D and
    k ∈ zBall \ Λ.
  - `NormalForm/Setting.lean:34`: zBall = {modeSize k ≤ K}.
  - `Fourier/Derivative.lean:37`: modeSize = Σ\|k_j\| (the ℓ¹ norm).
  - So (5) with \|k\|₁, at period one: \|k·ω/2π\| ≥ γ\|k\|₁^{−τ}/2π ≥ (γ/2π)K^{−τ} = α.
- **Frequency Lipschitz on the complex tube.** Confirmed at `NormalForm/Setting.lean:51-53`: `FreqLipschitz`
  uses sup norms on polyNbhd {Ic} rB. ω_i = ν_i³/I_i³ is diagonal, so L = max 3ν_i³/(2π\|I_i\|⁴) on the tube.
- **"weighted Fourier norm", "scalar ε = M₂μ".** Confirmed at `Weighted/Norm.lean:52,62`: the weight is
  e^{2πs\|k\|₁}, and `WBound` requires pointwise-in-I summability with sum ≤ M over polyNbhd base rB. This
  follows from analyticity on a wider radian strip (N6).
- **Product domain (fast tube × slow tube) in sup norm.** Confirmed at `Weighted/Domains.lean:32-36`:
  polyNbhd is a sup-norm neighbourhood, Dom = strip × polyNbhd. This matches MAIN (22) with physical slow
  width lam·rB = w.
- **Time and bracket conversion (θ = λ/2π, Ĥ = H/2π, z = ℓz̃).** Confirmed at `Setting.lean:59-64`:
  `realWfield` gives θ̇ = Ĥ_I, İ = −Ĥ_θ, q̇ = cĤ_p, ṗ = −cĤ_q. I recomputed θ̇ = H_I/2π, İ = −H_λ,
  ż̃ = J H_z/ℓ, so physical time is unchanged.
- **Planar slow convention (ξ,η) = (x,−y).**
  - `Poincare/Chart.lean:37-38`: v = √((1−Γ/(2Λ))/Λ)·(ξ,η).
  - `Kepler/Equation.lean:38`: keplerPhi v F = F − v₀ sinF + v₁ cosF.
  - `Chart.lean:43-51`: the q-formula is s·c + (v·c)/(1+s)·v − v, the same as MAIN (19).
  - MAIN has (k,l) = b_e(x,−y), so ξ = x and η = −y. The Hamiltonian signs check.
- **Frozen moving Hamiltonian equals MAIN (1).** Confirmed at `Frozen/Planetary/Defs/MovingHamiltonian.lean:44`:
  (1/m_i + μ/m0)\|p_i\|²/2 plus μΣ_{i<j} p_i·p_j/m0, which equals MAIN (1) at G = m0 = 1, m = ν.
- **Roadmap reuse list.** I spot-checked these declarations, and all exist:
  - 29 theorems, including `tube`, `amd_exit_forward/backward`, `moving_ode`, the `poincare*` family,
    `eccAnomC_spec`, `keplerSumGen_hess_norm_le`, `preimage`, `ang_mom`, `newton_to_moving` and
    `isNewtonSolutionOn_of_isMovingSolutionOn`;
  - 9 definitions, including `IsMovingSolutionOn`, `MovingUniqueOn` and `actualMasses`.
- **Proof status.** No `sorry` in any non-Frozen `.lean` file (grep). `Nonresonant` is imported by
  `KAM/Root/Nekhoroshev.lean:95`, so it is part of the default build.

**External pins (point 9).** MAIN uses no external analytic theorem as a supplier (MAIN:607). Its pins are
for identification or comparison only. I checked them against the PDFs/texts in `RESEARCH/_sources/`:

- **LP17 arXiv v2.**
  - §3 contains the conjecture sentence ("we conjecture that in absence of short period resonances,
    the AMD-stability ensures the practical long-term stability"), p.4.
  - (26)–(29) are the contact condition αe + e′ = 1 − α and the relative AMD γ√α D(e) + D(e′), with
    e, e′ ∈ [0,1].
  - These are exactly MAIN's B_ij/I_j.
  - §5.3 (strong/weak AMD-stability) is on p.10. The pins are correct.
- **Pöschel 1993, Normal Form Lemma, printed p.192.** Pinned in RESEARCH/LITERATURE.md, not in MAIN. I
  checked the scan image `_sources/poschel-p192.png`, and the transcription is accurate:
  - nonresonance at every point of D;
  - ε ≤ αr/(2⁷qK), r ≤ min(α/(pMK), r₀), Ks ≥ 6;
  - Ψ : V_{r/2,s/6}D → V_{r,s}D;
  - \|g − P_ΛT_K f\| ≤ 16cε², \|f_*\| ≤ e^{−Ks/6}ε, ‖Π_IΨ − I‖ ≤ cεr, with c = 2qK/(αr).
  - It has no slow pairs. The repository's `nf` is the slow-pair extension, with the extra condition SL.
    MAIN does not misuse Pöschel.
- **BMM22 App. B, Lemma B.1, p.380, and Pinzari–Liu Prop. 3.2 / Lemma 3.3.** The locators exist in the local
  texts. Neither is load-bearing.

## 5. Attack log (brief points 1–8): what was tried and why it failed to break the proof

1. **Normalization and identities.**
   - P = μp scales both the symplectic form and H by μ, so time is unchanged.
   - L = Σq_i × P_i is the true barycentric angular momentum, because Σ_{i=0}^n x_i × P_i = Σ q_i × P_i
     when P₀ = −ΣP_i. So C is exactly conserved up to ΣΔI.
   - The spatial frame alignment is a fixed rotation, which is symplectic. C_{e₃} = C holds exactly on the
     true orbit.
   - Off-orbit points of the analytic ball only need C_{e₃} ≥ Σ I D(e). This holds because
     I_i − H_i ≥ I_i − |L_i|.
2. **Thresholds.**
   - The minimum is over a compact, nonempty set, (0, 1−α) is feasible, and it is attained.
   - Continuity comes from the fixed-interval contact parameterization (15) with m(α) continuous.
   - Positivity: u = v = 0 cannot be in contact since α < 1.
   - B = min(B_cross, I₁) holds even when I₁ is not the smallest action, because B_cross < I_j for j ≥ 2.
   - The margin δ is used consistently: 𝒵₀ at δ/4, Lemma 8 at 3δ/16, the stop at δ/2, the improvement to 3δ/4.
3. **Charts.** I verified the planar Liouville form term by term. Spatially I verified the quaternion form,
   R e₃, the rotation contribution H dh + G dg (the node-line term vanishes because n̂ ⊥ L), the inverse
   (Z = G(1−ŵ₃)), and that the domain H > 0 is exactly Γ + Z < I.
4. **Whole-sublevel domain.**
   - Uniformity in I⁰: the chart does not depend on I⁰, so one compact real set and one tube serve all
     centres.
   - Uniformity in phases: Lemma 5 is phase-free (radial annuli).
   - Complex denominators: \|w·w − \|w₀\|²\| ≤ 2Qη + η² (bilinear, bounded by Hermitian norms), so
     Re(w·w) ≥ d²/2 and \|1/√(w·w)\| ≤ √2/d.
   - Nothing depends on μ: h, f and the chart are μ-free in this splitting.
5. **Normal form with evolving slow variables.**
   - The divisors k·ω(I⁰) are constant, so they commute with ∂_θ, ∂_I and ∂_z, and X_χ is X_f^osc
     divided mode by mode.
   - Slow derivatives enter (25) through the 1/σ Cauchy cost in z/b. The slow field μ/b is smaller than √μ.
   - No inverse symplectic matrix appears.
   - Diophantine at the centre for all k suffices because the nonlinearity h − h₀ is in the perturbation.
     The finite-cutoff tube statement (35) is never needed.
6. **Scaling.** See §3; correct.
7. **First exit.**
   - The stopped set (40) is relatively open and contains 0.
   - On it z ∈ 𝒵₀ because \|z\|²/2 = C < B(I⁰) − 7δ/16. This uses only the stop, not the conclusion.
   - Both Φ and Φ⁻¹ errors are counted (r/32 each), and the threshold movement Ω_B(r/4) ≤ δ/16.
   - There is no O(μ) chart/AMD discrepancy, because the canonical chart is exact and μ-free.
   - The continuation endpoint lies in a compact nonsingular set (Lemma 5 at δ/2). The improved bounds
     persist past t_*, which is a contradiction.
8. **Quantifiers.** Constants are fixed from (d, n, ν, 𝒜, δ, γ, τ) before μ and the initial data. The
   conclusion (9) gives no orbit crossing for canonical annuli. Lemma 16 transfers it to actual-velocity
   osculating annuli at the cost of 2A_oscμ.

## 6. What to formalize first

1. **Sharp barrier (Lemmas 2–6, planar), before any analysis.**
   - Define `pairThreshold` as an attained minimum and export its characterization. Never totalize it
     outside `OrderedActions`.
   - Prove continuity via (15).
   - Prove B = min(B_cross, I₁).
   - Prove the uniform barrier K_m together with the explicit d_⋆.
   - Prove the modulus Ω_B on one fixed U (N2).
   - This is self-contained and independently valuable. It is the Candidate-A barrier at the sharp
     threshold.
2. **A one-centre vertical slice of Lemma 13.** Do this second; it is the highest interface risk.
   - For one fixed I⁰, build `ExtNFHyp` from the planar chart Hamiltonian, including the 2π/period-one
     conversion, (ξ,η) = (x,−y), lam = w/rB and c = 2π/lam².
   - Discharge `hy`/`hF` for the physical orbit transported to rescaled chart coordinates on the stopped
     interval.
   - Prove (37) from the floor arithmetic (§7.5).
   - Everything else in the analytic chain is reuse.
3. **Lemma 8 packaging.** Build one compact K′ (the projection over L_δ) and use `tube`. Prove that every
   centre's product domain (22) lies in `complexTube K′ r` (N3). Get uniform M from compactness.
4. **Lemma 14, then Theorem 15, then Lemma 16.** Reuse `amd_exit_forward/backward` and `moving_ode`. Freeze
   the AMD convention (N8).
5. **Spatial last.**
   - Lemma 17 is the largest package: separate the rotation algebra, the Liouville identity on the dense
     set e > 0, Z > 0, the analytic extension, and the explicit inverse.
   - Then the spatial Lemmas 1 and 3.
   - Re-type `tube` for n fast + 2n slow coordinates (N12).
   - Then Lemma 18 and Theorem 19.

Any Lean brief for this campaign must repeat verbatim:

1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If
   a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused
   modules, preserving public import paths as cheap facades.

## 7. Coordinator's additional points (root-b8)

**7.1. δ ≥ min_𝒜 B on part of 𝒜. Correct and meaningful.**

- MAIN replaces BRAINSTORM's δ < min B by the centre set L_δ = {I⁰ ∈ L : B(I⁰) ≥ δ}. L_δ is a closed subset
  of compact L, since B is continuous on Q ⊃ L. So L_δ is compact or empty.
- Because C ≥ 0 (Lemma 3), any admissible initial state has I⁰ ∈ L_δ (MAIN:472).
- If L_δ = ∅ the theorem is vacuous, and "any positive constants" is legitimate (MAIN:257, MAIN:170).
- Boundary case B(I⁰) = δ:
  - the only admissible states have C = 0, i.e. circular and aligned;
  - 𝒵₀ still has squared radius 2(B − δ/4) = 3δ/2 > 0;
  - B(I) ≥ 15δ/16 on the real tube, so the 3δ/16 margin of Lemma 8 holds.
- Lemma 5 with m = δ/2: K_{δ/2} is nonempty when L_δ is nonempty, so d_pair is a genuine minimum.
  d_⋆ = a_min δ²/(8I_max²) uses only U.
- Nothing breaks. MAIN's form is strictly more general than BRAINSTORM's.

**7.2. Prograde and |L| ≠ 0 are derived, not assumed. Verified.**

- From C ≤ B − δ ≤ B_⋆ − δ:
  - If L = 0, then C = ΣI_i ≥ min I_i = B_⋆, a contradiction. So |L| > 0.
  - With H_i = L_i·L̂ we have ΣH_i = |L|, so C = Σ(I_i − H_i). Each summand is ≥ I_i − |L_i| ≥ 0.
    Hence H_i ≥ I_i − C ≥ δ.
- Planar: L̂ = sign(L), so every L_i has the sign of L. Reversing orientation by a reflection (q,p) ↦ (Rq,Rp)
  is symplectic, because RᵀR = I, and leaves H invariant. After it, L > 0 and all L_i > 0. Then
  C = ΣI − L = Σ_iΓ_i, which equals the repository's signed `physicalAMD` (N8).
- Also derived:
  - e_i < 1, from I_i√(1−e_i²) ≥ δ;
  - q_i ≠ q_j, from the positive pair gap of Lemma 5.
- The hypotheses q_i ≠ 0 and E_i < 0 are exactly what is needed to define I_i and C.

**7.3. Lemmas 8, 17, 18 (PROOF-PLAN's OPEN RISKS). Scrutinized; no gap.**

- **Lemma 8.** PROOF-PLAN:106's risk is "family-indexed compact-set packaging and agreement on overlaps".
  - Packaging: the chart does not depend on I⁰, so a single compact real set K′ serves every centre.
  - Overlaps: the pairwise-ball argument is right. Two complex balls with real centres that intersect have
    a real common point, and the intersection is convex hence connected, so the identity theorem applies.
  - The repository's `tube` already proves this at `ComplexTube.lean:165-190`, using a finite subcover with
    half-radii.
  - Only N3 needs stating.
- **Lemma 17.** I verified every identity independently (table row). The only formal-difficulty items:
  - analytic extension of the 2-form identity from the dense set e > 0, Z > 0;
  - the explicit analytic inverse, with c = √((1+ŵ₃)/2) > 1/√2 on H > 0.
- **Lemma 18.** The fixed-frame ball is safe off the invariable plane because Σ I_iD(e_i) = ΣΓ_i ≤ |z|²/2.
  Margins: G_i, H_i ≥ 3δ/16 and c_i² > 1/2.

**7.4. Spatial chart domain. MAIN's Γ + Z < I is sufficient; regular and symplectic there.**

- STATEMENTS:209 uses Z < 2(Λ − Γ). Since |t|² = Z/(2G), that condition is |t|² < 1: c is real, rotations
  up to ι < π, retrograde orbits included.
- MAIN's region Γ + Z < I is H > 0, equivalently |t|² < 1/2, equivalently ι < π/2.
- Every strong-sublevel state lies in MAIN's region:
  - on the true orbit after alignment, H_i ≥ δ initially and ≥ δ/2 on the stopped interval;
  - on the analytic ball, H_i ≥ 3δ/16 with a fixed collar.
- The larger domain is never needed. STATEMENTS itself says "the strong-domain proof uses the smaller region".
- Regular at e = 0 and Z = 0, because the formulas (18), (19), (46) contain no perihelion or node angle.
  Symplectic, as verified.

**7.5. Floor/power arithmetic (Lemmas 12 and 13). Correct.**

- N = ⌊κμ^{−a}⌋ ≤ κμ^{−a}, and x ↦ x^{τ+1} is increasing on x ≥ 0, so N^{τ+1} ≤ κ^{τ+1}μ^{−1/2}, because
  a(τ+1) = ½.
- This gives AεN^{τ+1} ≤ AM₁κ^{τ+1} ≤ q_D/2 and 4L_ω rN^{τ+1} ≤ 4L_ωκ^{τ+1} ≤ γ/2.
- If κμ^{−a} ≥ 2, then N ≥ κμ^{−a} − 1 ≥ κμ^{−a}/2 ≥ 1. So (log 2)N/2 ≥ cμ^{−a} with c = (log 2)κ/4, i.e.
  T_μ ≤ 2^{N/2}.
- Lemma 13:
  - K = ⌊κ₁μ^{−a}⌋ ≥ 1 for small μ, which `K_pos` and \|k\|₁^{−τ} ≥ K^{−τ} need.
  - K^{τ+1} ≤ κ₁^{τ+1}μ^{−1/2} gives KLr ≤ α/2 and ε ≤ αr/(256K) under MAIN's two κ₁ inequalities.
  - The prefactor s₁r/(5ε) = s₁D₀/(5M₂√μ) ≥ 1 for small μ.
- A real K (PROOF-PLAN:162) works equally well: the library takes K : ℝ, and zBall uses modeSize ≤ K. The
  floor is harmless; it is needed only because Lemma 11 needs an integer step count N.

## 8. Blocking issues

None.
