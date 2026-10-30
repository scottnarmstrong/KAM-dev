# Scouting the first formally verified KAM torus of a planetary model: LG00's secular Sun–Jupiter–Saturn system (SJS-LG00)

30 October 2026, branch `sjs-lg00`. This is a scouting study (Python, two small kernel probes). Nothing here is a
theorem or a certificate. Every number comes from `scripts/sjs/lg00/*.py` (section 8). The paper is U. Locatelli and
A. Giorgilli, *Invariant tori in the secular motions of the three-body planetary systems*, Celest. Mech. Dyn. Astron.
78 (2000) 47–74 (LG00). The local copy (text and page images) was read only.

**Verdict: feasible now.** A certificate for LG00's torus T′ can be checked with the landed **sharp** certifier
(`checkTorusCertificateSharp_sound`, isoenergetic `g1_sharp`).
- **Size:** L = 36 digits and about 2.5·10³ Fourier coefficients, against the lunar certificate's 88 digits and 8.4·10³.
- **Cost:** lunar-class, about 7–150 CPU-h per torus with the D34 fix, 54–71 CPU-h on today's code.
- **It needs no new theorem, only:**
  - a data generator (Python);
  - a Lean Diophantine lemma for LG00's noble frequency ratio (0.4–0.8k lines);
  - a representation of √(I₁I₂). The action–angle form of LG00's polynomial has it, and `HamExpr` has no square
    root: either a Taylor model (no Lean change, but then the theorem is about a polynomial within 10⁻²² of LG00's
    (11)) or a `sqrt` node (0.8–1.5k lines, the exact (11)).

**The honest claim:** to our knowledge, the first formally verified KAM torus of a planetary model. It is a formal reproduction of the
KAM part of LG00's rigorous 2000 result (one of its two confining tori; the second costs about the same), not new
mathematics.

**Beyond LG00.** Tori of the same model with two and three times LG00's eccentricities converge and certify under
the sharp theorem at L = 48–54 and S = 1.2–1.7·10⁴, about 30–50 CPU-h. LG00's own KAM step had a 3 % margin, so these
would plausibly be new results about the model; that was not established.

| Theorem on LG00's T′ (iso) | Threshold | Digits L | Support S | CPU-h per torus (D34-like ×1–20) | Status |
|---|---:|---:|---:|---:|---|
| Sealed `KAM.Iso.Apost` (landed certifier) | 10⁻¹³² | 142 | 3.8·10⁴ | 74–1 600 | possible, heavy |
| Sharp `KAM.Iso.Sharp.g1_sharp` (CertificateSharp) | 10⁻³¹ | 36 | 2.5·10³ | 7–150 | **recommended** |
| Route A `iso_g1_v2A` (proved, not wired) | 10⁻¹⁴ (10⁻¹²·² frequency-specific) | 16–18 | 550–680 | 3–75 | needs a wiring package |

**The model checks out.**
- The transcription of eq. (11) (69 monomials, exact rationals) reproduces the paper's energy (52) to 5·10⁻¹⁶, and
  its frequencies (12), ω′ and ω″ to our integrator's 10⁻⁸.
- The torus with LG00's Γ′ frequency converges to machine precision. Its energy lies inside LG00's interval (52).
- LG00 fixes the frequency ratio and the energy: exactly the isoenergetic form our certifiers check.
- γ_dir = 0.2251 for τ = 1, seven times LG00's conservative 8·10⁻⁶/|ω₂|.
- The kernel cost is calibrated on two probes at this size: one landed shard of a 3 025-term product, 14.1 s and
  5.0 GB.

## 1. The model (brief item 1)

**Transcription.** `scripts/sjs/lg00/lg00_data.py` holds eq. (11) as printed in Appendix A, without its additive
constant (the paper neglects it). Each coefficient is the exact decimal string, read as a `Fraction`.
- **Sources.** The digits come from the text layer; the monomials come from the page image of p. 24 and from the
  text layer's encoding. Both readings agree on all 69 entries.
- **Shape.** The polynomial has 69 monomials of degree 2, 4 and 6 in (ξ₁, ξ₂, η₁, η₂). They are exactly the monomials
  of these degrees that are even in η, which is the symmetry (ξ, η) ↦ (ξ, −η) stated at (15). Every coefficient is
  negative.
- **"129 monomials."** The brief and SJS-FEAS said 129. That is the size of (11)'s index range: all monomials of
  degree 2, 4 and 6 in 4 variables, 10 + 35 + 84. Only the 69 even ones are nonzero.
- **Data also transcribed:**
  - Tables 2–4 and eq. (12);
  - ω′ and ω″ of §4.3;
  - the curves Γ′ and Γ″ of (51);
  - the energy interval (52);
  - the Theorem 2 numbers.

**Conventions** (derived from (2), not stated in the paper).
- ξ = √(2P) cos p and η = √(2P) sin p, with p = −ϖ and P = Λ(1 − √(1 − e²)). So dη∧dξ = dp∧dP: **η is the
  coordinate and ξ the momentum**, and Hamilton's equations are η̇ = ∂H/∂ξ, ξ̇ = −∂H/∂η.
- With LG00's (14) this gives φ̇ = ∂H/∂I. The quadratic part is negative definite, so the frequencies are negative,
  as in the paper. Units are AU, year and G = 1, so frequencies are in rad/year.

**Checks** (`lg00_model.py`, results in `results/lg00_model.log`).

| Check | Ours | LG00 | Agreement |
|---|---|---|---|
| H(11) at Table 3, exact rationals | −1.69867157646253·10⁻⁷ | (52): [−1.6986715765408·10⁻⁷, −1.6986715763842·10⁻⁷] | inside, 5·10⁻¹⁶ from the centre |
| Frequencies of the Table 3 orbit (RK4, h = 100 yr, 2¹⁷ steps; Hann-window frequency analysis of the normal-mode signals) | −1.456175688·10⁻⁴, −2.585681076·10⁻⁴ rad/yr | (12): −1.456175704·10⁻⁴, −2.585681181·10⁻⁴ | 1.1·10⁻⁸, 4.1·10⁻⁸ |
| ω′ (ξ₁, η₁ × 0.98, (ξ₂, η₂) rescaled to keep the energy, the §4.3 recipe) | | −1.4567321458·10⁻⁴, −2.5923437515·10⁻⁴ | 1.1·10⁻⁸, 4.2·10⁻⁸ |
| ω″ (× 1.02) | | −1.4556152601·10⁻⁴, −2.5790797113·10⁻⁴ | 1.1·10⁻⁸, 3.9·10⁻⁸ |
| Linear actions of the Table 3 point | 6.476·10⁻⁴, 3.337·10⁻⁴ | Table 4 (after Birkhoff): 6.576·10⁻⁴, 3.210·10⁻⁴ | 1.5 %, 4 % (Birkhoff's O(e²)) |
| Γ′, Γ″ of (51): the Möbius matrices on g = (√5 − 1)/2 | det +1, det −1 | "noble frequencies" | unimodular: a prefix, then all partial quotients 1 |

- **The frequency residuals are our integrator's.** The 1–4·10⁻⁸ offsets are systematic, identical for the three
  orbits, and match RK4's energy drift of 2.7·10⁻⁷.
- **The energy check is the sharp one.** At the Table 3 point the degree-6 terms contribute about 10⁻³ of H, and
  (52) is 9·10⁻¹⁷ wide in relative terms. A misprint in any coefficient beyond about its 13th digit would therefore
  have shown.
- **No suspected misprint in (11), Tables 3–4, (12), (51) or (52).**

**Observations, not errata.**
- LG00's γ = 8·10⁻⁶ rad/yr (τ = 1) is 0.031 |ω₂|, against the infimum 0.225 |ω₂| along Γ′ and 0.072 along Γ″ (§2).
  It is a conservative constant valid for both curves under their condition (b).
- Table 2's g₂ and (12)'s g₂ differ by 1.3 %, as the paper itself states.

## 2. The torus (brief item 2)

**What LG00 targets.** Theorem 1 confines the Jupiter–Saturn secular orbit between two invariant 2-tori T′ and T″ of
the model, on the energy level E of (52).
- LG00 fixes the **frequency ratio**, a noble number on Γ′ (resp. Γ″), and the **energy**. They prove tori for every
  ω₂ in a 2·10⁻⁹-relative range and then use the continuity of E(ω).
- That is exactly the isoenergetic form of our theorems (fixed direction ω*, energy E₀, frequency s·ω*), which is the
  form the landed certifiers check (`G1Hyps` is the hypothesis list of `KAM.Iso.Apost.g1_explicit`; CertificateSharp
  uses `KAM.Iso.Sharp.g1_sharp`).
- The confinement step itself is a topological argument about the energy surface, outside any of our certificates.

**Chart** (`lg00_torus.py`).
- **Normal modes.** η = QY and ξ = Q⁻ᵀX (canonical), with H₂ = Σ λⱼ(Xⱼ² + Yⱼ²)/2 and λ = (−1.3731·10⁻⁴,
  −2.2238·10⁻⁴) rad/yr (−28.32″/yr, −45.87″/yr).
- **Action–angle variables.** LG00's (14), Xⱼ = √(2Iⱼ) cos φⱼ and Yⱼ = √(2Iⱼ) sin φⱼ, give
  h(φ, I) = Σ C_{m,k} (2I₁)^{m₁/2}(2I₂)^{m₂/2} cos(k·φ): LG00's form (15). It has 68 cosine terms after
  diagonalization; the 69th, the off-diagonal quadratic one, vanishes.
- Only harmonics with k₁ + k₂ even occur. Terms with odd m₁ (always together with odd m₂) carry √(I₁I₂).

**Frequency.** ω = ω₂(r, 1) with r = (5797287 + 2625484g)/(10316626 + 4672209g) = 0.5619363346117274 and ω₂ the centre
of the Γ′ range: ω = (−1.4567321458·10⁻⁴, −2.5923437515·10⁻⁴) rad/yr.

**Diophantine constant** (τ = 1, ℓ¹ norm). r is a unimodular image of g. Its continued fraction is
[0; 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4, 1, 4, 2, 1, 1, 1, …] (23 partial quotients, then all 1s; mpmath,
80 digits).
- Over all convergents and intermediate fractions up to q = 6·10¹¹, inf |k|₁|k·(r, 1)| = **0.2251**, at k =
  (28053, −15764); 0.2255 at (16, −9). Along Γ″ (a partial quotient 21) it is 0.0718.
- **How to certify it.** If (|k₁| + |k₂|)|k₁r + k₂| < 0.2251 < 1/2, then −k₂/k₁ is a convergent of r (Legendre). The
  prefix convergents are finitely many, and the tail convergents have complete quotient φ = 1/g exactly, so their
  products tend to (1 + r)/√5 ≈ 0.70.
- **The landed norm argument is of no use here** (`QuadraticDiophantine.lean`, written for the lunar frequencies).
  r's minimal polynomial has leading coefficient about 4·10¹³. A transfer through the unimodular matrix
  (`DiophantineTransfer.lean`) would lose a factor of about 10⁷ in γ.

**Newton solve** (parameterization method, Haro–Luque frame, continuation in ε, N = 64 and 128 grids, 1/3 cut).
- It converges quadratically from the averaged guess: |E| = 5.7·10⁻⁶ → 2.2·10⁻⁷ → 7.5·10⁻¹¹ → 3.5·10⁻¹⁷ → 8·10⁻¹⁹
  rad/yr. The last value is 3·10⁻¹⁵ relative to |ω|, which is machine precision.
- I₀ = (6.4009·10⁻⁴, 3.3227·10⁻⁴). max |u| = 0.115 rad, and max |v|/I₀ = 3.7 % and 8.3 %.
- **Its energy is −1.698671576460707·10⁻⁷**, inside (52), and 1·10⁻¹² relative from the energy of the Table 3 point:
  the centre of Γ′ is on LG00's energy level, as their construction intends.
- Torsion in the 2π chart: ⟨T⟩ = [[0.00575, 0.01656], [0.01656, 0.1058]], which is nondegenerate.

**Fourier decay.**
- The torus is analytic well beyond the strips that matter. Its slowest direction decays by about 0.74 digits per
  unit |k|₂ at ρ = 0.02, and the other directions by 1.2–1.5 (period-1 strip weights e^{2πρ|k|₁} included).
- The kept set at L digits is measured up to L = 13 and extrapolated from per-direction decay rates (36 sectors). It
  agrees with the counts within 4 % at L = 13.
- The invariance error left by truncating at L digits (relative to the largest coefficient) follows
  e(L) ≈ 10^{2.2 − 0.92L} in the certificate's chart (c = 10⁵, ℓ = 10⁻⁴), for ρ between 0.005 and 0.04.

| ρ (period-1) | S(30) | S(50) | S(80) | S(190) | Slowest decay (digits per unit \|k\|₂) |
|---:|---:|---:|---:|---:|---:|
| 0.005 | 1 361 | 3 754 | 9 573 | 53 804 | 0.77 |
| 0.01 | 1 412 | 3 898 | 9 945 | 55 907 | 0.75 |
| 0.02 | 1 526 | 4 216 | 10 761 | 60 532 | 0.71 |
| 0.04 | 1 803 | 4 993 | 12 760 | 71 860 | 0.64 |

S counts ±k on the parity sublattice (k₁ + k₂ even); real cosine/sine storage needs half of it. The box layout's
box/support ratio of the kept set is β = 2.9–3.2 (L = 8–13), including the parity sublattice.

**Beyond LG00's tori** (`lg00_amplitude.py`). LG00's KAM step had little margin: ε_{R″} = 0.840 against a threshold of
0.868. An a-posteriori certificate is limited only by the torus's own analyticity, so I continued the torus outward,
with actions f² I₀ at the averaged frequency (these runs test convergence and decay; no Diophantine data):

| f (amplitude) | Actions | Residual / \|ω\| | Slowest decay | Kept at L = 12 | max \|u\| |
|---:|---|---:|---:|---:|---:|
| 1 | (7.0, 3.3)·10⁻⁴ | 3·10⁻¹⁵ | 0.71 | 238 | 0.12 |
| 1.5 | (1.7, 0.8)·10⁻³ | 6·10⁻¹⁵ | 0.51 | 382 | 0.26 |
| 2 | (3.6, 1.4)·10⁻³ | 1·10⁻¹⁴ | 0.42 | 602 | 0.36 |
| 3 | (1.0, 0.32)·10⁻² | 2·10⁻¹⁴ | 0.35 | 762 | 0.41 |

Tori with three times LG00's eccentricities (nine times the actions) still converge to machine precision. Their
support at a given L grows only about 3×. The model itself (6th order in the eccentricities) is of course less
faithful there.

## 3. Thresholds against the reachable error (brief item 3)

**Which form.** LG00 fixes the frequency ratio and the energy, so the isoenergetic theorems are the relevant ones.
The fixed-frequency numbers are shown for comparison.

`lg00_oracle.py` evaluates every theorem on the torus's measured data in the certificate's chart:
- θ = φ/2π, I = I₀ + ℓa, h̃ = c·h/(2πℓ), K̃(θ) = (θ + u/2π, v/ℓ), ω̃ = cω/2π;
- free parameters: the strip ρ (period-1), the margin μ, the time scale c and the action scale ℓ; identity angle
  frame;
- the search: a grid of 360 points, then a coordinate refinement per theorem minimizing the support S(L).

**The criterion.** The truncation L is the smallest digit count with e(L) ≤ T·10⁻¹, using e(L) from §2 in the same
chart. S(L) is the support from §2.

| Theorem (mirror) | Form | log₁₀ T | L | Bits | S | ρ | μ | c | ℓ | M | σ_K | σ_B | Torsion inverse | γ̃ |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Sealed, `KAM.Iso.Apost.g1_explicit` (`thresholds.current_iso`): the landed certifier | iso | −132.2 | 142 | 497 | 3.8·10⁴ | 0.010 | 10⁻³ | 10⁴ | 10⁻³ | 63 | 1.26 | 1.36 | 52.8 | 0.093 |
| Sealed, `KAM.Apost.g1_explicit` (`current_fixed`) | fixed | −150.0 | 161 | 561 | 4.9·10⁴ | 0.010 | 10⁻² | 1.7·10⁴ | 10⁻³ | 135 | 1.26 | 1.36 | 133 | 0.16 |
| Sharp, `KAM.Iso.Sharp.g1_sharp` (`thresholds.sharp`): CertificateSharp | iso | **−31.1** | **36** | 145 | **2.5·10³** | 0.0058 | 10⁻⁵ | 10⁶ | 3·10⁻³ | 4.0·10³ | 1.26 | 1.35 | 0.21 | 9.3 |
| Sharp, `KAM.Sharp.g1_sharp` | fixed | −32.1 | 37 | 148 | 2.6·10³ | 0.0058 | 1.7·10⁻⁵ | 10⁶ | 3·10⁻³ | 4.0·10³ | 1.26 | 1.35 | 0.77 | 9.3 |
| Route A, `iso_g1_v2A` (`route_a_lean_mirror`, classical) | iso | **−13.9** | **18** | 85 | **680** | 0.017 | 10⁻⁵ | 10⁶ | 3·10⁻³ | 5.2·10³ | 1.26 | 1.36 | 0.21 | 9.3 |
| Route A, `g1_v2A` (classical) | fixed | −13.3 | 18 | 83 | 630 | 0.017 | 10⁻⁵ | 10⁶ | 3·10⁻³ | 5.2·10³ | 1.26 | 1.36 | 0.77 | 9.3 |
| Route A, iso, frequency-specific stage constants | iso | −12.2 | 16 | 79 | 545 | (as above) | | | | | | | | |
| Route A, fixed, frequency-specific | fixed | −11.8 | 16 | 77 | 521 | (as above) | | | | | | | | |

Bits = 3.33L + 24 (SO-GEN2's rule).

**Reading the table.**
- **Every theorem has a margin.** The torus can be truncated to any L, and e(L) ≈ 10^{−0.92L + O(1)} has no floor
  but the data's precision. So the margin is never the question; the support needed to reach T is.
- **Sealed theorem: L = 142, S = 3.8·10⁴.** That is 1.6 times the lunar torus's L = 88 and 4.5 times its S0 = 8.4k.
  Feasible, but heavy (§4).
- **Sharp theorem: L = 36, S = 2.5·10³.** Fewer digits and a third of the lunar support. The landed sharp certifier
  (`checkTorusCertificateSharp_sound`, `isoSharpG1 = KAM.Iso.Sharp.g1_sharp`) checks exactly this form.
- **Route A: L = 16–18, S = 545–680.** Proved in Lean (SHARP2-B9), but not wired into a certifier.
- **What binds.**
  - The sealed theorem binds on its γ⁴ρ^{4τ} structure with one size M.
  - The sharp theorem binds on M = sup|D²X_h̃| = 4.0·10³, against 80–500 for the other four derivative norms.
  - Route A binds on tail decay with classical constants, and on the σ_T cap (the torsion-inverse drift budget) with
    frequency-specific ones.
- **The frequency-specific constants gain 1.4 orders** over the classical ones on route A (c_freq/c_classical =
  0.30 at δ₀, 0.23 at δ₀/4), as SHARP2-B9's design predicts.
- **The chart scales matter by more than 40 orders.** A first grid (c ≤ 3·10⁵, ℓ ≤ 10⁻⁴) gave −175, −44.5 and −24.9
  for the three theorems. The time scale c makes |ω̃| = O(40) and γ̃ = O(10), and the action scale ℓ brings σ_K down
  to its angular floor 1 + |∂u|.

**Beyond LG00** (the f = 2 and f = 3 tori of §2, assuming a noble direction nearby with the same γ_dir = 0.225):

| Torus | Sharp (iso): log₁₀ T, L, S | Route A (iso, classical): log₁₀ T, L, S | D34-like CPU-h, sharp / route A (S-scaled from §4) |
|---|---|---|---|
| f = 1 (LG00's T′) | −31.1, 36, 2.5·10³ | −13.9, 18, 680 | 6.6 / 3.4 |
| f = 2 (4× the actions) | −41.8, 48, 1.2·10⁴ | −18.2, 23, 2.8·10³ | about 31 / 14 |
| f = 3 (9× the actions) | −48.1, 54, 1.7·10⁴ | −21.5, 26, 4.3·10³ | about 46 / 22 |

(`results/lg00_thresholds_f{2,3}.log`; the same search over c, ℓ, ρ, μ; ×1–20 calibration risk as in §4.)

Even three times LG00's eccentricities stays within lunar × 3 under the sharp theorem.

## 4. Representation and cost (brief item 4)

**The Hamiltonian as a `HamExpr`: one gap, the square root.**
- **The obstacle.** Our theorems (`G1Body`, `IG1Body`) live on 𝕋ⁿ × ℝⁿ: h is periodic in the angles and K is
  primary. A torus around an elliptic equilibrium is primary only in polar (action–angle) coordinates. There
  X = √(2I) cos φ, so the terms of (15) with odd m₁, m₂ carry √(I₁I₂).
- `HamExpr` has `const, pi, action, cosMode, sinMode, add, mul, div, pow, exp, sin, cos` and no square root (or
  logarithm). Neither does any canonical polynomial chart avoid it: an area-preserving radial chart of an annulus
  needs r = √(2I + c).
- **Two ways out:**
  1. **Taylor model, no Lean change.** Replace √(2Iⱼ) by √(2I₀ⱼ)·T_K(ℓaⱼ/I₀ⱼ), with T_K the degree-K Taylor
     polynomial of √(1 + x).
     - On the certificate's domain x ≤ ℓR/I₀ ≈ 0.1, so K = 19 leaves a remainder of 4·10⁻²³ relative.
     - The certified Hamiltonian is then a polynomial within 10⁻²² (relative) of LG00's (11) on the domain. LG00's
       own theorem is likewise about a truncation (of (19), at order 70).
     - It is honest if stated so, but it is a model of the model.
  2. **A `sqrt` node, the exact (11).** A new primitive with a witness, like the exp witnesses: the certificate gives
     s(θ) ≈ √(g(θ)); the checker bounds s² − g, applies a contraction step, and checks the branch (Re g > 0 on D).
     - The ball pass needs bounds of √ and its derivatives on a disc away from 0.
     - About **0.8–1.5k Lean lines**. HamExpr is SO-owned (`KAM/Certificate/Expr`), so this is either an SO package
       or a CertificateSharp-side expression type.
- **The linear change** η = QY, ξ = Q⁻ᵀX is exactly symplectic for any rational Q. A rational Q close to the
  normal-mode matrix gives an exact rational polynomial H∘T with an almost diagonal quadratic part. No approximation
  enters there.
- **Stating the result in LG00's variables** (Ψ∘K invariant for (11), with Ψ the explicit canonical map) is an
  optional transport lemma of about 0.2–0.4k lines.

**Frequency.** The certifiers take IsDiophantine of ω* as a separate hypothesis, which needs a Lean lemma for LG00's
r (§2):
- the Legendre and convergent argument: about 0.4–0.8k lines (Mathlib has Legendre's theorem for continued
  fractions), with γ_dir = 0.2251;
- or a substitute direction r̂ with a short continued fraction near r, proved by the norm argument of
  `QuadraticDiophantine.lean`: about 0.2k lines, but no longer LG00's Γ′.

**Operation counts** (`lg00_cost.py`; the Python mirror `adv_jet.py` of the landed jet compiler, run on my
`HamExpr`).
- The `HamExpr` is h̃ = c/(2πℓ)·[A + √(4I₁I₂)·B]: A and B are trigonometric polynomials (`cosMode`) with
  polynomial coefficients in the actions, grouped by (m₁, m₂), so √ occurs once.
- Char witnesses are cached per key and reflected for −k (`Compose.charResolve`). That leaves 24 checks per stage, 2
  model×model products each (`expWitnessRadiusOf`: n derivative residuals).

| HamExpr | Program slots | Invariance + energy: model ops / model×model | Torsion stage (d₁, d₂): model ops / model×model |
|---|---:|---:|---:|
| Taylor K = 19 | 8 538 | 1 402 / 146 (+48 for chars) | 3 067 / 302 (+48) |
| Taylor K = 10 | 8 124 | 1 294 / 110 | 2 869 / 248 |
| One `sqrt` node (K = 1 proxy, +2 for its witness) | 7 644 | 1 186 / 74 | 2 669 / 190 |
| Lunar torus, for comparison | 887 | 140 / 1 | 273 / 0 |

LG00 needs about 150–200 genuine model×model products per stage, against 1 for the Moon. Its supports are small, so
per-coefficient cost decides.

**Kernel probes at this size** (one niced Lean process, ≤ 5 GB; `results/lg00_probes_raw.jsonl`).
- **Landed `checkShard`**, the middle shard of a 3 025-term 2-D product (160 bits, `blockRows` 4, 27 shards, 23 517
  advice slots): **14.1 s kernel, 4.96 GB peak**. That is about 6 min per product, or 12–16 ms per advice slot.
- **Prototype D34-like shard** at the same size: 5.8 s, 4.16 GB. It re-packs the factors in every shard.
- SJS-FEAS's prototype checks the whole 3 025-term product in **one declaration: 34–37 s, 6.5 GB**. At LG00's
  supports a product therefore needs no sharding once D34 lands.
- **Lunar reference** (after D34, OVERNIGHT 11:19–11:29): one `blockRows`-32 shard takes +45 s of kernel time; 1 157
  shards make about 15 CPU-h per torus, plus about 190 s per shard to elaborate the literal data.

**Cost per torus** (`results/lg00_cost.log`).
- Inputs: the measured β = 3.0 (box/support of the kept set, parity included) and 7.7 advice slots per factor term
  per unit β.
- Low-precision Gram/torsion stage on the 17-digit support.
- "D34-like" is the per-slot model of SJS-FEAS (1.0 ms per slot, 1.4 ms per packed term, 1.26 ms per term per model
  op); "landed" is today's code at the probe's 12–16 ms per slot.

| Theorem | L | S | D34-like CPU-h | Landed CPU-h | Data elaboration CPU-h | Declarations, D34-like / landed | Peak (D34-like) |
|---|---:|---:|---:|---:|---:|---:|---:|
| Sealed, iso | 142 | 3.8·10⁴ | 74 | 610–800 | 9–30 | 3 454 / 91 392 | sharded at 6 GB |
| Sharp, iso | 36 | 2.5·10³ | **6.6** | 54–71 | 0.8–2.6 | 544 / 23 392 | 9.1 GB |
| Route A, iso | 18 | 680 | **3.4** | 27–36 | 0.4–1.3 | 544 / 11 968 | 4.7 GB |
| Route A, iso, frequency-specific | 16 | 545 | 3.0 | 24–32 | 0.3–1.2 | 544 / 10 880 | 4.4 GB |
| With a `sqrt` node: sealed / sharp / route A | | | 51 / 4.6 / 2.5 | 394–519 / 35–47 / 19–24 | | | |

**Calibration caveat (the same as SJS-FEAS).** This per-slot model counts only the demanded operations, and it
prices the lunar torus at 0.65 CPU-h against the measured 15 CPU-h after D34, an unresolved factor of about 20.
- If that factor carries over, the realistic D34 range is: **sealed 74–1 600, sharp 7–150, route A 3–75 CPU-h per
  torus.**
- The landed checker composes the whole program: 800 model×model products instead of the demanded 448, a factor of
  about 1.8.
- For comparison, a lunar torus costs 15 CPU-h of kernel time plus about 60 of elaboration. **The sharp and route-A
  certificates are lunar-class; the sealed one is lunar × 5–100.**

## 5. Verdict and plan (brief item 5)

**Verdict: feasible now, with the landed sharp certifier and two pieces of new work, none of them theorem work.**
- **The theorem.** `checkTorusCertificateSharp_sound` (`KAM.Iso.Sharp.g1_sharp`, the isoenergetic form that LG00's
  setting needs) gives a threshold of 10^−31 on this torus. That means L = 36 digits, S ≈ 2.5·10³ coefficients and
  145-bit data: less support than the lunar certificate.
- **The cost:** about 7–150 CPU-h per torus with the D34 fix, 54–71 CPU-h on today's code (×1–20 calibration risk).
  Days on this machine at most.
- **The sealed theorem** (the landed certifier) also works, but needs L = 142 and S = 3.8·10⁴: 74–1 600 CPU-h. Not
  the route to take.
- **Route A** (proved, SHARP2-B9) halves the digits again (L = 16–18, S ≈ 600, 3–75 CPU-h). It needs a certifier
  wiring package first and is not necessary.
- **The two pieces of new work:**
  1. a representation of √(I₁I₂): a Taylor model with no Lean change, or a `sqrt` node;
  2. a Lean Diophantine lemma for LG00's noble direction.

**The claim we could honestly make.**
> A formally verified (kernel-checked) KAM torus of Locatelli–Giorgilli's secular Sun–Jupiter–Saturn model: the
> invariant 2-torus with LG00's frequency ratio Γ′ (a noble number) on the energy level of the actual Jupiter–Saturn
> initial data.
- **It is a formal reproduction** of the KAM part of LG00's rigorous Theorem 1 (one of its two confining tori), not
  new mathematics.
- **T″ as well.** Γ″ has γ_dir = 0.072, three times smaller. Through γ⁴ that costs about 2 orders of threshold
  (sharp: about 10⁻³³ instead of 10⁻³¹, L about 38; an estimate, since T″ was not computed). That is cheap. The confinement itself (the orbit trapped between T′ and T″ on the energy
  surface) is a topological argument outside our certificates and is not proposed.
- **With the Taylor model,** the certified Hamiltonian is a polynomial within 10⁻²² (relative) of (11) on the
  certificate's domain, and the statement must say so. With a `sqrt` node it is (11) itself.
- **Beyond LG00:** tori of the same model at 2–3 times LG00's eccentricities (§2, §3), at a support that is still
  modest, would be new results about the model. LG00's own KAM step had a 3 % margin at their tori (ε_{R″} = 0.840
  against 0.868), so these are plausibly out of reach of their 2000 estimates; this was not established.
  Under the sharp theorem these need L = 48–54 and S = 1.2–1.7·10⁴ (§3), about 30–50 CPU-h with D34; that is
  feasible. Each needs its own noble direction and Diophantine lemma (P2's method).

**Package plan** (in order; Lean lines are estimates from the landed analogues):

| Package | Content | Size | CPU |
|---|---|---:|---:|
| **P1 LG00-DATA** | Generator, written in the SO track's style (`scripts/…/lg00/`):<br>• rational symplectic Q and the exact rational H∘T;<br>• the `HamExpr` (Taylor K = 19, or the `sqrt` node);<br>• the multiprecision torus (mixed-precision Newton: double-precision corrections against mpmath residuals, about 50 digits);<br>• char witnesses, Gram and torsion inverses, advice;<br>• emission in the `TorusCertificate` format | 1.5–2.5k Python lines | hours |
| **P2 LG00-FREQ** | `IsDiophantine (0.2250·|ω₂|) 1 ω*` for the Γ′ direction: Legendre plus the 23 explicit convergents and the golden tail; Γ″ in the same file | 0.4–0.8k Lean lines | minutes |
| P3 SQRT-NODE (recommended) | `sqrt` in the expression language with a witness check, ball bounds and the jet rule; the exact (11) instead of the Taylor model; −25 % on the products | 0.8–1.5k Lean lines (SO-owned path: coordinate) | — |
| **P4 LG00-CERT** | The CertificateSharp run: shards and declarations, sharp iso, T′ then T″; needs D34 landed (branch `inp-sopackfixl`) for the low end of the range | data only | 7–150 CPU-h per torus (54–71 on today's code) |
| P5 ROUTE-A-CERT (optional) | Wire `iso_g1_v2A` into CertificateSharp (route-A smallness, `RefHypA` data from the certificate) | 0.5–1k Lean lines | then 3–75 CPU-h per torus |
| P6 TRANSPORT (optional) | The theorem stated in LG00's (ξ, η): Ψ∘K invariant for (11) | 0.2–0.4k Lean lines | — |
| P7 BEYOND (optional) | Tori at f = 2–3 (§2): P1–P4 again, with a noble direction near their frequencies | P1 parameters | 30–50 CPU-h per torus (sharp, D34) |

**Recommended first step:** P1 and P2 in parallel; P4 with the Taylor model as soon as P1 emits. P3 can replace the
Taylor model before any announcement.

## 6. Caveats

- **Mirrors, not theorems.**
  - The thresholds are Python mirrors: `thresholds.py` (sealed and sharp) and `route_a_lean_mirror.py` (route A,
    transcribed by hand from the Lean definitions per SHARP2-B9). Nothing links them mechanically to Lean.
  - The frequency-specific constant is a floating-point value, not a certified `sdFinite` bound.
- **Norms.**
  - σ_K, σ_B, |L^⊤|, |N|, |N^⊤| and sup |T| are sampled sups on the distinguished boundary, × 1.01. That is what
    CertificateSharp's corner and grid bounds reach. The landed certifier's weighted ℓ¹ bounds are larger (σ_K ℓ¹/sup
    = 1.66 at one point checked), which matters only for the sealed theorem, already out of reach.
  - M is the term-wise majorant on D (the shape of the landed ball arithmetic), with the exact √ factors. A Taylor
    model of √ changes M by its remainder only.
- **Double-precision torus.** The digits beyond 13 are extrapolated: e(L) log-linearly from L ≤ 13, and S(L) from
  per-direction decay rates. A certificate needs a multiprecision torus (section 5, package P1).
- **Parameters.** Identity angle frame only (no unimodular frame search). The parameter search is a grid plus a
  coordinate refinement, so the optima may improve somewhat.
- **Operation counts** come from the mirror of the landed jet compiler on my HamExpr (grouped by (m₁, m₂), Taylor
  K = 19). A better HamExpr (shared chars, Horner in the modes) would lower them. The count of 118 chars
  (one witness per cosine and its conjugate) is not deduplicated.
- **Kernel cost.**
  - Two probes at this size (one landed shard, one prototype shard) plus SJS-FEAS's constants; single runs at load
    about 12 (±30 %).
  - The D34 fix is not in this worktree, so the D34-like figures rest on SJS-FEAS's prototype (one declaration per
    product, 34 s and 6.5 GB at 3 025 terms) and on SO-PACKFIX's lunar shard (+45 s).
  - Data elaboration is costed at 0.18–0.6 ms per element.
- **Amplitude scan.** Convergence and decay only; those tori have no Diophantine data yet.
- **Physics.** LG00's model is a truncated secular approximation (order 2 in the masses, 6 in the eccentricities,
  averaged over the fast angles). A theorem about it says nothing directly about the real planets beyond what LG00's
  own does.

## 7. Errata and observations

No suspected misprint was found in the transcribed data (section 1's checks). For the record:
- **"129 monomials"** (the brief, SJS-FEAS §7, from the literature subagent) counts the index range of (11). The
  printed polynomial has **69** monomials, every one even in η. Our own SJS-FEAS document should read "69 monomials
  (129 in the index range)"; the orchestrator may correct it, since I did not edit it (additive rule).
- **LG00's γ = 8·10⁻⁶ (τ = 1)** is conservative, not an erratum: 0.031 |ω₂| against the infima 0.225 |ω₂| (Γ′) and
  0.072 |ω₂| (Γ″).
- **The canonical pairing of (ξ, η) is not stated** in the paper. It follows from (2) (η the coordinate), and the sign
  of every reported frequency confirms it.
- **The frequency checks agree to 1–4·10⁻⁸ only,** the accuracy of our RK4 integration, not of the paper.
- **Table 4** is after the Birkhoff step, so it cannot be compared with the linear actions beyond O(e²).

## 8. Reproduction

Run from the worktree root (numpy and mpmath required; no scipy):

```
python3 -I scripts/sjs/lg00/lg00_model.py --json scripts/sjs/lg00/results/lg00_model.json     # checks of section 1 (2 min)
python3 -I scripts/sjs/lg00/lg00_torus.py 128                                                 # the torus (N = 128)
python3 -I scripts/sjs/lg00/lg00_amplitude.py                                                 # larger tori (section 2)
python3 -I scripts/sjs/lg00/lg00_oracle.py --json scripts/sjs/lg00/results/lg00_thresholds.json   # section 3 (~15 min)
python3 -I scripts/sjs/lg00/lg00_cost.py --json scripts/sjs/lg00/results/lg00_cost.json      # section 4
```

The kernel probes were generated by `scripts/sjs/kernel_probe_gen.py packed {Lshard,Fshard} --dim 2 --shape box --K 27
--bits 160 --rows 4` and run by `scripts/sjs/kernel_probe_run.py` (records in `results/lg00_probes_raw.jsonl`). The
probe files themselves were deleted.
