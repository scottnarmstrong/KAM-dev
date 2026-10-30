# SO-V2PKG: the N = 65 lunar certificates under the v2 certifier

Branch `inp-sov2pkg`. Python, data and Markdown only; no Lean file touched or built.

## Verdict

**v2 makes the N = 65 certificate about 3–5× cheaper, with the R2 parameters unchanged.** Use the refined branch of
route A (`routeARefined`) at truncation **L = 20 digits**, backend **CertFixed 96**, with five certified small-divisor
bites (the largest at l = 12).

| | v1 sharp (SO-GEN3) | **v2, refined route A (recommended)** |
|---|---:|---:|
| threshold at R2 (log₁₀, both tori) | −31.83 | **−14.26** (−14.06 with every site certified) |
| truncation L (digits) | 40 | **20** |
| fixed-point precision | 160 | **96** |
| err (lower / upper) | 6.8e-35 / 8.17e-35 | **1.6e-16 / 1.83e-16** |
| err / threshold | 10^−2.34 / 10^−2.26 | **10^−1.53 / 10^−1.47** |
| disp (lower / upper) | 2.6e-19 / 3.1e-19 | **5.65e-11 / 6.47e-11** (graph limit 9.7e-7) |
| v half-terms | 1180 / 1165 | **251 / 246** |
| packed products / shards per torus | 129 / 1230 | **129 / 667 (lower), 718 (upper)** |
| slot width, block pairs per shard | 337 bits, ≤ 8 | **208 bits, ≤ 4** |
| mirror wall time per torus (GENERATE + CHECK) | 21.8 min | **7.0 min** |
| projected kernel per torus | 3–5 CPU-h | **≈ 0.7–1.8 CPU-h** (§4.4) |
| largest single declaration | ≈ 9 GB (Ham pass) | ≈ 9 GB (Ham pass, now twice) |
| certified band max\|p − 1\| | 2.755 % | **2.755 %** (unchanged; it does not depend on the certifier) |

Every pass/fail decision above is made in exact rationals by a Python transcription of the Lean tests. That
transcription agrees with the four kernel-checked tests of SHARP2-C6 (§2.4). The seven landed sub-checks and
`checkSoGraph` pass on both L = 20 tori in the fixed-point mirror `sofx_gen.py`. **Not mirrored:** the
small-divisor bites (`biteOk`, `balBound`), the Ham claim pass and the frame-majorant pass (§5.3).

N = 80 and N = 100 become affordable in data size: thresholds −16.10 and −19.15, against v1's −35.97 and −41.75
(§5). Re-optimising ρ or σ (a package R3) buys at most about one digit of L, so **no R3 is recommended** (§4.6).

## 1. The v2 test, exactly (task 1)

`checkTorusCertificateV2 E c w = landedBase.check c && E.test c w` (`V2/Engine.lean`). `landedBase` is the seven
landed sub-checks, unchanged: static, Ham bounds, embedding, invariance, energy, Gram and torsion. Only the
smallness test changes. `routeAV2 = sharpV2.orElse (routeAFrozen.orElse routeARefined)`, so the witness is
`Sum.inl ()`, `Sum.inr (Sum.inl wF)` or `Sum.inr (Sum.inr wR)`.

| Branch | Witness | `test` reads from the certificate | Numbers the witness carries | Soundness through |
|---|---|---|---|---|
| `sharpV2` | `()` | `c.params` only (`sharpTest`) | none | the landed `sharpEngine` |
| `routeAFrozen` | `FrozenWit` | `c.params`, `c.freqBox` (via `boxNormUp`, `freqNormLo`) | X⋆, kp, ϑ, `c` (classical constants at δ_s), `cbar` (at b_s), `ctail` (at δ_kp), caps sB, sT, sLt, sN, sNt, t, and J (terms of ζ(2, 2^τ)) | `iso_g1_v2A_default` |
| `routeARefined` | `RefinedWit` | `c.params`, `c.freqBox`, **plus** `checkHamClaim c R` (disc ball pass on `c.ham` over the domain) and `checkFrameMajorants c (R.frame box)` (corner passes on the certificate's DK, Gram witness and torsion models) | a `FrozenWit`, the claim `R : RefClaim` (dh, dx, d2x, d2h, bL, bN, bNt, bT), the clock κ, and per-site `Option BiteWit` (E₁, l, J, B) | `iso_g1_branch_A` |

**`frozenCore n p box w`** = `0 < X⋆` ∧ `NumQ.wfOk` ∧ `okB (capQ) (defaultInitQ) X⋆` ∧ `torsionCapOk` ∧ `classicalListOk` ∧ `finalOk`.
- `NumQ` uses M₁ = M₂ = Mh2 = M, HY = M·sN, sK = σK − μ/2, Θ = σω·boxNormUp(box).
- The initial values are the frozen defaults: Lᵀ: 2n(σK−μ); N: (σK−μ)(σB−μ); Nᵀ: 2n(σK−μ)(σB−μ); T: hT = 4nMσK²σB² + 1.
- `finalOk`:
  - err < X⋆ γ⁴ δ₀⁴;
  - **max(C₂♯, C₃♯, c2Q, c3Q)·err ≤ disp·γ²ρ²**, where C₂♯ is v1's constant, so disp is as large as v1's;
  - disp < (σω − s)·freqNormLo(box).

**`refinedCore n p box w`** = `0 < X⋆` ∧ `wfOk` ∧ `okB (capQ) (initQ bL bN bNt bT …) X⋆` ∧ `sitesOk` ∧ `classicalOk` (tail) ∧ `finalOkA`.
- `NumQ` uses M₁ = dx, M₂ = d2x, HY = dh·sN, Mh2 = d2h.
- The initial values are the claim's.
- `finalOkA` is `finalOk` without C₂♯ and C₃♯.
- `siteOk`: `none` means the classical constant (`classicalOk`); `some w` needs n = 2, τ = 1, `clockOk` (box coordinate 1 is
  exactly (κ, 0)) and `biteOk`. `biteOk` is `balCheck` and `balBound ≤ B` on the fibre box, then
  B κ⁻² (γ b)² ≤ (3.1415·c)².

**`okB`** (the mirror of `routeAOkI`):
- J1: the five `condB` inequalities at every stage s ≤ kp, with x_{s+1} = 2^{4τ} C_{E,s} x_s².
- J2: 2^{4τ} C_{E,kp} x_kp ≤ 1.
- J3: nine budgets m₀ᵢ + Σ ≤ capᵢ. The caps are (μ/2, σK − μ/2, sB, sT, sLt, sN, sNt, t, ν/2).
  - The witness's free caps are taken tight: cap = m₀ + Σ, a fixed point.
  - The DK budget is μ/2 and the frequency budget is ν/2 = 5·10⁻⁷.

**Python mirror** (`scripts/spin_orbit/v2_q.py`). It transcribes every function above over `Fraction`, with the Lean
names: `Step` = `StepQ`, `Num` = `NumQ`, `okB`, `frozenCore`, `refinedCore`, `classicalOk`, `torsionCoefQ`, and so on. C₂♯ and C₃♯
come from `sharp_q.py`, whose R2 threshold the kernel checks (`lunarR2_sharp_C1`). The certified site constants come
from the float `c_freq` (`scripts/apost_sharp/smalldiv.py`) × 1.01; the kernel witness must be re-derived with the
balanced checker.

**Which branch for the Moon: `routeARefined`.**
- Its threshold is 10^−14.06 to 10^−14.26, against 10^−27.87 for `routeAFrozen` and 10^−31.83 for `sharpV2` (§2).
- The frozen branch also keeps v1's displacement constant (disp coefficient 10^15.58). At its own threshold that is
  harmless, but it brings nothing.
- The refined branch's disp coefficient is 10^5.6, so disp ≈ 6·10⁻¹¹. That is 4 orders below the graph check's
  limit disp < mono·ρ∞ = 9.7·10⁻⁷.
- The clock condition holds: the R2 boxes have coordinate 1 equal to (κ, 0) exactly (`lunarR2Box` of the row
  `[lunarR2Kappa]`).

## 2. Thresholds at R2, N = 65 (task 2)

Package `lunarR2` exactly (`KAM/SpinOrbit/LunarParamsR2.lean`), both boxes. ϑ = 1/8, J = 20. "Binding" is what fails at
1.1 X⋆. Threshold e\* = X⋆ γ⁴ δ₀⁴ (strict).

| Branch, configuration | log₁₀ e\* (lower = upper) | disp coefficient C/(γ²ρ²) | binding | largest bite |
|---|---:|---:|---|---:|
| `sharpV2` (v1, landed) | **−31.827** | 10^15.58 | branch E | — |
| `routeAFrozen`, kp = 5 | −27.873 | 10^15.58 (C₂♯) | J1 stage 5 (C_E), J2 | — |
| `routeARefined`, classical sites, kp = 3 | −18.656 | 10^8.71 | J2 (tail) | none |
| `routeARefined`, δ₀ + b₀–b₂ certified, kp = 3 ("d0b") | −15.551 | 10^5.65 | J2 | l = 11 |
| `routeARefined`, kp = 2, all certified | −14.475 | 10^5.56 | J2 | l = 12 |
| **`routeARefined`, δ₀, δ₁, b₀–b₂ certified, δ₂ classical, kp = 3 ("d01b")** | **−14.264** | **10^5.58** | J2 | **l = 12** |
| `routeARefined`, all certified, kp = 3 | −14.063 | 10^5.60 | J3 sT (torsion inverse) | l = 13 |
| `routeARefined`, all certified, kp = 4 or 5 | −14.063 | — | J3 sT | l = 14 / 15 |

**The gain over v1 is 17.6 orders (d01b), or 17.8 with every site certified.** ϑ scan for all-certified sites (log₁₀ e\*):

| kp | ϑ = 1/16 | ϑ = 1/8 | ϑ = 1/4 | ϑ = 1/2 |
|---:|---:|---:|---:|---:|
| 1 | −16.21 | −16.21 | −16.21 | −16.21 |
| 2 | −14.48 | −14.48 | −14.48 | −14.50 |
| 3 | −14.19 | −14.06 | −14.14 | −14.36 |
| 4 | −14.19 | −14.06 | −14.14 | −14.36 |

The non-monotonicity in ϑ, about 0.1 orders, comes from the tight-cap fixed point. The search is finite; neither
side's optimum is proved.

### 2.1 Inputs of the refined claim (N = 65, both tori agree to 10⁻⁴)

| claim | value | source |
|---|---:|---|
| dh, dx, d2x, d2h | 2.099, 2.020, 1.512, 2.141 | `checkHamBounds` sums of the SO-GEN3 sofx run (2.0777, 2.0, 1.4968, 2.1191; the same jet sums as `hamClaimOk`) × 1.01 |
| bL = \|Lᵀ\| | 1.830 | `v2_frame.py`: sampled on the four corners Im θ = (±ρ, ±ρ) of the 256 × 64 double torus, × 1.01 |
| bN, bNt | 2.253, 2.291 | same |
| bT = sup \|T\| | 10.393 | same; **validation:** the real average of T is 3.80717972285, against the certified centre 3.8071797228558 |

For comparison, the frozen default initial values are 7.47, 10.03, 40.1 and hT = 1754. The refined claim is what
makes the 13.6 orders between the frozen and refined branches.

### 2.2 Certified site constants (float, × 1.01; classical c♮ ≈ 0.0814)

| site | δ₀ | δ₁ | δ₂ | b₀ | b₁ | b₂ |
|---|---:|---:|---:|---:|---:|---:|
| bite | 1.189e-3 | 5.95e-4 | 2.97e-4 | 7.14e-3 | 3.58e-3 | 1.79e-3 |
| c | 0.001902 | 0.001881 | 0.001878 | 0.003742 | 0.002333 | 0.001954 |
| cut-off l (by R1's 2^l·bite ≈ 2.4 for δ, ≈ 1.8 for b) | 11 | 12 | 13 | 8 | 9 | 10 |

### 2.3 The recommended witness, checked exactly at the L = 20 err

`scripts/spin_orbit/v2_pkg65.py` (output `so-v2pkg-data/N65_witness_d01b.json`):

| torus | err | X⋆ (2× room) | disp (exact minimum, rounded **up**) | err / e\* | `refinedCore` (mirror) |
|---|---:|---:|---:|---:|---|
| lower | 1.60e-16 | 3 digits | 5.65e-11 | 10^−1.53 | true (Xs, wf, okB, tail, final) |
| upper | 1.83e-16 | 3 digits | 6.47e-11 | 10^−1.47 | true |

### 2.4 Cross-check against the Lean ℚ mirror (`v2_crosscheck.py`)

The Python mirror is run on the exact inputs of the kernel tests of SHARP2-C6:
- `Tests/Frozen.lean`: `r1_frozen_passes` true at err 1.15e-21 and `r1_frozen_rejects` false at 1.2e-21. Only `finalOk`
  flips.
- `Tests/RefinedR1.lean`: `r1_refinedCore` true at 4.7e-12 (with the sites as given) and `r1_final_rejects` (`finalOkA`)
  false at 4.8e-12.

Output: `MIRROR AGREES WITH THE KERNEL TESTS`. Independently, `sharp_q.py` reproduces `lunarR2_sharp_C1` and
`lunarR2_sharp_C1_fails` (10^−31.827).

## 3. Sizing rule and what bounds the truncation

- err ≤ e\*/10 (one order, the brief's rule). At d01b that means err ≤ 10^−15.26 = 5.5e-16.
- disp ≥ C·err/(γ²ρ²) rounded up, with C/(γ²ρ²) = 10^5.6. disp must also satisfy:
  - **`checkSoGraph`'s disp < mono·ρ∞ = 0.13537 × 1/140000 = 9.67e-7.** This is not binding until err ≈ 2e-12.
  - the ray room disp < (σω − s)κ ≈ 2.
- err versus L (`v2_emit_scan.sh`, ρ = 1/140):

| L | v half (lower) | emit e (lower / upper) |
|---:|---:|---:|
| 14 | 108 | 7.5e-11 / 6.5e-11 |
| 16 | 146 | 1.2e-12 / 1.2e-12 |
| 18 | 191 | 3.0e-14 / 3.1e-14 |
| **20** | **251** | **3.2e-16 / 3.7e-16** (checker rows: **1.6e-16 / 1.83e-16**) |
| 22 | 305 | 4.3e-18 / 3.9e-18 |
| 26 | 439 | 1.4e-21 / 1.2e-21 |
| 40 | 1180 | (SO-GEN3) 6.8e-35 |

  The emitter's e includes its gate G-J split; the checker's err (sofx rows × 1.001) is about half of it. L = 19 would
  give err ≈ 2e-15, only about 0.4 orders below the threshold, so **L = 20 is the cheapest truncation that keeps one
  order.**

## 4. Re-pricing N = 65 (task 3)

### 4.1 Configuration (R2 parameters unchanged)

| item | value | evidence |
|---|---|---|
| parameters | `lunarR2 err disp`, unchanged | — |
| truncation | Lv = LE = LJ = 20, data scale S = 3.33·20 + 24 = 91 bits | `rot_emit.py` |
| backend | **CertFixed 96** | all sub-checks pass in `sofx_gen` at `SO_PREC=96` |
| cfgFull / cfgLow | cut-off 100000 / **160**, Taylor 30, halvings 12; packed budgets **1e-20** / 1e-8 | as SO-GEN3 except the full budget (err is 1e-16, not 1e-34) |
| graph SOS slack | 3e-4, as SO-GEN3 | 3e-5 was tried: the SOS residual grows (1.2e-4 → 3.9e-4), so the band does not narrow |
| certifier witness | `Sum.inr (Sum.inr wR)`, configuration d01b, kp = 3, ϑ = 1/8, J = 20 | §2 |

### 4.2 Sub-checks at L = 20 (`v2_sofx.sh 65 lower|upper 20 96`, `SO_DISP_COEF=420000`)

| check | lower | upper |
|---|---|---|
| checkStatic | true | true |
| checkHamBounds | true; max 2.1191 ≤ 2.16 | true |
| checkEmbedding | true; room 0.0062, DK rows 1.86478 | true |
| checkInvariance | true; rows 1.598e-16, 5.9e-17; err 1.6e-16 | true; 1.828e-16; err 1.83e-16 |
| checkEnergy | true; 6.0e-19 | true; 6.7e-19 |
| checkGram | true; β = 5.36043, margin 0.0113 | true; margin 0.0112 |
| checkTorsion | true; ‖S‖ = 0.50406, δ_T = 2.8e-5, margin 0.0097 | true |
| checkSoGraph | true; disp 6.72e-11 < 9.67e-7 | true |
| sharpTest (v1) | false, as expected | false |

(The sofx run sizes disp at 4.2e5·err, a little above the exact minimum of §2.3. Neither the band nor any check is
sensitive to that.)

### 4.3 Products and shards (blockRows 32)

| | lower | upper | SO-GEN3 (L = 40) |
|---|---:|---:|---:|
| packed products | 129 | 129 | 129 |
| shards | **667** | **718** | 1230 / 1229 |
| block grid per product | 2×2 … 4×4 | 2×2 … 4×4 | up to 8×8 |
| block pairs per shard | ≤ 4 | ≤ 4 | ≤ 8 |
| slot width w (max) | **208 bits** | 208 | 337 |
| nonzero advice | 47,830 | 48,785 | 61,767 / 62,960 |

### 4.4 Kernel time and memory per torus (projection)

The SO-GEN3 model, rescaled by SO-PACKFIX: a blockRows-32 shard of 12 block pairs at w ≈ 659 bits costs ≈ 45 s of
kernel and 4.6 GB. Cost is taken linear in pairs, and between linear and quadratic in width.

| component | basis | time | peak per declaration |
|---|---|---:|---:|
| packed shards, landed sub-checks | 667–718 shards × (4/12)·(208/659)^{1…2}·45 s = 1.5–4.7 s | **0.3–0.9 CPU-h** | ≲ 1.5 GB |
| `checkFrameMajorants` (refined branch) | re-runs `gramCheck` twice, the `[4,0]` product and `torsionModels`: about 90 % of the packed shards again, unless DATA3 shares those product proofs | **+0.3–0.8 CPU-h** | ≲ 1.5 GB |
| `checkHamBounds` + `checkHamClaim` | SO-BALLDY: 91 s and 8.98 GB for the ball pass; the program does not depend on L; `checkHamClaim` runs the same `Slp.balls` | 2 × 91 s | **≈ 9.0 GB** |
| five certified bites | SHARP2-C6: l = 8, 9, 10, 11, 12 cost 2.4 + 6.1 + 10.8 + 34.3 + 85.2 s | ≈ 140 s | unmeasured alone; the six-bite R1 module peaked at 10.4 GB |
| `wfOk`, `okB`, `classicalOk`, `finalOkA` | SHARP2-C6 | < 1 s | small |
| **total** | | **≈ 0.7–1.8 CPU-h per torus, ≈ 1.4–3.6 for both** | max ≈ 9 GB |

Against SO-GEN3's 3–5 CPU-h per torus (6–10 for both), and with term data about 5× smaller for `Slp.compose`, v2 is
about 3–5× cheaper.

Not in either model: the per-declaration data baseline (literal elaboration). It was 190 s per shard at R1, with
8.5k-term factors at 659 bits; the R2-v2 factors are about 500 terms at 208 bits.

**Under the 10 GB cap.**
- Every packed shard is far under the cap.
- The Ham passes are at about 9.0 GB, as for v1, and must stay separate declarations.
- The open item is the **l = 12 bite (δ₁)**: its memory alone was never measured. DATA3's first probe should be
  `siteOk` at δ₁ in its own module.
- If it exceeds 10 GB, fall back to **d0b**: certify δ₀ (l = 11) and b₀–b₂ only. The threshold is then 10^−15.55, the
  largest bite drops to l = 11 (34 s), and err/e\* at L = 20 becomes 10^−0.26. That is short of the one-order rule, so
  d0b needs **L = 21** (err ≈ 2e-17, ≈ 280 half-terms).
- C6's other lever, a rounded `balBound`, would also cut the bite memory (a Lean change in the side campaign's file).
- The all-certified kp = 3 configuration needs an l = 13 bite (≈ 210 s, probably above 10 GB) and gains only 0.2
  orders. It is not recommended.

### 4.5 The certified band δ

| torus | pLo | pHi | disp | band |
|---|---:|---:|---:|---|
| lower ν₋ | 0.9724531 | 0.9935293 | 5.65e-11 | [0.9724531, 0.9935293] |
| upper ν₊ | 1.0064780 | 1.0275440 | 6.47e-11 | [1.0064780, 1.0275440] |

- **Certified band max\|p − 1\| = 2.755 %**, the same as SO-GEN3. It depends on the torus positions and the graph SOS
  slack, not on the certifier.
- The numerical extremes are 2.713 %. The 0.04-point gap is the SOS lower bound's slack plus residual (4.2e-4 on pLo).
  Reducing the slack alone does not help: at 3e-5 the residual rose to 3.9e-4 with 325 terms. A higher-degree SOS
  witness is the lever. It is pure data work and independent of v2.
- Confined window: (0.9935293, 1.0064780).

### 4.6 R3 (re-optimising ρ or σ): not recommended

d01b threshold against the L = 20 err (lower torus). σK and σB are bumped 1–2 % for the larger strips; the frame
claims were re-measured.

| ρ | log₁₀ e\* | err at L = 20 (emit e) | err / e\* |
|---|---:|---:|---:|
| 1/280 | −15.34 | 1.8e-16 | 10^−0.9 |
| **1/140 (R2)** | **−14.26** | 3.2e-16 | **10^−1.2** |
| 1/100 | −13.81 | 5.3e-16 | 10^−1.9 |
| 1/70 | −13.48 | (≈ 8e-16) | ≈ 10^−2.4 |

- A wider strip gains 0.7–1.1 orders, about one digit of L (20 → 19), which is about 10 % of the terms.
- It would need a new parameter package, re-enclosed majorants, new frozen-adjacent Lean pre-checks and new boxes.
- The binding constraint at all-certified sites is the torsion-inverse budget (J3 sT). Raising σT does not relax it,
  because the rate grows with sT².
- **No substantial gain, so stay at R2.**

## 5. N = 80 and N = 100 (task 4, sketch)

Packages keep R2's c, ρ, ρ∞, μ, ν, s, σω, M and σT. They take γ = κ/(N+2), σK = ‖DK‖ + μ and σB = ‖G⁻¹‖ (ℓ¹) + μ from
the SO-GEN3 emit logs (L = 32 and 26 models):
- N = 80: σK = 2.283, σB = 12.07;
- N = 100: σK = 2.881, σB = 40.56.

Frame claims are from `v2_frame.py` on the archived double tori; Ham claims are scaled from N = 65. `v2_sketch.py`;
lower tori.

| N | numerical band | v1 sharp | v2 frozen | **v2 refined (d01b)** | disp coeff. | L for one order | v half-terms | cost vs N = 65 (∝ terms² × width) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 65 | 2.713 % | −31.83 | −27.87 | **−14.26** | 10^5.58 | 20 | 251 | 1 |
| 80 | 2.652 % | −35.97 | −32.06 | **−16.10** | 10^6.39 | 22 (checker err ≈ 4e-18, est.) | 367 | ≈ 2.3× |
| 100 | 2.630 % | −41.75 | −37.86 | **−19.15** | 10^7.63 | 26 (≈ 3e-21, est.) | 658 | ≈ 8–9× |

Refined claims: N = 80: bL 2.20, bN 3.35, bNt 3.41, bT 22.9; N = 100: bL 2.74, bN 6.06, bNt 6.19, bT 75.2. At N ≥ 80
the binding constraint is J3 sT, so d01b equals all-certified.

**Reading.**
- Under v2, **N = 80 costs about 2–4 CPU-h per torus**, comparable to v1's N = 65.
- N = 100 costs about 6–15 CPU-h per torus.
- The data are now easy. L = 22 or 26 is far above the 256 × 64 alias floors (1e-37, 1e-29), so the stalled
  512 × 128 stage is no longer needed.
- Certified bands with today's SOS slack would be ≈ 2.69 % (N = 80) and ≈ 2.67 % (N = 100), against 2.755 % at
  N = 65. The floor is 2.62 %.
- **Risks not priced:**
  1. At N = 100 the crude `mono` bound may fail. SO-GEN3's certified mono at N = 65 was 0.135 against a true minimum
     of 0.450 (crude, no SOS). The true minima are 0.303 (N = 80) and 0.168 (N = 100), so an SOS mono witness
     (`SO_MONO_SLACK`) may be needed.
  2. checkGram and checkTorsion at σB = 12 and 40 have not been run at the v2 truncation.
  3. Each N needs its own Diophantine lemma (as SO-DION did for 65) and a parameter file.
- This is a pricing, not a switch: N = 65 stays the target.

## 6. Lean glue (task 5)

No landed declaration changes. Two small new files, about 150 lines in all, with no heartbeat concerns: everything
is term-mode composition of landed lemmas.

**`KAM/SpinOrbit/Graph/CertV2.lean`** (≈ 40 lines):
```lean
theorem checkStatic_of_checkTorusCertificateV2 {E : EngineV2} {c : TorusCertificate 2 α} {w : E.Wit}
    (hc : checkTorusCertificateV2 E c w = true) : checkStatic c = true
-- simp only [checkTorusCertificateV2, checkV2With, landedBase, Bool.and_eq_true] at hc; exact hc.1.1.1.1.1.1.1

theorem soRotBarrier_of_certV2 [LawfulCertArith α] (E : EngineV2) (g : SoGraphCert α) {w : E.Wit} {c : ℚ}
    (hc0 : 0 < c) (hham : g.base.ham = soRotHamExprScaled c)
    (hc : checkTorusCertificateV2 E g.base w = true) (hg : checkSoGraph g = true)
    {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  soRotBarrier_of_certified g hc0 hham (checkStatic_of_checkTorusCertificateV2 hc) hg
    (checkTorusCertificateV2_sound E hc hω hdio) hdio
```

**`KAM/SpinOrbit/LunarAssemblyV2.lean`** (≈ 110 lines):
- `lunar_barriers_of_v2Gen`: the statement of `lunar_barriers_of_sharpGen` with `(E : EngineV2) (wL wU : E.Wit)` and
  `hcL : checkTorusCertificateV2 E gL.base wL = true` (and `hcU`) in place of the sharp hypotheses. The proof is the
  same three lines, with `soRotBarrier_of_certV2`.
- `SoBackendV2 := CertFixed 96`.
- `lunar_barriers_of_R2V2`: the statement of `lunar_barriers_of_R2` over `SoGraphCert SoBackendV2`, with
  `(wL wU : routeAV2.Wit)` and `hcL : checkTorusCertificateV2 routeAV2 gL.base wL = true`. It is discharged by
  `lunar_barriers_of_v2Gen` with the same R2 Diophantine facts (`lunarRotFreq{Minus,Plus}N_isDiophantine_65`), and
  the same `lunarR2` parameters and boxes.
- A sharding helper for the data modules (definitional, ≈ 10 lines):
  ```lean
  theorem checkTorusCertificateV2_refined_of {c : TorusCertificate 2 α} {w : RefinedWit}
      (hb : landedBase.check c = true) (hH : checkHamClaim c w.R = true)
      (hF : checkFrameMajorants c (w.R.frame c.freqBox) = true)
      (hcore : refinedCore 2 c.params c.freqBox w = true) :
      checkTorusCertificateV2 routeAV2 c (Sum.inr (Sum.inr w)) = true
  ```
  `refinedCore_of` and `sitesOk_of` (landed) split `hcore` further, one declaration per bite.

**Alternatives considered.**
- A lemma deriving `checkTorusCertificateSharp gX.base = true` from a v2 pass is impossible: the sharp test is
  strictly stronger.
- Re-proving the sharp assembly with `CertifiedTorus` as the hypothesis would be a different statement shape. The
  route above reuses `soRotBarrier_of_certified`, which already takes `CertifiedTorus`, so it is the cheapest.
- If DATA3 keeps `CertFixed 160`, use `SoBackendR2` in place of `SoBackendV2`. Precision 96 is enough (§4.2) and
  smaller.

## 7. Recommendation for SO-DATA3

1. **Certifier:**
   - `checkTorusCertificateV2 routeAV2` with the witness `Sum.inr (Sum.inr wR)` (`routeARefined`).
   - kp = 3, ϑ = 1/8, J = 20.
   - Certified bites at δ₀ (l ≈ 11), δ₁ (l ≈ 12), b₀ (8), b₁ (9), b₂ (10); classical at δ₂ and the tail.
   - Tight caps (`v2_pkg65.py` gives a passing witness; re-derive the bites with the balanced checker).
2. **Parameters:** `lunarR2 err disp` unchanged, with err 1.6e-16 / 1.83e-16 and disp 5.65e-11 / 6.47e-11 (from the
   exact minimum, rounded up).
3. **Truncation and precision:** L = 20 (Lv = LE = LJ), S = 91 bits, backend CertFixed 96. Cut-offs 100000 / 160,
   packed budgets 1e-20 / 1e-8, graph SOS slack 3e-4.
4. **Refined claim** (both tori): dh 2.099, dx 2.020, d2x 1.512, d2h 2.141, bL 1.830, bN 2.253, bNt 2.291, bT 10.393.
   These are sampled values × 1.01. If `checkFrameMajorants` rejects one, the threshold is insensitive at the percent
   level, so raise it.
5. **Expected cost:**
   - ≈ 667 / 718 packed shards plus about 90 % again for the frame majorants (unless shared);
   - two Ham passes (91 s, 9 GB each) and five bites (≈ 140 s);
   - **≈ 0.7–1.8 CPU-h per torus**, every declaration ≲ 9 GB except the unmeasured l = 12 bite.
6. **First probes:**
   - (a) `siteOk` at δ₁ alone (memory);
   - (b) `checkFrameMajorants` on the lower torus (its real cost and whether the claim passes);
   - (c) one middle `[4,1]` shard at w = 208.
7. **Lean:** the glue of §6 (≈ 150 lines, two files).

## 8. Owner questions (each with a recommended answer)

1. **Switch the lunar certificate to the v2 refined route at L = 20, CertFixed 96?** Recommended: **yes**. The R2
   parameters, the band and the Diophantine lemmas are unchanged. The cost falls about 3–5×, and the landed sharp
   route remains available as `Sum.inl ()`.
2. **If the l = 12 bite does not fit under 10 GB, accept configuration d0b at L = 21?** Recommended: **yes**. Its
   threshold is 10^−15.55 and its largest bite l = 11, for about 10 % more terms.
3. **Move to N = 80 now that it is affordable?** Recommended: **no, not for DATA3**. It gains ≈ 0.06 points of band
   (≈ 2.69 % against 2.755 % certified), at ≈ 2.3× the cost, with a new package, a new Diophantine lemma and unrun
   Gram/torsion checks at σB = 12. Revisit after N = 65 lands, together with a better SOS graph witness, which gains
   about as much (2.755 → ≈ 2.72 %) at no certifier cost.

## 9. Errata and deviations

- **Pinned sources:** no suspected erratum.
- **In-repo observations (not errata):**
  - SO-GEN3's kernel projection omits the per-declaration data baseline (SO-PACKFIX: 190 s per R1 shard), and so does
    the one above.
  - `scripts/certifier/v2_adapter.py` defaults to a non-existent path (`/home/scott/KAM-dev-worktrees/sharp-plus`).
  - `SHARP-CERTIFIER-FOR-SO.md` suggests 16–18 digits; at R2 the answer is 20, because R2's ρ = 1/140 halves δ₀
    relative to R1 and the threshold scales as δ₀⁴.
- **Deviations:**
  - `sofx_gen.py` gained three opt-in environment overrides (`SO_DISP_COEF`, `SO_GRAPH_SLACK`, `SO_MONO_SLACK`). The
    defaults are byte-identical in behaviour.
  - The certified site constants are float estimates, not `biteOk` runs.
  - The frame claims are sampled, not enclosed (`checkFrameMajorants` was not mirrored).

## 10. Reproduction

All commands run from `scripts/spin_orbit`. `v2_r2.py`, `v2_sketch.py` and `v2_pkg65.py` need `mpmath`, so they run
without `-I`.

- `python3 -I v2_crosscheck.py`: the mirror against the C6 kernel tests (seconds).
- `python3 v2_r2.py --json OUT`: §2 table (≈ 10 min).
- `python3 v2_sketch.py OUT`: §2 site configurations and §5 (≈ 25 min).
- `python3 v2_pkg65.py OUT [errL errU]`: §2.3 witness and exact check.
- `SO_N=65 python3 -I v2_frame.py <kam-data>/so-gen3/g3/N65_lower_v256.npy lower [rho]`: frame claims.
- `./v2_emit_scan.sh 65 lower 20 [rho]`: re-emit at L. Then `./v2_sofx.sh 65 lower 20 96 TAG [disp_coef] [slack]`:
  the landed sub-checks (7 min).
- Data:
  - small, in `docs/tracks/SO/studies/so-v2pkg-data/`: thresholds and sketch JSON, the witness, the L = 20 sofx
    reports and logs, the emit logs, the ϑ/kp scan;
  - large, in `/mnt/HC_Volume_106379410/kam-data/so-v2pkg/`: emitted tori at L = 14–26 for N = 65, 80, 100, and the
    sofx outputs (advice and certificate JSON). sha256 in `so-v2pkg.sha256`.
