# A costed plan to certify a KAM torus of the Sun–Jupiter–Saturn system (SJS-PLAN)

30 October 2026, branch `sjs-plan`. Planning study with small experiments: Python, documents, tiny kernel probes. Nothing here is
a theorem or a certificate. Every number comes from `scripts/sjs/plan/` (section 9) or a cited receipt. Each is labelled
**measured**, **model** or **estimate**.

## Executive summary

**The big target is feasible with a modest budget, and the route is not the one the feasibility study expected.** One torus of
FH25's planar SJS system costs about **15–300 CPU-h** of kernel time and a **few hundred GB of ledger**. A rented 48-core machine
checks it in **1–20 hours**, for **under USD 200 of compute**. The cost is Lean work, not hardware: about **8–15k Lean lines**.

Three things changed against SJS-FEAS:

1. **The chart is the largest lever, and SJS-FEAS had no such row.** I computed FH25's torus and tested a chart built from polar
   coordinates in the secular normal modes, with synodic angles. Measured on the torus (majorants sampled, not enclosed):
   - **on a Delaunay polydisc the box contains e = 0, so the landed ball arithmetic cannot work there at all;** in the new chart it stays clear;
   - c_DXh falls from 129 to 1.75, and c_D²Xh from 5·10¹⁰ to 1.65·10³;
   - the threshold, in FH's units, rises from 10⁻⁴⁶·³ to **10⁻³⁸·⁰**;
   - the support falls by 2.7×, and the Kronecker box ratio from 4.4–5.7 to 2.5–2.6.
2. **The hybrid restart is not a kernel lever for SJS.** It halves the digits of K, as hoped (A = 2–5 measured, so K needs L ≈ 25),
   but the composition must still reach the final accuracy (L ≈ 45). The "hybrid + packed: 6–19 CPU-h" row of SJS-FEAS is wrong.
   The hybrid helps the numerics by a factor of 2–3 and costs the kernel up to 1.4×. **Do not make it a dependency.**
3. **A kernel limit nobody had met decides the block design.** The kernel refuses any `Nat` above 2²⁷ bytes (1.07 Gbit) unless
   `LEAN_NAT_MAX_SIZE` is set. Under the default limit a model has to be cut into 21–60 blocks. That is a ruling for the owner.

**What was checked.** The Python torus reproduces FH25: |⟨T⟩⁻¹| = 354.077 (FH: 354.07743), ⟨Ĝ⟩ = 2.176574188839 (FH:
2.176574188839), c_Xh = 0.089 (0.09), c_DXh = 134 (129), residual 1.7·10⁻⁹ at 128²×144 (FH: 5.3·10⁻¹⁰ at 128³). The threshold wrapper
reproduces SJS-FEAS's −48.5. The per-coefficient cost constants price the real lunar torus at 2.5 CPU-h against the measured 1.6–2.5,
which also closes SJS-FEAS's 11–22× calibration gap.

**The main uncertainty.** S(L) is measured up to L ≈ 10 and used at L ≈ 45: a factor 3 in cost. That extrapolation, and the size of
the packed layer's soundness proof, are the two things that could move this plan. Section 7 lists the gates that test them first.

### Decisions for the owner

| # | Decision | Recommendation | Why | If declined |
|---|---|---|---|---|
| 1 | What to build | The **packed big-integer layer** (one `Nat` per block of a model) with soundness proofs, 6–10k Lean lines | Today's checker costs 7·10⁴–5·10⁵ CPU-h and 5·10⁶–10⁷ theorems. Packed is about 10⁴× cheaper | The target stays out of reach |
| 2 | Chart | The **synodic regular chart**, with a new trusted checker node for the regular Kepler equation, 1–2k lines (as D45 did for `sqrt`) | Delaunay's polydisc contains e = 0. The chart is also worth 8 orders of threshold and 5–11× in F (operand bits) | Delaunay needs a tube-following domain for ball arithmetic (not designed), a Kepler node anyway, and 140–190 GB per product |
| 3 | `LEAN_NAT_MAX_SIZE` | **Allow it**, with the value stated in the replay instructions. Fallback: block-level Karatsuba under the default limit | It is a resource limit, not a trust matter, but it is an environment override a replayer must also set. It saves at least 7× | 200–7000 CPU-h, or about 60–1200 with Karatsuba plus one more proof |
| 4 | Hardware for the final run | **Rent** one 48-core machine with 256–768 GB and 1–2 TB of NVMe for a few days | lemma.farm has only **43 GB of free disk**; the ledger is 80–560 GB | Attach a 1 TB volume to lemma.farm; then 7–240 h wall with shards under 8 GB |
| 5 | Frequency and claim | An explicit cubic frequency within 10⁻⁸ of FH's ω: certified γ = 2.8·10⁻⁷, τ = 2 | Secular relative error 3·10⁻⁴, well inside what a planar model of the real system can mean | Stay closer to FH's ω: about 1 order of γ per decade of tolerance, 3.6 orders of threshold already spent |
| 6 | Theorem form | Route B, isoenergetic: the form the v2 certifier checks. **No new theorem work is required** | Route B beats route A′ by 8 orders here. Iso and fixed agree to 0.03 orders | — |
| 7 | Sequence | LG00 now, then the packed gate, then planar SJS. **Make secular SJSU optional** | LG00 is nearly ready. SJSU needs a model nobody printed, and it does not de-risk the Kepler chart | SJSU adds 2–3 weeks; a reduced-mass planar rehearsal is cheaper |
| 8 | Repositories | A separate repository for certificate data. The ledger stays out of git; publish hashes and a replay script | 80–560 GB of `.olean` literals. KAM-dev's default build never sees them | — |

**Timeline (estimate, ×2 either way):** LG00 in days; the packed gate in 1–2 days; Lean layer, Kepler node and statement in 2–3 weeks
in parallel; data and run in about a week. **Roughly 4–6 weeks to the headline theorem.**

**Risks, in order:**
1. S(L) at L ≈ 45 (factor 3).
2. The soundness proof of the packed layer, which is the largest new Lean (6–10k lines).
3. Whether ball arithmetic reaches the sampled majorants of the Kepler chart. Each ×10 costs 3 orders; ×20 is affordable.
4. Whether the kernel's memory law holds for many blocks in one declaration.

**The claim we could make:** a formally verified KAM torus of the planar three-body problem with the real Sun–Jupiter–Saturn masses
and eccentricities, at a frequency within 10⁻⁸ of the ephemeris. FH25 list their computer-assisted proof as "(In progress)" (ref. [19]). If it has not
appeared, this would be new mathematics, not only a formalization. I did not check the current literature; that must be done before anything is claimed.

## 1. Theorem side (brief item 1)

### 1.1 The torus and its chart

`sjs_torus.py` follows FH25 §3: translated tori by continuation from μ = 0, then invariant-torus refinement, in double precision.
Continuation on 96³ takes 11 minutes (1.9 GB), and refinement on 128²×144 takes 3 minutes (4.4 GB). A first attempt failed near
μ = 6.5·10⁻⁴: an aliasing instability at a mode next to the spectral cut, cured by the 2/3 rule. (Not physics.)

**FH's torus sits close to a chart singularity.** On it e₁ ranges over 0.027–0.065 and **e₂ over 0.012–0.093**. Delaunay's chart is singular at
e = 0, and the landed checker bounds H on a polydisc. Here that polydisc has radii (6.9, 7.8, 23.5)·10⁻⁴ in (L₁, L₂, Ĝ), while P_i = L_i − G_i are
2.7·10⁻³ and 1.8·10⁻³ at its centre with reach 3.0·10⁻³ and 3.1·10⁻³: **the box contains e₁ = 0 and e₂ = 0, so `ballSqrt` must fail on √(1 − G²/L²).** Delaunay
would need a domain that follows the tube, which the checker does not have. Polar coordinates in the secular normal modes do not have this problem:
- w = Qᵀz, where z_i = √(2P_i) e^{ip_i} are Poincaré's variables and Q is a rotation (φ = −1.0908, chosen to minimize the variation
  of a mode's action on the torus);
- w_j = √(2I_j) e^{iψ_j}, and on the torus I₅ and I₆ vary by only 27 % and 13 %.

**The synodic chart.** Eliminating Λ₂ gives canonical unimodular coordinates:

  (b₁, b₂, b₃) = (λ₁ − λ₂, λ₂ + ψ₅, λ₂ + ψ₆),   (Λ₁, I₅, I₆),   Λ₂ = C + I₅ + I₆ − Λ₁.

The elimination matters. In (Λ₁, Λ₂, I₆) the fast oscillation of the Λ's makes the box reach I₅ = 0, and c_D²Xh stays at 2·10⁹. In
(Λ₁, I₅, I₆) the box has radius 2·10⁻⁴ around I₅ = 1.5·10⁻³ and the box value equals the tube value.

Majorants in FH's normalization (2π angles, max norm, row sums; **sampled, not enclosed**, 8 000 points):

| Chart | Domain | c_Xh | c_DXh | c_D²Xh |
|---|---|---:|---:|---:|
| FH25, published | their tube | 0.09 | 129 | 5·10¹⁰ |
| Delaunay, ρ = 0.1 | tube | 0.090 | 287 | 1.6·10⁷ |
| Delaunay, ρ = 0.1 | box | 0.19 | 5.5·10³ | 4.1·10⁹ |
| Normal-mode polar (Λ₁, Λ₂, I₆), ρ = 0.1 | tube / box | 0.088 / 0.10 | 9.8 / 4.7·10³ | 2.6·10⁴ / 2.3·10⁹ |
| **Synodic, ρ = 0.1** | tube / box | 0.050 / 0.050 | 3.5 / 2.0 | 3.2·10³ / **2.0·10³** |
| **Synodic, ρ = 0.02** | tube / box | 0.050 / 0.050 | 1.6 / 1.75 | 1.4·10³ / **1.65·10³** |

The torus is also flatter there: the largest angle coefficient falls from 0.17–0.31 to 0.03–0.07, and action deviations from
8.6·10⁻⁴ (Ĝ) to 4–5·10⁻⁵ (I₅, I₆).

SJS-FEAS §3 said that charts give no gain on S and a gain on M worth "at most about the same number of orders". Both claims fall: c_DXh, which it
did not vary, enters route B with several powers (3 orders per decade of all majorants, section 1.2). The S gain has no mechanism yet. Per-axis
rates barely move (slowest axis 0.39 → 0.35), so the gain is in the shape of the support, not its reach.

### 1.2 Thresholds

`sjs_plan_thresholds.py` runs the mirrors on the measured data, searching ρ, ℓ, c and μ. The majorants are the box samples × 2.
Stages: 2 frequency-specific, classical tail, τ = 2. **Raw** means log₁₀ of the invariance error in FH's units, T·2π/c: this is the
comparison that does not depend on c. (SJS-FEAS's numbers are raw, with c = 1.)

| Data | γ | Route B, raw | Route A′, raw | ρ |
|---|---|---:|---:|---:|
| FH's constants (SJS-FEAS, reproduced: −48.49) | numerical | −48.5 | −64.5 | 0.1 |
| Delaunay, measured, chart scales tuned (its box M is a sample only; see 1.1) | numerical / certified | −43.2 / −46.3 | −50.7 / −55.2 | 0.02 |
| **Synodic, measured** | numerical / certified | **−34.3 / −38.0** | −41.7 / −46.3 | 0.02 |
| Synodic, measured | numerical / certified | −31.2 / −34.8 | −37.0 / −41.6 | 0.1 |

- **Best point:** ρ = 0.02, ℓ = 0.1, c = 3000, μ = 10⁻⁴, where T = 10⁻³⁵·³ in the chart, T_raw = 10⁻³⁸·⁰, with |⟨T⟩⁻¹| = 14 in the chart.
  A wider search over c up to 3·10⁵ gained at most 0.3 orders. ρ between 0.02 and 0.05 is equivalent once S's strip weight is counted.
- **Isoenergetic form** (the form the v2 certifier checks, `extendedTorsionAverage`): −38.02 against −37.99. No loss.
- **What binds:** route B's tail decay, everywhere. The certified γ therefore costs 3.6 orders. SHARP-PLUS's remark (Γ_spec in the
  weight; an emulation in SJS-FEAS §2.2) might recover much of that; it is not needed.
- **Sensitivity to the enclosure.** Scaling every majorant together: raw −37.4, −38.0, −40.7, −43.9, −47.1 at ×1, 2, 20, 200, 2000. So about
  3 orders per decade. ×20 costs 2.7 digits, or about 20 % in S.
- **The ℓ¹ entry** was not re-evaluated. It gives 0.1 orders on route B on R1, and is not route B's binding term.

Measured data are at a point of the search grid, not a proved optimum. Route B here is the design mirror. On R1 it sits 0.26 orders
from the Lean-certified value (−12.33 against −12.59). The chart is new to it only through the numbers.

### 1.3 Digits, support, bits

**Digits.** A truncation at L digits leaves E_ang = amp(L)·10⁻ᴸ in FH's units, measured amp = 226, 561, 1180, 2220 at L = 5–8. amp is
a sum over the dropped shell, so it grows polynomially. Extrapolating as L³ to L^4.5 gives 4·10⁵–5·10⁶ at L = 45. So
L = −log₁₀ T_raw + 7, including 0.7 of headroom.

**Support** (`sjs_spectrum.py`, 128²×144, full lattice, each component relative to its largest coefficient, ρ = 0.02, **measured**):

| L | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Delaunay | 1 782 | 4 594 | 9 840 | 18 836 | 32 606 | 52 130 | 76 788 |
| Regular | 1 162 | 2 490 | 4 626 | 7 876 | 12 576 | 19 198 | 28 202 |
| Ratio | 1.5 | 1.8 | 2.1 | 2.4 | 2.6 | 2.7 | 2.7 |

**Extrapolation (model, the plan's largest uncertainty).** S^{1/3} is linear in L. The measured slope for the regular chart rises from 3.2 to
3.65 per digit, so I take 3.7 (low) and 5.3 (high, the cross-polytope of the measured per-axis rates, which is an upper envelope).
Delaunay: 5.6–6.1.

| | SJS-FEAS, route B | Plan (synodic, certified γ) |
|---|---:|---:|
| Residual, raw | 10⁻⁴⁶·⁵…⁻⁵²·¹ | **10⁻³⁸·⁰** |
| L, bits (3.33 L + 24) | 57–62, 212–231 | **45, 174** |
| S, full lattice | 7–9·10⁶ | **4.3·10⁶–1.3·10⁷** |
| Layout β = box / S | 10 | **2.5–2.6 measured; 3 used** |
| Box | 7–9·10⁷ | **1.3–3.8·10⁷** |
| Reversibility | ÷2 | **verified to 10⁻¹²** (angles odd, actions even), so one real product per model product |

**Corrections to SJS-FEAS's support.**
- **The d'Alembert factor 7–14 does not hold on the torus.** True support over FH's product model is 1/6.2, 1/4.5, 1/3.7 at L = 6, 8, 10,
  and falling. With Delaunay's data at L = 56 the model gives S ≈ 2.7·10⁷ on the full lattice, 3.7× SJS-FEAS's. The tilt along
  (1, −1, 1) is not visible on the torus: its frame (k₁, k₂, m − k₁) changes nothing, and the full frame (k₁ − m, k₂ + m, m) doubles the box.
- **β** comes from a robust search over unimodular frames with entries ≤ 2 (99.5 % per axis). The best frame for the regular chart is rows
  (−1, 0, 1), (−1, −1, 0), (−2, −1, 0), extents 17 × 33 × 57 at L = 8. Stragglers outside that box need a sparse overflow block.
- **Intermediate models** (`sjs_intermediates.py`, Delaunay frame): 0.3–2.2× the union support of K. Cartesian positions 1.3, ∂H/∂Ĝ 2.2,
  1/r 0.3. K's union is a fair unit. ×2 is the honest risk on single models.

### 1.4 The hybrid restart on SJS

`sjs_hybrid.py` measures one additive Newton step on truncations, in Delaunay's chart at ρ = 0.02, in FH's units:

| L | Kept terms | |E| | |Ẽ| | |E₁| direct | |ΔK| | A = |Ẽ|/|E|² |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 584 | 6.95·10⁻³ | 1.39·10⁻³ | 1.70·10⁻³ | 2.3·10⁻¹ | 29 |
| 5 | 1 948 | 2.26·10⁻³ | 2.40·10⁻⁵ | 2.44·10⁻⁵ | 1.6·10⁻² | 4.7 |
| 6 | 5 042 | 5.61·10⁻⁴ | 7.00·10⁻⁷ | 7.00·10⁻⁷ | 2.2·10⁻³ | 2.2 |
| 7 | 10 772 | 1.18·10⁻⁴ | 4.73·10⁻⁸ | 4.74·10⁻⁸ | 3.7·10⁻⁴ | 3.4 |
| 8 | 20 370 | 2.22·10⁻⁵ | 2.76·10⁻⁸ (floor) | 2.76·10⁻⁸ | 5.6·10⁻⁵ | floor |

The linearized error matches the true new error, and the step is quadratic. I expected the slow frequency to make A huge; **it does not**.
L = 3 diverges (a step of 3.9 radians), and L = 4 barely contracts.

So a candidate needs residual √(T_raw/A) ≈ **10⁻¹⁹·²**: L_cand ≈ 25, 107 bits, S_cand = 0.7–2·10⁶. That is the "halving".

**But a certificate must enclose E at the final accuracy.** Ẽ = E + DX_h ΔK − DΔK·ω is 10⁻³⁸ only by cancellation between terms of size
10⁻¹⁹, so E's model needs absolute accuracy 10⁻³⁸ whatever K's digits (design APOST-SHARP-V2-HYBRID §3.2–3.3 says this; SJS-FEAS missed it).
Every intermediate of the composition is at L ≈ 45 with S as in the table. The hybrid then adds ΔK's product with DX_h: about one
Jacobian-vector pass of 190–250 products at half width.

| Effect of the hybrid on SJS | Factor |
|---|---:|
| Kernel, composition | 1 |
| Kernel, the JVP | +40 % |
| Kernel, frames, Gram, torsion | already cheap (section 3.3) |
| K's own data | digits ÷2 |
| Numerics | ÷2–3 |

For SO the balance differs (frame products dominate there). For SJS it is optional.

## 2. Numerical torus (brief item 2)

**Answer: yes, lemma.farm can compute it within 32 GB,** in 1–2 days, given a data volume. FH25's 10⁻⁵⁴ at 1024³ is far more than needed.

| Step | Method | Accuracy | Cost |
|---|---|---|---|
| 0 | Double precision, this study's solver (`sjs_torus.py`) | 2·10⁻⁹ | 15 min, 4.4 GB (**measured**) |
| 1 | Same, in the adapted frame, on the reversible half | 10⁻¹³ | about 1 CPU-h, 10–15 GB (estimate) |
| 2–4 | Multiprecision Newton: 10⁻¹³ → 10⁻²⁵ → 10⁻³⁸…⁻⁴⁵ | L = 45 | 20–62 CPU-h per step (model) |

**Model.** FH25: one Newton step took about a week on 8 cores at 1024³ and 76 digits, so 1 344 CPU-h, scaled linearly in grid points (log N) and as
digits^1.6. The plan's FFT grid is 4–13·10⁷ points against 10⁹, because S is smaller and β is 3.

**Memory.** FH25: 194 GB for one complex grid. The plan: 2–7 GB per grid on the reversible half, so 10–30 GB in core plus 30–100 GB of disk.

**A better route, native packed Newton** (model). The certificate's own arithmetic, run outside the kernel with GMP, replaces mpfr FFTs:
18–51 CPU-h per step, bit-exact with the kernel, so the producer and the checker are the same code. One product peaks at 14–40 GB in a
`lean` process, which exceeds lemma.farm's 10 GB cap, so it needs blocks or a non-Lean binary (`gmpy2` or C). Neither is installed here.

**With the hybrid:** steps 2–3 run on the candidate's small support, a final step evaluates E at L = 45 and solves at low precision: ÷2–3.

**Which torus.** FH25's own, moved to an explicit cubic frequency (section 5.3). I found no reason to pick another: the conditioning trouble
was the chart's. ⟨T⟩ is invertible, and Newton from FH's torus reaches the nearby frequency.

## 3. Kernel side (brief item 3)

### 3.1 Calibration

**Today's checker: constants from the SO-CSPLIT gates (`OVERNIGHT.md` 21:37; SO-CSPLIT §4).**
- 4.6 ms per advice slot (the 484×498 product's shards: 42 s, 7 × 1 312 slots), 3 ms per target slot.
- 0.15 ms per backend call (0.3–0.6 calibrated, gates 2–4× below), 23 calls per term per live op (census).
- About 5 s per theorem.

**Check:** on the real L = 20 lunar torus (667 shards, 351 k target slots, 10.7 M calls, 470 theorems) these give **2.5 CPU-h, against the measured 1.6–2.5**.

**That closes SJS-FEAS's 11–22× gap.** Two things caused it: the prototype's per-slot constants were 3–5× optimistic, and the op count was far
too low (3 products and 140 ops, against 129 packed products and 616 live slots). That lesson is why this study counts ops from a program (3.3).

**Packed: experiments E1 and E2 (`results/packed_probes.jsonl`, load 20–30, ±30 %).** The prototype runs one full model cycle in `decide +kernel`,
with no advice and no per-digit step: signed Kronecker product, per-cell rounding by mask and shift, range check, central truncation,
bit-parallel absolute value, digit-sum norm, weighted norm by one middle product.

| Operand | Mbit | MB | mul | + round, range | + abs, shell norm | + weighted norm | Peak (with generator) |
|---|---:|---:|---:|---:|---:|---:|---:|
| 10⁴ digits | 4.6 | 0.6 | 0.02 s | 0.05 | 0.05 | 0.07 | 0.83 GB |
| 10⁵ | 46 | 5.8 | 0.37 | 0.63 | 0.72 | 1.04 | 0.94 |
| 3·10⁵ | 138 | 17 | 0.86 | 0.86 | 1.12 | 3.81 | 1.93 |
| 10⁶ | 460 | 58 | 6.6 | 7.6 | 12.9 | — | 4.47 |

The same data as a lunar-size product (4·10⁵ bits): under 0.06 s against 60 s today, about 10³×.

**Literal × literal, from `.olean`:** 60 MB × 60 MB: 3.7 s user, peak 1.06 GB; 115 MB × 115 MB: 8.3 s, 1.61 GB. Laws used:
- **8 ns per operand bit** for one `Nat.mul`;
- **peak ≈ 0.45 GB + 10·F** (F = operand GB), 16·F if a cycle is split over 2–3 declarations. The kernel caches every intermediate in a declaration,
  so 1 cycle in one declaration costs about 50·F (at 58 MB: +2.7 GB);
- cycle = κ × mul, κ = 2–3.

**Getting data in (E2, measured).** I did not test the numeral parser at this size and would expect it to be too slow. A standalone writer (`lean --run`, `Lean.addDecl`, `writeModule`)
turns raw bytes into a module importing only `Init`, with one definition whose body is one literal:
- **115 000 000 bytes become a 115 001 888-byte `.olean`:** no overhead; the literal is stored raw.
- Import is mapped: 0.7 s, 0.69 GB touching it.
- The writer took 70 s for 115 MB in the interpreter, which a compiled join should cut.

**Kernel limits found (measured, Lean 4.35):**

| Limit | Value | Behaviour |
|---|---|---|
| `Nat` size | **2²⁷ bytes** (1.07 Gbit) unless `LEAN_NAT_MAX_SIZE` (bytes) is raised | clean kernel error |
| `Nat.shiftLeft` exponent | **< 2³²** | **`INTERNAL PANIC`**: the process dies, no clean error. A checker must never reach it |
| `Nat.pow` exponent | ≤ 2²⁴ | rejected above |
| `Nat.shiftRight` | no limit met | fine |

So under the default limit a product's operands sum to at most 2³⁰ bits, about 67 MB each. With an override, a shift over 537 MB must be done in steps.

### 3.2 The packed design

A model is one real digit array (reversibility) on a box in the adapted frame, as signed digits in cells of width w = 2p + log₂S + 2 ≈ 372 bits (p = 174).
- **Layout:** stride 1.5× on two axes, so terms outside the central box land in gutters. No padding on the third axis, because the integer product does not wrap.
  **Operand F = 2.25·w·box** bits, product 2F. (SJS-FEAS's 3.375·w·β·S on a half lattice is 1.69·w·box: 25 % low.)
- **Dropped terms** are bounded analytically: every model carries a second anisotropic norm with weights e^{Σ r_i|k_i|}, r_i near the decay rates, so a term
  outside the box costs 10⁻ᴸ. Computing that norm is one middle product.
- **Blocks:** cut along the long axis. Sub-products are 0.75·nb². Each block can use its own width, since far blocks have small coefficients: an extra factor of up to 2, not counted.
- **Ledger:** the kernel's cache forces outputs into literals, one set per product. SJS-FEAS's "only K and witnesses, 3–4 GB" is wrong: the ledger is (N_full + 25) models of box·p bits.

### 3.3 Operation counts

`sjs_ops.py` writes the program for H in the synodic chart with regular Kepler variables (eccentric longitude F; k + ih = ε z̄; no polar coordinates), on a hash-consed symbolic ring. This
replaces SJS-FEAS's hand estimate of 60–150 products.

| Program | Model × model | Scalar × model | Adds | inv | sqrt | Characters | Kepler |
|---|---:|---:|---:|---:|---:|---:|---:|
| H only | 94 | 21 | 44 | 7 | 5 | 3 | 2 |
| **∇H, forward jets (the landed compiler's shape)** | **657** | 85 | 417 | 12 | 5 | 3 | 2 |
| **∇H, reverse mode** | **252** | | | | | | |
| Hessian, forward (torsion stage) | 4 974 | 298 | 4 826 | 12 | 5 | 3 | 2 |

- **Reverse mode** (or a hand-coded gradient) saves 2.6×, and needs its own soundness theorem, 1–2k lines.
- **The torsion stage is cheap despite its count.** ⟨T⟩⁻¹ and sup|T| need 3–6 digits, not 17: S_low ≈ 10⁴ terms, F ≈ 5 Mbit, 0.05–0.1 s per product, about 10 minutes.
  The landed certifiers' cfgLow is 17 digits; a smaller value needs checking against route B's budgets.
- A sharper hand-written program would lower these counts. They are not a proved minimum.

### 3.4 Cost per torus

Plan scenario (synodic, certified γ, L = 45, S = 4.3·10⁶–1.3·10⁷, box 1.3–3.8·10⁷, F = 1.3–4 GB). Ranges run from (low S, reverse, κ = 2) to (high S, forward, κ = 3). **Model** on measured
constants. Kernel only; the numerics of section 2 and the literal writer are extra.

| Checker | CPU-h per torus | Shard peak | Blocks per factor | Declarations | Outlook |
|---|---:|---:|---:|---:|---|
| **(a) Today's checker** (post CSPLIT) | **7·10⁴–5·10⁵** | 4 GB | — | 5·10⁶–1.4·10⁷ | not feasible; advice 1–3 TB |
| **(b) Packed**, one `Nat` per model, big memory | **14–143** | 22–64 GB | 1 | 252–657 | needs the override |
| (b) Packed, shards ≤ 8 GB | **29–950** | 7.6 GB | 3–9 | 300–7·10³ | needs the override |
| (b) Packed, default limit | **210–6 700** | 1.5 GB | 21–60 | 10⁴–3·10⁵ | no override; Karatsuba at block level would give about 60–1 200 (estimate) |
| **(c) Hybrid + packed** | (b) × 1–1.4 | as (b) | as (b) | as (b) | no kernel gain |

Ledger 78–562 GB.

**One shard.** At 8 GB: a block pair of 0.45 GB operands, 1–1.5 min, up to 6 pairs per declaration only where the caches allow. Under the default limit: 65 MB operands, 9–13 s, 1.5 GB.
One whole product takes 3–13 min with one `Nat`, 7–86 min at 8 GB shards, and 45 min to 9.5 h under the default limit.

For comparison, in the same model: Delaunay's chart needs F = 14–22 GB, 140–220 GB per product and 0.8–3 TB of ledger, if it could be bounded at all (1.1). Synodic at numerical γ is about 30 % below the rows above.

**Uncertainty, honestly:**

| Factor | Range | Basis |
|---|---:|---|
| S(45) | ×3 | extrapolated from L ≤ 10 |
| N_full | ×2.6 | counted; the choice is reverse or forward |
| κ, cycle | ×1.5 | measured to 460 Mbit |
| Largest intermediates | up to ×2, not in the table | measured in Delaunay's frame |
| Enclosure of M | 20 % in S per ×20 | sensitivity measured |
| GMP timings | ±30 % | single runs at load 20–30; log factor to F = 4 GB not measured |

The default-limit row is entirely inside the measured range of block sizes. The 8 GB row extrapolates 4× in F, and the one-`Nat` row 12–35×.

## 4. Hardware (brief item 4)

Wall clock for the plan scenario. Concurrency = min(cores, RAM/peak), and 6 for unblocked products (the program's DAG). Reverse-mode low end, forward-mode high end. Prices are
ballparks from aggregators and listings, to be re-checked: AWS r7i.24xlarge ≈ USD 6.35/h (96 vCPU, 768 GiB), x2iedn.24xlarge ≈ USD 20/h (3 TiB), Hetzner AX162-R from about €200–270/month (48 cores, 256 GB,
up to 1.15 TB optional).

| Option | Mode | Peak per process | Concurrent | Wall (low S … high S) | Compute cost |
|---|---|---:|---:|---:|---:|
| (a) lemma.farm, default limit | default | 1.5 GB | 8 | 26–99 h … 220–840 h | 0, **plus a data volume** |
| (a) lemma.farm, 8 GB shards | override | 7.6 GB | 4 | 7–27 h … 62–240 h | 0, **plus a data volume** |
| (b) 48 cores, 256 GB | 8 GB shards | 7.6 GB | 31 | 1–3.5 h … 8–31 h | one month, about €200–270 |
| (b) 48 cores, 768 GB | 8 GB shards | 7.6 GB | 48 | 0.6–2.3 h … 5–20 h | USD 4–130 |
| (b) 48 cores, 768 GB | one `Nat` | 22–64 GB | 6 | 2–8 h … 7–24 h | USD 14–150 |
| (c) Cluster, 1 000 cores | today's checker | 4 GB | 1 000 | 3–20 days | order of USD 10⁴–10⁵; 10⁷ theorems, not sensible |

**What each step needs:**
- **lemma.farm** is enough for: all Lean development, gates, LG00, data generation up to step 1, and FFT Newton steps (10–30 GB).
- **Disk is the blocker,** not memory: 43 GB free on `/`, against 80–560 GB. Even with deletion, the final module must import every `.olean`.
- **A rented machine** needs: 48 cores, ≥ 256 GB, ≥ 1 TB NVMe, for about a week. It buys the difference between hours and weeks for the final run. No step in the table needs more than about 64 GB per process.
- **A cluster buys nothing** on the packed route. It would only make sense for today's checker, and that is not sensible.
- **Memory is not the point of renting.** At 8 GB shards a big machine gains through core count, not RAM, which is why 256 GB and 768 GB barely differ.

## 5. De-risking experiments (brief item 5)

### 5.1 Run now

| # | Experiment | Cost | Result |
|---|---|---|---|
| E1 | Packed model cycle in the kernel, 4.6–460 Mbit | < 1 min per size | works; 8 ns/bit; κ = 2–3; memory law |
| E2 | Literals through `.olean`; kernel limits | minutes | no overhead; **`LEAN_NAT_MAX_SIZE`, `shiftLeft` panic** |
| E3 | Cubic frequency, certified γ | 4 min | section 5.3 |
| E4 | Coarse SJS torus | 15 min | **reproduces FH25** |
| E5 | Spectrum per chart, frames | 2 min | S ÷2.7, β 2.5 |
| E6 | Majorants per chart | 5 min | **7.5 orders on c_D²Xh** |
| E7 | Hybrid constant | 20 min | A = 2–5; composition unchanged |
| E8 | Operation count | seconds | 252 / 657, not 60–150 |
| E9 | Intermediates' support | 3 min | 0.3–2.2 × K |

**One probe went over budget:** `t_full` at 10⁶ digits peaked at **4.47 GB**, over the "~4 GB" limit of the brief. No process was killed and it was not repeated at that size.

### 5.2 Next, in order of uncertainty removed (each < 8 GB, < 1 CPU-h unless noted)

| # | Experiment | Removes |
|---|---|---|
| X1 | **Double-double torus to L ≈ 20–25** in the adapted frame on the reversible half, or a packed Newton from E4's torus (a few CPU-h) | **The ×3 on S**, the largest number in this plan |
| X2 | **The packed gate:** a real 3-D reversible product with blocks, central box, anisotropic tail and literal I/O, on E4's actual torus coefficients at S = 10⁵ | layout, β, sparse overflow |
| X3 | Ball-arithmetic mirror of the synodic H on the box | sampled against enclosed M, the Kepler node's bounds |
| X4 | Several block products accumulated in one declaration, with cgroup peak | memory law at many blocks |
| X5 | A minimal `lean` round trip: one model operation as two modules, literal in and literal out, with `lake` | module overhead per declaration |
| X6 | The route-B budgets at L_low = 3–6 for frames and torsion | whether the torsion stage is as cheap as 3.3 says |

### 5.3 The certified Diophantine constant (E3, `sjs_dioph.py`)

For a_j ∈ ℤ[x] with x a root of a monic cubic, and ω_j = a_j(x₀)/D: for k ≠ 0 the norm of k·a is a nonzero integer, so

  |k·ω| ≥ 1/(D m₁ m₂ |k|₁²),   m_i = max_j |a_j(x_i)|.

So ω is (γ, 2)-Diophantine with γ = 1/(D m₁ m₂). This is `CubicDiophantine.lean`'s argument, using the frequency's own conjugates: a transfer through a matrix norm would lose a further (size of the matrix)². A closest-vector
search in the Minkowski lattice gives the tradeoff. **γ ≈ (5–30) × the absolute tolerance on ω**, as the lattice heuristic predicts:

| |ω − ω_FH| ≤ | Best field | D | Certified γ, τ = 2 | Rel. error ω₁ | Rel. error ω₃ |
|---:|---|---:|---:|---:|---:|
| 10⁻⁶ | x³ − x − 1 | 6.3·10⁶ | 1.4·10⁻⁵ | 1.6·10⁻⁶ | 2.1·10⁻² |
| 10⁻⁷ | x³ + x − 1 | 4.5·10⁵ | 2.0·10⁻⁶ | 3.3·10⁻⁸ | 4.5·10⁻³ |
| **10⁻⁸** | **x³ − x − 1** | **5.6·10⁷** | **2.8·10⁻⁷** | **4.7·10⁻⁸** | **2.9·10⁻⁴** |
| 10⁻⁹ | x³ + x − 1 | 4.0·10⁸ | 1.5·10⁻⁸ | 5.1·10⁻⁹ | 3.3·10⁻⁵ |
| 10⁻¹⁰ | x³ − x − 1 | 1.0·10⁹ | 2.7·10⁻⁹ | 1.1·10⁻⁹ | 7.9·10⁻⁷ |

- For comparison: FH25 certify a non-explicit vector within 10⁻⁸⁰ with γ = 1.69·10⁻⁶, τ = 2.4; the numerical infimum for τ = 2 is 1.85·10⁻⁵, at k = (0, 0, 1). Each explicit vector has that numerical value too (checked for |k|₁ ≤ 400).
- **Recommended:** the 10⁻⁸ row. FH's ω₃ has 21 printed digits, but the secular frequency of a planar model is not meaningful to 3·10⁻⁴ anyway.
- **Lean:** a general lemma for a monic cubic and an integer matrix, 0.3–0.5k lines, on the pattern of `CubicDiophantine.lean`. Frequency-specific stage sums: about 9·10³ near-resonant fibres at δ = 2.65·10⁻³ and 2.3·10⁵ at δ = 5.3·10⁻⁴ (`S3`), plausible in the fibered form, not yet priced in the kernel.

## 6. Milestones and agents (brief item 6)

### 6.1 Sequence

| Milestone | Status | Size | Cost | What it proves | Owner |
|---|---|---|---:|---|---|
| **M0 LG00** | P1, P2 done on `lg00-prep`; `HamExpr.sqrt` landed (D45) | Wire to v2; run | L = 18–36; about 3–40 CPU-h on today's checker (scaled from the lunar gates, not measured) | First verified KAM torus of a planetary model; reproduces a 2000 result | Approve the run and repo |
| **M1 Packed layer** | E1, E2 here | 6–10k lines | — | Reusable: lock, lunar, all later tori | D34-level ruling on the layer; `LEAN_NAT_MAX_SIZE` |
| M2 Secular SJSU (optional) | Nothing exists; the model is not printed | Model generator 2–3k Python; 3-DOF data | Low: S ≤ 1.7·10⁵ | New rigorous result for a truncated model | Decide whether it is worth 2–3 weeks |
| M2′ Reduced-mass rehearsal | E4's solver covers it | Parameters | Hours | Pipeline test of the Kepler chart | Nothing |
| **M3 Planar SJS** | This plan | Sections below | 15–300 CPU-h | The big target | Statement, hardware, repo |

**Why SJSU drops to optional.** SJS-FEAS ranked it between LG00 and SJS because of cost. With the chart, SJS itself is reachable, while SJSU needs a generator for a model of 9.4·10⁷ intermediate monomials,
and it exercises neither Kepler nor the chart. A reduced-mass rehearsal tests more of the real pipeline, at no modelling cost.

### 6.2 Packages for M3

| Package | Content | Size | Runs after | Parallel with | Needs |
|---|---|---:|---|---|---|
| **X1** | Support to L ≈ 25 | Python | — | X2 | — |
| **X2 PK-GATE** | The packed gate (no proofs) | 300 lines | — | X1 | **Go/no-go** |
| A1 SJS-STATEMENT | H of FH25 (2.1)–(2.2) as a definition, the canonical chart, the theorem; independent audit; freeze | 0.5–1k | gate | B1, C1, D1 | **Owner approval, freeze** |
| B1 KEPLER-NODE | `HamExpr` node for the regular Kepler equation: eval, witness, ball, jet (cf. LOCK-SQRT) | 1–2k | gate | A1, C1, D1 | **Trusted extension ruling; SO-owned path** |
| B2 GRADIENT | Reverse or hand-written gradient with soundness | 1–2k | B1 | C2 | Optional: saves 2.6× |
| C1 PK-CORE | Digits, signed Kronecker identity, mask rounding, range, abs | 2–3k | gate | A1, B1, D1 | — |
| C2 PK-NORMS | Weighted and anisotropic norms, tail bound, blocks | 1.5–3k | C1 | B2 | — |
| C3 PK-BRIDGE | Packed models to the `Encloses` contract | 1–1.5k | C2 | — | — |
| C4 PK-ENGINE | Invariance, energy, witnesses, frames and torsion on packed models; `EngineV2` wiring | 1–2k | C3, B1 | — | — |
| D1 CUBIC-DIO | General cubic lemma, the chosen ω | 0.3–0.5k | gate | A1, B1, C1 | Decision 5 |
| E1 SJS-GEN | Torus, Newton, writer, plan, ledger | 2–3k Python | C1, B1 | — | Data volume |
| E2 REHEARSAL | M2′ through the whole pipeline | run | C4, E1 | — | — |
| E3 SJS-RUN | The certificate, in its own repo | run | E2 | — | **Hardware, budget** |

Total about 8–15k Lean lines (B2 optional) and 3k Python. Audits as on the v2 track. X1 and X2 are the only blockers: **if X2 fails** (stays more than 3× above the laws of 3.1), the fallback is a sparse-block per-coefficient route on a cluster, and the target becomes a funded project.

### 6.3 What is needed from the owner

1. Decisions 1–8 above.
2. Approval of the SJS statement before freezing (A1).
3. A trusted-extension ruling for the Kepler node, like D45.
4. A ruling on the packed layer's place: `KAM/Certificate` is SO-owned, so a new `KAM/Packed` is the natural home.
5. A separate repository and an off-git store for the ledger.
6. Budget: about USD 200–500 of compute, or €270 for one month, plus a 1–2 TB volume.

## 7. What could change this plan

| Gate | If it goes badly | Effect |
|---|---|---|
| X1: S(25) | slope stays near 5.3 | High-S column: rented machine, 5–20 h. Still feasible |
| X2: 3-D product | Sparse overflow costs more than β = 3 implies | ×2. Width-adaptive blocks recover some |
| X3: enclosure of M | > ×100 of the sample | ≥ 6 orders; L ≈ 51; ×1.6 in cost |
| Kernel at F > 1 GB | not measured above 920 Mbit | blocks, as in the 8 GB rows |
| Owner declines the override | default limit | Karatsuba at block level, or weeks on one machine |
| PK proofs | > 2× the estimate | calendar only |

## 8. Corrections, errata, observations

**Corrections to our own SJS-FEAS** (not edited, additive rule; the orchestrator may annotate it):

| Claim in SJS-FEAS | Finding here |
|---|---|
| Hybrid + packed: 6–19 CPU-h | Wrong: the composition stays at the final accuracy; no kernel gain |
| Charts: no gain on S | 2.7× measured; c_D²Xh 7.5 orders down; c_DXh, not varied there, 2 orders down |
| d'Alembert: S ÷7 on the torus | ÷3.7 at L = 10 and falling; about ÷1–1.3 by L = 56 in the model |
| Frame (k₁, k₂, m − k₁): box/S about 10, against 46 | No gain on the torus; a searched frame gives 4.4–5.7 (Delaunay), 2.5 (regular) |
| 60–150 full products | 252 (reverse), 657 (forward) |
| Memory 4–8× factor | 10× one product; 16× per cycle split; 50× if unsplit |
| Packed needs 3–4 GB of data | Ledger 80–560 GB: kernel caches force checkpoints |
| Factor bits 3.375·w·β·S | 2.25·w·box = 4.5·w·β·S_half |
| Unresolved 11–22× calibration gap | Closed (3.1) |

**Pinned sources:** no suspected erratum in FH25 §§3–5. Its printed Ĝ, torsion and vector-field constants were reproduced independently. Two remarks, neither an error:
- FH25's c_D²Xh = 5·10¹⁰ is far above its tube (7·10⁶–1.6·10⁷ sampled) and within about a decade of a sampled Delaunay box (2–4·10⁹). That box contains e = 0, so a sample there says little.
- Fig. 3's ρ_ĝ = 0.316 is a marginal of summed moduli; the envelope rate is 0.39–0.41.

**Toolchain:** `Nat.shiftLeft` with exponent ≥ 2³² ends the process with `INTERNAL PANIC` instead of a kernel error (Lean 4.35). Reported, not worked around in any tracked file.

**Deviation from the brief:** one probe at 4.47 GB (5.1). No SO-owned path, frozen file, GitHub or `kernel-tests/` build was touched.

**Scope.** Not done: any Lean module; any 3-D packed product; an enclosure of any majorant; any ball-arithmetic run on the chart; a literature check of the novelty claim.

## 9. Reproduction

From the worktree root, `python3 -I`, numpy and mpmath. `OUT` is any scratch directory. Torus files (30–100 MB) are not committed.

```
python3 -I scripts/sjs/plan/sjs_torus.py --grid 96 96 96 --steps 20 --newton 3 --refine 6 --save OUT/t96.npz        # 11 min, 1.9 GB
python3 -I scripts/sjs/plan/sjs_torus.py --grid 128 128 144 --load OUT/t96.npz --refine 5 --save OUT/t128.npz       # 3 min, 4.4 GB
python3 -I scripts/sjs/plan/sjs_spectrum.py OUT/t128.npz --json scripts/sjs/plan/results/spectrum128.json           # section 1.3
python3 -I scripts/sjs/plan/sjs_chart.py OUT/t96.npz                                                                # checks, majorants
python3 -I scripts/sjs/plan/sjs_plan_sens.py OUT/t96.npz --json scripts/sjs/plan/results/sens.json                  # 1.1, sensitivity
python3 -I scripts/sjs/plan/sjs_plan_thresholds.py OUT/t96.npz --quick --json scripts/sjs/plan/results/thresholds_quick.json   # 1.2
python3 -I scripts/sjs/plan/sjs_plan_thresholds.py OUT/t96.npz --charts syn --rhos 0.05,0.1,0.15,0.2 --ells 0.3,0.1,0.03 \
    --cs 3000,10000,30000,100000,300000 --mus 1e-4,1e-5 --json scripts/sjs/plan/results/thresholds_syn.json
python3 -I scripts/sjs/plan/sjs_plan_iso.py OUT/t96.npz syn 0.02 0.1 3000 1e-4                                      # iso form
python3 -I scripts/sjs/plan/sjs_hybrid.py OUT/t128.npz --json scripts/sjs/plan/results/hybrid_A.json                # 1.4
python3 -I scripts/sjs/plan/sjs_intermediates.py OUT/t128.npz --json scripts/sjs/plan/results/intermediates.json    # 1.3
python3 -I scripts/sjs/plan/sjs_ops.py --json scripts/sjs/plan/results/sjs_ops.json                                 # 3.3
python3 -I scripts/sjs/plan/sjs_dioph.py --json scripts/sjs/plan/results/sjs_dioph.json                             # 5.3
python3 -I scripts/sjs/plan/sjs_plan_cost.py --json scripts/sjs/plan/results/sjs_plan_cost.json                     # 2-4
python3 -I scripts/sjs/plan/packed_probe_run.py scripts/sjs/plan/results/packed_probes.jsonl --sizes 1e4 1e5 3e5     # E1, one process at a time
```

`sjs_torus_diag.py` is the diagnostic that located the aliasing instability. E2's probe files were transient; `literal_probe_gen.py` regenerates the producer form, and section 3.1 records the standalone writer's shape.
The mirrors in `scripts/apost_sharp/` and `scripts/certifier/` are imported read-only. `sjs_plan_thresholds.py` is slow (10–30 min) at load 20–30.
