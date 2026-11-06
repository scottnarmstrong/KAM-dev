# SJSU gate 2, phase 1: the SR gates (T2-CONF, D74)

6 November 2026, branch `inp-sjsu-g2`. Program T2-CONF, phase 1: gates SR-1 to SR-7 of
[sjs-rigor-plan.md](sjs-rigor-plan.md) §4, run before any Lean. Code and receipts are in
[`scripts/sjsu/rigor/`](../../scripts/sjsu/rigor/). Nothing is frozen and no repository Lean was written.

**Labels.**
- **measured:** a receipt in `scripts/sjsu/rigor/results/`.
- **rigorous:** arb ball arithmetic (python-flint 0.9.0), every truncation and tail bounded.
- **estimate:** a law or judgement, with its method stated.

## Verdicts

| Gate | Verdict | Result | Receipt |
|---|---|---|---|
| SR-1 EXACT-MODEL | **PASS for the complex form; FAIL for the real form** | The real form is not exactly rotation-invariant; owner decision below | `sr1.json` |
| SR-2 RATIONAL-ROTATION | **PASS** | V′ exact orthogonal (87-bit denominator), \|V′ − V\| = 1.2·10⁻¹³; T_full(10⁻⁶) = 2.75·10¹² yr; face margin ≥ 0.577δ | `vprime.json`, `sr-vp-L8.log` |
| SR-3 ALIAS | **PASS** | In-band majorants move 2.9–4.8 % of η_j from a 128² to a 256² grid | `sr3-*.log` |
| SR-4 BALL-MIRROR | **PASS** | Rigorous η = (6.7, 3.1, 7.4)·10⁻²⁰, **T = 6.7·10¹² yr** (674× over 10¹⁰); face margin 0.577δ | `sr4-*.json`, `sr4-full.log` |
| SR-5 OPCOUNT | **PASS** | 36,298 products + 2,540 truncations; 0.23–0.35 CPU-h by the law, about 1–1.5 CPU-h at SR-6's rate; ledger 0.09–1.35 GB | `sr5.json` |
| SR-6 KSHARD | **PASS with whitened literals** | ≤ 0.15 s and ≤ 1 GB per product declaration; raw packed chunks cost 6.4 s per declaration (low-limb collisions) | `sr6.json` |
| SR-7 Q-RADIUS | **PASS** | r_max = 3.36·10⁻⁶ (sup norm in (ξ, η)) | `sr7.json` |

**Decisions the gates take.**
- **SR-4: Taylor degree and width.** L_v = 8 and δ = 10⁻⁶ (κ = 2) are confirmed.
  - The degree > 8 parts are at most 1.6·10⁻²¹ (dropped products) and 1.8·10⁻²¹ (H tails).
  - The binding term is the degree-7 Birkhoff remainder of the LB = 6 observables, 6·10⁻²⁰.
  - No Cauchy tail is needed: the binomial tails of ∂H̃ are explicit.
- **SR-5 and SR-6: precision and cost.**
  - p = 64 bits per coefficient adds 10 % to η, so p = 80 with a 16-bit guard.
  - The kernel cost is about 1–2 CPU-h. This is far below the plan's 2.5–250 (central 4–6), because the products are 2-D slot pairs of about 1.3 Mbit.
  - Literals must be XOR-whitened.

Total phase-1 compute: about 1.3 CPU-h (estimate from the unit and `time` records), within the 3 CPU-h budget.

## SR-1 EXACT-MODEL (`sr1_exact_model.py`, 17 s)

**The real form (38,466 terms) fails.** The plan names it as the model of record (§1.1, §3.1).
- Read exactly, its complex image has **30,032 charged monomials**, and {C, H} has 34,952 nonzero terms.
- Cause: each real coefficient was rounded to 25 digits independently, which breaks the linear relations that encode rotation invariance.
- Size: the charged coefficients are about 3·10⁻²⁶ relative (e.g. 4.5·10⁻¹³ against 1.4·10¹³ at degree 18). Their majorant at the nominal radii is 2.0·10⁻³⁴, against 1.1·10⁻⁷ for H.
- Census, reversibility (no term odd in η) and the parse of z* pass.

**The published complex form (7,941 terms) passes every identity exactly:**
- charge 0 on every term;
- real coefficients with c_ab = c_ba;
- {C, H} ≡ 0;
- H(z*) = −5.22983516352663049817339571061·10⁻⁸, against −5.22983516352663049817339496888·10⁻⁸ from the real form (difference 7·10⁻³³).

**Owner decision (sent to kam-38).** Make the complex form the frozen `SJSU18-O2` data definition:
H(ξ, η) = Σ c_ab z^a z̄^b with z = (ξ − iη)/√2. It is real-valued, and since the degree is even it has rational
real coefficients. It is also 5× less frozen data.

The alternative is to keep the real form and carry its charged part (≤ 2·10⁻³⁴) as a bounded perturbation. That
loses the φ-reduction for that part and costs more Lean.

## SR-2 RATIONAL-ROTATION (`sr2_rational_rotation.py`, `sr2_rerun.sh`)

**Construction.** V′ = R(q)·D:
- R(q) is the rotation of the integer quaternion q = (−339719194785, 5086734484916, 8572864664712,
  −718132710016). It is the Cayley transform of the skew matrix of (q₁, q₂, q₃)/q₀, with entries integer/N and
  N = 100000000000001529127486481 (87 bits).
- D = diag(1, 1, −1) keeps det V′ = det V = −1.
- V′ᵀV′ = I exactly; \|V′ − V\|max = 1.16·10⁻¹³; the off-diagonal of V′ᵀAV′ is 1.2·10⁻¹⁷.

**Rerun (producer with `SJSU_VPRIME`):**
- T_full(10⁻⁶) = 2.754·10¹² yr in V′ against 2.706·10¹² with the float V (receipt 2.707·10¹²);
- face margins (0.6454, 0.5768, 0.8131)δ, identical to the float V.

## SR-3 ALIAS (`sr3_alias.sh`)

The same V′ producer was run at Lv = 8 on G2 = 128 and G2 = 256. The 256 grid is twice the 128 grid's
Nyquist, which covers twice the largest product mode, 2 × 55.
- **In-band majorants (|k|₁ ≤ 80):** (7.30, 3.57, 7.93)·10⁻²⁰ → (6.75, 3.04, 7.40)·10⁻²⁰. The change is
  5.4·10⁻²¹, i.e. 2.9–4.8 % of η_j.
- **Full-grid η:** grows 2.8× (1.5·10⁻¹⁹ → 4.2·10⁻¹⁹). This is float64 rounding noise spread over 4× more
  modes, not aliasing; SR-4 has no such floor.
- **Tails at Lv = 8:** dropped ≤ 7.5·10⁻²², H tails ≤ 1.5·10⁻²¹. This is the first sign that Lv = 8 suffices.

## SR-4 BALL-MIRROR (`ballft.py`, `sr4_ball_mirror.py`; 10.4 CPU-min, peak 2.6 GB)

**Setting.**
- **Model of record:** the complex form (SR-1), mapped exactly to modal coordinates by V′: `fmpq_mpoly`
  composition, 7,941 terms in 714 groups n, all charge-0 and reversible (checked).
- **Literal producer data** (run `sr-vp-L8`), read as exact dyadics:
  - S: 816 modes in the hexagon of order 60;
  - Ī = I* + c₀;
  - F_j: 165 u-monomials × 1,951 modes.
- **Exact parity:** F_j is replaced by its even part and S by its odd part. The producer's F has a genuine
  odd-in-φ part of about 10⁻¹⁷ (measured in weighted norm), not rounding noise. Under the reversibility
  R: φ ↦ −φ, F_e = (F + F∘R)/2 is a valid literal observable with sup|{F_e, H}| ≤ sup|{F, H}|.
- **Tube:** centred on B₀ (τ̃ = 0, since the stage-2 torus is within 4.4·10⁻¹³ of B₀), with
  |u_j| ≤ r = κδ = 2·10⁻⁶.

**Method (rigorous).**
- **Fourier models:** real trigonometric polynomials with arb coefficients and exact parity, plus a remainder
  ball in the W-norm Σ|f_k|(1 + h(k)), h the hexagonal norm. The W-norm is a Banach algebra norm and bounds
  ∂_φ in ℓ¹.
- **Products:** Kronecker-packed arb_poly products, truncated to h ≤ 60, with the dropped modes added to the
  ball.
- **Powers B₀^{s/2}:**
  - witnesses W ≈ √B₀ and Y ≈ 1/√B₀, after one arb Newton step;
  - a contraction proof of ‖√B₀ − W‖_W ≤ ρ (ρ ≤ 5·10⁻¹⁹) and a Neumann bound for 1/√B₀ (≤ 5·10⁻¹⁴);
  - all other powers by products.
- **Taylor coefficients h_m of H̃(u, φ) = H(B₀ + u, q), |m| ≤ 9:** nested Horner over (n₃, n₂, n₁),
  13,614 products.
- **Brackets:** {F_j, H̃} = −Σ_a [∂_{φa}F·D_aH̃ − D_aF·∂_{φa}H̃], with D_a = ∂_{u_a} − ∂_{u_3}. These are
  exact series products of degree ≤ 8 (22,564 products). Slot pairs whose weighted bound is below 10⁻²⁸ are
  bounded instead of multiplied (≈ 4,400 per j, total 6·10⁻²⁶).
- **Remainders:** dropped products of degree > 8 by degree profiles. Binomial tails of ∂H̃ beyond degree 8 use
  sup|T_n| and a rigorous [B_min, B_max] (grid plus a Lipschitz margin; the B₀ evaluation is in float with an
  explicit slack).

**Sanity.** H̃ at z* is −5.2298351635266285·10⁻⁸, against the exact −5.22983516352663·10⁻⁸ (SR-1).

**Results, δ = 10⁻⁶** (`sr4-sr-vp-L8-Lv8-d1e-06.json`; a first run with a weaker witness Newton order gave the same η to three digits):

| j | η_j | truncated series | Fourier balls | dropped | H tails | T = (δ/2)/η_j | face margin |
|---|---:|---:|---:|---:|---:|---:|---:|
| J | 6.71·10⁻²⁰ | 6.49·10⁻²⁰ | 1.8·10⁻²⁴ | 1.2·10⁻²¹ | 1.0·10⁻²¹ | 7.4·10¹² yr | 0.6454δ |
| S | 3.06·10⁻²⁰ | 2.78·10⁻²⁰ | 2.0·10⁻²⁴ | 1.6·10⁻²¹ | 1.2·10⁻²¹ | 1.6·10¹³ yr | 0.5768δ |
| U | 7.42·10⁻²⁰ | 7.15·10⁻²⁰ | 2.8·10⁻²⁴ | 0.9·10⁻²¹ | 1.8·10⁻²¹ | 6.7·10¹² yr | 0.8131δ |

- **Truncated series by u-degree (U):** 3·10⁻²¹, 2·10⁻²³, …, then 1·10⁻²³ at degree 6, **6·10⁻²⁰ at degree 7**,
  5·10⁻²¹ at degree 8. The degree-7 term is the observables' Birkhoff remainder (LB = 6). The L10/LB8
  observables would remove it, at a cost of 286 instead of 165 u-slots.
- **Regularity:** min B₀ − r = (2.87·10⁻⁴, 6.47·10⁻⁴, 2.29·10⁻⁵) > 0.
- **Fixed-point emulation:** a checker with p fractional bits per model adds about 0.04–0.06·2⁻ᵖ to η_j, so
  p = 64 adds 10 %.

**PASS:** T ≥ 10¹⁰ yr for every j (factor 674; 1,350 over 5 Gyr) and face margin ≥ 0.3δ.

**(e) Eccentricities on the tube** (float grid of 2048² with progressive 8× refinement and explicit Lipschitz
margins; the max is exact at the vertices of the √I box, by convexity; the min uses a support-function bound of
the zonotope):

| Planet | e range on the tube (this report) | Gate report (27-point vertex sampling) |
|---|---|---|
| Jupiter | [0.02668, 0.06112] | [0.02692, 0.06101] |
| Saturn | **[0.00932, 0.08454]** | [0.01058, 0.08439] |
| Uranus | **[0.00658, 0.06206]** | [0.00708, 0.06201] |

**Finding.** The gate report's tube ranges sample only 27 points of the action box and miss its edges. The
plan's example statement intervals [0.010, 0.085] (S) and [0.007, 0.063] (U) are therefore **false for the
tube**. Two ways forward:
- use [0.026, 0.062], [0.009, 0.085], [0.006, 0.063];
- or enclose over D ⊂ tube, where |u_j| ≤ δ + sup|E_j| ≈ 1.4δ instead of 2δ, which is tighter.

This is a phase-2 statement choice. The float evaluation in (e) is not enclosed; the Lean enclosure is N6.

## SR-5 OPCOUNT (`sr5_opcount.py`)

SR-4's straight-line program, priced with sjs-plan's laws (`sjs-plan.md` §3.1–3.2) at p = 80:
- **Program:** 36,298 2-D products (powers 120, H̃ build 13,614, brackets 22,564) and 2,540 truncations.
- **Operands:** ≤ 1.46 Mbit (cell width 173 bits, box ≤ 61², stride 1.5).
- **Kernel multiplication:** 0.23 (κ = 2) to 0.35 (κ = 3) CPU-h.
- **SR-6 correction:** at the measured ≤ 0.15 s per product declaration (decoding included), the 36k products
  take about **1–1.5 CPU-h** in one declaration each, or less if products are summed inside a truncation
  declaration.
- **Ledger:**
  - 0.09 GB for one literal per truncation (elaboration 0.2–0.3 CPU-h);
  - 1.35 GB for one per product (2.7–3.9 CPU-h).
- **Peak:** about 0.45 GB per declaration by the law; ≤ 1 GB measured (SR-6).
- **Inputs:** H_z 0.66 Mbit; S, F and witnesses about 3 Mbit.
- **H_w = H_z∘V′ in the kernel (estimate):** by symmetric powers, C′_d = S_d(V′)ᵀ C_d S_d(V′) for d ≤ 9, with
  matrices up to 55 × 55. That is 6.8·10⁵ exact rational multiply-adds with entries up to about 1,650 bits:
  one-off and cheap. A list-based composition would cost 10⁴ CPU-h or more.

**PASS:** kernel ≤ 50 CPU-h, ledger ≤ 5 GB and declarations ≤ 8 GB, each by 1–2 orders of magnitude. The plan's
central 4–6 CPU-h assumed about 150 full Fourier–Taylor products of 165 × 2,791 coefficients. Here the same work
is 2-D slot-pair products of about 1.3 Mbit, and the bracket stage skips about 13k negligible pairs.

## SR-6 KSHARD (`sr6_kshard.py`; standalone `lean`, v4.35.0, core `Nat` only, no options; kam-38 approved)

**Setup.**
- **Product:** one real-size slot-pair product. A = ∂_{φ₁} of the u_U slot of F_U (support 25, 1,900 modes)
  times B = √B₀,U (support 30, 2,791 modes).
- **Packing:** p = 80, cell 173 bits, stride 121. Signed parts are split into four nonnegative literals, so the
  check is 4 `Nat.mul`s.
- **Operands:** 1.26 Mbit; product 2.9 Mbit.
- **Literals:** balanced `Nat.add`/`Nat.shiftLeft` trees of 288-bit chunks in sub-definitions of ≤ 256 chunks.
  The first attempt used `+`/`<<<` notation over 5,000-leaf trees and hit `maximum recursion depth` in the
  elaborator. That was a design signal, fixed by explicit applications, not by options.

| File (wall, peak) | Real chunks | Low 64 bits randomized |
|---|---:|---:|
| Data only | 16.4 s, 0.86 GB | 5.9 s, 0.86 GB |
| + product (4 mul, 2 checks) | 18.1 s, 0.87 GB | 5.9 s, 0.88 GB |
| + mask bounds (`>>>`, `&&&`) | 22.3 s, 0.97 GB | 7.0 s, 0.98 GB |
| 40 product declarations | 274 s (**6.4 s each**) | 9.6 s (**0.093 s each**) |
| 40 decode-only declarations | | 11.8 s (0.15 s each) |

**Reading.**
- With randomized low limbs, a declaration that re-decodes the six literals and checks a product costs
  0.09–0.15 s. The multiplication is not separable from decoding at this size, and is consistent with the law's
  0.02–0.03 s.
- The peak (≤ 1 GB) is within 0.45 GB + 10F + 1 GB = 1.45 GB.
- **With the real chunks it is 70× slower.** The packed cells carry zero headroom bits, so many 288-bit chunks
  share their low 64 bits: 11,632 distinct low limbs in the real data against 17,833 randomized. This is the
  SO-3 hazard (`lean-kernel-nat-literal-hash.md`).

**Verdict: PASS, conditional on XOR-whitened literals** (the natRamp mask) in the phase-2 generator.

## SR-7 Q-RADIUS (`sr7_qradius.py`)

**Method.** A mean-value bound on the sup-norm ball about z*. The chain z → w = V′ᵀz → (I, q) → (u, φ) uses
derivative bounds of F over the whole tube and exact z*:
- c_j = F_j(z*) to 30 digits: −1.706352954445792·10⁻¹⁶, −5.611114287436537·10⁻¹⁴, 5.628196475003494·10⁻¹⁴;
- u(z*) is at most 2·10⁻¹⁹.

**Result.** **r_max = 3.36·10⁻⁶**, bound by Saturn's |F − c| ≤ δ/2, with Lipschitz constants
(0.106, 0.149, 0.024). The tube condition |u| ≤ 2δ is far from binding (≤ 4.4·10⁻⁷).

**PASS** (≥ 10⁻⁶). A statement Q of radius r = 3·10⁻⁶ or 10⁻⁶ is available. The bound sums float
upper bounds of arb quantities without directed rounding; its margins are wide.

## Phase-2 inputs fixed by phase 1

1. **Model of record:** the complex form (owner decision pending; SR-1).
2. **Chart:** V′ = R(q)·D as in SR-2, with an 87-bit denominator.
3. **Observables:** Lv = 8, δ = 10⁻⁶, κ = 2, tube centred on B₀.
   - Literal data: even F_j (165 slots, K = 50), odd S (816 modes, K = 60), Ī, W and Y witnesses (KH = 60).
   - Optional: the L10/LB8 observables for 2× on η.
4. **Checker:** 2-D slot-pair packed products at p = 80, cell ≤ 173 bits, ≤ 1.5 Mbit operands.
   - W-norm balls for the Fourier truncations, binomial sup tails for u-degree > 8, degree profiles for the
     dropped products.
   - H_w by symmetric-power matrices.
   - Whitened literals.
5. **Statement constants (to settle):** r ∈ {10⁻⁶, 3·10⁻⁶}, T = 5·10⁹ yr, and eccentricity intervals that
   contain the tube ranges above (not the plan's examples).

## Errata, deviations, uncertainties

- **Erratum candidate (non-pinned doc).** `sjsu-near-torus-gate.md` §5's "range on the tube" is a 27-point
  sample, not a range. The true lower ends are 0.0093 (S) and 0.0066 (U). The plan's §1.1 example intervals
  inherit the error.
- **Plan inconsistency.**
  - §1.1/§3.1 name the real form as the model of record, while SR-1 is phrased on the 7,941 complex terms.
    The real form fails the exact identities (SR-1).
  - The plan's κδ-tube eccentricity intervals: see above.
- **Producer observation.** The float F has a genuine odd part (about 10⁻¹⁷). Its origin (the frequency-free
  Kolmogorov steps or the recentring) was not investigated; the even part is used.
- **Deviations.**
  - `scripts/sjsu/gate2/common.py` gains an opt-in `SJSU_VPRIME` switch; the default behaviour is unchanged.
  - SR-4 ran twice. The first run used a weaker witness Newton order (ρ_inv ≤ 1.1·10⁻¹¹, Fourier balls
    1·10⁻²³); the receipt is the final code's run.
- **Process.**
  - One `pkill -f` during development matched my own shell and the quick test it was running; no other process
    was affected. Later kills were by PID only.
  - My status messages to kam-38 at "13:52", "14:12" and "14:58" UTC carried estimated rather than clock times.
- **Uncertainties.**
  - SR-6 resolves product cost only to about 0.05 s.
  - SR-5's κ and per-declaration overheads follow the 2-D design measured here; packed Fourier–Taylor products
    with whole Taylor slots per literal are not measured.
  - The eccentricity and B₀-range enclosures use float evaluation with explicit margins, not interval
    arithmetic.

## Reproduce

python-flint goes in a venv on the HC volume. Run from the repository root, one heavy job at a time, each
under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 nice -n 10`.

```sh
python3 -m venv --system-site-packages $VENV && $VENV/bin/pip install python-flint==0.9.0
R=scripts/sjsu/rigor
python3 $R/sr1_exact_model.py                       # SR-1, 17 s
python3 $R/sr2_rational_rotation.py && sh $R/sr2_rerun.sh   # SR-2 (+ SR-3 baseline), ~5 CPU-min
sh $R/sr3_alias.sh                                  # SR-3, ~7 CPU-min, 3.8 GB at G2 = 256
(cd $R && $VENV/bin/python sr4_ball_mirror.py)      # SR-4, ~10 CPU-min, 2.6 GB
python3 $R/sr5_opcount.py --tag sr4-sr-vp-L8-Lv8-d1e-06      # SR-5
python3 $R/sr6_kshard.py --p 80 --out <scratch>; lean <scratch>/Ksh_*.lean   # SR-6, under MemoryMax=4G
(cd $R && $VENV/bin/python sr7_qradius.py)          # SR-7, ~1 min
```
