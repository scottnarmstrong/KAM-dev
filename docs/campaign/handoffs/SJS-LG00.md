# SJS-LG00 handoff: scouting a certificate for LG00's secular Sun–Jupiter–Saturn torus

Brief: `/home/scott/kam-tools/briefs/SJS-LG00.md` (Opus). Branch `sjs-lg00`, from `sharp-v2` at 3e1a4872. LOCAL-COMMON
applies.

This is a scouting study: Python, documents, and two throwaway kernel probes in `.drafts/` (deleted). No Lean file was
added or edited and nothing was built. No SO-owned path was touched: `scripts/spin_orbit/adv_jet.py` and the
`scripts/apost_sharp` mirrors were imported read-only. The paper (`/home/scott/kam-tools/papers/lg00-sjs-cmda/`) was
read only: its text layer, plus one page rendered to PNG in the session scratchpad.

## Answer

**Feasible now**, with the landed sharp certifier (`checkTorusCertificateSharp_sound`, isoenergetic
`KAM.Iso.Sharp.g1_sharp`).

| Theorem (iso) | Threshold | L | S | CPU-h per torus |
|---|---:|---:|---:|---:|
| Sealed (landed certifier) | 10⁻¹³² | 142 | 3.8·10⁴ | 74–1 600 |
| **Sharp (CertificateSharp)** | 10⁻³¹ | **36** | **2.5·10³** | **7–150 with D34; 54–71 on today's code** |
| Route A (proved, not wired) | 10⁻¹⁴ (10⁻¹²·² frequency-specific) | 16–18 | 550–680 | 3–75 |

For comparison, the lunar certificate has L = 88 and S0 = 8.4·10³ and costs about 15 CPU-h of kernel time per torus.

New work needed, none of it a theorem:
- **P1:** a Python generator, 1.5–2.5k lines.
- **P2:** a Lean Diophantine lemma for LG00's noble ratio (Legendre plus convergents), 0.4–0.8k lines.
- **Either** a Taylor model of √(I₁I₂), with no Lean change but a weaker statement (a polynomial within 10⁻²² of
  (11)), **or P3**, a `sqrt` node with a witness, 0.8–1.5k lines on an SO-owned path.

**Honest claim:** to our knowledge, the first formally verified KAM torus of a planetary model. It would be a formal
reproduction of the KAM part of LG00's rigorous 2000 result, not new mathematics.

**Beyond LG00:** tori of the same model at 2–3× LG00's eccentricities converge and fit the sharp theorem (L = 48–54,
S = 1.2–1.7·10⁴, about 30–50 CPU-h). They would plausibly be new results about the model; that was not established.

The package plan is §5 of the document.

## Files (new)

- `docs/explorations/sjs-lg00-scout.md`: the deliverable.
- `scripts/sjs/lg00/lg00_data.py`:
  - eq. (11), 69 monomials, exact decimal strings;
  - Tables 2–4, (12), ω′ and ω″, (51), (52), and the Theorem 2 numbers.
- `scripts/sjs/lg00/lg00_model.py`: evaluation, canonical conventions, normal modes, RK4 plus frequency analysis, and
  the checks against (52), (12), ω′, ω″ and Table 4.
- `scripts/sjs/lg00/lg00_torus.py`: the action–angle form (15), the Γ′ frequency, and the Newton solve
  (parameterization method) of the torus.
- `scripts/sjs/lg00/lg00_amplitude.py`: tori at 1–3× the eccentricities.
- `scripts/sjs/lg00/lg00_oracle.py`:
  - norms in the certificate's chart (sampled sups and the M majorant);
  - the theorem mirrors (sealed, sharp, route-A Lean mirror; fixed and iso);
  - truncation digits and support;
  - the parameter search.
- `scripts/sjs/lg00/lg00_cost.py`: the `HamExpr` (Taylor or √), jet counts through `adv_jet.py`, support geometry, and
  the cost model with the probe calibration.
- `scripts/sjs/lg00/results/`:
  - `lg00_model.{json,log}`;
  - `lg00_torus_N128.npz`, `lg00_torus_f{2,3}.npz`;
  - `lg00_amplitude.{json,log}`;
  - `lg00_thresholds.{json,log}`, `lg00_thresholds_f{2,3}.{json,log}`;
  - `lg00_cost.{json,log}`;
  - `lg00_probes_raw.jsonl`.
- `docs/campaign/handoffs/SJS-LG00.md`: this handoff.

## Checks run and their output

- `python3 -I scripts/sjs/lg00/lg00_model.py`:
  - **Energy.** H(Table 3) = −1.69867157646253·10⁻⁷, inside (52), at 4.9·10⁻¹⁶ from its centre.
  - **Frequencies.** −1.456175688·10⁻⁴ and −2.585681076·10⁻⁴ rad/yr, against (12)'s −1.456175704·10⁻⁴ and
    −2.585681181·10⁻⁴ (relative −1.1·10⁻⁸, −4.1·10⁻⁸; RK4 drift 2.7·10⁻⁷).
  - **ω′ and ω″** within 1.1·10⁻⁸ / 4.2·10⁻⁸ and 1.1·10⁻⁸ / 3.9·10⁻⁸.
  - **Linear actions** 6.476·10⁻⁴, 3.337·10⁻⁴, against Table 4's 6.576·10⁻⁴, 3.210·10⁻⁴ (after Birkhoff).
- `python3 -I scripts/sjs/lg00/lg00_torus.py 128`:
  - 68 cosine terms in (15);
  - Newton: |E| 5.7·10⁻⁶ → 2.2·10⁻⁷ → 7.5·10⁻¹¹ → 3.5·10⁻¹⁷ → 8.1·10⁻¹⁹ rad/yr;
  - I₀ = (6.4009·10⁻⁴, 3.3227·10⁻⁴), energy −1.698671576460707·10⁻⁷ (inside (52)).
- **Continued fraction of r** (mpmath, 80 digits): Γ′ = [0; 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4, 1, 4, 2,
  1, 1, 1, …], det +1. inf (|k₁| + |k₂|)|k₁r + k₂| = 0.2251 over convergents and intermediate fractions up to
  q = 6·10¹¹. Γ″ gives 0.0718 (det −1).
- **`lg00_oracle.py`** (360-point grid plus coordinate refinement; about 15 min):
  - **Sealed:** iso −132.2 (L 142, S 3.78·10⁴), fixed −150.0.
  - **Sharp:** iso −31.1 (L 36, S 2.46·10³), fixed −32.1.
  - **Route A:** iso −13.9 (L 18, S 680), fixed −13.3, frequency-specific −12.2 / −11.8.
  - **Binding conditions** (route A): tail decay with classical constants, the σ_T cap with frequency-specific ones.
- **`--torus …f2/f3 --which v1,Aiso`:**
  - f = 2: sharp −41.8 (L 48, S 1.17·10⁴), route A −18.2 (L 23, S 2.84·10³);
  - f = 3: sharp −48.1 (L 54, S 1.73·10⁴), route A −21.5 (L 26, S 4.31·10³).
- **`lg00_cost.py`:**
  - Jet counts (shared √, Taylor K = 19): invariance + energy 1 402 model ops and 146 model×model products; torsion
    stage 3 067 and 302; whole program 8 538 slots, 800 model×model products.
  - With a √ node (K = 1 proxy): 74 and 190 products.
  - The cost table of §4.
- **Kernel probes** (`kernel_probe_gen.py`/`kernel_probe_run.py` from SJS-FEAS, one niced process, deleted after):
  - landed `checkShard`, K = 27 2-D box (S = 3 025), 160 bits, `blockRows` 4: **14.1 s kernel, 4.96 GB**, exit 0;
  - prototype `Fshard` at the same size: 5.77 s, 4.16 GB.
- **`sh scripts/lint_sources.sh`:** exit 1. Nothing comes from this branch, which adds no Lean file:
  - 26 Lean lines over 100 characters in `KAM/Sharp2/{Data,ModConstantsData,ModConstantsMono,…}.lean`
    (pre-existing);
  - `KAM.lean` over 1500 lines (known, SHARP2-B9 item 2);
  - `check_lean_modules: PASS (1526 Lean files, 0 comparator configurations)`;
  - `FROZEN-ANCHOR GUARD OK`;
  - the ABI step failed on the missing frozen olean `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean`
    (the known worktree failure).

  The worktree already had `.lake/packages`, so nothing was fetched.
- **`#print axioms`:** not applicable; no Lean declaration was added. The probes used no heartbeat or recursion
  overrides.

## Uncertainties

- **Thresholds are Python mirrors**, not linked mechanically to Lean. The route-A mirror was transcribed by hand
  (SHARP2-B9), and the frequency-specific constant is a floating-point value.
- **Sharp-regime norms.** σ_K, σ_B and the frame sups are sampled on the distinguished boundary (× 1.01), which is
  what CertificateSharp's corner and grid bounds reach. M is a term-wise majorant with the exact √ factors.
- **Double-precision torus.** Digits beyond 13 are extrapolated: e(L) log-linear, S(L) from per-direction decay
  rates (agreeing with the counts within 4 % at L = 13).
- **Search scope.** Identity angle frame only. The grid optima may move by a few digits.
- **Operation counts** come from the mirror on my `HamExpr`; a better expression lowers them. The char-witness count
  (24 checks × 2 products) is my reading of `Compose.charResolve` and `expWitnessRadiusOf`.
- **Cost.**
  - The demanded-work model prices the lunar torus about 20× below its measured cost (SJS-FEAS), hence the ×1–20
    ranges.
  - The D34 fix is not in this worktree; its figures rest on SJS-FEAS's prototype and SO-PACKFIX's lunar shard.
  - Probes are single runs at load about 12.
- **Not computed:** the T″ torus (Γ″; about 2 orders of threshold lower by γ⁴), and the multiprecision torus.
- **The f = 2–3 tori** have no Diophantine data yet; the same γ_dir = 0.225 was assumed.

## Suspected errata and deviations

**Pinned sources: no suspected misprint in LG00.** The energy check would show an error beyond about the 13th digit
of any coefficient. Observations, not errata:
- the canonical pairing of (ξ, η) is not stated in the paper (it follows from (2));
- LG00's γ = 8·10⁻⁶ is conservative (0.031 |ω₂| against 0.225 |ω₂| on Γ′);
- Table 4 includes the Birkhoff step.

**Our own material (please record):**
- **The "129 monomials"** in the brief and in `docs/explorations/sjs-feasibility.md` §7 (SJS-FEAS, from its literature
  subagent) is the index range of (11). The printed polynomial has **69** monomials, all even in η. I did not edit
  the SJS-FEAS document (additive rule).
- **The brief calls `KAM.Apost` "the sealed v1 theorem".** In SHARP-CERTSIDE and SJS-FEAS that theorem is "v0", and
  "v1" is the sharp one. The document says "sealed", "sharp" and "route A" to avoid the clash.

**Deviations:**
- I used `KAM.Iso.Apost` (iso) as the sealed theorem the landed certifier checks, and listed `KAM.Apost` (fixed)
  beside it.
- I rendered page 24 of the paper to PNG (`pdftoppm`) in my scratchpad, to read the monomials. That is reading, not
  execution.
- The probes reused SJS-FEAS's generator and runner unchanged. The worktree's `.drafts/` did not exist, so I created
  it (it is gitignored).
