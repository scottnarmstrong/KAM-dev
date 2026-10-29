# P11A-P7b prover handoff (branch inp-p11ap7b, 94d6bbcf; contains P7 round 1 (partial) and P11A-P5 (passed); offloaded package run by the main orchestrator)


Branch `inp-p11ap7b` (off inp + inp-p11ap7 + inp-p11ap5). All files build through the gate, no `sorry`, no
`axiom`, no heartbeat override, all lines <= 100 columns, every file < 350 lines.

## Files (new, all under `KAM/Planetary/Preparation/`)
| file | content |
|---|---|
| `SlowAverageZ.lean` | `p11eta1_pos`, `p11_gbar_data`; `p11_slow_polar` (polar_avg on `p11R4` with S=MF/16 and on `p11Gbar` with S=eta1); `p11_rho_cauchy`, `p11_partial_rho_jet` (cauchy_open in rho, then `p11PartialVec_norm_le`) |
| `SlowAverageOsc.lean` | `p11SlowJ/p11SlowR/p11PolPt/p11SlowSec`; polar point bound (`p11PolPt_norm_le`), exact `G∘Π = sec + R4∘Π + Gbar∘Π` (`p11_slow_G_polar`), `p11_gbar_osc`, `p11_gbar_avg_osc`, `p11_slow_osc_pointwise` (|(R4+gbar)(J,Π) - (AR+AB)(J,ρ)| <= c0 eps² + c1 eta1 √eps) |
| `SlowAverageKey.lean` | `p11_slow_key` (`C + ΣΩρ/2π + AR + AB = p11PolarAverage G` for Re ρ>0, via `polar_average_linear`/`_normalization`), `p11_slow_avg_real` (polar average of G real at real data) |
| `SlowAverageDom.lean` | holomorphy of `p11PolarC` on Re ρ>0, `p11_polarC_mem` (polar chart point lies in the fast domain, `‖Π‖<=4√eps`), `p11_polarC_real`, `p11_f1_periodic` (f1 1-periodic in θ from lattice clause + periodic F) |
| `SlowAverageF2.lean` | `p11SlowBox`, `P11SlowPolarOut`, definitions `p11SlowZ`, `p11SlowH0`, `p11SlowF2`; `p11_slow_f2_numeric`; `p11_slow_f2_sup` (sup |f2| <= C0 eps^{5/2} log^{2τ+1} on strip σ/6) |
| `SlowAverageW.lean` | holomorphy of `f2`, periodicity in all angles, `p11_slow_f2_wbound` (weighted bound via `KAM.summableWeighted_torusCoeffW`, width σ/12 from σ/6) |
| `SlowAverageJet.lean` | `p11_slow_rho_bound` (|∂ρ(AR+AB)| <= c(eps+eta1), radii πeps/4 and π rz²/64), `p11_slow_Z_jets` (J-jet clause, R = s1/4) |
| `SlowAverageReal.lean` | `p11_slow_secZ_eq`, reality of `h0` and `f2` |
| `SlowAverage.lean` | `P11SlowOscSpec`, `p11_slow_osc_at`, **`p11_slow_osc`** (the packaged output) |

## What P7c / P7d consume
```
theorem p11_slow_osc (hC : P11SecularSpec D C) :
  ∃ c eps2, 1 ≤ c ∧ 0 < eps2 ∧ ∀ eps, 0 < eps → eps ≤ eps2 → ∀ Fast, P11FastSpec C eps Fast →
    ∃ Z h0 f2, P11SlowOscSpec C Fast eps c Z h0 f2
```
`P11SlowOscSpec` (all on the box `p11SlowBox C eps = D(J0, s1/4) × D(2π eps, π eps)`, strip width `s = σ/12`):
fast identity `h0 + f2 = p11WorkingH C eps (Fast.map (p11PolarC z))` (= clause 1 of `P11SlowSpecOf`); `h0 = h + eps*p11PolarAverage G`
(clause 2); `h0 = h + eps*(C + ΣΩρ/2π + Z)` (clause 3, literal form); `Z` holomorphic on the
`{‖J-J0‖<s1/2, ‖ρ‖<π rz²/16}` domain (clause 4); the J-jets of `∂ρ Z` with constant `c` (clause 5);
`‖Z‖ <= 2^{2n}(MF/16 + p11eta1)` on that domain (new; gives `|∂_J Ĝ0|` by Cauchy for P7c); `h0` holomorphic on the box;
`f2` holomorphic and `RealOn` on strip×box; `h0` real at real points; `f2` 1-periodic in all 2n angles (needed by `aniso_field`/`aniso_avg`);
`p11WBound box σ/12 f2 (c eps^{5/2} log^{2τ+1})`.
Since `s2 <= s1/4`, `V2 ⊆ p11SlowBox` and `Vh ⊆ V2`: every clause restricts (WBound/DifferentiableOn/RealOn are monotone in the set).
Constants: `c` of the statement dominates `p11SlowCZ C` and `coth(π σ/12)^{2n} * p11SlowC0 C c1`; any larger `c` also works
(P7d: take `max` with P7c's constant, then every field of `P11SlowOscSpec` and of `P11SlowSpecOf` holds with that `c`; the spec fields are monotone in `c`).
Smallness used: `eps*MF <= e^{-1}`, `128*eps < rz²`, `eps <= eps1` of `p11eta1_source_rate` (all packaged in `eps2`).
Note the clause "h0 real" for `P11SlowSpecOf`'s `∀ I, realInclusion I ∈ Vh → (h0 …).im = 0` is `p11_slow_h0_real`; `g2` reality is P7c.

## Approach / graph mapping
as-osc: `p11_slow_polar` (polar_avg(b),(d)+(a),(c) with k=4 for R4, S=eta1 for gbar), `p11_slow_key`/`secZ_eq`,
`p11_slow_osc_pointwise`+`p11_slow_f2_sup` (oscillation `c(eps²+eta1√eps)` via `p11_radial_schwarz_gen`/`p11PolarAverage_norm_le_pow`
(order-one Schwarz, avoiding the eps-ball square root of the source) and `|f1| <= (eps MF)^3`), `p11_slow_rho_bound`/`Z_jets`
(e2/cauchy_open, `p11PartialVec_norm_le`), weighted bound = the sup→weighted conversion of as-concl's (a) (`summableWeighted_torusCoeffW`).
The identity `G∘Π - (C+ΣΩρ/2π+Z) = R4∘Π + gbar∘Π - (AR+AB)` is exact algebra (`x²+y² = ρ/π`); the polar-average identities are used only
for `h0` (clause 2), reality, and the oscillation of `gbar` (`AB - gbar(J,0)`).
`f2` is real because `h0` is (clause 2 + `G` real) and `f1`, `G∘Π` are real (no reality of `Ω` needed).

## Checks
- Gate builds (`inp_lake_build.sh`) of every module above, last: `Build completed successfully (9350 jobs)`.
- `sh scripts/lint_sources.sh`: only the pre-existing `KAM.lean is out of date` notice; `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- `#print axioms KAM.Planetary.p11_slow_osc` / `p11_slow_osc_at` / `p11_slow_polar`: `[propext, Classical.choice, Quot.sound]`.
- No short-name clash: each declared name was grepped against the rest of KAM (no hits).

## Design signals
- `p11_slow_f2_sup` first exceeded the default heartbeat budget as one proof; split into `p11_slow_f2_numeric` (pure real bookkeeping) and the geometric lemma. No override used.

## Uncertainties / deviations / errata
- No signed statement changed; none proved (all exported lemmas are UNSIGNED with distinct names). `Slow.lean` facade not touched (P7d adds the import).
- `p11SlowBox` uses radius `s1/4` for J (not `s2`): chosen so P7b is independent of `nu`/`K2`; it contains every `V` of `P11SlowSpecOf`.
- Source remark (no erratum): the source bounds the oscillation of `ε ḡ∘Π` by `η1√ε` using Cauchy at radius rz/4; here it is the order-one Schwarz bound, equivalent. The source's `|∂ρ AR4| <= c M_F eps r_z^{-4}` is reproduced with radius πeps/4 (constant `p11SlowCZ`).
- Suspected errata: none found.

ORCHESTRATOR RULINGS: 23:35 split of P11A-P7's core into P7b (plan steps 1-2: polar normalization, Z, h0, f2 and bounds), P7c (steps 3-4: divisor, displacement, aniso_avg, parametric in P7b's outputs) and P7d (assembly of avg_slow_of_spec and the signed wrappers); 00:20 each piece audited as it finishes. avg_slow itself, the divisor clauses and aniso_avg are NOT findings here.

AUDIT FOCUS: design docs/tracks/P/design/P11A-LEAN-DESIGN.md (avg_slow and steps as-osc, as-nr, as-b2, as-concl as the node table maps them) and the P7 round-1 handoff (docs/tracks/P/audits/P11A-P7-handoff.md, plan steps 1-2); signatures /root/code/KAM-inp/.drafts/design/P11ASignatures.lean (P11SlowSpec: the shapes of Z, h0, f2 and their clauses). Check each delivered bound has exactly the shape the P11SlowSpec clauses need (constants, exponents eps^(5/2) log(1/eps)^(2 tau+1), radii, strip widths), that the f2 sup bound uses P5's p11eta1_source_rate (amended p11d1), the reality and periodicity clauses, and no hypothesis P7d cannot discharge. Audit ONLY KAM/Planetary/Preparation/SlowAverage*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
Orchestrator note: p11SlowBox / p11SlowBox_mem were renamed p11SlowAvgBox / p11SlowAvgBox_mem (P7c defines a different p11SlowBox, the Z-domain box of P11SlowSpecOf).
