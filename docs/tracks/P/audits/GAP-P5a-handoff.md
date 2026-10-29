# Handoff GAP-P5a (branch inp-gp5a)

## Files (new, append-only)
- `KAM/Planetary/PGAssembly/ScaleNodes.lean` (~205 lines)
- `KAM/Planetary/PGAssembly/ExtensionNodes.lean` (~70 lines)
KAM.lean not edited: `lint_sources.sh` reports "KAM.lean is out of date" (expected; orchestrator regenerates
via `scripts/gen_root_imports.py`). All other lint checks PASS (modules, frozen anchors, ABI hashes).

## Node -> declaration
| node | declaration |
|---|---|
| stepP:p5:kc-eval | `KAM.Planetary.kc_eval` (0<r, 0<mu≤1): L = C₁/μ; x = C₁⁴/κ₀² (the P3 expression E·M²·L/γ₁²) and ≤ 1; cutoff = pgK0 (K = K₀); ρ̂ as displayed; eHat = Ê; Ê = C₁²r⁵/ρ̂²; Ê = max{9C₁⁴K₀^{2τ+2}/κ₀², 4C₁²/κ₁²} |
| stepP:p5:kc-small | `kc_small`: ĉÊ < 1 ∧ γ₂ = μγ₁ ∧ γ₂ ≤ γ₁ |
| bpP:p5:kam-cond | `kam_cond_node`: L = C₁/μ, x ≤ 1, K = K₀, Ê = max, ĉÊ<1, γ₂ ≤ γ₁, n < τ |
| stepP:p5:rk-dir (+ completes bpP:p5:rK) | `rk_dir` (admissible d (pgRstar d) r mu): Ê < 1/(2¹³n); rK < ρ̂/(256n) ≤ λ₁/(512n); rK < min{t,λ₁}; rK < ρ̄/2; 2rK/ℓ ≤ κ₁√r/(64n); (1+2rK/ℓ)^b < 2 |
| stepP:p5:be-an | `be_an` (wrapper): holomorphy in I of jetP0/jetOmega/jetBeta, joint continuity, jetBeta symmetric |
| stepP:p5:be-jet | `be_jet`: for mu∈[0,mu0], k≤4, v: holomorphy of I ↦ ∂ₓ^k Q(mu,I;0)v on D_c; vanishing on V; vanishing on D_c |

## Already closed (LEAN_STATUS PROVED on this branch; skipped)
stepP:p5:ext-loc, ext-glue, ext-per, ext-H0 (all PROVED, local to parent `ext`). No AMENDMENTS entries touch the ten nodes.

## Approach
kc-eval/kc-small restate the landed `pgKamScale_*`, `chat_Ehat_lt`, `params_*` facts under the *weaker* source hypotheses
(0<r, 0<mu≤1) instead of `admissible`: the landed `pgKamScale_L/cutoff/rhoHat/eHat` are re-proved privately (`kcnode_*`)
with `mu ≤ 1`. The Ê = max identity is new (min-case split). rk_dir combines `r_k`, `chat_Ehat_lt`, `rhoHat_le_l1`, `av_dyn`.
be-jet uses `differentiableOn_slice_jet`, `remainder_jet_real`, `remainder_jet_tube`.

## Checks
- Gate builds of `KAM.Planetary.PGAssembly.ScaleNodes` and `...ExtensionNodes`: success, no warnings in my files.
- `#print axioms` of kc_eval, kc_small, kam_cond_node, rk_dir, be_jet, be_an: [propext, Classical.choice, Quot.sound].
- Lines ≤ 100 cols; no set_option; no sorry.

## Uncertainties / errata / deviations
- Cw-style audit points: none. `kam_cond_node` does not restate the κ₀,κ₁,G choice order (that is `kam_cond`/`PGScaleSpec`, landed) nor the G bounds; auditor may want `pgScales_spec` cited for items 1-3 of the lemma.
- x is expressed via the P3 record fields (E·M²·L/γ₁²), since no named `x` def exists.
- be-jet: connectedness of D_c and the identity theorem are used via landed `remainder_jet_tube` (not re-proved). be-an's source gap (parameter integration) is covered by landed `avgFun_*` lemmas.
- No source errata found.

## Orchestrator-note self-check (three points)
1. Premises: no export takes a dependency's output as hypothesis. kc_*/kam_cond_node: only 0<r, 0<mu≤1. be_*: mu∈[0,mu0], k≤4. rk_dir uses `admissible d (pgRstar d) r mu` (the landed rendering of "admissible (r,mu)"; its bounds are derived inside from `r_k`, `av_dyn`) — auditor to confirm acceptable.
2. Domain: be_jet holds for all complex I in the tube and all v; kc_* for all real r>0, mu∈(0,1].
3. Literal clauses: `kam_cond_node` now also states the ρ̂ min-display and Ê = C₁²r⁵/ρ̂² (previously omitted); K = K₀ is `cutoff = pgK0 d (pgScales d)`, (r,mu)-independent. The κ₀,κ₁,G choice is landed as `pgScales_spec`, not restated.

## Round 2 (fix of audit-1 finding F1)

- File changed: `KAM/Planetary/PGAssembly/ScaleNodes.lean` only (`kam_cond_node`); other nodes untouched.
- Approach: `kam_cond_node d` now states `PGScaleSpec d (pgScales d)` (κ₀, κ₁, G items 1-3, fixed by `d`
  before `(r, mu)`), then for all `0<r`, `0<mu≤1`: `L = C₁/μ`; the actual P3 expression
  `E*M^2*L/γ₁^2 = C₁^4/κ₀^2`; `C₁^4/κ₀^2 ≤ 1`; `K = K₀`; bridges `rhoHat (pgKamScale ..) =
  (params ..).rhoHat`, `eHat (pgKamScale ..) = (params ..).Ehat`; ρ̂ min display; Ê = C₁²r⁵/ρ̂²;
  Ê max display; `ĉÊ<1`; `γ₂≤γ₁`; `n<τ`. Components come from `kc_eval`/`kc_small`/`pgScales_spec`.
  No new premise. Signature changed from `{r mu} → hyps → conj` to `spec ∧ ∀ {r mu}, hyps → conj`
  (no other users in the repo).
- Checks: gate build of ScaleNodes succeeded (9230 jobs); lines ≤ 100; axioms of `kam_cond_node`:
 `[propext, Classical.choice, Quot.sound]`; `scripts/lint_sources.sh` run (KAM.lean out-of-date notice is the permitted exception).
- Uncertainties/errata/deviations: none new.
