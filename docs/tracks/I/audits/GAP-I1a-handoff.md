# GAP-I1a prover handoff (branch inp-gi1a, db305f13; off inp; track I graph-gap programme package run by the main orchestrator)


## Files (new, append-only; no landed file edited)
- `KAM/Iso/Linear/DioDirichlet.lean` (~215 lines): n-dimensional Dirichlet emptiness.
- `KAM/Iso/Linear/SettingSrc.lean` (~105 lines): literal `SettingSrc`, projection, k-bridge.
- `KAM/Iso/Linear/FullRange.lean` (~190 lines): the eight parent exports.
`KAM.lean` is NOT regenerated (rule 10): `lint_sources.sh` reports "KAM.lean is out of date; run
scripts/gen_root_imports.py" for these three modules; the orchestrator must regenerate.
GAP-I1b should import `KAM.Iso.Linear.SettingSrc` (and `FullRange` for `mSize_max_one`).

## Node -> declaration (all in `KAM.Iso.Linear` unless noted)
| node | declaration |
|---|---|
| (N1 key lemma) | `KAM.IsDiophantine.n_sub_one_le_tau : 2 ≤ n → 0 < γ → IsDiophantine γ τ ω → n-1 ≤ τ` (DioDirichlet) |
| bpI:p1:setting | `SettingSrc n τ M D H ω γ` (τ ≥ 0, no σ's; fields as `Setting` minus σ's, plus `dH_le`); `SettingSrc.setting` (→ `Setting n τ M σK σB σT …` same τ, any σ>0), `SettingSrc.tau_ge` |
| bpI:p1:setting#k-bridge | `SettingSrc.k_bridge`: `Standing n τ M 1 1 1 D H ω γ ∧ ‖DH‖ ≤ M ∧ 0 ≤ τ ∧ 1 ≤ n ∧ ∀ K r (0<r) holo (IsUnit det G on strip), ` the five `frozen_agreement` identities + torsionAverage = avg (conditional on continuity, as in `frozen_agreement`) |
| bpI:p1:extended-basic | `extended_basic_src` |
| bpI:p1:last-row | `last_row_src` |
| bpI:p1:energy-approx | `energy_approx_src` (a)-(e), `energy_defect_src` (f) |
| bpI:p1:energy-conservation | `energy_conservation_src` |
| bpI:p1:reduced | `reduced_src` |
| bpI:p1:geometry-noA5 | `geometry_noA5_src` |
| bpI:p1:perturbation-noA5 | `perturbation_noA5_src` |

All current LEAN_STATUS were NOT_STARTED (none skipped).

## Approach
- Dirichlet: pigeonhole (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`) on k·ω for k ∈ {0..N}ⁿ,
  buckets of the rescaled value in `m = (N+1)ⁿ-1` cells, giving nonzero d, |d_i| ≤ N,
  |d·ω| Nⁿ ≤ 2N‖ω‖₁; then with τ⁺ = max τ 0 < n-1, γ ≤ C N^{-(n-1-τ⁺)} for all N, contradiction by
  `tendsto_rpow_atTop`. `2 ≤ n` is needed (false for n = 1, τ<0, e.g. ω = 1).
- Exports restate the landed conclusions verbatim with `hS : SettingSrc` and construct the landed
  `Setting … 1 1 1` inside the proof (no proved output taken as premise).
- `geometry_noA5_src`, `perturbation_noA5_src`: σK σB σT are FREE reals (no positivity), per §2.9 "all σT":
  I weaken the bounds to `max σ 1` and use `mSize_max_one` (𝔪 unchanged) after unfolding the constants.
  Hypotheses `AdmissibleNoTwist σK σB …`/`hDK`/`hG` are the source's; no σ positivity is derived (not needed).

## Checks
- Gate builds: `inp_lake_build.sh … KAM.Iso.Linear.DioDirichlet`, `…SettingSrc`, `…FullRange`: all
  "Build completed successfully", no warnings.
- `#print axioms` of every export above (11 declarations): `[propext, Classical.choice, Quot.sound]` only.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message
  is the expected "KAM.lean is out of date".
- No heartbeat options; files < 250 lines; lines ≤ 100 columns; short names `bucket_bounds`,
  `exists_small_combination` (namespace `KAM.DioDirichlet`), `mSize_max_one` unused elsewhere in KAM.

## Uncertainties / errata / deviations
- No erratum. `n_sub_one_le_tau` takes `2 ≤ n` as in the plan.
- `k_bridge`'s frozen-agreement clause is quantified over all `K` holomorphic on a strip with
  invertible Gram (as `frozen_agreement`); the "Standing at σ=1" part is the projection.
- DEPGRAPH LEAN_STATUS/LEAN_REF updates are left to the orchestrator.

ORCHESTRATOR RULING: track I graph-gap programme (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md, section GAP-I1a). RULING N1 (OVERNIGHT 05:10, owner to review): option (i), the literal route: the Lean Setting forces tau >= n-1 while the source says tau >= 0; this package proves that for n >= 2 the Diophantine set is empty when tau < n-1 (so the restriction loses nothing) and exports each Part-1 parent under the source's literal tau >= 0 via SettingSrc. Check: the key lemma is TRUE and correctly proved (n-dimensional Dirichlet); for n = 1, tau >= 0 coincides with tau >= n-1; each parent export states its node literally under the source hypotheses with tau >= 0. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/I/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint-I lines it cites; per-node verdict: does the named declaration state the literal conclusion under only the source's hypotheses, quantifiers in source order? An export taking a proved dependency's OUTPUT as a premise is a FAIL. Audit ONLY KAM/Iso/Linear/DioDirichlet.lean, SettingSrc.lean and FullRange.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
