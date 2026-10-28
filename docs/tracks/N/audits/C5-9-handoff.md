# C5-9 prover handoff (branch inp-c59, d4e285b; contains inp-c58 (C5-8, delivered); offloaded package run by the main orchestrator; prover on claude-12)


## Files (new)
- `KAM/Canonical/TransformSeries.lean` (~230 lines): helper engine (not in the signature file).
- `KAM/Canonical/Transform.lean` (~270 lines): `liftRemainder` and `transform`, copied verbatim from
  `NPart145Signatures.lean` (only line wraps differ), plus helpers.
No other file touched (KAM.lean not regenerated: lint reports "KAM.lean is out of date", expected; the
sub-orchestrator regenerates it).

## Node
`bpN:p5:transform` = `KAM.Canonical.transform` (all 8 conjuncts: identity, integral form, pointwise HasSum,
InClass, both bounds, tail convergence in WBound), and the def `KAM.Canonical.liftRemainder`.

## Approach
- `TransformSeries`: `wbound_add`/`coeff_add` (new subadditivity of the weighted norm; coefficients of sums),
  `inClass_poissonBracket` (`{u,v} ∈ O(r,s)` for `v ∈ O(r',s')`, `r≤r'`, `s≤s'`; needed because hw gives a
  WBound but not InClass of `{h,φ}`), `remTerm`/`remBound`, `remTerm_bound` (each term `a_i ∈ O(r-ρ,s-σ)`,
  `|a_i| ≤ q^{i+1}(Mw/(i+2)+F₀)` from C5-8 `lieTerm_bound` for `w` and `f₀`), `remSeries_{class,bound,tail,hasSum}`
  (uniform_limit_holomorphic, wbound_tsum), `remBound_tsum_le` (`q ≤ η`, `q/(1-q) ≤ η/(1-η)`).
- `Transform`: `adPow` of `c•φ` scales by `c^j`; `flow_series` (`u∘X^t = ∑ t^j ad^j u/j!` via C5-8 `series_eq` for
  `tφ` + `flow_smul`); `integral_flow_hasSum` (termwise `∫₀¹`, dominated convergence);
  `transform_identity`: `h∘X¹ = h + ∫₀¹ w∘X^t` (`taylor_lie`, N=1; needs no bound on h), `f₀∘X¹` by `series_eq`;
  hence `𝓡 = (∫₀¹ w∘X^t − w) + (f₀∘X¹ − f₀)`, HasSum of the remainder terms. Integral form of `𝓡` from
  `taylor_poschel` (C5-6) by cancellation. Negative `Mw`/`F₀`: handled in `remSeries_bounds` (`wbound_of_neg`,
  vacuous); other conjuncts use `max Mw 0`, `max F₀ 0`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-c59 KAM.Canonical.Transform`: success (3208 jobs), no sorry/warnings in my files.
- `sh scripts/lint_sources.sh`: only "KAM.lean is out of date"; check_lean_modules PASS, frozen guard OK, ABI hashes OK.
- `#print axioms KAM.Canonical.transform`: `[propext, Classical.choice, Quot.sound]`.
- No `set_option`, no heartbeat overrides; files well under 1500 lines.

## Uncertainties / errata / deviations
- Extra module `TransformSeries` and extra defs/lemmas (names above) beyond the single module in the design table.
- No statement defects found; no errata. Signature unchanged.
- No design signals (all proofs elaborate at default heartbeats).

AUDIT FOCUS (design docs/tracks/N/design/PART145-LEAN-DESIGN.md row C5-9 and proof plan; binding audit-2 notes; audits PART145-design-audit-{1,2}.md; blueprint-N p5 transform): (1) statements = blueprint and signature (the canonical transformation theorem: transformed Hamiltonian in weighted norms with constants and losses); (2) proofs sound (composition C5-8, Lie C5-6); (3) hygiene. Audit ONLY the C5-9 module(s) (git diff inp-c58...HEAD restricted to KAM/Canonical/).
