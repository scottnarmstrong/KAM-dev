Audited HEAD `45b792e11c083d56266ac3e935d57be8ce9c5db3`; package `21dbff642`; SHA256: `KAM/EffectiveStability/Tube/Initial/Point.lean` = `175efbe7d6c9e4a6fd915b43627b65c7007b76842378ce79015b382a60af8596`; `KAM/EffectiveStability/Tube/Initial/Partials.lean` = `d24e92b3c001f014424695f8a7977a902ff0ed67807589220c1d39a2c2fdf30b`; `KAM/EffectiveStability/SJSU/Initial/Data.lean` = `9132c5d1fbdc658e5f18dae1a3af8536ac98bbb8479e115b560d4d35702eef11`; `KAM/EffectiveStability/SJSU/Initial/Main.lean` = `49ec4bf2e918623b9556414de75876337dc4ab68fef791467dae260fb55eeb4a`; `KAM/EffectiveStability/SJSU/Ecc/Main.lean` = `7aef992b2288d976f14700f18b882815728ec18cd62a757d35cc345d6b53fca6`; `KAM/EffectiveStability/Tube/Ecc/Center.lean` = `5e3ba12a169d489cde8927d567c388eb77a34a22f1bb5ec93fb4b6fe29284851`; `KAM/EffectiveStability/Tube/Ecc/Defs.lean` = `218702cf8d7fccb3a5b57958447cbaea502586703f20f4e35d4e6bac4dc85b08`.

**Verdict: PASS WITH NOTES for the delivered N5c/N5b interface.** No blocking defect in the audited
Lean statements or proofs. This does not certify standalone closure of the original brief's literal
observable target: its coefficient bounds and the literal face centre remain N7 obligations, as the
handoff explicitly records. Findings N1 and N2 preserve that boundary.

The audited seven Lean files are byte-identical to package commit `21dbff642` at the HEAD above.
`gen_init.py` and its inputs were also inspected; the three N6 files received rename-only review.
The shared worktree contains other workers' modified/untracked files, including dependencies under
`SJSU/Ham/`, `Tube/Poly/`, `SJSU/Confinement/`, and `Tube/Check/`. Those are contextual consumer/import
reads, not additional audited packages. No source or handoff was edited; the only writes for this audit
are this report and the permitted audit scratch probe/logs. No commit, push, branch switch, or root
regeneration was performed.

**N1 — Nonblocking scope boundary: the literal observable attachment is still conditional.**
Location: `KAM/EffectiveStability/SJSU/Initial/Main.lean:164` and
`docs/explorations/sjsu-g2-handoffs/N5c-Q.md:67`.

Quoted statement: `chartLip … (fun l => (sjsuFuMax j l : ℝ)) (fun b => (sjsuFphiMax j b : ℝ)) *
(1 / 10 ^ 6) ≤ 1 / 10 ^ 6 / 2`.
The handoff qualifies target 3 with “once N7's norms meet the ceilings.”

This theorem checks a rational expression in proposed ceilings. It does not itself assert that the
literal F-v1 observables have those derivative bounds, or export their variation on Q. Calling it
unconditional closure of the original target would be wrong. The module docstring at Main.lean:28–31
correctly states the remaining attachment. The inspected consumer
`SJSU/Confinement/Statement.lean:127–135,155–159` still takes `hfper`, `hfd`, `hFu`, `hFφ`, and `hface` as
inputs while plugging in the proved N5c constants. Thus the interface is usable and no hidden
conclusion-shaped premise was introduced by N5c.

Suggested completion: N7 must instantiate the generic Partials lemmas for its exact literal/pruned
observables, prove their coefficient sums meet these ceilings, and supply their periodicity and
smoothness. Retain the conditional qualification until those receipts land. The independent exact
Python sums below support feasibility, but are not substituted for that Lean attachment.

**N2 — Nonblocking handoff overstatement: the face lemma bounds a supplied centre; it does not choose it.**
Location: `docs/explorations/sjsu-g2-handoffs/N5c-Q.md:70`, quoting
“`c̃_j`, `γ_j` come from `abs_obs_sub_le_of_face`”; compare
`KAM/EffectiveStability/Tube/Initial/Point.lean:272–277`.

The lemma takes `{ct ε ρ : ℝ}` and a bound `|f (u, φ) - ct - u j| ≤ ε` as inputs. It yields
`|f (tubeChart V B z) - ct| ≤ ε + μ j`. It supplies the valid choice `γ_j = ε_j + μ_j` for any
already supplied `ct`; it does not construct the literal `c̃_j = ct j` requested in the original brief.
The current consumer also leaves `{ct ε η : Fin 3 → ℝ}` as parameters (Statement.lean:122).

Suggested wording: “N7 supplies the literal `c̃_j` and its face bound; this lemma supplies
`γ_j = ε_j + sjsuMu`.” The replacement for a direct centre evaluation is mathematically valid:
`|f(z*)-ct| ≤ |f(z*)-ct-u_j(z*)| + |u_j(z*)|`, with no circular use of the confinement conclusion.
Its remaining margin is exactly `10⁻⁶ + 2 ε_j + 10⁻⁹ < 2·10⁻⁶`.

**Statement, source, and edge-case checks.**

- `Data.lean:29–42`: independently parsed all six raw `xi_eta_secular` decimals without a binary-float
  round trip. They agree textually with the approved draft v2 and the scratch draft
  `.drafts/g2scratch/t2/stmt.txt`. Lean's pair is `(η, ξ)`, so `x.1` is coordinates and `x.2` momenta;
  rational `sjsuEtaQ`/`sjsuXiQ` agree exactly with the decimal vectors.
- `Data.lean:45–50` and `Main.lean:60–68`: rotated data are `V′ᵀη*`, `V′ᵀξ*`, using columns, with no
  index permutation or transpose reversal. `sjsuVq_eq_eccV` checks the N5a/N6 rotations agree exactly.
- `Main.lean:106–137`: all `Fin 3` modes on the full closed ball, including its boundary, have
  `q_j²+p_j² ≥ a_j > 0`. The ball is nonempty (contains `sjsuZStar`); zero actions are correctly
  excluded by the proved lower bounds. The consumer's `mem_closedBall_iff_coords` is exactly the
  original coordinate box, using the product/Pi sup norm.
- `Point.lean:38–96`: independent derivative sign check:
  `∂_b[-m_l σ cos(m·φ)] = +m_l σ m_b sin(m·φ)`. Taking absolute values gives the declared `lipSum`
  majorants, with no missing minus sign or factor two.
- `Point.lean:100–140,180–182`: independent phase check:
  `(p_a-iq_a)(p_2+iq_2) = (p_a p_2+q_a q_2) + i(p_a q_2-q_a p_2)`.
  Its unit phase is `exp(i(θ_a-θ_2))`, with `θ=arg(p-iq)`, exactly the chart's reduced angles.
  `a.castSucc` maps `Fin 2` to modes 0 and 1, and reference mode is 2. The absent normalization by
  `√2` cancels in the unit phase. No continuity of a global branch of `arg` is assumed here.
- `Point.lean:145–176,202–266`: the squared rational unit-circle test retains both nonnegative-sign
  checks; nonzero ζ is supplied separately by `modesPos`. The enclosure includes both circle errors,
  fixed-point rounding `tau`, and the exact action `(q²+p²)/2`. `sjsuPt₁_ok`, `sjsuPt₂_ok`, and
  `sjsuMu_ok` are kernel-checked closed numerical propositions, not assumptions.
- `Partials.lean:94–120`: product/chain rules yield the advertised finite coefficient majorants.
  When `μ_i l=0`, the coefficient zero kills that derivative, so natural subtraction of `e_l` is
  harmless, also at `u=0` and `ρ=0`. The nonempty `Fin 3` bound `hu` supplies `ρ≥0`; no omitted
  positivity premise makes the result false. Empty sums and negative Fourier modes cause no issue.
- `Partials.lean:124–152`: periodicity is for arbitrary integer vectors and both sine/cosine parity
  choices. The increment is `2π(k₀m₀+k₁m₁)`, as required by the consumer.
- All instance theorems have only index/point binders and proved numerical hypotheses. Generic helpers
  are explicitly conditional on rational structural tests, differentiability, or coefficient/face
  bounds. They do not stand in for unpaid source theorems.
- All three N6 changes equal the parent text after the declared identifier replacements and whitespace
  normalization: `sjsuB → sjsuEccCenter`, and `pairSum/treeSum/pairSum_sum/treeSum_eq →` their Q names.
  A Lean `rfl` check also confirms `sjsuEccCenter k φ = sjsuB φ k`.

**Generator and numerical checks.**

Executed `gen_init.py` from its intended scratch directory with its output `open(..., 'w')` intercepted
in memory. No audited file was rewritten. Result: **EMITTER BYTE MATCH PASS** against committed Data.lean.
The generator's floats only propose ceiling headroom; its hLF arithmetic uses `Fraction`, and the Lean
instance independently proves its numerical checks with `decide +kernel`/`norm_num`.

Independently recomputed exact `Fraction` coefficient sums from all 965,745 F-v1 coefficient entries
(165 u-slots per observable, degree ≤ 8). Used
`Fu_jl = Σ_m m_l ρ^(|m|-1) Σ_k |a_jmk|` for `m_l>0` and
`Fφ_jb = Σ_m ρ^|m| Σ_k |k_b| |a_jmk|`, with `ρ=2·10⁻⁶`.
All 15 inequalities `sum ≤ 0.95 * ceiling` passed using exact rational comparison.
Displayed numbers below are rounded summaries of those exact sums:

| j | Fu (three action directions) | Fφ (two angle directions) |
|---|---|---|
| 0 | 1.129468968, 0.021715117, 0.027425925 | 3.67344e-7, 3.11222e-7 |
| 1 | 0.138543405, 1.021255607, 0.053010549 | 3.15762e-7, 4.49955e-7 |
| 2 | 0.023540689, 0.001665636, 1.071417863 | 6.70079e-8, 1.55154e-7 |

The ceiling-based `chartLip*r` is `(9.0312221e-8, 1.1851029e-7, 2.3921704e-8)`, below `5e-7`.
The independent rational expression `μ + Lu_j*r` is
`(7.3056263e-8, 9.6837126e-8, 1.9664974e-8)`, below `2e-6`.
This verifies the handoff's rounded margin claims, without certifying a future changed/pruned dataset.

Supplementary SHA256 evidence:

| Input | SHA256 |
|---|---|
| `.drafts/g2/scratch/N5c-Q/gen_init.py` | `fe15d3a8d354f5fc9121ba3afcd102b2b7a72019da912a67d0cf9dfe9a5c388a` |
| `.drafts/g2/scratch/N5c-Q/qdata.json` | `b0a73921ecd05c407bbf2e94886582f852f8e6efd615d327c5400b23cf81b609` |
| `.drafts/g2/scratch/N5c-Q/fbounds.json` | `98473a59ae2c3b55052b05a5c11db300371060dce75813112b62afb23c724d0b` |
| `.drafts/g2/data/F-v1.json` | `40cf26e2a1f669a36cd13d86891f18620089f04c2e3a198afdb03f6670d1c825` |
| `.drafts/g2/data/literal-v1.json` | `95b841cee81ef862a7bc7631b28c84eb387e04cb1505e8cc105fd2ce9b33306e` |
| `applications/sjsu/validation/table2_map_poincare_order1.json` | `8300d2f33bf6301fc29ec13366aad502b5e03186558f39e20714e622ad72c610` |
| `.drafts/g2scratch/t2/stmt.txt` | `16424cdc10231b2fa589ca925de301272156b8ecaadfe5fcedd3cc943a75325f` |
| `docs/explorations/sjsu-g2-t2conf-proposal.md` (approved draft v2) | `bb10fff984271f398baf149b964234779d126641f2f4d522b580ed8a5a9744f4` |
| `docs/explorations/sjsu-g2-handoffs/N5c-Q.md` | `ab76bff2312789f28632ce68afcb1dbbb212ba0cf73114128c916f170a714ac2` |

**Builds and axioms (fresh audit commands, serialized).**

Each row is one invocation `.drafts/g2/g2lake build <Module>`, exit 0:

| Module (`KAM.EffectiveStability.` prefix) | Exact completion output |
|---|---|
| `Tube.Initial.Point` | `Build completed successfully (2794 jobs).` |
| `Tube.Initial.Partials` | `Build completed successfully (2918 jobs).` |
| `SJSU.Initial.Data` | `Build completed successfully (1930 jobs).` |
| `SJSU.Initial.Main` | `Build completed successfully (2805 jobs).` |
| `SJSU.Ecc.Main` | `Build completed successfully (2190 jobs).` |
| `Tube.Ecc.Center` | `Build completed successfully (1993 jobs).` |
| `Tube.Ecc.Defs` | `Build completed successfully (1992 jobs).` |

Partials' build replayed existing dependency deprecation/unused-simp warnings in Algebra.Bounds,
Trig.Tube, Trig.Trunc, and Certificate.Arith.PiHigh. No audited-file warning or default-heartbeat
failure was emitted. All commands used the required g2lake lock/capped wrapper; no direct Lean/Lake
command or resource override was used.

Ran exactly one axiom scratch file:
`.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/N5c-Q-Axioms-1.lean` (exit 0).
It checks every theorem declared in the four Initial modules, the renamed sum lemmas, and
`sjsu_tube_gamma`, `sjsu_tube_ecc`, `sjsu_tube_ecc_of_dev`: **51/51** outputs are exactly
`[propext, Classical.choice, Quot.sound]`. This includes all SJSU ball/centre/ceiling results,
`abs_tubeU_le_of_point`, `abs_obs_sub_le_of_face`, both partial majorants, differentiability, and all
periodicity results. The same file checks the centre rename compatibility by `rfl`.
Full output: `.drafts/g2/scratch/audit/N5c-Q-Axioms-1.log`, SHA256
`9919fa9e4ff7b08335ad297e7c92abc7f30b39c0dba700f837ecd2e78dec973c`.

**Rules and lint scope.**

Package-local code-mask scans found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`,
`EuclideanSpace`, `native_decide`, or `sorryAx`. Module headers/imports/docstrings/public sections and
exposure attributes are present. Actual line counts:

| File (under `KAM/EffectiveStability/`) | Lines |
|---|---:|
| `Tube/Initial/Point.lean` | 286 |
| `Tube/Initial/Partials.lean` | 156 |
| `SJSU/Initial/Data.lean` | 90 |
| `SJSU/Initial/Main.lean` | 174 |
| `SJSU/Ecc/Main.lean` | 116 |
| `Tube/Ecc/Center.lean` | 325 |
| `Tube/Ecc/Defs.lean` | 288 |

All are below 1500. The handoff's 285/172 counts for Point/Main are stale by 1/2 lines; this has no
proof effect. `git diff 21dbff642 -- <the seven paths>` and package-scoped `git status --short` are
empty. The explicit N6 rename paths are authorized by the audit launch. Other dirty paths are shared
worktree activity, not attributed to this package or changed by this auditor.

Per the launch instruction “Lint: use .drafts/g2/lint_noabi.sh only if needed, once,” no whole-tree lint
was rerun: the package-local checks and targeted builds suffice for this review, and the handoff
already records its global lint failure in unrelated/generated files. No ABI or frozen-anchor gate
was run or claimed passed. Generated roots and frozen/manifest files were left untouched.

No suspected pinned-source erratum or auditor-introduced mathematical deviation was found. The remaining
uncertainty is the supplier/consumer attachment in N1–N2; this report does not upgrade it to a proved
literal observable theorem or a completed confinement seal.
