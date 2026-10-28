# S7-8 independent package audit 1

Verdict: **PASS WITH NOTES** for `bpN:p7:resonant-prop2` / `KAM.Stability.resonant_prop2`.
No mathematical or statement-fidelity blocker found. This is an infrastructure package, not a
provider or frozen-anchor seal: no frozen theorem is proved or sealed by this change. Notes concern
unused hypotheses, the permitted stale generated root, and an auditor scheduling deviation below.

## Scope and authority

Audited only `KAM/Nekhoroshev/Stability/ResonantStability{Hess,Core,}.lean`, as directed by the handoff.
Read AGENTS, PLAN, DECISIONS, the package audit brief, handoff, Track N statement, Part 7 blueprint,
Parts 6–7 design v2 and both design audits, and relevant imported definitions/contracts. The two design
audits reside in `docs/tracks/N/design/`, rather than the handoff's suggested `audits/` directory.
The signature file is absent locally; read `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean`.
The user's exact report destination overrides the generic brief's main-worktree destination.

Snapshot:

- HEAD: `24b68094a99ec0957766ee39324a05098a6c190b`.
- `inp`: `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`.
- `inp-n68b`: `71c948960935fe32cd69d6d17bf932b9d691b906`.
- Both `git diff inp...HEAD` and `git diff inp-n68b...HEAD` contain exactly the same three new
  Lean files, 742 lines total (407, 172, 163).
- Design SHA-256: `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2`.
- Part 7 blueprint SHA-256: `f3d6e993abd74759469db1c9ae3c2c6d7cc65555a6d13167e8bfc7c38493e4bd`.
- External signature SHA-256: `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f`.

## Statement and proof audit

The declaration from `theorem resonant_prop2` through its type is text-identical to the supplied
signature (excluding the body). The design Appendix B.8 at lines 1283–1316 agrees. A scratch probe
copied that exact declaration under `auditSignature`, replaced its body by `exact resonant_prop2`
applied to all 26 explicit binders in order, and checked:

```lean
example : type_of% @auditSignature := @resonant_prop2
```

This elaborated without diagnostics other than the requested axiom output. Frozen-provider equality
and a literal frozen seal are inapplicable: this package adds no provider and targets no frozen anchor.
The probe checks the analogous complete design declaration, not an invented frozen target.

The source-contract checks preserve arbitrary real D, subgroup Λ, n ≥ 1, complex Euclidean Hessian,
real quasi-convexity, geometric strip s, κ = 2πKs, p/q, √n in the radius bound, Mr ≤ ℓ/2,
Euclidean radius r/2, and the max-norm consequence. An arbitrary nonnegative size upper bound ε and
any frequency bound Ω replace exact norm/max values conservatively; their quantifiers remain inside
the fixed input data and I₀. The multiplied time inequality handles Ωε = 0 without division;
Λ = univ permits every t in J. No supplied flow, future confinement, or normal-form existence
hypothesis is added to the final result. This remains a stopped-orbit estimate, not global existence.

The Hessian restriction differentiates Re h after real inclusion on open neighborhoods, identifies
both real derivatives locally, and applies complex Cauchy–Schwarz. The frequency estimate uses
Hessian symmetry and ‖v‖∞ ≤ ‖v‖₂ ≤ √n‖v‖∞, giving exactly L = √n M. The weaker real restriction
lemmas need holomorphy but no reality hypothesis; this is a valid generalization.

`Prop2Hyp.nums` derives every field of `Prop2Nums` from the literal source hypotheses. In particular
ε ≤ mr²/256, the normal-form smallness, half-radius Hessian bound and Lipschitz bound are proved,
not smuggled in through a structure. Case A obtains Ψ,g,fs from N6-8 `normal_form`, bounds g by
5ε/4 and fs by exp(-κ/6)ε ≤ ε/2, chooses ζ = 2ε, and proves the Euclidean displacement ≤ ρ'/4.
S7-4 `preimage_nfl` supplies actual preimages. Cases B/C construct identity data and use respectively
(g,fs,η) = (0,f,ε) and (f,0,0); no resonance-support fact is assumed in case C.

The core constructs S7-6 `ResSetting` at radius r/2 with δ' = mr/8 and ρ' = mr/(32M) ≤ r/32.
It invokes S7-3 `transfer` with ϱ = r/2 - ρ' and d ≤ ρ'/4. The admissibility predicate is
`I = I₀ ∧ (Λ = univ ∨ time bound)`: equality restricts Ω's use to the center at which its bound
was supplied. Its downward time closure is proved. The shifted frequency ball is contained in
the original closed radius-r/2 ball by the triangle inequality and d ≤ ρ'/4. The two half-radius
conditions for `resonant_lemma2` follow from hc2/hc3. Transfer returns ϱ + 2d ≤ r/2.
The case-specific arithmetic proves the core's time premise: case A cancels exp(-κ/6) against
exp(κ/6), case B uses exp(κ/6) ≤ 3, and case C has η = 0. Thus the core's normal-form and time
hypotheses are discharged by construction in the public result.

## Declaration ledger

Names below are in `KAM.Stability`; H = ResonantStabilityHess, C = ResonantStabilityCore,
R = ResonantStability. All declarations, including private lemmas and new proposition bundles,
are listed. Helper statements are local proof decompositions, not replacements for source results.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| p2-red, real inclusion | `realInclusion_mem_polyNbhd''` (H:34, private) | PASS | Max-norm neighborhood inclusion. |
| p2-red, norm bridge | `euclid_ofReal'` (H:39, private) | PASS | Real inclusion preserves Euclidean size. |
| p2-red, duality | `norm_apply_le_euclid` (H:43) | PASS | Complex finite-dimensional Cauchy–Schwarz. |
| p2-red, regularity | `contDiffOn_realPart` (H:56) | PASS | Holomorphy implies smooth real restriction on entire open tube. |
| p2-red, first derivative | `fderiv_realPart` (H:68) | PASS | Correct real derivative of Re h after inclusion. |
| p2-red, K real restriction | `hessBound_of_complex` (H:86) | PASS | Complex operator bound gives real bilinear bound; no lost factors. |
| p2-red / p6:lipschitz | `freqLipschitz_of_complex` (H:136) | PASS | Correct √n conversion. |
| p2-t12/t3/concl | `prop2_core` (C:33) | PASS WITH NOTES | Conditional transfer helper fully discharged by cases; hδ and hd0 unused. |
| Identity map | `reMap_id` (R:33) | PASS | Unconditional real-map identity. |
| Real preimage | `reMap_eq_of` (R:36) | PASS | Exact equality on real-inclusion image. |
| T1 norm bridge | `euclid_re_le` (R:43) | PASS | Coordinate real part contracts Euclidean size. |
| T2 identity data | `mem_realStrip_of_mem` (R:50) | PASS | Positive-radius membership for arbitrary D. |
| Source hypotheses | `Prop2Hyp` (R:58) | PASS | Exactly the final theorem's 26 premises. |
| Conclusion abbreviation | `Prop2Concl` (R:89) | PASS | Literal Euclidean confinement, including all-time/full-resonance case. |
| p2-red consequences | `Prop2Nums` (R:98) | PASS | Derived numerical and analytic facts, constructed by nums. |
| p2-red | `Prop2Hyp.nums` (R:112) | PASS | Proves all bundled consequences from source inputs. |
| p2-concl, norm conversion | `Prop2Concl.wrap` (R:161) | PASS | Transparent helper adding max-norm consequence to proved confinement. |
| p2-cases B/C | `prop2_idData` (R:172) | PASS | Holomorphic, real, symplectic identity with maps-to and preimages. |
| Positive displacement cap | `prop2_hρ0` (R:191) | PASS | Arithmetic positivity, no added final premise. |
| p2-cases C | `prop2_caseC` (R:195) | PASS | All modes resonant, zero remainder, unlimited time. |
| p2-cases B | `prop2_caseB` (R:220) | PASS | Half-radius identity case with original perturbation. |
| p2-cases A / p2-t12 | `prop2_caseA` (R:256) | PASS | Normal form, projections, displacement and surjectivity consumed correctly. |
| bpN:p7:resonant-prop2 | `resonant_prop2` (R:369) | PASS | Exact signature, complete three-case assembly, no extra premise. |

## Definitions and assumptions

- `Prop2Hyp`: a Prop-valued structure whose fields are the literal source/standing hypotheses;
  no result-shaped field or off-carrier fallback.
- `Prop2Concl`: a Prop-valued definition of the exact intermediate Euclidean conclusion for arbitrary
  input data. Used as a goal in cases, then as an explicitly named elementary wrapper premise.
  It is never a hypothesis of `resonant_prop2`.
- `Prop2Nums`: a Prop-valued record of derived bounds; every field is proved by `Prop2Hyp.nums`.
  No consumer can inject an unpaid field into the main proof.
- No other new def/abbrev/structure, instance, numerical fallback, totalized inverse, or substitute
  Hamiltonian is introduced. Existing `realH (h+f)` is the frozen `realHamiltonian h f` on real inputs;
  IsOrbit uses the frozen Hamiltonian vector field and genuine two-sided derivatives. Holomorphy
  on the open tube supplies differentiability wherever derivatives are used.
- Read-only import traversal visited 117 project modules: no `KAM.Provider.*` module and no frozen
  theorem anchor. Its 19 frozen imports are definitions. In particular there is no imported
  DRAFT_SORRY theorem or provider dependency. Standard-axiom checks independently guard the proof closure.

## Independent verification receipts

All following Lean commands use the default resource budgets. No resource override was introduced.

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-s78 KAM.Nekhoroshev.Stability.ResonantStabilityHess \
  KAM.Nekhoroshev.Stability.ResonantStabilityCore KAM.Nekhoroshev.Stability.ResonantStability
[inp-gate] slot 1 acquired 08:39:30
✔ [3292/3292] Built KAM.Nekhoroshev.Stability.ResonantStability (33s)
Build completed successfully (3292 jobs).
exit 0
```

Only package warnings: unused `hδ` (Core:37) and `hd0` (Core:62). Replayed upstream warnings concern
Gradient:168 `hgr`, ODE/Exit:36 an unused section variable, Transfer:174 `hϱ`, and
Resonant:263 `hPid`, :391 `ht₁0`. These are not proof holes or resource failures.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S78Audit1.lean
exit 0
```

The signature copy, explicit application, and `type_of%` check succeeded. Exact axiom output for every
new public theorem follows:

```text
'KAM.Stability.reMap_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.reMap_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.euclid_re_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.mem_realStrip_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.Prop2Hyp.nums' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.Prop2Concl.wrap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.prop2_idData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.prop2_hρ0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.prop2_caseC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.prop2_caseB' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.prop2_caseA' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.resonant_prop2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.prop2_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.norm_apply_le_euclid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.contDiffOn_realPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.fderiv_realPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.hessBound_of_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.freqLipschitz_of_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Stability.ResonantStability \
  KAM.Nekhoroshev.Stability.ResonantStabilityCore \
  KAM.Nekhoroshev.Stability.ResonantStabilityHess
replaying KAM.Nekhoroshev.Stability.ResonantStabilityHess
replaying KAM.Nekhoroshev.Stability.ResonantStabilityCore
replaying KAM.Nekhoroshev.Stability.ResonantStability
exit 0
```

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (481 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the explicitly permitted stale generated `KAM.lean`; no long-line,
module, frozen-anchor, ABI, or forbidden-token failure occurred. The first lint run returned the
same four output lines and exit 1; the receipt above is the independent serialized rerun.

Static checks: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option` or `EuclideanSpace`
in the three files. All have copyright, module declaration, public imports, module docstring,
exposed public noncomputable section, and ambient Fin-coordinate types. File lengths are 407/172/163;
maximum Unicode line lengths are 100/100/97. Both comparison-base `git diff --check` runs exited 0.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

Auditor procedural deviation: the first plain `sh scripts/lint_sources.sh` was launched while the
build gate was waiting. Its later ABI subprocess was therefore not guaranteed to serialize with the
build, and that first command did not explicitly set nice/LEAN_NUM_THREADS. This was an auditor
scheduling error, not a package change. The final lint run uses
`LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` after the build, probe and kernel replay
have each completed; those latter checks are serialized. No unrelated process was stopped.

## Errata, deviations, and limits

No new suspected pinned-source defect or blueprint contradiction was found. No PDF claim was newly
certified in this package audit. The inherited source qualifications remain explicit:

- `blueprint-N/parts/p7-stability.tex:268` quotes Pos93 p.199:
  “$|⟨ω(I(s)),PΔI⟩| ≤ (5/4)δ‖ΔI‖$”. The estimate available away from the initial tube includes
  `M‖I(s)-I₀‖`; the blueprint's repair adds `Mr ≤ ℓ/4` for Lemma 2 and `Mr ≤ ℓ/2` for Proposition 2.
  The final signature retains hc3, and the core applies it at half radius. This is an inherited
  source-proof gap/deviation, not a claim here that the original theorem is false.
- Same file:269 quotes the p.200 small-κ instruction to use `g=0, f_*=f`. Its omitted radius choice
  is supplied explicitly as r/2, preserving Lemma 2's `r ≤ 2ℓ/m` requirement. Case B does this.
- The blueprint's √n correction and κ = 2πKs follow the declared Euclidean/max-norm conversion
  and period-one convention. No source constant was silently reused under a changed norm.
- The design's previously unlisted real-Hessian restriction is genuinely proved in Hess:86;
  no K provider or frozen placeholder is imported to pay for it.

The core's unused hδ/hd0 are harmless redundant hypotheses; dropping them would be an optional
cleanup. No production edit is requested for seal readiness of this infrastructure API. Later
headline assembly, frozen provider equality, root closure, and global solution existence remain
outside S7-8. The statement packet's real-only Hessian source gap is not resolved by this package;
it explicitly requires a complex bound.

Only this exact worktree report is retained as an auditor edit. The pre-existing untracked
S7-8-handoff.md is preserved; auditor scratch is removed after checks. No state-changing git,
frozen edit, root regeneration, cache fetch, heartbeat override, or source repair was performed.

