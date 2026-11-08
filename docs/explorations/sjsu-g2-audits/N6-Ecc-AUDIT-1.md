Audited commit `945749ce63d9502ad36c8430c1ef28598a7e917a`; SHA256 (pinned files; .drafts inputs hashed as read): `KAM/EffectiveStability/SJSU/Ecc/Data.lean`=5eac0bd07ef1624ba85e8ba17d910d431f44ac97f48762d273defd3d6a0ad260; `KAM/EffectiveStability/SJSU/Ecc/Main.lean`=9a3849e94e40228d1dbc1d09a22066ac00897d0b8946ea5b20528c672ff6e32e; `KAM/EffectiveStability/SJSU/Ecc/Modes0.lean`=9c8ee48ff7bb389bcbf25b00a0c08102697adef8d6d2c4aa07c56016b5212a48; `KAM/EffectiveStability/SJSU/Ecc/Modes1.lean`=c07646f84e1e47ed4920695d0b665e2ca85d65fca99e2ab2109d130166ad2423; `KAM/EffectiveStability/SJSU/Ecc/TreeMM.lean`=950295723fc393878bf3774a8ad95b267531a41b26779a21020ad98bb8271449; `KAM/EffectiveStability/SJSU/Ecc/TreeMP.lean`=46c7a2d4bcd7b6300e10117126a6031474eba1535cd743843c76ecfc68badeec; `KAM/EffectiveStability/SJSU/Ecc/TreePM.lean`=180e1cb75e555553622888d8cb7b5c850c5a9096a77ca0364438dc4db8b8f4ad; `KAM/EffectiveStability/SJSU/Ecc/TreePP.lean`=9c3a6446b3277e54607973e7c76ed298fd2f7a5da01ba9683d73f8dcaf47004b; `KAM/EffectiveStability/Tube/Ecc/Center.lean`=7e469826845d988d430f3463809e891edeb61d431b94df37d5e21bbe0b30ed82; `KAM/EffectiveStability/Tube/Ecc/Circle.lean`=3d16215eae940a4adb3dbe7f484b7e78b043071864b00a1b3950e1d3149b5331; `KAM/EffectiveStability/Tube/Ecc/Defs.lean`=7533b6b4fbabb7ab7f34efbaf570560b6ca5c5e7af19d04bdfd93c00b5ed67d3; `KAM/EffectiveStability/Tube/Ecc/Gamma.lean`=36bad1f8fe37b36270aac0c86223b80b9cd46d6861da9548e8d2cb87e80c6fec; `KAM/EffectiveStability/Tube/Ecc/Sound.lean`=eff8e8fb3725c62667cac688f1e202232802460b1303b373ae8e0cfe8105305c; `docs/explorations/sjsu-g2-handoffs/N6-Ecc.md`=68f972bfe3160f852b0291b43e22475e4de90e17f8dbc5aea088a4fdf3d9a2e3; `.drafts/g2/BRIEF-N6-Ecc.md`=4b8d005d02964e6c8fc7ebdc9bd935ae9502af644192bff144dc0a85dbb0edd2; `.drafts/g2/data/literal-v1.json`=95b841cee81ef862a7bc7631b28c84eb387e04cb1505e8cc105fd2ce9b33306e; `applications/sjsu/data/sjsu18-o2.json`=702b0b3a3c7c713d48cc3044f90bd13795b79f255550275cc7937c5d8a067772; `docs/explorations/sjsu-g2-t2conf-proposal.md`=bb10fff984271f398baf149b964234779d126641f2f4d522b580ed8a5a9744f4; `docs/explorations/sjsu-g2-decisions.md`=fc420d8841fd99773093c7ececbbb59b3389ee8ccfe3da83cde8a5abfa1650d2; `KAM/Frozen/Planetary/Defs/OscillatorAction.lean`=ad724cd5e19a4d4d420c5e30fbcd9f656107affaefa62e9e76c82fa66a4447c5.

# N6-Ecc audit 1

**Verdict: PASS WITH NOTES.** At the pinned commit, the package proves owner ruling (a) on the entire closed tube: Jupiter `[0.026, 0.062]`, Saturn `[0.009, 0.085]`, Uranus `[0.006, 0.063]`. No mathematical, statement, data, rounding, coverage, or axiom defect was found. The two findings below concern the handoff's description of the evidence.

## Scope and authority

Focused, refute-first package audit, tier 2. Authority: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `.drafts/g2/WORKER-RULES.md`, `.drafts/g2/AUDIT-PKG-brief.md`, `.drafts/g2/BRIEF-N6-Ecc.md`, the launch instruction, and owner ruling (a). D76 is recorded at `docs/explorations/sjsu-g2-decisions.md:14` and adopts draft v2 of `docs/explorations/sjsu-g2-t2conf-proposal.md`.

The audited implementation is exactly the 13 Lean files in `KAM/EffectiveStability/Tube/Ecc/` and `KAM/EffectiveStability/SJSU/Ecc/` at `945749ce63d9502ad36c8430c1ef28598a7e917a`, together with its handoff. The first-line hashes are of that revision. All 13 working files were byte-identical when the snapshot and first checks ran.

At closeout the shared checkout's HEAD had advanced to `c2a92e9d1a00b5eda686e5e9345ac737d17c6329`. A final byte comparison against the original revision still confirmed all 13 package files unchanged except for the authorized pure rename below; the audit target was not moved.

During the audit the author renamed `SJSU.sjsuB` to `SJSU.sjsuEccCenter` in `SJSU/Ecc/Main.lean`. The user explicitly authorized treating this pure rename as outside the findings. A byte comparison confirmed that the working file was exactly the pinned file with every `sjsuB` replaced by `sjsuEccCenter`; no other bytes changed. Its observed successor hash was `92d46167cf971b4d7b81e3e7dce6981d992572ff58e416235c461607d4e6f338`. Line references below refer to the pinned revision, whose line numbering is preserved by that rename.

Only this report was retained by the auditor. The explicitly required transient Lean probe was created under `.drafts/g2/scratch/audit/` and removed after its contents and results were recorded here. No implementation, generator, frozen file, manifest, root, branch, or commit was changed by the auditor. Concurrent changes from other workers were left alone.

## Findings

### N1 — minor: the handoff overcounts the certificate blocks

Anchor: `docs/explorations/sjsu-g2-handoffs/N6-Ecc.md:29`, “900 leaves in **46 blocks** of ≤ 32 leaves”.

The actual trees contain 16 PP, 6 PM, 12 MP, and 8 MM block declarations: **42**, containing respectively 326, 154, 234, and 186 leaves: **900** in total. Suggested fix: change `46` to `42` in the handoff. No checker or certificate change is needed.

Refutation: counted the parsed tree block definitions independently of the handoff, then separately counted the `sjsuEccBlk*_ok` theorem declarations and `decide +kernel` commands. Both give `16 + 6 + 12 + 8 = 42`. **Survived; documentation only.**

### N2 — minor: phase-1 float estimates are described as true ranges

Anchor: `docs/explorations/sjsu-g2-handoffs/N6-Ecc.md:212`, “**The true ranges are phase 1's (see the brief).**”

The package brief explicitly labels those numbers “float evaluation ... NOT an interval enclosure”. The approved proposal, lines 52–56, likewise calls them “float estimates” and assigns their enclosure to N6. A successful enclosure proves the stated intervals; it does not prove that the phase-1 estimated extrema are the true extrema. Suggested fix: say “The tighter phase-1 ranges are numerical estimates; the certified enclosure is the one above.”

Refutation: checked whether a separate extremum theorem or exact phase-1 enclosure justified that sentence. The package proves containment, and the handoff's preceding table is an outward per-cell enclosure, not an extremum-attainment result. The brief and phase-1 gates explicitly deny rigorous enclosure status to the float ranges. **Survived; documentation only.** This does not affect the Lean theorem.

## Statements, hypotheses, and D76 correspondence

The source target is `I = B(φ) + v`, every `φ ∈ ℝ²`, every `|v_k| ≤ 2/10⁶`, and all three planet indices. `sjsu_tube_gamma` (`Main.lean:70`), `sjsu_tube_ecc` (`:91`), and `sjsu_tube_ecc_of_dev` (`:102`) have precisely that scope. They require neither a grid-phase assumption, a certificate from their caller, a nonzero-action premise, nor any eccentricity estimate as a hypothesis. `sjsu_tube_ecc_of_dev` supplies the tube premise by cancellation from `hv`.

The binder classification below expands the only project-owned premise (`hI`); `sjsuB` is its literal center definition, not an assumption package. Counts are per theorem; there are no additional instance binders.

| Theorem | Expanded binder | Bin | Authority |
|---|---|---|---|
| `sjsu_tube_gamma` | `φ : Fin 2 → ℝ` | TYPING | brief, whole phase torus via real representatives |
| same | `I : Fin 3 → ℝ` | TYPING | brief, three modal actions |
| same | `hI : ∀ k : Fin 3, abs (I k - tubeCenter sjsuEccModes sjsuEccIbar k φ) ≤ 2/10⁶` | SOURCE | brief, closed tube |
| same | `j : Fin 3` | TYPING | brief, J/S/U order |
| `sjsu_tube_ecc` | `φ : Fin 2 → ℝ` | TYPING | same |
| same | `I : Fin 3 → ℝ` | TYPING | same |
| same | `hI : ∀ k : Fin 3, abs (I k - tubeCenter sjsuEccModes sjsuEccIbar k φ) ≤ 2/10⁶` | SOURCE | same |
| same | `j : Fin 3` | TYPING | same |
| `sjsu_tube_ecc_of_dev` | `φ : Fin 2 → ℝ` | TYPING | same |
| same | `v : Fin 3 → ℝ` | TYPING | brief, deviations |
| same | `hv : ∀ k : Fin 3, abs (v k) ≤ 2/10⁶` | SOURCE | brief, closed deviation box |
| same | `j : Fin 3` | TYPING | same |

For each: SOURCE 1, STANDING 0, TYPING 3, RULED 0, EXCESS 0. Owner ruling (a) fixes the conclusion intervals. The `Fin 3` variables inside the universal premises are typing binders. The generic checker theorem has explicit computable global/tree checks as advertised in the brief; the SJSU theorems discharge them in their proofs using `sjsuEcc_globalOK` and `sjsuEccTrees_ok`. They are not passed on as hypotheses.

Definitions: **BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.** This covers `modeK`, `tubeCenter`, `eccGamma`, the SJSU center, the literal data, and `sjsuLambdaStar`. The Gaussian and checker definitions were checked through their defining equations and soundness proofs as described below. No characterized object or arbitrary choice construction is involved.

Independent normalization check:

* Differentiating `S = Σ_m i σ_m exp(i m·φ)` gives coefficient `-m_k σ_m`; `m_3 = -m_1-m_2`. Both signs and the use of **all** positive and negative mode rows match `literal-v1.json`'s `doc` and `Defs.lean:39`.
* `eccGamma` (`Defs.lean:45`) is the sum of squares of the real and imaginary parts of `Σ_k V′_jk √I_k exp(i q_k)`, `q = (φ₀,φ₁,0)`. `eccGamma_eq_normSq` (`Sound.lean:269`) proves this exact identity.
* `eccGamma_phase` (`Sound.lean:281`) removes a common absolute angle by `φ = (θ₀-θ₂, θ₁-θ₂)`; the proof uses the angle addition formulas and `sin² θ₂ + cos² θ₂ = 1`. No `Complex.arg` branch or chosen fundamental domain is used by N6.
* D76 uses `z = (ξ-iη)/√2`, so `normSq z = (ξ²+η²)/2`. The frozen definition `KAM/Frozen/Planetary/Defs/OscillatorAction.lean:37` is exactly `(p_j²+q_j²)/2`. Hence N6's `Γ = normSq z` has the correct factor, and its formula `√(1-(1-Γ/Λ*)²)` is exactly D76's fixed-reference secular-model eccentricity. The minus sign on `iη` does not change `normSq`. There is no replacement by `√(2Γ/Λ*)` or by osculating eccentricity.
* `sjsu_ecc_conditions` (`Main.lean:79`) establishes positive `Λ*`, `Γ_hi < Λ*`, and the rational square comparisons at the literal interval endpoints. `ecc_bounds_of_gamma` (`Gamma.lean:201`) uses these to control `1-Γ/Λ*` on its nonnegative branch. The six endpoints and all three reference actions match the approved proposal verbatim.

Fresh Lean exact-type applications checked both the action and deviation formulations, using the literal center and literal `Λ*` values, and checked the defining equation of `eccGamma` by `rfl`.

**Consumer boundary:** this is a complete N6 tube-enclosure result, not a proof of the D76 confinement theorem. N5 must still supply its actual point's tube membership and identify its coordinate/center functions with these definitions. The handoff explicitly assigns that connection to N5 (`:102–107`, `:228–230`); N6 does not assume it. No N5/N7 theorem or sealing claim is certified by this audit.

## Proof audit: chart coverage and cell linearization

**Coverage passes.** `wt t = (1+it)/(1-it)` has no real pole. `wt_of_cos_nonneg` (`Circle.lean:352`) represents a unit point `(c,y)` with `c ≥ 0` by `t=y/(1+c) ∈ [-1,1]`. `exists_circ` (`:367`) applies that construction either to `(cos φ,sin φ)` or its negative. In particular, the former chart's missing point `-1` is the other chart at `t=0`; `±i` are included at the parameter endpoints. The product of the two sign choices covers all phases. `checkTree_sound` (`Sound.lean:249`) branches at the midpoint with `≤` on one side and `>` implying `≥` on the other, and carries the unchanged coordinate bounds. Thus there are no missing edges, corners, or split boundaries.

The independent source parser also checked every actual tree's midpoint partition of `[-1,1]²`: exact area 4 for each root, with 326/154/234/186 leaves and maximum depths 11/9/10/10. Area was only a supplementary check: coverage follows from the full binary split structure and the theorem, not from area equality alone.

**Chart remainder passes.** At `c`, `D = ±2i/(1-ic)²`. With `A=1-it`, `B=1-ic`, the exact remainder is `±2(B-A)²/(A B²)`. Since `abs A ≥ 1` and `abs B² = 1+c²`, its norm is at most `2(t-c)²/(1+c²)`. `norm_circ_remainder` (`Circle.lean:289`) proves that identity and bound. Adding the derivative norm gives `2h(1+h)/(1+c²)` for the chord. `cell_geom` substitutes the full closed cell's half-width; no Hessian bound on the center is silently assumed.

**Cell estimate passes.** Independently expand, with `sc=(sl+sh)/2`, `ds=(sh-sl)/2`,

```text
δ = z-zc = Σ_k V_k (s_k-sc_k) P_k + Σ_{a=0,1} V_a s_a (w_a-P_a), P_2=1.
w_a-P_a = x_a D_a + ρ_a.
```

The second sum uses the actual `s_a`, bounded by `sh_a`; it retains the mixed action/angle contribution. The support bound on `abs Re(zc conj δ)` is exactly `E` from `zErr`, and the triangle bound on `norm δ` is exactly `R` from `zRad`. Consequently `normSq z ≤ G+2E+R²`. For the lower bound, `Re(zc conj z) ≥ G-E ≥ 0` and Cauchy–Schwarz imply `(G-E)² ≤ G normSq z`. `gammaOK` explicitly checks `G>0`, `E≤G`, and `Glo G≤(G-E)²`; dividing by positive `G` is sound. These are the inequalities proved in `normSq_bounds_of_cell` (`Gamma.lean:46`) and consumed in `cellZOK_sound` (`Sound.lean:151`).

The square-root check includes nonnegative endpoints and square comparisons on both sides of the full center error plus radius. It bounds every `√I_k`, not just box vertices. The actual 900 leaves also have strictly positive lower action bounds; the minimum independently certified bounds, shown approximately, are `(2.83374683559e-4, 6.42008423824e-4, 2.23239031245e-5)`. Thus totalized real square roots do not conceal negative-action or vacuous-domain behavior in this instance.

## Proof audit: rounding and literal data

**All literal comparisons pass.** A Python standard-library parser, independent of the author's generator and pickle, read the actual Lean data rows and compared `Fraction` values against the JSON. All 2,790 `(m₁,m₂,σ)` triples agree in file order, and their indices are exactly the nonzero hexagon `abs m₁+abs m₂+abs(m₁+m₂)≤60`. The three `Ibar` entries, nine `Vprime_exact` entries, and three `Lambda_star` decimal strings all agree exactly. The radius is exactly the JSON's `kappa * delta = 2/10⁶`.

**No coefficient is dropped without a bound.** `fixOf` selects 130 nonzero truncations at scale `2^48`; both fixed indices are bounded by 7. `errSum` ranges over all 2,790 exact rows, including those truncating to zero. Independently computed sums and their checked caps are:

| k | rounding sum (approximate display) | exact rational cap, displayed as decimal |
|---|---:|---:|
| 0 | `8.16866746792e-13` | `8.169e-13` |
| 1 | `1.10243542212e-12` | `1.103e-12` |
| 2 | `8.85008990709e-13` | `8.851e-13` |

The two Lipschitz vectors are approximately `(2.65175546850e-5, 2.52926170242e-5, 1.40973435065e-6)` and `(2.52926170242e-5, 2.88613434505e-5, 3.79323664939e-6)`; each component is below its exact rational cap in `sjsuEccData`.

`treeSum_eq` proves that the balanced evaluation is the entire list sum. `abs_tubeCenterW_sub_fix_le` (`Center.lean:246`) charges exactly the above rounding error at unit points; `abs_tubeCenterW_sub_le` (`:184`) controls the movement of the **exact** modes, including negative powers. `GZ.toC_zpowT` (`Circle.lean:156`) handles negative powers by conjugation, with the explicit index bounds preventing an out-of-range table default. `circN_pos` excludes denominator zero. `bSumZ_div_eq` (`Center.lean:277`) restores the exact scale `2^K N₁^M N₂^M`. Together `cellCenter_close` (`Sound.lean:104`) yields the full `ε₁ L₁ + ε₂ L₂ + τ` bound. The center is never replaced in the public theorem by its 130-mode approximation.

The independent parser expanded all actual Lean tree definitions and replayed every leaf using exact `Fraction` arithmetic. All 900 passed all square-root and gamma comparisons. Its worst-leaf gamma bounds reproduce the handoff:

| planet | lower bound (approximate display) | upper bound (approximate display) |
|---|---:|---:|
| J | `0.000182557599687` | `0.00103746676114` |
| S | `8.88473369375e-6` | `0.000792701234225` |
| U | `8.70395538226e-7` | `9.42988691678e-5` |

All acceptance comparisons used exact fractions; decimal displays above were produced only after the comparisons. Float-guided certificate generation is outside the trust boundary: the generic theorem and kernel checks validate the resulting certificates.

## Verification

The following single targeted invocation explicitly named every package module, including all application modules, through the required serialized wrapper:

```sh
.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Ecc.Circle KAM.EffectiveStability.Tube.Ecc.Defs KAM.EffectiveStability.Tube.Ecc.Center KAM.EffectiveStability.Tube.Ecc.Gamma KAM.EffectiveStability.Tube.Ecc.Sound KAM.EffectiveStability.SJSU.Ecc.Modes0 KAM.EffectiveStability.SJSU.Ecc.Modes1 KAM.EffectiveStability.SJSU.Ecc.Data KAM.EffectiveStability.SJSU.Ecc.TreePP KAM.EffectiveStability.SJSU.Ecc.TreePM KAM.EffectiveStability.SJSU.Ecc.TreeMP KAM.EffectiveStability.SJSU.Ecc.TreeMM KAM.EffectiveStability.SJSU.Ecc.Main
```

Exit 0; exact output: `Build completed successfully (2190 jobs).` This invocation reused the existing build cache; it does not independently remeasure the author's reported four CPU-minutes or peak memory. No clean, rebuild of Mathlib, library-wide build, option override, or parallel Lean process was launched by the auditor.

```sh
.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/N6-Ecc-AUDIT-1.lean
```

Exit 0. All 24 printed axiom lists were exactly `[propext, Classical.choice, Quot.sound]`, for these fully qualified exports (prefix `KAM.EffectiveStability.`):

```text
Tube.exists_circ
Tube.norm_circ_remainder
Tube.norm_circ_sub
Tube.GZ.toC_zpowT
Tube.abs_tubeCenterW_sub_le
Tube.abs_tubeCenterW_sub_fix_le
Tube.bSumZ_div_eq
Tube.normSq_bounds_of_cell
Tube.leafOK_sound
Tube.checkTree_sound
Tube.eccGamma_eq_normSq
Tube.eccGamma_phase
Tube.eccGamma_bounds_of_check
Tube.ecc_bounds_of_gamma
SJSU.sjsuEcc_globalOK
SJSU.sjsuEccTreePP_ok
SJSU.sjsuEccTreePM_ok
SJSU.sjsuEccTreeMP_ok
SJSU.sjsuEccTreeMM_ok
SJSU.sjsuEccTrees_ok
SJSU.sjsu_ecc_conditions
SJSU.sjsu_tube_gamma
SJSU.sjsu_tube_ecc
SJSU.sjsu_tube_ecc_of_dev
```

For example, the exact final theorem output was:

```text
'KAM.EffectiveStability.SJSU.sjsu_tube_ecc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same probe also compiled the three exact-type checks recorded in Appendix A. The first build validated byte-identical pinned sources. The axiom probe uses an explicit center formula, avoiding ambiguity with N5a's differently curried `sjsuB`; its checks are valid under the authorized pure rename as well.

Mechanical source checks: `wc -l KAM/EffectiveStability/Tube/Ecc/*.lean KAM/EffectiveStability/SJSU/Ecc/*.lean` gives 8,121 lines in total, individual counts `325,383,288,223,315; 211,114,1426,1426,699,901,559,1251` in that glob order. The maximum is 1,426. The package-only command below produced no matches (exit 1):

```sh
rg -n '\b(sorry|admit|axiom|unsafe|opaque|set_option|native_decide|EuclideanSpace)\b' KAM/EffectiveStability/Tube/Ecc KAM/EffectiveStability/SJSU/Ecc
```

Every file has its copyright header, `module`, public imports, module docstring, exposed definitions through its section attribute, and public section. No forbidden metaprogramming or provider imports were found. A separate check of the pinned Git bytes confirmed that all 13 modules satisfy these header/size/forbidden-word checks and have no non-import line longer than 100 characters.

```sh
.drafts/g2/lint_noabi.sh
```

Run once, as required by the worker rules' 15:25 UTC amendment; **exit 1**. `abi_hashes` was deliberately skipped, and the full `scripts/lint_sources.sh` was not run. Relevant exact output excerpts:

```text
Lean lines over 100 characters:
/mnt/HC_Volume_106379410/kam-sjsu-g2/KAM/EffectiveStability/SJSU/Ecc/Main.lean:70:106
/mnt/HC_Volume_106379410/kam-sjsu-g2/KAM/EffectiveStability/SJSU/Ecc/Main.lean:91:104
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (18399 Lean files, 0 comparator configurations)
Ran 29 tests in 4.682s
OK
Ran 8 tests in 0.008s
OK
FROZEN-ANCHOR GUARD OK
```

The excerpt omits other workers' overlong-line diagnostics in `SJSU/Ham/`, `SJSU/Model/`, `Tube/Engine/`, and `Tube/Poly/`. The two live Ecc diagnostics arise solely from the explicitly authorized post-snapshot rename (longer identifier); they are not findings against `945749ce6`. The pinned N6 files have no overlong lines, as checked separately. Generated roots are outside this auditor's write authority and were not regenerated. There were no forbidden-proof, oversized-file, module-header, or frozen-anchor failures. The global lint exit is recorded as a shared-worktree integration exception, not a package-mathematics PASS for the entire worktree.

## Limits, decisions, and closeout

The adaptive rational-chart partition and first-order center Lipschitz estimate differ from the brief's suggested uniform Hessian grid. The design was explicitly left to the author, the chart remainder is second order, and the complete inequalities are proved and checked; this is an acceptable documented design choice. The 130 fixed-point modes are likewise an implementation choice with the full omitted-mode error paid.

Application routing is an orchestrator integration task: the handoff (`:189–190`) already says a `KAMSJSU` prefix is needed in `scripts/build_roots.json`. At the audited revision that registration is not yet present. This audit built SJSU/Ecc only by explicit module names as instructed. It does not approve adding those modules to the generated core roots or claim that the final application library is registered.

No suspected defect in the pinned mathematical source was found. N1 and N2 are handoff deviations from the actual implementation/evidence and are reported for the orchestrator; no repair was made. The authorized pure center rename is not a finding. All requested mathematical checks are complete within the N6 scope; final N5 consumption, D76 theorem closure/sealing, fresh kernel replay of all cached artifacts, and independent performance benchmarking are outside this package audit.

## Appendix A: exact-type checks in the transient probe

The probe imported `KAM.EffectiveStability.SJSU.Ecc.Main`, opened `KAM.EffectiveStability.Tube` and `KAM.EffectiveStability.SJSU`, issued the 24 `#print axioms` commands listed above, then compiled:

```lean
example (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ)
    (hI : ∀ k, |I k - tubeCenter sjsuEccModes sjsuEccIbar k φ| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    ![0.026, 0.009, 0.006] j ≤
      Real.sqrt (1 - (1 - eccGamma sjsuEccV I φ j /
        ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
          4.7474331515411474555e-2] j) ^ 2) ∧
      Real.sqrt (1 - (1 - eccGamma sjsuEccV I φ j /
        ![5.3993226066969503769e-1, 2.1912825008425995084e-1,
          4.7474331515411474555e-2] j) ^ 2) ≤ ![0.062, 0.085, 0.063] j :=
  sjsu_tube_ecc φ I hI j

example (φ : Fin 2 → ℝ) (v : Fin 3 → ℝ) (hv : ∀ k, |v k| ≤ 2 / 10 ^ 6)
    (j : Fin 3) :
    ![0.026, 0.009, 0.006] j ≤
      Real.sqrt (1 - (1 - eccGamma sjsuEccV
        (fun k => tubeCenter sjsuEccModes sjsuEccIbar k φ + v k) φ j / sjsuLambdaStar j) ^ 2) ∧
      Real.sqrt (1 - (1 - eccGamma sjsuEccV
        (fun k => tubeCenter sjsuEccModes sjsuEccIbar k φ + v k) φ j / sjsuLambdaStar j) ^ 2) ≤
        ![0.062, 0.085, 0.063] j :=
  sjsu_tube_ecc_of_dev φ v hv j

example (V : Fin 3 → Fin 3 → ℚ) (I : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) :
    eccGamma V I φ j =
      (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.cos (![φ 0, φ 1, 0] k)) ^ 2 +
      (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.sin (![φ 0, φ 1, 0] k)) ^ 2 := rfl
```

## Appendix B: reproducible independent data and leaf check

This is a standalone Python standard-library check. It reads the pinned Lean bytes directly from Git, never imports the author's generator, and never reads `trees.pkl`. To reproduce from this worktree:

```sh
python3 - <<'PY'
from pathlib import Path
report = Path('docs/explorations/sjsu-g2-audits/N6-Ecc-AUDIT-1.md').read_text()
code = report.split('```python\n', 1)[1].split('\n```', 1)[0]
exec(compile(code, '<N6-Ecc audit independent checker>', 'exec'))
PY
```

```python
from pathlib import Path
from fractions import Fraction as F
import subprocess, re, json, hashlib
REV = '945749ce63d9502ad36c8430c1ef28598a7e917a'
BASE = 'KAM/EffectiveStability/SJSU/Ecc/'
def src(name):
    return subprocess.check_output(['git', 'show', REV+':'+BASE+name+'.lean']).decode()
def checked_json(path, sha):
    b = Path(path).read_bytes()
    assert hashlib.sha256(b).hexdigest() == sha
    return json.loads(b)
d = checked_json('.drafts/g2/data/literal-v1.json',
    '95b841cee81ef862a7bc7631b28c84eb387e04cb1505e8cc105fd2ce9b33306e')
p = checked_json('applications/sjsu/data/sjsu18-o2.json',
    '702b0b3a3c7c713d48cc3044f90bd13795b79f255550275cc7937c5d8a067772')
rows = []
for part in ['Modes0', 'Modes1']:
    body = src(part).split('def sjsuEcc'+part, 1)[1]
    for line in body.splitlines():
        if line.strip().startswith('dyMode '):
            m,n,a,e = map(int, re.findall(r'-?\d+', line))
            rows.append((m,n,F(a,2**e)))
assert rows == [(*map(int,k.split(',')),F(v)) for k,v in d['sigma'].items()]
assert len(rows) == 2790
assert {(m,n) for m,n,_ in rows} == {(m,n) for m in range(-30,31)
    for n in range(-30,31) if 0 < abs(m)+abs(n)+abs(m+n) <= 60}
s = src('Data')
def rats(t):
    return [F(int(a),int(b)) for a,b in re.findall(r'\((-?\d+) / (\d+) : ℚ\)',t)]
def definition(name): return s.split('def '+name,1)[1].split('/--',1)[0]
ib = rats(definition('sjsuEccIbar')); vf = rats(definition('sjsuEccV'))
assert ib == list(map(F,d['Ibar']))
assert vf == [F(x) for row in d['Vprime_exact'] for x in row]
V = [vf[i:i+3] for i in range(0,9,3)]
ls = re.findall(r'\d+\.\d+e-\d+',
    src('Main').split('def sjsuLambdaStar',1)[1].split('/--',1)[0])
assert ls == p['parameters']['Lambda_star']; lam = list(map(F,ls))
fix = [tuple(map(int,x)) for x in re.findall(r'\((-?\d+), (-?\d+), (-?\d+)\)',
    definition('sjsuEccFix'))]
def trunc(x): return (1 if x>=0 else -1)*(abs(x.numerator)//x.denominator)
assert fix == [(m,n,trunc(a*2**48)) for m,n,a in rows if trunc(a*2**48)]
assert len(fix)==130 and max(max(abs(m),abs(n)) for m,n,_ in fix)==7
assert all('  '+k+' := '+str(v) in s for k,v in [('K',48),('PS',48),('M',7)])
fields = {}
for name in ['r','L₁','L₂','tau','Glo','Ghi']:
    tail = s.split('  '+name+' :=',1)[1]
    fields[name] = rats(tail.split('  Glo :=',1)[0] if name=='tau'
        else tail.split('\n  ',1)[0])
assert fields['r'] == [F(d['delta'])*F(d['kappa'])] == [F(2,10**6)]
def mk(m,n,k): return (m,n,-m-n)[k]
err = [sum(abs(mk(m,n,k))*abs(a-F(trunc(a*2**48),2**48))
    for m,n,a in rows) for k in range(3)]
lip = [[sum(abs(mk(m,n,k)*a)*abs((m,n)[axis]) for m,n,a in rows)
    for k in range(3)] for axis in range(2)]
assert all(err[k]<=fields['tau'][k] for k in range(3))
assert all(lip[a][k]<=fields[['L₁','L₂'][a]][k] for a in range(2) for k in range(3))
lo=list(map(F,['.026','.009','.006'])); hi=list(map(F,['.062','.085','.063']))
for j in range(3):
    gl,gh=fields['Glo'][j],fields['Ghi'][j]; L=lam[j]
    assert 0<gl<=gh<L and (1-gl/L)**2<=1-lo[j]**2 and 1-hi[j]**2<=(1-gh/L)**2
print('LITERAL_DATA_AND_GLOBAL_CHECKS: PASS (2790 exact modes, 130 fixed modes)')
def expr(tok,i,defs):
    if tok[i]=='(':
        t,i=expr(tok,i+1,defs); assert tok[i]==')'; return t,i+1
    head=tok[i]; i+=1
    if head=='leaf': return ('leaf',tuple(map(int,tok[i:i+9]))),i+9
    if head=='split':
        ax=int(tok[i]=='true'); a,i=expr(tok,i+1,defs); b,i=expr(tok,i,defs)
        return ('split',ax,a,b),i
    return defs[head],i
leaves=[]; block_counts=[]
for suffix in ['PP','PM','MP','MM']:
    text=src('Tree'+suffix); defs={}
    for match in re.finditer(r'^def (sjsuEcc(?:Blk\w+|Tree\w+)) : ETree :=\n(.*?)'
        r'(?=\n(?:theorem |/--))',text,re.M|re.S):
        name,body=match.groups(); tok=re.findall(r'\(|\)|\w+',body)
        t,i=expr(tok,0,defs); assert i==len(tok); defs[name]=t
    signs=tuple(1 if c=='P' else -1 for c in suffix)
    def visit(t,box,depth=0):
        if t[0]=='leaf':
            leaves.append((signs,box,t[1]))
            return 1,depth,(box[1]-box[0])*(box[3]-box[2])
        _,ax,l,r=t; a,b,c,e=box; mid=(a+b)/2 if ax==0 else (c+e)/2
        lb=(a,mid,c,e) if ax==0 else (a,b,c,mid)
        rb=(mid,b,c,e) if ax==0 else (a,b,mid,e)
        nl,dl,al=visit(l,lb,depth+1); nr,dr,ar=visit(r,rb,depth+1)
        return nl+nr,max(dl,dr),al+ar
    n,depth,area=visit(defs['sjsuEccTree'+suffix],(F(-1),F(1),F(-1),F(1)))
    assert area==4
    blocks=sum('Blk' in name for name in defs); block_counts.append(blocks)
    assert blocks==len(re.findall(r'^theorem sjsuEccBlk\w+_ok',text,re.M))
    assert blocks==len(re.findall(r'^  decide \+kernel$',text,re.M))
    print('TREE',suffix,'leaves',n,'blocks',blocks,'maxdepth',depth,'area',area)
assert len(leaves)==900 and sum(block_counts)==42
def mul(a,b): return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def power(p,m):
    if m<0: p=(p[0],-p[1]); m=-m
    z=(F(1),F(0))
    for _ in range(m): z=mul(z,p)
    return z
minI=[None]*3; worstlo=[None]*3; worsthi=[None]*3
for signs,box,cert in leaves:
    P=[]; D=[]; hh=[]; eps=[]; rho=[]
    for sign,(a,b) in zip(signs,[(box[0],box[1]),(box[2],box[3])]):
        c=(a+b)/2; h=(b-a)/2; den=1+c*c
        P.append((sign*(1-c*c)/den,sign*2*c/den))
        D.append((-sign*4*c/den**2,sign*2*(1-c*c)/den**2))
        hh.append(h); eps.append(2*h*(1+h)/den); rho.append(2*h*h/den)
    pw=[{m:power(p,m) for m in range(-7,8)} for p in P]; bc=ib.copy()
    for m,n,a in fix:
        v=mul(pw[0][m],pw[1][n])[0]
        for k in range(3): bc[k]-=F(mk(m,n,k)*a,2**48)*v
    sl=[F(x,2**48) for x in cert[:3]]; sh=[F(x,2**48) for x in cert[3:6]]
    Z=[F(x,2**48) for x in cert[6:]]
    for k in range(3):
        eta=eps[0]*fields['L₁'][k]+eps[1]*fields['L₂'][k]+fields['tau'][k]
        il=bc[k]-eta-fields['r'][0]; iu=bc[k]+eta+fields['r'][0]
        assert 0<sl[k] and sl[k]**2<=il and 0<=sh[k] and iu<=sh[k]**2
        minI[k]=il if minI[k] is None else min(minI[k],il)
    sc=[(a+b)/2 for a,b in zip(sl,sh)]; ds=[(b-a)/2 for a,b in zip(sl,sh)]
    P.append((F(1),F(0)))
    for j in range(3):
        z=tuple(sum(V[j][k]*sc[k]*P[k][a] for k in range(3)) for a in range(2))
        G=sum(x*x for x in z)
        def dot(p): return sum(a*b for a,b in zip(z,p))
        E=sum(abs(V[j][k])*ds[k]*abs(dot(P[k])) for k in range(3))
        E+=sum(abs(V[j][a])*sh[a]*(hh[a]*abs(dot(D[a]))+Z[j]*rho[a]) for a in range(2))
        R=sum(abs(V[j][k])*ds[k] for k in range(3))
        R+=sum(abs(V[j][a])*sh[a]*eps[a] for a in range(2))
        assert 0<=Z[j] and G<=Z[j]**2 and G+2*E+R**2<=fields['Ghi'][j]
        assert 0<G and E<=G and fields['Glo'][j]*G<=(G-E)**2
        l=(G-E)**2/G; u=G+2*E+R**2
        worstlo[j]=l if worstlo[j] is None else min(worstlo[j],l)
        worsthi[j]=u if worsthi[j] is None else max(worsthi[j],u)
print('LEAF_REPLAY: PASS (900 leaves; all comparisons exact)')
for label,xs in [('MIN_ACTION',minI),('GAMMA_LO',worstlo),('GAMMA_HI',worsthi)]:
    print(label,[format(float(x),'.12g') for x in xs])
```

Exit 0; exact output:

```text
LITERAL_DATA_AND_GLOBAL_CHECKS: PASS (2790 exact modes, 130 fixed modes)
TREE PP leaves 326 blocks 16 maxdepth 11 area 4
TREE PM leaves 154 blocks 6 maxdepth 9 area 4
TREE MP leaves 234 blocks 12 maxdepth 10 area 4
TREE MM leaves 186 blocks 8 maxdepth 10 area 4
LEAF_REPLAY: PASS (900 leaves; all comparisons exact)
MIN_ACTION ['0.000283374683559', '0.000642008423824', '2.23239031245e-05']
GAMMA_LO ['0.000182557599687', '8.88473369375e-06', '8.70395538226e-07']
GAMMA_HI ['0.00103746676114', '0.000792701234225', '9.42988691678e-05']
```

READY g2-audit-n6-1
