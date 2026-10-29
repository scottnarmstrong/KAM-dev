# N11-F1 independent package audit 1 (Composition / Transform, blueprint-N Part 11b)

**Verdict: FAIL.** The cause is naming hygiene (audit focus (d)), not mathematics.

- Mathematically the package passes.
  - All six signed declarations match the signature file.
  - `extFlow` is imported from `ExtFlow.lean`, not redefined.
  - Every graph node mapped to these modules is established.
  - No premise is added.
  - No `sorry`, `axiom`, `admit` or heartbeat option appears, and every line is ≤ 100 columns.
- It fails rule (d): 21 unsigned public helpers reuse short names already declared elsewhere in KAM (F1-1, F1-2).
  - Campaign precedent: N11-B audit-1 failed on the same rule, and ruling 18:50 exempts only signed names.
  - The handoff's claim that the helpers were "grepped unique" is false.
- The fix is a mechanical rename or privatization with no statement change. A delta round-2 audit can be limited
  to that rename plus a gate build.

| Result | Verdict |
|---|---|
| (a) Signed declarations = signature file | PASS (7/7; `transform_integral` differs only in its line wrapping and the `Set.Icc` qualifier, so it elaborates to the same term) |
| (b) Slice complete (node table) | PASS (all 6 nodes) |
| (c) Proof soundness, no added premises | PASS (static review; not compiled here) |
| (d) Hygiene | **FAIL**. The short-name rule fails (F1-1, F1-2). No EuclideanSpace, no harmful root shadow, lines ≤ 100, no sorry/axiom/admit/maxHeartbeats |
| Duplication across Partial modules | No duplicate of a signed declaration. Private and helper duplicates are recorded in F1-3 |

## Scope and inputs

This audit is static and read-only. Lean cannot run on this machine, so nothing was compiled.

- **Not re-verified:** the "compiles clean" status and the axiom lists come from the prover handoff.
- **Files audited:** only `KAM/Nekhoroshev/Partial/{Composition,CompositionCoeff,Transform,TransformIntegral}.lean`.
- **Checkout:** `lane-n-handoff`, HEAD `89d9eca2ee2efe081d087d25afa796c73982c36b`.
- **Signed text:** compared by a whitespace-normalized mechanical diff.
- **Short names:** a declaration indexer was run over all 11,959 KAM declarations, including structure fields.

| Input | SHA-256 |
|---|---|
| Composition.lean (590 lines) | `abef1dbe20b99b32c8c4e86d423de3252214d7ca61de400d08084bee22fa4643` |
| CompositionCoeff.lean (218) | `f699cba11d4bf2bd2a7b0272e47639990d358d055ba193b2fad7be6fa0561e16` |
| Transform.lean (380) | `54504ae7526f9ba8b14bfd6bb98b8fa35b52d251bb6974ff5088569f4d1dafc2` |
| TransformIntegral.lean (315) | `545195acfb97de26ef276e71fbc58f318bce72e03ef5fc2fff8e12653d252d98` |
| ExtFlow.lean (F2, imported) | `7f1b71ffd5b6175085ef042357de276b736b35172ccb794c149a0397d121d435` |
| N11Sig-zohar.lean (authoritative) | `a70ec4d6b7036e98453b49d2710b2f4b6945fc08e1d5b4ecd4cb7899ea298c22` |
| N11-LEAN-DESIGN.md | `f48f720851c9b81326f9f6a24d5a42c8346283c41cf1d6a48285ce0e311fdafb` |
| p11b-partial-nf.tex | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |

The authoritative signature file differs from the tracked `docs/tracks/N/design/N11-SIGNATURES.md` only in
`iterative`, which gains `(hc : 0 < b.c)` (ruling F2-C1). None of the F1 declarations is affected.

## (a) Signed declarations

| Signed declaration | Signature file | Module | Equal? |
|---|---|---|---|
| `structure ExtCompose` (11 fields + docstring) | L247–259 | Composition.lean:49–61 | PASS (exact) |
| `def extFlow` | L261–262 | ExtFlow.lean:27–28 (imported publicly by Composition.lean:13; **not** redefined in F1) | PASS (exact) |
| `theorem composition_domain` (+ docstring) | L781–787 | Composition.lean:182–188 | PASS (exact) |
| `theorem composition` | L264–275 | Composition.lean:519–530 | PASS (exact) |
| `theorem composition_real` | L789–792 | Composition.lean:549–552 | PASS (exact) |
| `theorem transform` | L277–288 | Transform.lean:329–340 | PASS (exact) |
| `theorem transform_integral` (+ docstring) | L290–299 | Transform.lean:365–375 | PASS. The text differs only by `Icc` → `Set.Icc` (L368–372) and the wrapping of the 104-column `hdcont` line (L371–372). Transform.lean opens both `Set` and `Finset`, so the `Set.` qualifier is needed; the elaborated term is the same (F1-7) |

## (b) Node coverage

Sources: design node table L197–L208 and blueprint p11b L88–106.

| Graph node | Lean declaration(s) | Result | Reason |
|---|---|---|---|
| `bpN:p11:composition` | `composition_domain`, `composition`, `composition_real` (signed) | PASS | **(i)** `composition_domain`.1: ν(X^c_φ) ≤ V/(ρσ) = η/2 on Ω = 𝒟_{R'-ρ,s'-σ}. `ExtCompose.eta_half`: η/2 ≤ 1/4. `composition_domain`.2: X^t z ∈ 𝒟_{R-(1-η/2)ρ, s-(1-η/2)σ}. `ExtCompose.tube_sub`: that set lies in 𝒟_{R,s}. `ExtCompose.gaugeInterior_half`: 𝒟_{R-ρ,s-σ} ⊂ Ω^{1/2}. Holomorphy of X^t on Ω^{1/2} is `KAM.Canonical.flow_b` and is used in the proof (TransformIntegral.lean:83–88).<br>**(ii)** `composition`.3 gives HasSum, `composition`.4 gives norm convergence, and `composition`.2 at t = 1 gives the bound (1-η)⁻¹U.<br>**(iii)** Class and bound for X^t with \|t\|η come from `composition`.2. The X^t series is `ExtCompose.flow_series` (Transform.lean:93).<br>**(iv)** `composition_real` |
| `stepN:p11:co-field` | `ExtCompose.field_bound`, `smallField`, `gaugeInterior_half`, `composition_domain` | PASS | `vf` with losses (ρ,σ), the gauge identity `norm_extGauge`, and `flow_a` (a) |
| `stepN:p11:co-series` | `ExtCompose.lieTerm_bound`, `lieSeries_summable/class/bound/tail` | PASS | `adjoint` term bounds (e²η/8)^j U. `q_facts_ext` gives q ≤ η and q < 1. Uniform limit via `uniform_limit_holomorphic`, periodicity by tsum_congr, weighted bound via `wbound_tsum_ext` |
| `stepN:p11:co-remainder` | `ExtCompose.extAd_traj_bound`, `series_eq`, `hasSum_pt` | PASS | It uses fixed losses (3ρ/4, 3σ/4) in place of the blueprint's (1-ε)ρ, (1-ε)σ, which is valid because ε ≤ 1/4. SL is preserved, η̂ = 16η/9 ≤ 8/9 and q̂ < 1. `ext_taylor` with `ext_taylor_bound` on Ω = 𝒟_{R,s} gives remainder → 0 and `tendsto_nhds_unique` |
| `bpN:p11:ext-e-upper` | `Real.exp_one_lt_d9` | PASS | Used at Composition.lean:120 (`exp_one_bounds`). It gives e² < 7.4 in `q_facts_ext` (L126) |
| `bpN:p11:transform` | `transform`, `transform_integral` (signed) | PASS | The identity, R ∈ 𝒪_{R-ρ,s-σ} and \|R\| ≤ η/(1-η)(W/2+U) come from `transform`. The integral clause (G ∈ 𝒪_{R-ρ,s-σ}, \|G\| ≤ (1-η)⁻¹U) is `transform_integral` |
| `stepN:p11:tr-taylor` | `ext_taylor_second` (E2, Lie.lean:200) inside `transform` (Transform.lean:344–349); series form via `transform_identity`, `extRemSeries_*` | PASS | It matches the blueprint recipe exactly: Ω = 𝒟_{R,s}, γ(t) = X^t z, solution and γ 0 = z from `traj_solution` (composition (i) + `tube_sub`), and h, f, φ holomorphic on 𝒟_{R,s}. The series form takes a different route: `ext_taylor` with N = 1 gives h∘X¹ = h + ∫ w∘X^t, then the Lie series of w∘X^t is integrated termwise (`integral_flow_hasSum`). The blueprint instead uses an N-th remainder for h. The result is the same, Σ_{j≥1}(ad^j w/(j+1)! + ad^j f/j!) |
| `stepN:p11:tr-int` | `ExtCompose.integral_inClass`, `integral_bound`, `paramHyp_integrand`, `coeff_integral_ext` | PASS | Holomorphy comes from `ParamHyp.intervalIntegral`, periodicity from `flow_d` translation covariance, and Fubini on [0,1]×[0,1]ⁿ gives the coefficients. The slice bound is (1-\|t\|η)⁻¹U ≤ (1-η)⁻¹U by composition (iii) |

**Consumer check for the narrowing in signed `composition`.**

What the signature leaves out:

- (i) does not export holomorphy of X^t.
- (iii) exports only the class and the bound, not the X^t series.

What `iterative` (N11-H) needs, per blueprint L136–139:

- **it-taylor.** `transform` with `ExtCompose b R s (R-ρ) (s-σ) ρ σ V φ`. Admissible from 2ρ < R and 2σ < s. Its X is
  syntactically `extFlow b R s ρ σ φ`, the same term as `iterative`'s Φ. The conclusion is on 𝒟_{R-2ρ,s-2σ}, and
  the `rem` integrand matches {g+f_t, φ}_c.
- **it-est.**
  - `transform_integral` with v_t = {g+f_t, φ}_c, which is affine in t and so jointly continuous.
  - `composition`.2 at t = 1 for (f − T f)∘Φ.
- **(e).** `composition_real` with u = h + f₀. It needs only reality of u, not a class membership.
- **Holomorphy and images of Φ.** These come from F2's `canonical_map`.

Every need is met. No other consumer of F1 exists in the design.

## Findings

### F1-1. Unsigned public helpers reuse short names (MAJOR; blocking under (d))

The rule: "no reused public HELPER short name … any other declaration with the same last name component anywhere
in KAM is a finding, signed names exempt". The `ExtCompose` structure fields are part of the signed structure, so they
are exempt.

The F1 helpers below are public and unsigned. Each repeats a short name already declared elsewhere in KAM, mostly the
Part 5 original it ports in `KAM.Canonical`. Every earlier N11 package kept such helpers `private`: a whole-Partial
scan finds reused short names only on signed declarations.

| F1 helper (file:line) | Existing declaration(s) with the same short name | Used outside its own module? |
|---|---|---|
| `ExtCompose.eta_nonneg` (Composition.lean:141) | `KAM.Canonical.ComposeData.eta_nonneg` (Canonical/CompositionSeries.lean:79) | yes (Transform, TransformIntegral) |
| `ExtCompose.field_bound` (Composition.lean:154) | Canonical/CanonicalMap.lean:168; Planetary/MaximalStep/AffineFlowBasic.lean:119; Planetary/Averaging/OscillatorFlowProps.lean:66 | no |
| `ExtCompose.smallField` (Composition.lean:159) | Canonical/CompositionDomain.lean:96; Canonical/CanonicalMap.lean:187; AffineFlowBasic.lean:170; OscillatorFlowProps.lean:71 | yes |
| `ExtCompose.gaugeInterior_half` (Composition.lean:171) | Canonical/CompositionDomain.lean:128; Canonical/CanonicalMap.lean:198 | yes |
| `ExtCompose.lieTerm_bound` (Composition.lean:214) | Canonical/CompositionSeries.lean:62 | yes |
| `ExtCompose.lieSeries_summable` (Composition.lean:236) | Canonical/CompositionSeries.lean:99 | yes |
| `ExtCompose.lieSeries_class` (Composition.lean:244) | Canonical/CompositionSeries.lean:107 | no |
| `ExtCompose.lieSeries_bound` (Composition.lean:258) | Canonical/CompositionSeries.lean:123 | no |
| `ExtCompose.lieSeries_tail` (Composition.lean:268) | Canonical/CompositionSeries.lean:134 | no |
| `ExtCompose.series_eq` (Composition.lean:344) | Canonical/CompositionSeries.lean:195 | yes |
| `ExtCompose.smul` (Composition.lean:418) | `KAM.Canonical.ComposeData.smul` (Canonical/Composition.lean:73); `KAM.Planetary.OrbitJet.Jet5.smul` (OrbitJet/Jet.lean:42); field `KAM.Stability.IsActionNorm.smul` (Nekhoroshev/Stability/Setting.lean:137) | yes |
| `ExtCompose.flow_smul` (Composition.lean:438) | Canonical/Composition.lean:98 | yes |
| `ExtCompose.flow_series` (Transform.lean:93) | Canonical/Transform.lean:83 | no |
| `ExtCompose.integral_flow_hasSum` (Transform.lean:102) | Canonical/Transform.lean:93 | no |
| `ExtCompose.transform_identity` (Transform.lean:291) | Canonical/Transform.lean:148 | no |
| `ExtCompose.field_periodic` (TransformIntegral.lean:57) | Canonical/CompositionIntegralClass.lean:119; Canonical/CanonicalMap.lean:126 (private); `KAM.Planetary.oscClass.field_periodic` (OscillatorFlowMap.lean:133) | no |
| `ExtCompose.paramHyp_integrand` (TransformIntegral.lean:79) | Canonical/CompositionIntegralClass.lean:54 | no |
| `ExtCompose.integral_inClass` (TransformIntegral.lean:135) | Canonical/CompositionIntegralClass.lean:134 | yes (Transform.lean:376) |
| `ExtCompose.continuousOn_integrand` (TransformIntegral.lean:231) | Canonical/CompositionIntegral.lean:88 | no |
| `extGauge`, `norm_extGauge` (Composition.lean:66, 70) | identical full names, `private`, in Partial/CanonicalMap.lean:46, 50 (see F1-2) | yes (TransformIntegral) |

**Fix.**

1. Make the module-local helpers `private`; dot notation still works inside the module:
   - Composition: `field_bound`, `lieSeries_class`, `lieSeries_bound`, `lieSeries_tail`.
   - Transform: `flow_series`, `integral_flow_hasSum`, `transform_identity`.
   - TransformIntegral: `field_periodic`, `paramHyp_integrand`, `continuousOn_integrand`.
2. Rename the cross-module helpers to short names unused anywhere in KAM. Examples:
   - `ExtCompose.ext_eta_nonneg`
   - `ExtCompose.extSmallField`
   - `ExtCompose.ext_gaugeInterior_half`
   - `ExtCompose.extLieTerm_bound`
   - `ExtCompose.extLieSeries_summable`
   - `ExtCompose.ext_series_eq`
   - `ExtCompose.smul_ext`
   - `ExtCompose.extFlow_smul`
   - `ExtCompose.ext_integral_inClass` (the name the TransformIntegral docstring already uses)
3. Re-run the whole-library short-name and full-name grep, then the gate build.

No statement changes.

### F1-2. Public `extGauge`/`norm_extGauge` share their full names with F2's private copies (MINOR; latent build hazard)

**Location.** Composition.lean:66–73 declares public `KAM.Nekhoroshev.extGauge` with implicit `{ρ σ}` and public
`norm_extGauge`. CanonicalMap.lean:46–53 declares `private` `KAM.Nekhoroshev.extGauge` with explicit `(ρ σ : ℝ)` and
`private norm_extGauge`. Both are in the same namespace, and the bodies are identical.

**Current state: no clash.**

- No module imports both the Composition chain and CanonicalMap:
  - CanonicalMap imports ExtFlow, VectorField, RealSystem, Symplectic, FlowInverse and Cauchy, none of which reaches
    Composition.
  - Composition, TransformIntegral and Transform do not import CanonicalMap.
  - `KAM.lean` is not regenerated and imports neither.
- Importing both later (in the regenerated `KAM.lean` or N11-H `Iterative`) is safe. A private name is mangled with
  its module (`_private.KAM.Nekhoroshev.Partial.CanonicalMap.0.KAM.Nekhoroshev.extGauge`), so it is a different
  constant from the public one.
- This is consistent with the report that the 28-module combined build compiles.

**The hazard.**

- If `CanonicalMap.lean` ever imports `Composition` directly or transitively, its `private def extGauge` will not
  compile. Lean core's `checkNotAlreadyDeclared` rejects a private declaration whose user name is already a public
  constant: "a non-private declaration 'KAM.Nekhoroshev.extGauge' has already been declared".
- This follows from Lean core behaviour and was not build-verified here.
- Such an import is plausible if F2 round 2 reuses F1 helpers such as `mem_Dom_of_scaled_le`.
- It is also a literal F1-1 short-name hit.

**Duplication.** The F1 triple `extGauge`, `norm_extGauge`, `mem_Dom_of_scaled_le` duplicates F2's private triple
`extGauge`, `norm_extGauge`, `dom_of_scaled_le` (CanonicalMap.lean:46–69). The two differ only in binder
explicitness and positivity side conditions.

**Fix, preferred.** Put one public gauge triple, under unique names (for example `scaledGauge`, `norm_scaledGauge`,
`mem_Dom_of_scaled_le`), in the shared `ExtFlow.lean` or a new small `Partial/Gauge.lean` imported by both F1 and F2.
Then delete F2's private copies; this is an F2-side edit to coordinate with F2 round 2.

**Fix, minimal F1-only.** Rename F1's pair as in F1-1.

### F1-3. Proofs duplicated across Partial modules (MINOR; non-blocking)

No signed declaration is duplicated. In particular `extFlow` is imported, and no other `ExtCompose`, `composition*` or
`transform*` exists under `KAM.Nekhoroshev`.

Helper logic is re-proved, though:

- **`differentiableOn_wfield`, three copies.**
  - Composition.lean:104 private `differentiableOn_wfield'`.
  - Lie.lean:39 private `differentiableOn_wfield`, with a verbatim identical proof.
  - CanonicalMap.lean:72 private `differentiableOn_wfield`.
- **Reality of the field.** `composition_real`'s inline `hreal` (Composition.lean:556–563) re-proves CanonicalMap.lean:88
  private `wfield_real`.
- **Periodicity of the field.** `ExtCompose.field_periodic` (TransformIntegral.lean:57) re-proves CanonicalMap.lean:110
  private `wfield_periodic`, which is more general.
- **Angle translation.** `add_single_eq_ext` (TransformIntegral.lean:36) re-proves CanonicalMap.lean:101 private
  `prod_add_mk`.
- **Inside F1.** Composition.lean:395 private `wfield_smul_real` is a special case of Transform.lean:51
  `wfield_const_mul_ext`, which needs no differentiability hypothesis.
- **The `CompositionCoeff` `*_ext` helpers.** They re-prove general-dimension facts already in KAM:
  - lane P's public `KAM.Planetary.wbound_congr_flat` (Planetary/Averaging/OscillatorGen.lean:44).
  - lane P's public `coeff_integral_flat` (OscillatorCompositionIntegral.lean:54).
  - Partial/Bracket.lean:317 private `wbound_congr`.

  Reusing the lane-P helpers would import heavy modules, so keeping the copies is acceptable.

**Fix (optional).** Export one public `wfield` regularity/periodicity/reality kit from `Lie.lean`/`Setting.lean` (or
the shared gauge module of F1-2) and reuse it in F1 and F2.

### F1-4. Dead export `wbound_of_neg_ext` (NOTE)

CompositionCoeff.lean:79 declares `wbound_of_neg_ext`, and nothing in KAM uses it.

- Part 5 needed `wbound_of_neg` because its statements lacked `0 ≤ U`.
- The N11 signatures carry `hU`/`hW`, so the port has no use for it.

**Fix.** Delete it, or make it `private`.

### F1-5. Stale and inaccurate docstrings (NOTE)

- TransformIntegral.lean:20 and :23 name `ext_integral_inClass` and `ext_integral_bound`, which do not exist. The real
  names are `ExtCompose.integral_inClass` (L135) and `ExtCompose.integral_bound` (L263).
- Composition.lean:34 says "The engine is the Part 5 one (`KAM.Canonical.CompositionSeries`)". The file actually
  re-proves a port of that engine on `EC n k` and does not use it.

**Fix.** Correct the text, together with the F1-1 renames.

### F1-6. Awkward extraction at TransformIntegral.lean:84–88 (NOTE, style)

`obtain ⟨fd, fm⟩ : (…) ∧ True := ⟨(KAM.Canonical.flow_b (hc.smallField hk)).2.1, trivial⟩` introduces a binder `fm`
that is never used. The prover reports no warnings; that was not re-verified.

**Fix.** `have fd := (KAM.Canonical.flow_b (hc.smallField hk)).2.1`.

### F1-7. `transform_integral` text differs from the signature in form only (NOTE; no action)

- Transform.lean:368–372 writes `Set.Icc` where the signature has `Icc`.
- It wraps `hdcont` over two lines because signature L296 is 104 columns long.

Both changes are needed: one for the 100-column rule, the other because `open Finset` makes `Icc` ambiguous. The
elaborated statement is identical. This is recorded only for completeness.

## Hygiene detail (d)

**Passes.**

- No `EuclideanSpace`.
- No `sorry`/`axiom`/`admit`/`set_option`/`maxHeartbeats`/`native_decide`/`unsafe`/`opaque`. The one `admitted`
  match is docstring prose at CompositionCoeff.lean:78. A whole-KAM grep finds none of these tokens outside
  `KAM/Frozen`, so no upstream `sorry` exists either.
- Longest lines are 99/98/99/99 characters; no file exceeds 100 columns.
- File sizes are 590/218/380/315 lines, all below 1500.
- The module skeleton is complete in every file: copyright, `module`, public imports, docstring,
  `@[expose] public noncomputable section`.
- **Root shadow: none.**
  - The public declarations directly in `KAM.Nekhoroshev` are the signed six plus helpers ending in `_ext`, and
    `extGauge`, `cubeE`, `q_facts_ext`, `mem_Dom_of_scaled_le`. None equals a root Mathlib/Lean name.
  - `ExtCompose.div_nonneg'`, `ExtCompose.smul` and the rest sit in the sub-namespace `ExtCompose`, are used only
    through dot notation, and `div_nonneg'` occurs nowhere else in KAM.
- **Full-name clashes: none** with any `KAM.Nekhoroshev.*` declaration in KAM, including Part 5's averaging
  declarations in the same namespace. The one exception is the private pair in F1-2.

**Fails.** Short-name reuse, under F1-1 and F1-2.

## Notes

1. **§10 Q5 answers.**
   - `cubeE`, `mem_Dom_of_scaled_le` and `q_facts_ext` have unique short names; they differ from Part 5's
     `KAM.Canonical.mem_Dom_of_scaledNorm_le` and `KAM.Canonical.q_facts`.
   - `extGauge` and `norm_extGauge` are not unique (F1-2).
   - The use of `ext_taylor_second` matches step `tr-taylor` (node table above).
2. **Module list deviation.** The design row N11-F1 (L360) lists only `Composition.lean` and `Transform.lean`. The
   package adds `CompositionCoeff.lean` and `TransformIntegral.lean`, a split at theorem boundaries that the design
   allows, and depends on F2's `ExtFlow.lean`, which is not in the design table (handoff §10 Q2).
   - Merge order matters: `inp-n11f1` already contains `inp-n11f2`, including the F2 `CanonicalMap.lean` whose
     integration audit failed.
3. **Signature-only premises are all source premises.** `hU : 0 ≤ U` and `hW : 0 ≤ W` are kept as signed. The
   internal helpers (`include` sections) carry only `ExtCompose` fields, `hk` and class/bound premises.
   `transform_integral`'s `hdcont` is used only in the class part, which matches the blueprint.
4. **Not verified here.**
   - The gate build.
   - `#print axioms`; the handoff reports `[propext, Classical.choice, Quot.sound]` for the five theorems.
   - The absence of linter warnings.
   - The Lean-core behaviour claimed in F1-2.

   Round 2 should re-run the gate build and the whole-library short-name and full-name grep after the renames.

## Fix applied (lane N, 2026-10-28)

F1-1 and F1-2 were fixed by renaming only; no statement changed.
- **Made `private` (module-local):**
  - Composition: `field_bound`, `lieSeries_class`, `lieSeries_bound`, `lieSeries_tail`.
  - Transform: `flow_series`, `integral_flow_hasSum`, `transform_identity`.
  - TransformIntegral: `field_periodic`, `paramHyp_integrand`, `continuousOn_integrand`.
- **Renamed (cross-module):**
  - `ExtCompose.eta_nonneg` → `ext_eta_nonneg`; `smallField` → `extSmallField`;
    `gaugeInterior_half` → `ext_gaugeInterior_half`; `lieTerm_bound` → `extLieTerm_bound`.
  - `lieSeries_summable` → `extLieSeries_summable`; `series_eq` → `ext_series_eq`; `smul` → `smul_ext`;
    `flow_smul` → `extCompose_flow_smul`; `integral_inClass` → `ext_integral_inClass`.
  - `extGauge`/`norm_extGauge` → `extComposeGauge`/`norm_extComposeGauge`.
- **Checks:**
  - All new names are unused elsewhere in KAM.
  - The four modules rebuild with 0 errors and no warnings.
