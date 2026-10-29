# DEFS-P3 independent definitions audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-defaud3`.

**Overall: FAIL for closing both requested nodes.** `bpP:p11:sec-E#data` is **NOT CLOSABLE** under the handoff's whole-object policy. `bpP:p5:rstar#Cgamma` is **CLOSABLE / PASS** with `LEAN_REF: KAM.Planetary.pgCgamma` (`KAM/Planetary/PGAssembly/ThresholdAlg.lean:128`). This is a definitions audit, not a provider seal or a new theorem proof. No frozen theorem is proposed for sealing.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the DEFS-P3 handoff, track P's statement, both controlling blueprint excerpts, P11A/P45 design node tables, the shared signatures, and relevant landed definitions/proofs and previous P7/P8/P8a/P8e/P10/P5-TH audit receipts. Fresh verification below takes precedence over those receipts.

The explicit user report destination overrides the generic brief's MAIN-worktree destination. This report is in the requested audit worktree. Repository changes are report-only; temporary verification files were confined to `.lake/abi-scratch/` and removed afterward. No state-changing git, generated-file repair, frozen-file edit, or manifest edit was performed.

Snapshot:

- HEAD and merge base: `40f08ebcae39acd680cd863807038b7d80616745` (`Regenerate KAM.lean (GAP-ISM)`).
- `inp` when checked: `495ed75861e71e83e99bb9ed978f979c57657aaf`.
- `git diff inp...HEAD`: empty; HEAD is an ancestor of the currently advanced `inp`. Thus this is an audit of the landed snapshot, not newly changed Lean declarations. Nothing on the advancing branch is silently incorporated.
- Initial status: only the supplied untracked `docs/tracks/P/audits/DEFS-P3-handoff.md`.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.

All declaration names below are in `KAM.Planetary` unless qualified otherwise. Path prefixes `Preparation/` and `PGAssembly/` mean `KAM/Planetary/Preparation/` and `KAM/Planetary/PGAssembly/` respectively. `C := p11SecularData D`, `A := p11SlowData D nu eps`, `F := p11FastData D eps`, and `Q₀ := p11PrepQ D nu eps` are only report abbreviations.

## Node verdicts and decisive findings

| Node | Verdict | Reason / LEAN_REF |
|---|---|---|
| `bpP:p11:sec-E#data` | **NOT CLOSABLE / FAIL** | Exact affine rescaling, cube, direct N/P formulas and actual derivatives exist. The literal full domain E and its mapping iff are not supplied by the named signed objects; the named wrapper domain is strictly smaller. The full domain-table properties and full complex H₂/pullback identity are not exported together as the source asserts. A free data structure or conditional selected witness cannot itself replace those source objects. |
| `bpP:p5:rstar#Cgamma` | **CLOSABLE / PASS** | `KAM.Planetary.pgCgamma`, `PGAssembly/ThresholdAlg.lean:128`: exact signed `G*(30/s_*)^(tau+1)` on every `PGData a b`, with no local fallback or dependence on r or mu. |

**F1 — full E versus signed neighbourhood.** Blueprint `p11-cp09-preparation.tex:189` defines E by angle strip width sigma_F/72, fast action radius 2, and slow action radius pi/2. `p11WrV` (`WrapperChain.lean:29`) instead uses `actionNbhd (p11PreparedBox n) 1`. `P11PreparedSpec` (`PreparedData.lean:40–43`) uses that same smaller domain. The exact E is expressible using existing generic definitions as `KAM.complexStrip (n+n) (C.sigma/72) ×ˢ p11Box 0 2 (Real.pi/2)`; no specialized landed definition names that expression. Its availability as an expression does not make `p11WrV` equal to E or extend theorems stated on `p11WrV`. These are not equal sets. With all angles zero, a fast action 7/4 and all slow actions zero is in E but outside that neighbourhood: `p11_actionNbhd_norm_lt` bounds every action coordinate there strictly below 3/2. A successful scratch Lean counterexample verifies nonmembership for n=1; the same coordinate construction works in every positive dimension, including physical n≥2. This is not a signed-signature mismatch: the signed specification deliberately states the narrower result. It is a literal source-node coverage gap under the present handoff.

**F2 — the mapping iff is unpaid.** Blueprint line 189 asserts mapping the entire radius-(2,pi/2) polydisc into V₂/2 **iff** `2*eps ≤ s₂/2`, in the standing positive-eps, positive-dimension regime. `p11Rescale_mem_box` (`PreparedBasic.lean:98`) proves only a sufficient inclusion for the smaller `actionNbhd` domain, assuming `pi*eps ≤ s₂`; `p11_freq_U1_sub` (`PreparedFreq.lean:49`) similarly assumes `5*eps ≤ s₂`. Neither states the full-domain equivalence or its necessity. The real symplectic and shift properties do have named lemmas and are not missing.

**F3 — source objects versus output contracts.** `P11PreparedData` is arbitrary function data. `P11PreparedSpec`/`P11PreparedFullSpec` are propositions, not definitions of the source Hamiltonians. `p11PreparedData` is literally `if exists Q, FullSpec ... Q then choose else default` (`PreparedData.lean:107–108`), exactly as signed. It therefore fails the present no-arbitrary-witness/no-fallback test as an unconditional source-object definition. This does **not** refute `prepared`, `amount`, or `data_star`: `Amount.lean:109–115` proves the guard and uses `choose_spec` on its small-eps interval. The better direct object is `p11PreparedCoreOf`/`p11PreparedCore`/`p11PrepQ`, whose N/P bodies are the formulas globally; those still do not define E or prove F2.

**F4 — domain table and complex identities (coverage notes, not a separate kernel failure).** A substantial part of the table is implemented, including the exact mixed Cauchy radii and the h₀ derivative identities. These are credited below. They do not provide a single named source-domain definition for E, all neighbourhood embeddings, or the exact complete domain-table package. H₂ and H-hat occur as composed/summed expressions, with source equations on their specified domains; a standalone literal complex H₂ and its full-E normalized pullback identity were not located. The real physical identity of `P11PreparedSpec` is valuable but has a smaller domain and takes real parts. It is not a full complex identity on E.

To close `sec-E#data` under this handoff, supply or explicitly identify: the exact E object; the full polydisc mapping iff with standing premises; source H₂ and H-hat expression references with the asserted complex equality on their actual domain; named domain-table/neighbourhood lemmas covering the table; and named identification of the normalized fast/slow frequency expressions on the claimed source domain. Use the direct formula constructions rather than treating an arbitrary selected record as the source formula on its whole carrier. Alternatively, the orchestrator must explicitly split/narrow the graph node and record the residual source claims; this auditor does not make that change.

## Every source object: definition classification

A FAITHFUL-WITH-NOTE row credits the explicit formula or stated restricted theorem, not an unproved extension to all source domains. A MISSING row can have a nearby candidate: that candidate is listed to make the exact shortfall reviewable.

| Source object (blueprint P11:189–194) | Landed declaration / locator | Classification | Body / property assessment |
|---|---|---|---|
| rho-tilde₀ = constant 2*pi*eps | `p11SlowCenter`, `Preparation/SlowDivisor.lean:32`; `p11DevCenter`, `PreparedDev.lean:31` | FAITHFUL | Full centre is `(J₀, rho-tilde₀)` with literal constant slow block, no branch. |
| A_eps, complex affine chart | `p11Rescale`, `SlowData.lean:31` | FAITHFUL | Exact formula on every phase point; angle-first product carrier regroups `(theta,zeta)` and `(r,rho')` without changing coordinates. Signed body matches. |
| A_eps on real points | `p11RescaleReal`, `PreparedBasic.lean:55`; `p11Rescale_real`, :59 | FAITHFUL | Literal real formula, with named compatibility with real inclusion. |
| epsilon-scaled symplectic pullback | `p11RescaleReal_chart`, `WrapperChain.lean:63` | FAITHFUL-WITH-NOTE | Named real analytic / eps-symplectic theorem for arbitrary O, J₀, eps. It proves the form identity, rather than assuming chart validity in a field. Complex affine differentiability is separately `p11Rescale_differentiable`, `PreparedBasic:125`. |
| commutation with angle shifts | `p11RescaleReal_shift`, `WrapperChain.lean:79` | FAITHFUL-WITH-NOTE | Named real lattice-shift theorem. Complex formula leaves angles unchanged definitionally. |
| full radius-(2,pi/2) chart-domain mapping iff | nearest `p11Rescale_mem_box`, `PreparedBasic.lean:98`; `p11_freq_U1_sub`, `PreparedFreq.lean:49` | MISSING | Only sufficient smaller-domain maps are named; no exact iff. F2. |
| E, strip times radius-(2,pi/2) action polydisc | nearest `p11WrV`, `WrapperChain.lean:29` | NOT FAITHFUL | Candidate is strip times K+1, strictly smaller; exact E definition not located. F1. |
| N_eps | `(p11PreparedCoreOf C F A eps W).N`, `PreparedBasic.lean:39–42`; `p11PreparedCore`, :50; `p11PrepQ`, `PreparedChoice.lean:39` | FAITHFUL-WITH-NOTE | Literal `(h₀+g₂)(rescaled actions)/eps` on the entire public carrier, no branch in constructor. Parametric stage data are inputs. Physical specialization uses upstream selected stages; interpretation/regularity is proved only on the signed small-eps domain. |
| P_eps | `(p11PreparedCoreOf C F A eps W).P`, `PreparedBasic.lean:43` | FAITHFUL-WITH-NOTE | Literal `f₃(rescale z)/eps` globally for input A. Same upstream/domain qualification as N; no local fallback. |
| H₂ = H o Phi¹ o Theta-hat o Psi₂ | `p11WorkingH`, `Holomorphic.lean:68`, composed with `F.map`, `p11PolarC`, `A.Psi`; source identity in `P11SlowSpecOf`, `SlowData.lean:54ff` | FAITHFUL-WITH-NOTE | Correct composition is available as an expression in these named objects. No standalone H₂ declaration was found; the composed expression itself has the right formula. Equalities attaching it to h₀+g₂+f₃ are restricted by the slow-stage specification, not global identities of arbitrary stage functions. |
| H-hat_eps = H₂ o A_eps/eps = N_eps+P_eps | `fun z => Q₀.N z.2 + Q₀.P z`; `p11PreparedCoreOf_chain_eq`, `PreparedBasic.lean:326`; `P11PreparedSpec`, `PreparedData.lean:70–72` | FAITHFUL-WITH-NOTE | Sum is a literal expression of faithful direct components. Named chain identity is real physical and on K+1; no standalone normalized complex pullback definition and full-E equality. F4. |
| actual prepared output selector | `p11PreparedData`, `PreparedData.lean:107` | NOT FAITHFUL | Signed conditional witness/default, not globally the source formula. FullSpec under a proved guard is sound but fails this handoff's stricter unconditional object test. F3. |
| K_eps, closed unit cube | `p11PreparedBox`, `SlowData.lean:34` | FAITHFUL | Exact `Set.pi univ (Icc (-1/2) (1/2))`, in dimension n+n. |
| meas(K_eps)=1 | `p11PreparedBox_volume`, `Datum.lean:33` | FAITHFUL | Named equality for every n, actual product Lebesgue volume. |
| d=diam(K_eps)=1 | `p11PreparedBox_diam`, `Datum.lean:38` | FAITHFUL-WITH-NOTE | Requires `1 ≤ n+n`; physical n≥2 discharges it. The empty-dimensional cube has diameter zero, so this premise is necessary. |
| vartheta=1/4 | `(p11WrDatum D b).vartheta`, `WrapperDatum.lean:35` | FAITHFUL | Literal field value for every D,b. |
| eps-star=1/2 | `(p11WrDatum D b).epsLoss`, `WrapperDatum.lean:41` | FAITHFUL | Literal field value, no selected threshold substitution. |
| s=s-star=sigma₃/6=sigma_F/72 | `(p11WrDatum D b).s`, `WrapperDatum.lean:36`; slow width `SlowData.lean:61` | FAITHFUL | Literal sigma/72; sigma₃=sigma/12, so sigma₃/6 is sigma/72. |
| N=2n | `p11WrDatum : QuantitativeData (n+n)`, `WrapperDatum.lean:31` | FAITHFUL | Dimension is the type index; n+n=2*n arithmetically. |
| mu=mu-bar | `(p11WrDatum D b).mu`, `WrapperDatum.lean:32` | FAITHFUL | Exactly `(p11PatchData D).mu`. |
| tau_D=max(n*mu-bar,2n) | `(p11WrDatum D b).tau`, `WrapperDatum.lean:34`; `P11SecularFullSpec.tau_eq`, `HoloData.lean:95` | FAITHFUL-WITH-NOTE | Uses C.tau. Its max identity is proved for the selected secular data via `holo_chart`; not definitional rfl. No epsilon dependence is introduced. |
| K+2vartheta, K+3vartheta, K+4vartheta and embedding in D(0,3/2) | `KAM.actionNbhd` expressions, `PreparedData.lean:40–43`; `p11_actionNbhd_norm_lt`, `PreparedBasic.lean:85` | FAITHFUL-WITH-NOTE | Radius 1 corresponds to 4vartheta, 3/4 to 3vartheta. Named norm lemma covers the outer radius; smaller neighbourhoods embed by monotonicity. No single named export states the entire source chain and its final block radii. |
| V₂/2: original J/rho action domains for g₂,f₃ | `p11WrSlowDom`, `WrapperParts.lean:74`; `p11Box`, `RectangularBracket.lean:36`; `P11SlowSpecOf`, `SlowData.lean:58–60,86–89` | FAITHFUL | Exact centre and half radii; f₃ includes angle strip sigma/72, g₂ is action-only. |
| rescaled estimate region: coordinate radii 5eps/4 | `p11PreparedFreq` bounds in `PreparedData.lean:43,59–60`; `p11_prin_g2_jet`, `PreparedJets.lean:51` | FAITHFUL-WITH-NOTE | K+3/4 implies coordinate norm <5/4; source's “i.e.” should not be interpreted as equality of complex sets (see S1). Named mixed-jet lemma works on an enclosing region. |
| g₂ Cauchy discs: s₂/4 in J, eps/4 in rho | `p11_prin_g2_jet`, `PreparedJets.lean:51–100`; generic `p11PartialVec_norm_le_poly`, `PreparedCauchy.lean:120` | FAITHFUL-WITH-NOTE | Exact radii occur in theorem conclusion and its proved closed-polydisc inclusion. Assumes original J distance <s₂/4, not merely a bound on rescaled actions. h5/small eps supplies the link; no named complete domain-table implication was found. |
| f₃ Cauchy-disc geometry on V₂/2 | `p11WrSlowDom`, `WrapperParts.lean:74`; same action polydisc as g₂ | FAITHFUL-WITH-NOTE | Domain is exact; geometry used in the g₂ proof is applicable to that action domain. A separate named f₃ domain-table/closed-disc export was not located. |
| Z-hat domain D(J₀,s₁/2) x D(0,pi*r_z²/16) | `p11SlowZDom`, `SlowDivisor.lean:42`; differentiability clause in `P11SlowSpecOf`, `SlowData.lean:71–74` | FAITHFUL | Literal intended inequalities on the full set carrier. Predicate is credited as a domain declaration, not proof of an arbitrary Z's regularity. |
| G-hat₀ object and holomorphic domain | `p11PolarAverage F.G`, `PolarAverage.lean:69`; `p11_dev_G0_diff`, `PreparedDev.lean:70` | FAITHFUL-WITH-NOTE | Actual torus average, not an arbitrary witness. Named J-holomorphy holds on a larger rho disc pi*(r_z/2)²; restriction covers the source. Whole-carrier sqrt/integral formula makes no off-domain analytic claim. |
| Z/G-hat₀ Cauchy radii s₁/4 and pi*eps/4 / pi*r_z²/32 | `p11_slow_rho_bound`, `SlowAverageJet.lean:48`; `p11_slow_Z_jets`, :138; `p11_prin_G0_jet`, `PreparedJets.lean:554` | FAITHFUL-WITH-NOTE | Named derivative estimates implement substantive parts, and local radius arguments occur in their proofs. Exact full table, especially an independently named pi*r_z²/32 disc inclusion for the stated objects, is not a literal export of these declarations. Do not close that property by naming a definition alone. |
| h=h₀+g₂ | `p11DevH`, `PreparedDev.lean:519`; `p11DevH_eq`, :521 | FAITHFUL-WITH-NOTE | Literal sum, packed as Fin 1-valued function for differentiation. Exact scalar recovery lemma; no changed Hamiltonian. |
| omega-hat_eps=gradient N_eps | `p11PreparedFreq`, `PreparedData.lean:33`; `p11PreparedFreqR`, :35; `p11_freq_partial_eq`, `PreparedFreq.lean:98` | FAITHFUL-WITH-NOTE | Actual complex derivative and its real restriction; named chain-rule identification under differentiability and N's formula. Total fderiv off differentiability domains is not claimed to be an analytic frequency. |
| split omega-hat=(omega-hat¹,eps*omega-hat²) | `p11PrepChk`, `PreparedChoice.lean:31`; `p11_prep_freqR_eq`, :104; FullSpec in `PreparedData.lean:86` | FAITHFUL-WITH-NOTE | Direct normalized derivative formula divides only the slow output block by eps. Named equality on stated small-eps real region; no arbitrary frequency is substituted. |
| omega-hat¹=omega+eps*d_J G-hat₀+d_J g₂ | `p11_dev_J`, `PreparedDev.lean:84`; direct derivative in `p11PrepChk`, `PreparedChoice.lean:31` | FAITHFUL-WITH-NOTE | Exact h₀ J-derivative identity, plus derivative linearity gives source expansion on its regularity region. A named final full-source-domain expansion for Q's fast block was not located. |
| omega-hat²=Omega-tilde+d_rho Z-hat+eps⁻¹*d_rho g₂ | `p11_dev_h0_rho`, `PreparedDev.lean:187`; `p11SlowNormalizedFreq`, `PreparedData.lean:76`; `p11PrepChk`, `PreparedChoice.lean:31` | FAITHFUL-WITH-NOTE | h₀ derivative is exactly eps*(Omega/(2*pi)+dZ); normalized derivative retains d(g₂)/eps. Named final expansion for the entire claimed domain still requires attachment/linearity and eps≠0. |

| Source object (blueprint P5:152) | Landed declaration / locator | Classification | Reason |
|---|---|---|---|
| C_gamma := G*(30/s_star)^(tau+1) | `pgCgamma`, `PGAssembly/ThresholdAlg.lean:128–129` | FAITHFUL | Exact signed body, all `PGData a b`. `pgWidth` is s_star (`Extension.lean:40`), `pgTau a b=(a+b)+1` (`Scales.lean:61`), and G is `(pgScales d).G` (`Scales.lean:128`). |

The source chooses G and s_star as data-dependent constants. `pgScales` selects a proved `PGScaleSpec` witness (`Scales.lean:68,87,128–130`), and `pgExtension` selects a proved extension (`Extension.lean:36–40`); these are legitimate upstream choices of the source's allowed constants. `pgCgamma` itself is a fixed formula for those constants, with no fallback, r/mu parameter, extra hypothesis, or arbitrary C_gamma witness. `pgWidth_pos`, `pgScales_G_pos`, and `pgCgamma_pos` prove positivity rather than assume it.

## Signature and definition checks

Shared signed files used read-only:

- `P11ASignatures.lean` SHA256 `fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.
- `P45Signatures.lean` SHA256 `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304`.

Whitespace-normalized declaration comparisons: MATCH for `p11Rescale`, `p11PreparedBox`, `P11PreparedData`, `p11PreparedFreq`, `p11PreparedFreqR`, `P11PreparedSpec`, `p11M0`, `p11SlowNormalizedFreq`, `P11PreparedFullSpec`, `p11PreparedData`, `pgCgamma` (11/11). An initial script included the following `open Classical in` in only one FullSpec extraction; correcting the declaration delimiter yielded MATCH. There was no semantic mismatch.

Fresh Lean probe copied all seven PreparedData defs from the signed file under distinct names and checked `example : @original = @signed_original := rfl`. Also checked unconditional rfl identities for direct core N/P and C_gamma, and the strict-neighbourhood counterexample. Final probe exit 0. The first probe had an unfinished Fin-index simplification and an axiom print for a module not imported by the probe; both scratch-only errors were corrected. No failed probe is counted as a passing verification.

No new public declaration exists in the three-dot diff. In the landed focus slice: the data records are raw function records, not hypotheses; specs are explicit predicates; affine maps/cube/domain predicates and the direct core constructors are literal objects; witness selectors remain conditional outputs with guard obligations. No arbitrary record or FullSpec predicate is credited as an unconditional source definition. No provider type-equality or seal-body probe applies because DEFS-P3 adds/seals no provider or frozen theorem.

## Fresh hygiene and verification

All Lean-related commands were serialized, `LEAN_NUM_THREADS=1`; direct Lean/checker invocations used `nice -n 5`. The compile-gate script itself runs `nice -n 5 lake build`. No other Lean/Lake command from this audit overlapped a build, checker, probe, or lint's ABI Lean process.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-defaud3 KAM.Planetary.Preparation.Datum KAM.Planetary.Preparation.WrapperChain KAM.Planetary.Preparation.WrapperDatum KAM.Planetary.PGAssembly.Threshold
   ```

   Exit **0**. Output began `[inp-gate] slot 1 acquired 06:23:27 ...`; final line `Build completed successfully (9600 jobs).` Existing replay warnings concerned unused variables/arguments and deprecated lemma names; no build error. The job count includes cached dependency jobs, not a clean rebuild.

2. Lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **0**, complete output:

   ```text
   check_lean_modules: PASS (1279 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No stale-root exception was needed. This checks forbidden escapes/resource overrides, file size, module framing, generated files and frozen integrity. No forbidden token, over-1500-line file, or ambient `EuclideanSpace` failure occurred.

3. Fresh body/formula/domain and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/DEFS-P3-probe.lean
   ```

   Final exit **0**. Every following axiom print had exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`:

   ```text
   p11Rescale, p11PreparedBox, p11PreparedCoreOf, p11PreparedCore,
   p11PrepQ, p11PrepChk, p11PreparedData, p11PreparedFreq,
   p11SlowNormalizedFreq, p11WrDatum, pgCgamma,
   prepared, amount, data_star,
   p11PreparedBox_isCompact, p11PreparedBox_volume, p11PreparedBox_diam,
   p11RescaleReal_chart, p11RescaleReal_shift, p11Rescale_mem_box,
   p11_freq_partial_eq, p11_prin_g2_jet, p11_dev_h0_rho, p11_dev_J,
   pgCgamma_pos, param_facts
   ```

   Exact Lean output format, for example:
   `'KAM.Planetary.data_star' depends on axioms: [propext, Classical.choice, Quot.sound]`.
   These are fresh checks of cited landed results, not a claim that new theorems were introduced by this audit.

4. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.Datum KAM.Planetary.Preparation.WrapperChain KAM.Planetary.Preparation.WrapperDatum KAM.Planetary.PGAssembly.Threshold
   ```

   Exit **0**, complete verbose output:

   ```text
   replaying KAM.Planetary.PGAssembly.Threshold
   replaying KAM.Planetary.Preparation.WrapperDatum
   replaying KAM.Planetary.Preparation.WrapperChain
   replaying KAM.Planetary.Preparation.Datum
   ```

5. Import closure inspected from those four roots: **554 KAM modules**, **zero provider imports**, **67 imported frozen files**, all manifest state **SEALED**, no unrecognized/unsealed frozen import. The frozen `FixedHamiltonian` definition is the exact physical Newtonian definition, not an abstract perturbation substituted in the chain identity.

6. `git diff --check`: exit **0**. Protected-path three-dot diff is empty. Final repository status and scratch cleanup were checked after writing this report.

## Suspected blueprint/source defects and limits

**S1 — complex-neighbourhood “i.e.” is too strong if literal.** `blueprint-P/parts/p11-cp09-preparation.tex:193` says “the points used for estimates are those of K_epsilon+3vartheta, i.e.” the two radius-5eps/4 inequalities. For the existing `actionNbhd` convention this is only a containment, not equality: a purely imaginary rescaled action of magnitude 1 is inside the radius-5/4 centred polydisc but has distance at least 1 from the real cube, so is outside K+3/4. The estimates on the enclosing polydisc are useful and stronger; the text should distinguish containment from equality. No source or blueprint was edited.

**S2 — coarse node mapping hides residual objects.** `docs/tracks/P/design/P11A-LEAN-DESIGN.md:200` maps the entire node to `p11Rescale`, `p11PreparedBox`, `P11PreparedData`. The first two match their objects; the third is only a raw record type. That mapping alone cannot discharge E, its iff, the domain-table properties, or frequency/complex-Hamiltonian identities. Previous split package audits correctly allowed their signed narrower scopes; those scoped passes do not close this broader definitions node.

No new defect in the frozen definitions, no pinned external-source erratum, and no implementation deviation introduced by this auditor were found. This audit compares the supplied local blueprint and signed design; it does not independently rederive CP09 from a PDF. F1–F4 are source coverage/definition-policy findings, not evidence of an inconsistent Lean kernel or unsound already-proved restricted theorem. Owner review of the handoff's overnight definition-node policy remains as stated in the handoff.

## Exact final axiom output

```text
'KAM.Planetary.p11Rescale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PrepQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PrepChk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowNormalizedFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgCgamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amount' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.data_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedBox_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedBox_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedBox_diam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_mem_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_partial_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_g2_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_h0_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgCgamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.param_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
```
