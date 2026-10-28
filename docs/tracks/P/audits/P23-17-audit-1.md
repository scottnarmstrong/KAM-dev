# P23-17 independent package audit 1

Overall verdict: **PASS WITH NOTES for the private conditional package**. All required checks are recorded below. There is no signed/frozen P23-17 declaration and no provider to seal. This is not a seal-ready verdict for `two_scale_kam`, P23-22, or any frozen planetary theorem. The open initial-tube corollary and future joint-consumer integration require the distinctions recorded below.

Audited snapshot: HEAD `7ddf51852e0e6e7a5b9c11fed6bec8c9fe11803a`, worktree `/root/code/KAM-inp-p2317`. Compared `git diff inp...HEAD` (inp `c8ccbea983b7ef343dce78b81036554ef803f565`) and `git diff inp-p2316...HEAD` (P23-16 `bcb4386313c4dcb1066452c3d32fc859d1acc183`). Both diffs contain only the two audited files: `LimitActionsChain.lean` (136 lines) and `LimitActions.lean` (443 lines), 579 insertions. The pre-existing untracked handoff was preserved. Only this report is a persistent audit edit; probes were confined to `.lake/abi-scratch/` and removed. The user's exact worktree report path overrides the common brief's main-worktree wording.

Read AGENTS.md, PLAN, DECISIONS, common package audit brief, P23-17 handoff/AUDIT FOCUS, P23 design (P23-17 row, N2, shared-witness contract and release gate), both design audits, track-P statement, P3a iterative statement and P3b L20–39. Checked the relevant frozen action-neighborhood and planetary coordinate/block definitions. Authority here is the local pinned blueprint/design, not an independent re-audit of the CP10 PDF. The blueprint SHA256 is `e923c1f3856cd7c27fc73b1a5bdb21139a31d0484e30421c4e0db9cfdff86c1a`.

## Expanded hypotheses and applicability

`ActionSteps` is explicitly an internal result bundle, not a source-defined predicate or a new standing/source assumption. As a source theorem, `limit_actions_of_steps` would be CONDITIONAL, with eight produced inputs; the design explicitly authorizes that private boundary. Every input is already produced by `iterative` on **one** tuple `(Ds, hs, fs, Ψ, Φ, is)`:

| Expanded field (Chain L34–50) | Exact producer from Iteration.lean | Projection in applicability proof | Classification |
|---|---|---|---|
| `hs_zero` | L34, `hs 0 = h` | `h1` | Derived dependency |
| `hyp` | L35, all stage KamHyp | `hK` | Derived dependency |
| `step` | L39–42, frequency and both block bounds | `(hI j).2.1` | Derived dependency |
| `lip` | L43–46, stage defect Lipschitz | `(hI j).2.2.1` | Derived dependency |
| `Ds_succ` | L47, real-part image equality | `(hI j).2.2.2` | Derived dependency |
| `maps` | L60, complex action maps real bases to real bases | `(ht j).2.2` | Derived dependency |
| `eHat_sq` | L76, quadratic error recurrence | `(hr j).1` | Derived dependency |
| `rho_hi` | L78, radius recurrence | `(hr j).2.2.1` | Derived dependency |

No field assumes a chain limit, summability, uniform convergence, telescoped displacement, product bound, half-radius location, composed frequency identity, or limit Lipschitz estimate. The stage `KamHyp` is the existing P23-16 output, not a newly strengthened hypothesis. Its standing content (Setting L42–67) is dimension/τ, nine positive parameters, gamma ordering, widths, normalizations, L bound, holomorphic/reality/class/norm inputs, frequency injectivity, Hessian/inverse bounds and KAM smallness. P23-17 changes none of it.

Binder accounting for the principal helper: `{a,b,sbar,p,h,Ds,hs,fs,is}` are nine TYPING parameters; `S` expands into the eight derived inputs above. SOURCE=0, STANDING=0, RULED=0 at this private boundary; these eight would be EXCESS if advertised as premises of the source theorem. They are permitted only as the expressly designated conditional interface. Auxiliary point binders `I,J,j,m,v` are typing; `I ∈ Ds 0`, `J ∈ Ds 0` are the source domain restrictions, not analytic proof assumptions. `iterative_actionSteps` instead assumes only the original `H : KamHyp D sbar p h f`; all eight fields are constructed in its proof (LimitActions L434–436).

The applicability theorem calls `iterative H` once, retains its same `Ψ, Φ, is`, and constructs `S` solely by projections. An independent scratch composition also obtains that original tuple once, constructs `S`, and immediately applies `limit_actions_of_steps S` without selecting new stages. It keeps `Ψ, Φ` in the existential tuple. The package's standalone applicability theorem intentionally forgets other iterative conjuncts: a future consumer must retain the original full result locally, as the handoff says, rather than separately choose witnesses from several existential theorems. P23-22 is not in this checkout and its actual joint consumer is not certified here.

## Declaration inventory and source comparison

Names below are in `KAM.Planetary`; short names in the `ActionSteps` namespace are prefixed `ActionSteps.`. C denotes LimitActionsChain, L denotes LimitActions.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| Private interface | `ActionSteps` C30 | PASS | Exactly eight produced fields, as expanded above. |
| Composed actions | `actionChain` C53 | PASS | Identity at zero, next complex action map then real part. |
| la-wp | `ActionSteps.chain_mem` C63 | PASS | Induction through exact image domains. |
| la-wp / real composition | `ActionSteps.incl_chain_succ` C70 | PASS | `maps` proves imaginary parts vanish at chain points. |
| Block norm adapter | `ActionSteps.norm_first_incl` C83 | PASS | Real inclusion preserves first-block max norm. |
| Block norm adapter | `ActionSteps.norm_last_incl` C89 | PASS | Same for second block. |
| la-tele | `ActionSteps.chain_step` C96 | PASS | Both constant source block ratios, factor 10. |
| (iv) | `ActionSteps.chain_freq` C116 | PASS | Same chain; step frequency identity and hs zero. |
| Scalar prerequisite | `ActionSteps.e_nonneg` L40 | PASS | Existing stage-hypothesis consequence. |
| Scalar prerequisite | `ActionSteps.rho_pos` L43 | PASS | Positive actual rhoHat, no replacement radius. |
| la-tele scalar sums | `ActionSteps.scalar_sums` L47 | PASS | Applies proved `sums`, c=0 only for unweighted estimates. |
| la-tele | `ActionSteps.rho_le_zero` L59 | PASS | Geometric radius domination. |
| la-tele tail | `ActionSteps.rho_anti` L65 | PASS | Recurrence implies monotonicity from any stage. |
| la-tele | `ActionSteps.partial_sum_le` L75 | PASS | Finite error sum bounded by actual summable tail. |
| la-tele block telescoping | `ActionSteps.chain_block_le` L82 | PASS | Both 20(Mbar_i/Mbar) constants and same chain. |
| Sup norm conversion | `ActionSteps.ratio_le_one` L145 | PASS | Stage normalization, positive denominator. |
| la-tele | `ActionSteps.chain_sup_step` L152 | PASS | Reassembles blocks in Fin-Pi max norm. |
| la-lip | `ActionSteps.chain_lip` L173 | PASS | Recursion on composed defects, no assumed composed bound. |
| la-lip smallness | `ActionSteps.two_sided_small` L207 | PASS | 8192n Ehat0 < 1 from KAM constant. |
| la-lip product | `ActionSteps.prod_le` L215 | PASS | Product ≤ exp(sum) ≤ 1+2560n Ehat0. |
| la-tele | `ActionSteps.summable_step` L241 | PASS | Nonnegative summable majorant, actual rhoHat. |
| la-tele tail | `ActionSteps.tail_sum_le` L251 | PASS | 20 rhoHat_j Ehat_j, with correct shifted indices. |
| la-tele convergence | `ActionSteps.chain_limit` L270 | PASS | Completeness plus the same summable step bound. |
| limit-actions; la-loc; la-lip | `limit_actions_of_steps` L289 | PASS WITH NOTES | Uniform convergence, blocks, tails, strict stage half-tubes, defect bound, injectivity and frequency; see endpoint note. |
| Release-gate applicability | `iterative_actionSteps` L428 | PASS | All fields discharged on one P23-16 tuple. Future joint consumer remains separate. |

The endpoint is existentially quantified after all stage witnesses, a function on real Fin-Pi actions; all claims are restricted to `Ds 0`. All constants depend only on the stated scale data and dimension. Uniformity is genuine `TendstoUniformlyOn`, not merely pointwise convergence. The proof uses a stage-independent geometric majorant. Tail estimates are at every j, including zero. Location uses exactly `(seq p j).ρ / 2` and the actual open frozen tube. Lipschitz estimates use the same i at every pair, not pointwise-selected incompatible maps. `chain_freq` concerns `actionChain is j`, not a substituted inverse or limit chain.

## Definition classification

- `ActionSteps`: transparent Prop structure collecting proved outputs. BODY_MATCH=OK as an internal interface; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS **as a private proof bundle only**, not a literal source hypothesis.
- `actionChain`: literal total primitive recursion on ℕ, identity then real part of successive given complex maps. BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS. No fallback, conditional junk branch or arbitrary stage choice. Real projection is mathematically exact on the asserted domain, independently proved by `incl_chain_succ` from the produced real-base mapping property.
- No other new def/abbrev/structure. The proof-local `choose! i` selects proved limits, not an exported arbitrary averaged-map definition. On `Ds 0` uniqueness follows from uniqueness of limits in the finite-dimensional Hausdorff space. Values off `Ds 0` are never used to claim source properties, invertibility on the full ambient space, or an ambient extension. The empty-domain case is vacuous.

## Notes, endpoint conventions, and release limits

**N1 — Non-strict initial displacement is not literally the open-tube corollary.** P3b L24 says “in particular Dstar ⊂ Re(D0)_(20 Ehat0 rhoHat0)”. The exported L298 bound is `≤ 20 Ehat0 rhoHat0`; with frozen `actionNbhd` (strict `<`), that inequality alone does not imply membership in this open tube. This is a genuine distinction in the private conclusion, not an interchangeable endpoint convention. The design's explicit `limit_actions` bullet is covered, including strict half-radius tubes at every stage. The extra source corollary is recoverable from the retained same-witness data: Ehat0>0 follows from Ehat1≥0 and Ehat1<Ehat0²; Ehat1≤Ehat0, rhoHat1≤rhoHat0/16, and triangle with the j=1 tail give

    ‖i I - I‖ ≤ 10 Ehat0 rhoHat0 + 20 rhoHat1 Ehat1
                 ≤ (45/4) Ehat0 rhoHat0 < 20 Ehat0 rhoHat0.

This uses no additional premise. The scratch probe checks that implication from `S` and the actual tail conclusion. Keep this corollary when consuming the full blueprint claim; the non-strict displayed bound alone is weaker. No claim here that an exported source-facing theorem already contains the strict corollary.

**N2 — Stronger stage smallness and cast normalization are sound.** `Ehat_j<1/160` is proved upstream from the same stage `KamHyp` (IterationReal L36), rather than assumed as an added premise; it implies the blueprint's 1/40. In the location proof, 20 Ehat_j<1/8 together with rhoHat_j≤rho_j and positive radius gives strict `<rho_j/2`. Natural addition casts and the real sum of casts agree by `Nat.cast_add`; the explicit rewrites in the chain recursion and final result enforce that equality. There is no changed n or constant dependency.

The two-sided estimates use the explicit upper bound Λ=2560n Ehat0 in place of the optimal defect seminorm λ. This supplies the standard quantitative bi-Lipschitz consequence with Λ<1/3; the pairwise defect inequality also implies the source seminorm bound. It does not assert a different norm or a fixed 9/10 factor.

**N3 — Private release gate scope.** Exact helper types and this same-witness applicability audit are supplied here. No frozen anchor changes, provider sealing, or completed P23-22 consumer exist in this package. Later packages must preserve the original iterative tuple and invoke this helper in that joint proof. This audit cannot certify those future applications or close an unrelated planetary root. “Private” is the design's interface status; these Lean names are publicly accessible, not declared with the Lean `private` keyword.

Suspected pinned-source defects: **none established**. P3b L36 writes a non-strict intermediate inequality while claiming an open half-tube; its strict smallness premise does give the strict estimate, and the Lean proof supplies it. P3b L24's tighter initial tube requires the sharper estimate above. These are exposed endpoint details, not a refutation of the blueprint. Deviations introduced by this audit: none in production code.

## Exact private signature and applicability command

The following is the complete helper command, in the file's variable context L34–36 and namespace `KAM.Planetary`:

```lean
theorem limit_actions_of_steps (S : ActionSteps sbar p h Ds hs fs is) :
    ∃ i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ),
      TendstoUniformlyOn (actionChain is) i atTop (Ds 0) ∧
      (∀ I ∈ Ds 0, ∀ j, actionChain is j I ∈ Ds j) ∧
      (∀ I ∈ Ds 0,
        ‖firstBlock (b := b) (i I - I)‖ ≤
          20 * (p.Mbar₁ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) ∧
        ‖lastBlock (a := a) (i I - I)‖ ≤
          20 * (p.Mbar₂ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) ∧
        ‖i I - I‖ ≤ 20 * eHat (seq p 0) * rhoHat (seq p 0)) ∧
      (∀ I ∈ Ds 0, ∀ j, ‖i I - actionChain is j I‖ ≤ 20 * rhoHat (seq p j) * eHat (seq p j)) ∧
      (∀ I ∈ Ds 0, ∀ j, i I ∈ realTube (Ds j) ((seq p j).ρ / 2)) ∧
      (∀ I ∈ Ds 0, ∀ J ∈ Ds 0,
        ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat (seq p 0) * ‖I - J‖) ∧
      2560 * (a + b : ℝ) * eHat (seq p 0) < 1 / 3 ∧
      (∀ I ∈ Ds 0, ∀ J ∈ Ds 0,
        (1 - 2560 * (a + b : ℝ) * eHat (seq p 0)) * ‖I - J‖ ≤ ‖i I - i J‖ ∧
        ‖i I - i J‖ ≤ (1 + 2560 * (a + b : ℝ) * eHat (seq p 0)) * ‖I - J‖) ∧
      Set.InjOn i (Ds 0) ∧
      (∀ I ∈ Ds 0, ∀ j, realFreq (hs j) (actionChain is j I) = realFreq h I) := by
  classical
  choose! i hi using fun I (hI : I ∈ Ds 0) => S.chain_limit hI
  have hn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  have e0 := S.e_nonneg 0
  have hsm := S.two_sided_small
  have hlam : 2560 * ((a + b : ℕ) : ℝ) * eHat (seq p 0) < 1 / 3 := by nlinarith
  rw [Nat.cast_add] at hlam
  have hlamN : 2560 * (((a + b : ℕ) : ℝ)) * eHat (seq p 0) < 1 / 3 := by
    rw [Nat.cast_add]; exact hlam
  -- block and sup bounds at the limit
  have hcF : Continuous fun v : Fin (a + b) → ℝ => firstBlock (b := b) v :=
    continuous_pi fun k => continuous_apply _
  have hcL : Continuous fun v : Fin (a + b) → ℝ => lastBlock (a := a) v :=
    continuous_pi fun k => continuous_apply _
  have hblk : ∀ I ∈ Ds 0,
      ‖firstBlock (b := b) (i I - I)‖ ≤
        20 * (p.Mbar₁ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) ∧
      ‖lastBlock (a := a) (i I - I)‖ ≤
        20 * (p.Mbar₂ / p.Mbar) * eHat (seq p 0) * rhoHat (seq p 0) := by
    intro I hI
    have hl := (hi I hI).1
    have t1 : Tendsto (fun j => ‖firstBlock (b := b) (actionChain is j I - I)‖) atTop
        (𝓝 ‖firstBlock (b := b) (i I - I)‖) :=
      ((hcF.comp (continuous_id.sub continuous_const)).norm.tendsto _).comp hl
    have t2 : Tendsto (fun j => ‖lastBlock (a := a) (actionChain is j I - I)‖) atTop
        (𝓝 ‖lastBlock (a := a) (i I - I)‖) :=
      ((hcL.comp (continuous_id.sub continuous_const)).norm.tendsto _).comp hl
    exact ⟨le_of_tendsto' t1 fun j => (S.chain_block_le hI j).1,
      le_of_tendsto' t2 fun j => (S.chain_block_le hI j).2⟩
  have hsup : ∀ I ∈ Ds 0, ‖i I - I‖ ≤ 20 * eHat (seq p 0) * rhoHat (seq p 0) := by
    intro I hI
    obtain ⟨b1, b2⟩ := hblk I hI
    obtain ⟨r1, r2⟩ := S.ratio_le_one
    have := mul_nonneg e0 (S.rho_pos 0).le
    rw [← KAM.norm_realInclusion]
    refine (S.hyp 0).sup_norm_le (mul_nonneg (mul_nonneg (by norm_num) e0) (S.rho_pos 0).le) ?_ ?_
    · rw [ActionSteps.norm_first_incl]
      nlinarith
    · rw [ActionSteps.norm_last_incl]
      nlinarith
  have hLip : ∀ I ∈ Ds 0, ∀ J ∈ Ds 0,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * ((a + b : ℕ) : ℝ) * eHat (seq p 0) * ‖I - J‖ := by
    intro I hI J hJ
    have t : Tendsto (fun j => ‖(actionChain is j I - I) - (actionChain is j J - J)‖) atTop
        (𝓝 ‖(i I - I) - (i J - J)‖) :=
      (((hi I hI).1.sub_const I).sub ((hi J hJ).1.sub_const J)).norm
    refine le_of_tendsto' t fun j => (S.chain_lip hI hJ j).trans ?_
    have := S.prod_le j
    gcongr
    linarith
  have hlow : ∀ I ∈ Ds 0, ∀ J ∈ Ds 0,
      (1 - 2560 * ((a + b : ℕ) : ℝ) * eHat (seq p 0)) * ‖I - J‖ ≤ ‖i I - i J‖ ∧
      ‖i I - i J‖ ≤ (1 + 2560 * ((a + b : ℕ) : ℝ) * eHat (seq p 0)) * ‖I - J‖ := by
    intro I hI J hJ
    have hl := hLip I hI J hJ
    have e : i I - i J = (I - J) + ((i I - I) - (i J - J)) := by abel
    constructor
    · have := norm_sub_norm_le (I - J) (-((i I - I) - (i J - J)))
      have e' : i I - i J = (I - J) - (-((i I - I) - (i J - J))) := by abel
      rw [e']
      refine le_trans ?_ (norm_sub_norm_le _ _)
      rw [norm_neg]; linarith
    · rw [e]; refine (norm_add_le _ _).trans ?_; linarith
  refine ⟨i, ?_, fun I hI j => S.chain_mem hI j, fun I hI => ⟨(hblk I hI).1, (hblk I hI).2,
    hsup I hI⟩, fun I hI j => (hi I hI).2 j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hr0 := S.rho_pos 0
    have tz : Tendsto (fun j : ℕ => 10 * rhoHat (seq p 0) * (1 / 16 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num)).const_mul (10 * rhoHat (seq p 0))
    filter_upwards [tz.eventually (gt_mem_nhds hε)] with j hj I hI
    rw [dist_eq_norm]
    have h1 := S.scalar_sums.2 j
    have h2 : eHat (seq p j) ≤ 1 / 2 := by
      have := (S.hyp j).eHat_lt_small; linarith
    have := S.e_nonneg j
    have := S.rho_pos j
    calc _ ≤ 20 * rhoHat (seq p j) * eHat (seq p j) := by
          exact (hi I hI).2 j
      _ ≤ 10 * rhoHat (seq p j) := by nlinarith
      _ ≤ 10 * (rhoHat (seq p 0) / 16 ^ j) := by gcongr
      _ = 10 * rhoHat (seq p 0) * (1 / 16 : ℝ) ^ j := by rw [one_div, inv_pow]; ring
      _ < ε := hj
  · intro I hI j
    refine ⟨actionChain is j I, S.chain_mem hI j, ?_⟩
    have hb := (hi I hI).2 j
    have hρ : rhoHat (seq p j) ≤ (seq p j).ρ := (S.hyp j).R_le_ρ
    have hR := S.rho_pos j
    have he := (S.hyp j).eHat_lt_small
    have : ‖KAM.realInclusion (a + b) (i I) - (fun k => ((actionChain is j I k : ℝ) : ℂ))‖ =
        ‖i I - actionChain is j I‖ := by
      have e : (fun k => ((actionChain is j I k : ℝ) : ℂ)) =
          KAM.realInclusion (a + b) (actionChain is j I) := rfl
      rw [e, ← map_sub, KAM.norm_realInclusion]
    rw [this]
    nlinarith [S.e_nonneg j]
  · intro I hI J hJ
    have := hLip I hI J hJ
    rw [Nat.cast_add] at this
    exact this
  · rw [← Nat.cast_add]; exact hlamN
  · intro I hI J hJ
    have := hlow I hI J hJ
    rw [Nat.cast_add] at this
    exact this
  · intro I hI J hJ hIJ
    have := (hlow I hI J hJ).1
    rw [hIJ, sub_self, norm_zero] at this
    have hpos : 0 < 1 - 2560 * ((a + b : ℕ) : ℝ) * eHat (seq p 0) := by linarith
    have := le_antisymm this
      (by positivity : 0 ≤ (1 - 2560 * ((a + b : ℕ) : ℝ) * eHat (seq p 0)) * ‖I - J‖)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact sub_eq_zero.1 (norm_eq_zero.1 h)
  · intro I hI j; exact S.chain_freq hI j
```

The complete applicability command (same context) is:

```lean
theorem iterative_actionSteps {D : Set (Fin (a + b) → ℝ)} {f : CHam (a + b)}
    (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧ ActionSteps sbar p h Ds hs fs is := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, h0, h1, -, -, -, hK, -, hI, -, ht, -, hr⟩ := iterative H
  exact ⟨Ds, hs, fs, Ψ, Φ, is, h0, ⟨h1, hK, fun j => (hI j).2.1, fun j => (hI j).2.2.1,
    fun j => (hI j).2.2.2, fun j => (ht j).2.2, fun j => (hr j).1, fun j => (hr j).2.2.1⟩⟩

```

## Independent verification receipts

All Lean/Lake invocations were serialized within this audit, at niceness 5 and with `LEAN_NUM_THREADS=1`. The targeted build used the prescribed gate; no clean/update/cache fetch or dependency edits occurred.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2317 KAM.Planetary.TwoScale.LimitActions
```

Exit **0**. Output included `[inp-gate] slot 2 acquired 12:27:24 for KAM.Planetary.TwoScale.LimitActions` and `Build completed successfully (9165 jobs).` This was a warm replay build, not an independently forced recompilation. Scoped warnings: unused Ψ and Φ at L431. Replayed upstream warnings were unused variables in Diophantine, Inverse, StepNonres, Finite and deprecated APIs in StepNonres/StepPerturb; no errors or sorry warnings.

2. Public-theorem axioms and exact same-witness/endpoint probes:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2317Audit.lean
```

Final run exit **0**, only the two unused Ψ/Φ probe warnings. Exact axiom output for all 23 exports:

```text
'KAM.Planetary.ActionSteps.chain_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.incl_chain_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.norm_first_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.norm_last_incl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.chain_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.chain_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.e_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.scalar_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.rho_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.rho_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.partial_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.chain_block_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.ratio_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.chain_sup_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.chain_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.two_sided_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.prod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.summable_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.tail_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ActionSteps.chain_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limit_actions_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iterative_actionSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The final probe examples, preserved here so the deleted scratch is reproducible after importing LimitActions and opening the namespaces used by that module:

```lean
variable {a b : ℕ} {sbar : ℝ} {p : ScaleData} {h : (Fin (a+b) → ℂ) → ℂ}
 {Ds : ℕ → Set (Fin (a+b) → ℝ)} {hs : ℕ → (Fin (a+b) → ℂ) → ℂ}
 {fs : ℕ → CHam (a+b)} {is : ℕ → (Fin (a+b) → ℂ) → (Fin (a+b) → ℂ)}
example {D : Set (Fin (a+b) → ℝ)} {f : CHam (a+b)} (H : KamHyp D sbar p h f) :
 ∃ (Ds : ℕ → Set (Fin (a+b) → ℝ)) (hs : ℕ → (Fin (a+b) → ℂ) → ℂ)
   (fs : ℕ → CHam (a+b)) (Ψ Φ : ℕ → CPhase (a+b) → CPhase (a+b))
   (is : ℕ → (Fin (a+b) → ℂ) → (Fin (a+b) → ℂ))
   (i : (Fin (a+b) → ℝ) → (Fin (a+b) → ℝ)),
   Ds 0 = dioBase D h p ∧ ActionSteps sbar p h Ds hs fs is ∧
   TendstoUniformlyOn (actionChain is) i atTop (Ds 0) := by
 obtain ⟨Ds, hs, fs, Ψ, Φ, is, h0, h1, -, -, -, hK, -, hI, -, ht, -, hr⟩ := iterative H
 have S : ActionSteps sbar p h Ds hs fs is :=
   ⟨h1, hK, fun j => (hI j).2.1, fun j => (hI j).2.2.1,
    fun j => (hI j).2.2.2, fun j => (ht j).2.2, fun j => (hr j).1, fun j => (hr j).2.2.1⟩
 obtain ⟨i, hi⟩ := limit_actions_of_steps S
 exact ⟨Ds, hs, fs, Ψ, Φ, is, i, h0, S, hi.1⟩

-- Does the same tail output imply the blueprint's strict initial tube?
example (S : ActionSteps sbar p h Ds hs fs is)
 (i : (Fin (a+b) → ℝ) → (Fin (a+b) → ℝ))
 (htail : ∀ I ∈ Ds 0, ∀ j, ‖i I - actionChain is j I‖ ≤ 20 * rhoHat (seq p j) * eHat (seq p j))
 {I : Fin (a+b) → ℝ} (hI : I ∈ Ds 0) :
 ‖i I - I‖ < 20 * eHat (seq p 0) * rhoHat (seq p 0) := by
 have he0 : 0 < eHat (seq p 0) := by
   have := S.e_nonneg 0
   have := S.e_nonneg 1
   have := S.eHat_sq 0
   nlinarith
 have he1 := S.e_nonneg 1
 have heSmall := (S.hyp 0).eHat_lt_small
 have heSq := S.eHat_sq 0
 have he : eHat (seq p 1) ≤ eHat (seq p 0) := by nlinarith
 have hr0 := S.rho_pos 0
 have hr1 := S.rho_pos 1
 have hr : rhoHat (seq p 1) ≤ rhoHat (seq p 0) / 16 := S.rho_hi 0
 have ht := htail I hI 1
 have hc := S.chain_sup_step hI 0
 change ‖actionChain is 1 I - I‖ ≤ 10 * eHat (seq p 0) * rhoHat (seq p 0) at hc
 have bound : rhoHat (seq p 1) * eHat (seq p 1) ≤
     (rhoHat (seq p 0) / 16) * eHat (seq p 0) :=
   mul_le_mul hr he he1 (by positivity)
 have triangle := norm_add_le (i I - actionChain is 1 I) (actionChain is 1 I - I)
 have eqn : (i I - actionChain is 1 I) + (actionChain is 1 I - I) = i I - I := by abel
 rw [eqn] at triangle
 nlinarith [mul_pos he0 hr0]
```

Probe development: the first attempt referenced an upstream non-exported `KamHyp.eHat_pos` lemma; it was replaced by a direct argument from the produced nonnegativity and quadratic recurrence. A subsequent failed tactic compared a fully unfolded chain norm against an unexpanded one; a definitional `change` aligned them. Neither failure was in package code, and both are resolved in the successful final probe above.

3. Kernel replay, one invocation for both modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.LimitActionsChain KAM.Planetary.TwoScale.LimitActions
```

Exit **0**, exact output:

```text
replaying KAM.Planetary.TwoScale.LimitActions
replaying KAM.Planetary.TwoScale.LimitActionsChain
```

4. Static import and hygiene inspection: project import closure has 119 modules, no provider imports and no frozen theorem imports. The twelve frozen imports are all manifest-state SEALED definitions: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary Fast, Phase, Slow. Scoped files have copyright/license/authors, `module`, `public import`, module docstring and exposed public noncomputable section. No forbidden proof escape, resource override or EuclideanSpace occurs; both entire files are below 1500 lines.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Both exited **0** with empty output. Scope is also identical against inp-p2316. Source SHA256 values:

```text
9ce919f1bf434050bf384ad28da29a6e7e095d21a80e6d79f111b33181ec3077  KAM/Planetary/TwoScale/LimitActions.lean
700f31068af00649ebc5561c93d08842b143efef4a663b50a29c706f300ad10d  KAM/Planetary/TwoScale/LimitActionsChain.lean
```

5. Full source lint (after the build, probe and kernel replay finished):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, exact combined output in order:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (574 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the stale generated root explicitly permitted by the audit brief. No generated root was edited. The complete frozen textual guard and elaborated ABI checks passed; this is not merely a static-only lint receipt. An earlier preliminary lint was stopped in its Python textual-check phase before it could launch ABI Lean, then rerun fully with the environment/niceness above after the other Lean jobs completed. No overlapping audit Lean/Lake invocation occurred.

6. Final report/scope checks:

```sh
git diff --check
git diff --no-index --check /dev/null /root/code/KAM-inp-p2317/docs/tracks/P/audits/P23-17-audit-1.md
git status --short
```

Whitespace checks exited **0**, no output. Independent inventory check: **PASS (23 theorem rows, 2 definition rows)**. Final status contains only this untracked report and the pre-existing untracked `P23-17-handoff.md`; no tracked source modification. The audit-owned probe was deleted. Protected paths remain unchanged.

Final disposition: **PASS WITH NOTES, private conditional P23-17 package**. Same-witness applicability, the complete design bullet, permitted axiom closure and kernel replay pass. The non-strict initial bound requires the proved strict corollary above for literal open-tube consumption; actual future joint P23-22 integration remains outside this audit. No frozen result is sealed by this verdict.
