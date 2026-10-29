# N11-N / N11-P independent audit 1 (refute-first, by reading)

Date: 2026-10-28. Auditor: independent Claude agent. Lean was **not** run (it cannot run on this machine);
all statements below come from reading and grep. The remote compile was reported by the caller, not
re-checked here.

## Verdicts

- **N11-N (`KAM/Nekhoroshev/Partial/Block.lean`, `block`, node `bpN:p11:block`): PASS WITH NOTES.**
  The signed statement matches exactly. The slice is complete and the proof is sound, given the two signed
  placeholders `nonresonant` and `resonant`. The short-name reuse NP-1 was present in the revision
  read when the audit began, and was fixed in the revision audited (rename at 18:51, verified). The
  remaining finding, NP-2, is low severity and does not block.
- **N11-P (`KAM/Provider/Nekhoroshev/PartialConvexNekhoroshev.lean`, the provider for `bpN:p0:partial`):
  PASS WITH NOTES.** The type is the frozen anchor's text exactly, and it resolves to the same constants.
  The empty-G branch, the quantifier order, the σ = −1 time reversal and the quarantine are all correct.
  Sealing still waits on the real N11-M1 and N11-M2 proofs (Note N-4).

## Scope and revisions audited

| Item | Value |
|---|---|
| Block.lean | `SP/n11/w/KAM/Nekhoroshev/Partial/Block.lean`, 411 lines, sha256 `fccc1ba3ed26a872d5e454551cc1347e9dcb5e257a98f29f2d6d3dabfbac5829` (mtime 18:51). **It changed during the audit:** the 18:35 revision had `slowScale_extCx` at L61 (see NP-1). The only diff is that rename plus a line wrap. |
| Provider | `SP/n11/w/KAM/Provider/Nekhoroshev/PartialConvexNekhoroshev.lean`, 155 lines, sha256 `3b7530dbae66dcd7dc5dced07599459876b681bbec0100f7957673a1bf2d6474` |
| Signature file | `SP/n11/N11Sig-zohar.lean` (sha256 `a70ec4d6…`). Block at L723–738 and the provider at L815–844 also match `REPO/docs/tracks/N/design/N11-SIGNATURES.md`, `N11Sig-live.lean` and `N11Signatures.lean`; those variants differ only in `iterative`/`canonical_map`. |
| Frozen anchor | `REPO/KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean`, sha256 `e6bb9443…`. This equals the design's pin (N11-LEAN-DESIGN L19). |
| Upstream | REPO detached at `lane-n-handoff` (`89d9eca2`), clean |
| Placeholders | `SP/n11/w/.../Nonresonant.lean` and `Resonant.lean`. After whitespace normalization they equal signature L601–612 and L614–626. |

## (a) Signed declarations: equality with the signature file

| Declaration | Signature / frozen source | Implementation | Context check | Result |
|---|---|---|---|---|
| `KAM.Nekhoroshev.block` | N11Sig-zohar L723–738 | Block.lean L237–252 | `diff` of the statement text is empty. The signature context opens `Set Metric KAM.Weighted KAM.NormalForm`; the implementation opens only `Set`. Every identifier in the statement resolves in `KAM.Nekhoroshev` (`PartialData`, `DefiniteSign`, `constants`, `IsPartialPerturbation`, `ER`, `realWfield`, `liftFast`, `signedH`, `signedF`, `extCx`, `physicalDomain`, `innerCore`, `fastAction`, `slowPair`), at root (`HasDerivAt`, `Real.pi`) or via `Set` (`EqOn`, `uIcc`). A whole-KAM grep finds no same-named declaration in an opened namespace (the only other `constants` is in `KAM.Planetary.TwoScale`), so both contexts elaborate the same term. | **EXACT** |
| `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` | anchor L48–77; signature L815–844 | provider L52–81 | `diff` against the anchor differs only in `:=` versus `:= by`. Binder names, order and explicitness are identical: `{n k}` plus 23 explicit binders. Name resolution is analysed under "Seal-key checks" below. | **EXACT** |

## (b) Node coverage

| Graph node | Declaration / location | Result | Reason |
|---|---|---|---|
| `bpN:p11:block` | `block`, Block.lean L237–407 | PASS | Signed, equal to the signature. The conclusion is `‖fastAction (y u) − Ic‖ ≤ R0/(2K)` on `uIcc 0 t1`, the literal sup-norm conclusion. |
| `stepN:p11:bl-block` | L270–276 | PASS | `block_data a hne hμ hε hσ hκ hIc` gives Λ, r with r_Θ ≤ r ≤ R0/K, 0 < r, and α = (9/8)M1Kr. r_B = r through `block_setting a μ Ic r`, so λ = w/r and c = 2π/λ² hold by definition. `hrr0 : r ≤ r0` comes from K ≥ 1 and A ≥ 1 (L273–274). |
| `stepN:p11:bl-sl` | L277–292 | PASS | 64πk·s·r = 16kρr ≤ d²/16 = w². This follows from (B2), multiplied out (L280), and r·K ≤ R0 (L282). |
| `stepN:p11:bl-ext` | L293–353, with `nblk_transport` L167 and `nblk_dom` L195 | PASS | `domain` supplies `ext_class` and `WBound ≤ ε` for f̆ (L296). `hconv.hol` gives h̆ holomorphic on V_r(Ic). `ExtNFHyp` is assembled with K_a = K/√n, α, L = √n·M1, p = 9/8 and κ = 2πK_a·s, and `divisor_size` holds with equality. ỹ = S_λ⁻¹y solves the weight-c field on W^e_r (`hFt`, `hyt`), and S_λ(W^e_r) ⊆ 𝒲(Ic, r0) (`nblk_dom`). core(D, d) ⊆ S = core(D, 3d/4) is `hcore` (L342–347). |
| `stepN:p11:bl-theta` | L368–391 | PASS | Λ = ⊥ is rewritten to `{0}` (L369–370). `conjExp (9/8) = 9`, and `hsmall` is block-data (5). T_nr ≥ T_P because m1·r_Θ ≤ M1·r and 5 ≤ 240 (L376–388). Finally r/2 ≤ R0/(2K) (L354–356). |
| `stepN:p11:bl-res` | L392–407 | PASS | `NearResonance` at δ < m1r/32 is weakened to m1r/32 (L393–396). `hε1` covers (5), and `hconv` is the m1/M1 convexity. T_Λ ≥ T_P because r_Θ ≤ r (L397–404). Then ‖·‖∞ ≤ euclid by `norm_le_euclid`, `bpN:p1:norm-compare` (L407). |
| `bpN:p0:partial` | `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` | PASS | Frozen type exactly, proved from `block`, `threshold`, `domain_field`, `orbit` and `theta_*`. |
| `stepN:p11:final-empty` | provider L83–88 | PASS | G = ∅ gives μ₀ = 1, and `hz0.1 : fast(z 0).2 ∈ ∅` is absurd. For G ≠ ∅, m ≤ M_C comes from `hessian_at_sign` inside `block` (Block L264). |
| `stepN:p11:final-data` | provider L89–96, plus `constants` | PASS (Note N-7) | `PartialData` is built from exactly the 23 frozen binders, and the constants are definitional (Constants.lean L52–74). The side remark A ≥ 11 is not stated; only 1 ≤ A is used (Block L265–267). |
| `stepN:p11:final-mu` | provider L97–100 | PASS | `threshold a hne` gives all six comparisons (ε ≤ ε0, d ≤ ρ, κ ≥ 6, (B2), R0/(2K) ≤ d/2, time), and all six are used. The explicit μ_a…μ_f are GAP-A's `nthr_final_mu` (graph LEAN_REF). |
| `stepN:p11:final-time` | provider L100 (`htime`), L108 | PASS | μ⁻¹exp(μ^(−a_n)) ≤ blockTime. The closed form T_P is GAP-A's `nthr_final_time`. |
| `stepN:p11:final-given` | provider L105–108 | PASS | t ≥ 0, t ≤ C and t ≤ T_P. The case t = 0 is covered uniformly (`uIcc 0 0`). |
| `stepN:p11:final-orbit` | provider L109–119 | PASS | `IsSolutionOn` is unpacked (`.2.1` DifferentiableAt, `.2.2` HasDerivAt), and `orbit` converts it to (θ∘z)′ = X^{2π}_{Ĥ}. `domain_field` at R = r0 identifies σF0 on 𝒲(Ic, r0). The slow pair comes via `theta_slowq`/`theta_slowp`, and x(0) ∈ S via `innerCore_mono`. |
| `stepN:p11:final-sign` | provider L124–151 | PASS | For σ = 1: J = [0, C], F = 1•F0, t1 = t. For σ = −1: ȳ(u) = θ(z(−u)) with derivative from `HasDerivAt.scomp` and `hasDerivAt_neg`, J = [−C, 0], F = (−1)•F0, t1 = −t; `hstop` uses `uIcc_of_ge`, and `neg_neg` brings the result back. |
| `stepN:p11:final-drift` | provider L120–123 | PASS | R0/(2K) ≤ d/2 = μ^{b_n}/2, and `fastAction ∘ theta = fast` (`fastAction_theta`). |
| `stepN:p11:final-order` | provider L97–99 | PASS (Note N-7) | μ₀ is obtained from `threshold a hne` before `refine` introduces μ, P, C, z, t. That μ₀ depends only on (n, k, ρ, g, m, Mc) holds by construction: `threshold` is `nthr_key (constants a) k …` (Threshold.lean L191–192). |

No unsigned export is named after a graph node.

## (c) Soundness: the `nblk*` helpers checked by hand

| Helper | Line | Content | Check |
|---|---|---|---|
| `nblkFactor`, `nblkScale` | 34, 37 | S_t(θ; I, x) = (θ; I, t·x) | Correct definitions |
| `nblkFactor_fast`, `nblkFactor_slow` | 39, 42 | Factor 1 on fast coordinates, t on slow ones | ✓ |
| `nblkScale_cancel` | 45 | t ≠ 0 ⇒ S_t ∘ S_{t⁻¹} = id | ✓ |
| `fastAction_nblkScale`, `slowPair_nblkScale` | 53, 56 | I is unchanged; slowPair ↦ t • slowPair | ✓ |
| `nblk_slowScale_extCx` | 61 | `slowScale t ∘ extCx = extCx ∘ S_t` | ✓ (same content as private Domain.lean:354) |
| `nblkCLM`, `nblkCLM_apply`, `nblkCLE`, `nblkCLE_apply` | 76–94 | S_t as a CLM, and as a CLE with inverse S_{t⁻¹} for t ≠ 0 | ✓ (extensionally equal to the public `slowScaleReal`) |
| `nblkScale_single`, `_fst`, `_fst'`, `_snd`, `fastAction_extCx_nblkScale` | 96–116 | Basis-vector and component identities | ✓ |
| `nblk_isOpen` | 118 | `b.realDom R` is open: preimage of the open `Dom` under the continuous `extCx` | ✓ |
| `nblk_field` | 127 | t ≠ 0, c·t² = 2π, Hs = Hp∘S_t on an open U ∋ z ⇒ X^c_{Hs}(z) = S_t⁻¹ X^{2π}_{Hp}(S_t z) | ✓ Mathematically, ∂_{q,p}Hs = t·∂_{q,p}Hp and c·t = 2π/t. No differentiability premise is needed, because `comp_right_fderiv` applies to an equivalence. No added premise. |
| `nblk_transport` | 167 | Given rB, w > 0, Re Hc∘extCx = Hp∘S_λ on W^e_{rB}, S_λ(W^e) ⊆ W and F = X^{2π}_{Hp} on W: S_λ⁻¹FS_λ = X^c_{realHamiltonianExt} on W^e, and ỹ = S_λ⁻¹y satisfies ỹ′ = (S_λ⁻¹FS_λ)(ỹ) | ✓ c·λ² = 2π because c := 2π/λ², and λ ≠ 0 from both positivity premises (pitfall §9.2 handled). |
| `nblk_dom` | 195 | z ∈ W^e_r ⇒ S_λz ∈ `physicalDomain Ic r0 (d/4) (innerCore D (3d/4))`, using λ·r = d/4 and r ≤ r0 | ✓ |

Duplication with upstream is content only; no name clashes (Note N-1).

On the provider side, `slowPair_theta`, `fastAction_theta` and `innerCore_mono` are correct as stated. No premise is added to any signed declaration. No conclusion-shaped hypothesis appears.

## Seal-key checks (provider, by reading)

| Check | Result |
|---|---|
| Exact frozen type | **PASS.** The text is identical to anchor L48–77. Unqualified statement identifiers (`HasDefiniteFastPart`, `IsPartialPerturbation`, `IsSolutionOn`, `realPart`, `complexifyPhase`, `innerCore`, `partialDriftExponent`, `partialTimeExponent`) are all `KAM.Nekhoroshev.*` frozen definitions. The anchor reaches them as namespace members; the provider reaches them through `open KAM.Nekhoroshev`. No `KAM.X` or `KAM.Provider.X` declaration exists that would win first in the provider's namespace. The other `innerCore` and `realPart` live in `KAM.Planetary` and `KAM.Iso.Confinement`, which are never opened. KAM has no nested `Real`/`Set`/`Metric` namespaces. The 113-module KAM import closure has no `instance`, no `scoped` or `local` instance/notation, and no `attribute [instance]`. The provider's extra `open Set` adds no candidate for any statement identifier. Conclusion: the provider's type elaborates the same as the anchor's, and importing the provider at the seal leaves the anchor's elaboration unchanged. |
| Manifest | `manifest/frozen-anchors.json` L8914–9020: id `nekhoroshev.d25.partialConvex_nekhoroshev.v1`, path `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean`, export `KAM.Nekhoroshev.partialConvex_nekhoroshev`, implementation module `KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev`, export `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev`, state DRAFT_SORRY. ✓ |
| Seal body binders | The 23 explicit binders, in order, are `hn hk G G' D hG hGc hG' hGc' hD ρ g m Mcomplex hρ hMc hcollar h hhol hC2 hreal hHess hdef`. This matches LANE-N-HANDOFF §3. ✓ |
| Empty-G branch | L84–88: `Set.eq_empty_or_nonempty`, μ₀ = 1, contradiction from `hz0.1`. ✓ |
| μ₀ before μ, P, C, z, t | L98 `obtain ⟨μ0, hμ0, hthr⟩ := threshold a hne`, then L99 `refine ⟨μ0, hμ0, fun μ … t ht hslow => ?_⟩`. ✓ |
| σ = −1 time reversal | L135–151, as in the node table. Derivative: `(horb (−u) hu').scomp u (hasDerivAt_neg u)` gives `(−1) • F0(θ(z(−u)))`. ✓ |
| Quarantine | Imports (L8–10) are `Partial.Block`, `Partial.Threshold` and `Frozen.Nekhoroshev.Defs.IsSolutionOn`. The transitive KAM closure (113 modules) contains no `KAM.Frozen.*.Theorems.*` module and no `KAM.Provider.*` module other than itself. ✓ The root generator skips DRAFT_SORRY providers (`gen_root_imports.py` L42–55). |
| sorry / axiom sources | Only `Partial/Nonresonant.lean` and `Partial/Resonant.lean`, the expected placeholders. No other module in the closure contains `sorry`, `admit` or `axiom`. |

## (d) Hygiene

| Check | Block.lean | Provider |
|---|---|---|
| Lines ≤ 100 (Unicode count) | max 100 (L283) ✓ | max 99 (L16) ✓ |
| File ≤ 1500 lines | 411 ✓ (design estimate 450) | 155 ✓ (design estimate 300) |
| `sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`set_option`/`maxHeartbeats` | none ✓ | none ✓ |
| `EuclideanSpace` | none ✓ (`euclid` is the KAM `Fin n` function) | none ✓ |
| Module form (`check_lean_modules.py --files`) | PASS ✓ | PASS ✓ |
| Reused public helper short names (whole `REPO/KAM` grep, including private declarations) | 21 helpers. In the audited revision, none is reused; `nblk_slowScale_extCx` is unique. Earlier revision: NP-1. | 3 helpers (`slowPair_theta`, `fastAction_theta`, `innerCore_mono`), none reused. This includes the shared `KAM.Provider.Nekhoroshev` namespace with 6 other providers. |
| Signed names | `block`: no other declaration in KAM | `partialConvex_nekhoroshev`: only the frozen anchor, the expected pairing |
| Harmful root shadow | None, judged by the names (Mathlib is not available locally; no helper name is a plausible root Mathlib name). `block` occurs in KAM only in prose. | None |
| Redefined signed or upstream declarations | None. `block_data`, `domain`, `domain_field`, `hessian_at_sign`, `threshold`, `orbit`, `theta_*` and `nthr_pos` are imported. | None |

## Findings

**NP-1. Hygiene (d), reused public helper short name. Severity: blocking under rule (d). RESOLVED in the
audited revision (verified).**
`Block.lean:61` (18:35 revision) declared public `theorem slowScale_extCx`. That reuses the short name of
`private theorem slowScale_extCx` in `REPO/KAM/Nekhoroshev/Partial/Domain.lean:354`: same namespace
`KAM.Nekhoroshev`, near-identical content. It compiled only because the Domain declaration is private.
`import all` of Domain together with Block would expose both names.
Fix, already applied at 18:51: rename to `nblk_slowScale_extCx` (L61, use at L336). A re-grep of `REPO/KAM` finds no other
declaration ending in `nblk_slowScale_extCx`. Remaining action: re-run the remote compile on revision
`fccc1ba3…`. The change is a rename plus a line wrap, so the risk is negligible.

**NP-2. Campaign convention "internal helpers: distinct names, blueprint-node citations" (OVERNIGHT
09:00/13:08). Severity: low, non-blocking.**
Three helpers carry the whole of `stepN:p11:bl-ext` but cite no node: `Block.lean:126` (`nblk_field`), `:166` (`nblk_transport`)
and `:194` (`nblk_dom`). The section header at `:31` cites none either. The provider helpers at `PartialConvexNekhoroshev.lean:34`, `:41` and `:47` serve
`stepN:p11:final-orbit` and also cite none.
Fix: append "(`stepN:p11:bl-ext`)" to the three Block docstrings and the `### Rescaling the slow pair` header.
Append "(`stepN:p11:final-orbit`)" to the provider helper docstrings. Comments only; no statement changes.

## Notes

- **N-1. Content duplication with Domain.lean; names are distinct.**
  - `nblkCLM`/`nblkCLE` duplicate the public `slowScaleReal` (Domain L441) and the private `slowEquiv` (L465).
  - `nblk_field` generalizes the private `slowScaleReal_realWfield` (L515) to an `EqOn` on an open set. `block` needs this generalization because F is arbitrary off 𝒲.
  - `nblk_isOpen` duplicates the inline `hopen` in `domain_field_scaled` (L713–715).
  - Domain's privacy forced part of this. An optional follow-up could derive `hFt` from `domain_field_scaled` (clause 5, R = r) together with `domain_field` and `hF`, removing `nblk_field` and most of the `nblkCLE` layer. The orbit chain rule would remain.
- **N-2. Imports.**
  - Block.lean L9–12 publicly imports modules the proof alone uses: Hessian, BlockData, Nonresonant and Resonant. `block`'s statement needs only Domain's interface. The provider's needs are met by Domain (Coordinates) plus its own Threshold import. Plain `import` would keep the NF stack out of Block's public interface once M1/M2 land.
  - L13 imports Threshold, only for `nthr_pos`. That N→O edge is not in the design row N11-N ("G, M1, M2, E3"). It is acyclic, since Threshold imports only Constants and Mathlib.
- **N-3. Possible linter warnings (unverifiable without the gate log).**
  - `he0` (Block L255) is never used.
  - The provider's `with hIc_def` (L103) and `with hH` (L111) are never used.
  - `hA` is plausibly consumed by `positivity` at L359.
  - If the gate reports unused variables, write `-` in place of `he0` and drop the two `with` clauses.
- **N-4. Sealing preconditions.**
  - `block` and the provider depend on `sorryAx` only through `nonresonant` and `resonant` (placeholders equal to signature L601–612 and L614–626).
  - The seal-key `#print axioms` probe will fail until N11-M1 and N11-M2 land with exactly those statements. The placeholder files also contain `sorry`, which lint forbids outside `KAM/Frozen`.
  - The consumer edges are met. `block` passes `ExtNFHyp` with radius/width positivity, K_a = K/√n, L = √n·M1, p = 9/8 and Λ = `{0}` (Θ case) or `Λ : AddSubgroup` (resonant case). The provider passes everything `block` requires.
- **N-5. Shared work tree.**
  - `w/KAM/Nekhoroshev/Partial/TailStub.lean` redefines signed upstream declarations: `block_setting`, `signedH`, `signedF`, `slowScale`, `blockPert`, `hessian`, `domain`, `block_data`, `physicalDomain`, `domain_field`, `hessian_at_sign` and `nonresonant`. Neither audited module imports it, and it must never be landed.
  - Other agents added `Composition`, `CompositionCoeff`, `Transform`, `TransformIntegral`, `Iterative` and `NormalForm` to `w/` during this audit. None is in the audited modules' import closure (re-checked after the change).
- **N-6. Mid-audit edit.** Block.lean changed at 18:51 while this audit ran. All line numbers and hashes above refer to
  revision `fccc1ba3…`. A full re-read confirmed that the change is only the NP-1 rename.
- **N-7. Literal step remarks not stated as Lean facts.** None is needed by the proof, and none blocks.
  - final-data's "A ≥ 11" is not stated (A ≥ 40 follows from m ≤ M_C).
  - final-order's "μ₀ depends only on (n, k, ρ, g, m, M_C)" holds by construction of `threshold`, not as a statement.
  - final-mu/final-time's explicit formulas live in GAP-A (`ThresholdExplicit`), which the graph already cites.
- **N-8. Naming nits.**
  - `nblkScale_fst` (about `(v, 0)`) and `nblkScale_fst'` (about `.1`) are different facts. A prime conventionally marks a variant of the same statement, so consider `nblkScale_apply_fst`.
  - `nblk_dom`'s `hd : 0 < d` departs from the `hd : d ≤ ρ` convention used in the signed theorems.
- **N-9. Not checked here.** Lean elaboration, warnings and `#print axioms` (no Lean on this machine); root-shadowing against Mathlib by grep (no local
  Mathlib); the mathematical truth of the `nonresonant`/`resonant` signed statements (other audits).

## Notes applied (lane N, 2026-10-28)

- NP-2: the helpers' docstrings now cite `stepN:p11:bl-ext` (Block) and `stepN:p11:final-orbit` (provider).
- Hessian, BlockData, Nonresonant and Resonant are now plain `import`s in Block.lean.
- `nblkScale_fst'` was renamed to `nblkScale_fst_eq`.
