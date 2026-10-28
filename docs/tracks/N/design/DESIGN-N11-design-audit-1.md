# DESIGN-N11 independent design audit 1

Overall verdict: **FAIL**.

The delivered file elaborates, and the provider statement matches its frozen anchor exactly. The design is not ready for dispatch as an exact implementation of all cited source contracts: the energy lemma adds a complex Hessian premise, three intermediate exports omit source conclusions, the resonant-gradient export unnecessarily assumes reality, and one named Mathlib theorem has the wrong namespace. These are design/interface findings, not counterexamples to the frozen theorem. Proposed repairs below are report-only.

## Scope, snapshot and method

Audit date: 2026-10-28. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the exact external audit brief and the designer handoff. Scope is the 44 theorem obligations and 76 literal definition/structure/abbreviation declarations in the delivered signatures, their blueprint sources, N-p11ab/N-p11c packet contracts, root and consumers. This is a tier-2, refute-first correspondence/design audit, with a separate adversarial recheck of each finding. No mathematical proof closure or pinned-PDF re-audit is claimed.

Frozen-v1 inputs:

| Input | Revision or SHA-256 |
|---|---|
| Audited HEAD | `bd2159ab74084f46f51c200dec05af420901d4ce` |
| Comparison branch `inp` at inspection | `31315a8b040b2ecefe792c4e03f9b30bfc72799c` |
| Design | `11ab65aa71d3d10f5294cbdc61a4fc668aeb21a770c0a98d658ca16c41df573a` |
| Delivered signatures / Appendix A | `eed38f9bacd07e1d939bba378e8a19d6666221c243cbfaee5b4bcf0643204346` |
| p11a | `dede87e5ec7b638136dff072abbf021b24ed4a4cedf6befae88eddf6e87d57b3` |
| p11b | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| p11c | `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea` |
| N graph DEPGRAPH | `941c8d1d4bb6c17e3369d57b86441798544e1dabc8a9af1735882f75aa8972d2` |
| Frozen partial-convex theorem | `e6bb9443a34096433a84e3450162ed032b07d934352c7ecaaa10eb7caf16b4a3` |

`git diff inp...HEAD` contains only the 1236-line design addition. Appendix A equals the 812-line delivery byte for byte. All 122 nodes in the two Part-11 packets occur in the design inventory; the frozen root is the 123rd entry. Node-count coverage does not establish statement completeness.

Authorization: only this report is a persistent audit edit. The user-authorized copy in `.drafts/scratch/N11Signatures.lean` was refreshed from the original; temporary probes use `.lake/abi-scratch/` and are removed after checking. No git mutation, production/frozen/manifest edit, dependency build, network operation or delegated work was performed.

Hereafter A/B/C mean the pinned p11a/p11b/p11c files, and S means the pinned delivered signatures; line references always refer to frozen-v1. PASS in the following ledger means acceptable target correspondence (possibly via explicitly assigned wrappers/reuse), not a proved theorem. Companion exports are considered together, rather than requiring every wrapper to duplicate an entire source lemma.

## Theorem signature ledger

All unqualified names below are in `KAM.Nekhoroshev`, except the provider row.

| Lean name (S line) | Blueprint label, prefixed `bpN:p11:` unless stated | Verdict | Reason |
|---|---|---|---|
| `orbit` (106) | `orbit` | PASS | Exact frozen field; period conversion preserves actions, slow coordinates and time. |
| `exponents` (111) | `exponents` | PASS | Omitted positive comparison consequences follow arithmetically from displayed inequalities. |
| `ext_part4` (170) | `ext-part4` | PASS | Sup bound wrapper; other Part-4 statements are explicitly reused at independent base dimension. |
| `bracket` (174) | `bracket` | PASS | Fast and slow constants and domain losses match. |
| `bracket_dominated` (184) | `bracket` | PASS | Nonnegative c and SL give the stated half-sum bound. |
| `bracket_g` (190) | `bracket-g` | PASS | Literal finite decomposition and source weights. |
| `vf` (201) | `vf` | PASS | Scaled field and slow component bounds; SL and k positivity retained. |
| `flow` (209) | `flow` | PASS | Partial wrapper; generic flow_a–d are explicitly direct imports, reality has its own wrapper. |
| `symplectic` (221) | `symplectic` | PASS | Functional canonical identity; form, determinant and bracket exports below supply companion clauses. |
| `adjoint` (227) | `adjoint` | PASS | Factorial-normalized bound has e squared times eta over eight. |
| `ext_taylor` (236) | `ext-taylor` | PASS | Correct recursive bracket orientation and integral kernel. |
| `composition` (260) | `composition` | PASS | Maps, all-time norm bound, pointwise HasSum and uniform weighted convergence. |
| `transform` (273) | `transform` | PASS | Integral remainder, sign and bound match. |
| `transform_integral` (287) | `transform` | PASS | Joint function and derivative continuity retained. |
| `canonical_map` (297) | `canonical-map` | FAIL | F2: inverse image inclusion on the intermediate domain is omitted. |
| `hom` (319) | `hom` | PASS | Independent base dimension, divisor alpha/q, sign and real-frequency guard match. |
| `iterative` (361) | `iterative` | FAIL | F2: holomorphy, image domain, translation equivariance and explicit left inverse are omitted. |
| `nf` (401) | `nf` | PASS | Direct source target matches; implementation consumption of iterative requires F2 repair. |
| `real_system` (426) | `real-system` | FAIL | F2: periodicity of the vector field is omitted. |
| `real_system_bounds` (436) | `real-system` | PASS | Correct fixed-base angular derivative sum and factor 1/(e s). |
| `conj` (459) | `conj` | PASS | Real restriction of the actual complex map and exact orbit predicate. |
| `preimage` (463) | `preimage` | PASS | Source non-strict upper margins retained; positive block scales are typing data. |
| `continuation` (474) | `continuation` | PASS | Independent transverse dimension, compact tail and maximal solution match. |
| `real_system_resonant` (507) | `real-system` | FAIL | F3: additional reality premise and real-part-only conclusion narrow clause (d). |
| `transfer_conditional` (515) | `transfer` | PASS | T3 is visibly conditional; arbitrary original extension, closed prefixes and infinite T retained. |
| `energy_free` (550) | `energy-free` | FAIL | F1: FastConvex adds a complex Hessian bound absent from this source lemma. |
| `nonresonant` (565) | `nonresonant` | PASS | Exact stopped hypotheses, max norm, time constant 5 and radius half. |
| `resonant` (578) | `resonant` | PASS | Complex bound is a source premise here; p=9/8, time 240 and Euclidean drift match. |
| `hessian` (636) | `hessian` | PASS | Local signed consequences; frozen global hypotheses remain in PartialData. |
| `domain` (649) | `domain` | PASS | Complex domain inclusion and normalized weighted bound; other clauses are separate exports. |
| `block_data` (660) | `block-data` | PASS | Consumer-facing geometric consequences; lattice enumeration is intentionally upstream. |
| `domain_field` (677) | `domain` | PASS | Frozen Hamiltonian equals signed physical weighted field on the actual open set. |
| `block` (687) | `block` | PASS | Physical/scaled carriers separated; exact stopped prefix and drift. |
| `threshold` (704) | `constants / p0:partial` | PASS | Threshold precedes perturbation and orbit; six comparisons uniform in initial point. |
| `hessian_at_sign` (713) | `hessian` | PASS | Uses the selected frozen sign rather than choosing an incompatible second witness. |
| `flow_real` (719) | `flow` | PASS | Actual generic flow; real-locus tangent condition, no hidden domain symmetry assumption. |
| `ext_taylor_bound` (726) | `ext-taylor` | PASS | Uniform integrand bound avoids an unjustified maximum choice. |
| `symplectic_bracket` (734) | `symplectic` | PASS | Holomorphic observable invariance on explicit image domain. |
| `symplectic_det` (740) | `symplectic` | PASS | Nondegenerate weight and determinant plus/minus one. |
| `composition_domain` (746) | `composition` | PASS | Retains smaller image tube from clause (i). |
| `composition_real` (753) | `composition` | PASS | Stronger reality-only observable assumption suffices for the reality conclusion. |
| `ext_taylor_regular` (759) | `ext-taylor` | PASS | Within derivatives on [0,1] preserve endpoint interpretation. |
| `symplectic_form` (770) | `symplectic` | PASS | Inverse slow weight c inverse in the preserved form. |
| `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` (779) | `p0:partial` | PASS | Provider command type byte-identical to the frozen theorem; all premises and quantifiers retained. |

## Findings and proposed complete signatures

### F1 — Major: `energy_free` adds a complex Hessian hypothesis

Evidence: C L77–81 (`bpN:p11:energy-free`) assumes the upper Hessian bound **“on U={|I-Ic|<r}”**, the real action domain. The packet says the same. S L550–553 instead requires `FastConvex`; its `hessian` field at S L544–546 quantifies over **every complex** `I ∈ polyNbhd ... r` and every complex vector. That stronger premise belongs to the later resonant proposition (C L113–115), not to the energy lemma.

Refutation recheck: holomorphy and a bound on the real slice do not give the same bound on the complex tube. In one fast dimension, `h(z)=z²+cos(L z)/(4L²)` has real Hessian in `[7/4,9/4]`, while its complex Hessian at `z=i r/2` is `2-cosh(Lr/2)/4`, whose magnitude exceeds `9/4` for sufficiently large L. Thus this is a strict premise change, not a harmless rewriting. The current resonant consumer can supply the stronger bound; that does not repair fidelity of the standalone source lemma under the brief's explicit extra-premise rule.

Proposed fix: retain `FastConvex` for the resonant/domain packages, introduce the following real-bound bundle for the energy lemma, and prove its extraction from `FastConvex` in the Hessian package. No new frozen premise is needed.

```lean
structure RealFastConvex (Ic : Fin n → ℝ) (R m M : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop where
  m_pos : 0 < m
  m_le : m ≤ M
  hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n Ic} R)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n Ic} R →
    (h (KAM.realInclusion n I)).im = 0
  convex : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    m*euclid v^2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I v v
  hessian_real : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    euclid (fun i => fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) v) ≤ M*euclid v

theorem energy_free (b : PartialBlock n k) {r s m M ε η ζ δ : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {g fs : EC n k → ℂ}
    (hr : 0 < r) (hs : 0 < s) (hh : RealFastConvex b.Ic r m M h)
    (hg : ext_class b r s g) (hf : ext_class b r s fs)
    (hgb : WBound b.base r s g (5*ε/4)) (hfb : WBound b.base r s fs η)
    (hsupp : ∀ J ∈ polyNbhd b.base r, ∀ j : Fin n → ℤ, j ∉ Λ → coeff g J j = 0)
    (hε : 0 < ε) (hη : 0 ≤ η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) (hζε : ζ ≤ ε/Real.exp 1)
    (hsmall : ε ≤ m*r^2/2^12) (hSL : 16*k*b.c*s ≤ r)
    (hδ : 0 < δ) (hδr : δ ≤ m*r/16) (hnr : NearResonance Λ h b.Ic δ)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ExtOrbit b r (liftFast h+g+fs) J y)
    (hinit : euclid (fastAction (y 0)-b.Ic) < δ/(4*M))
    (hslow : ∀ u ∈ J, ∃ v ∈ b.S, ‖slowPair (y u)-b.lam⁻¹ • v‖ < r/2) :
    ∀ t ∈ J, |t| ≤ s*m*r/(20*M*ζ) → euclid (fastAction (y t)-fastAction (y 0)) ≤ r/4 := sorry
```

### F2 — Major: three source conclusions are absent from their assigned exports

Evidence:

- **`iterative`**, B L127–132 and the `bpN:p11:iterative` packet: “holomorphic ... with values in ... theta-translation equivariant” and an explicit flow left inverse. S L361–399 exports the residual bound, identity, canonical predicate, injectivity, displacements and reality, but no holomorphy, image inclusion, translation equivariance or left-inverse identity. B L152 and L160 (`nf`) use the step maps as maps between nested domains and telescope these properties. Proving exactly the delivered iterative signature leaves those required facts unexported.
- **`canonical_map`**, B L109 and its packet: “Phi,Psi ... with values in Omega”. S L304 has `MapsTo Φ U ...` but no `MapsTo Ψ U ...`. Inverse identities only on the smaller domain do not express that missing clause on all U.
- **`real_system`**, C L9 and its packet: “X ... is C1 and theta-periodic”. S L426–434 exports scalar-Hamiltonian periodicity, not field periodicity. The `continuation` signature S L478–479 requires the field periodicity explicitly; the compact-tail transfer argument C L68 uses it.

Refutation recheck: `ExtCanonical` does not supply holomorphy or equivariance by definition. The missing step-map properties can be proved by revisiting `canonical_map`; the missing inverse image clause can be proved from the generic inverse flow, and field periodicity can be obtained by differentiating the scalar identity. This makes all three repairs feasible, but those facts are neither current conclusions nor separately named extended bridge signatures. The finding is incomplete source contracts, not mathematical falsity. Directly imported generic `flow_a`–`flow_d` and the explicit companion Taylor/symplectic exports were checked and are not counted as omissions.

Proposed fix: replace these three signatures with the complete blocks below. Existing premises, estimates and witnesses are preserved; only the missing source conclusions are added.

```lean
theorem canonical_map (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ V : ℝ} {φ : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R/2) (hσ : 0 < σ) (hσs : σ < s/2)
    (hSL : slowLoss b.c ρ σ k) (hV : 0 ≤ V) (hsmall : V/(ρ*σ) ≤ 1/2)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ V) :
    let Φ := extFlow b R s ρ σ φ 1
    let Ψ := extFlow b R s ρ σ φ (-1)
    let U := Dom n b.base (R-3*ρ/2) (s-3*σ/2)
    DifferentiableOn ℂ Φ U ∧ DifferentiableOn ℂ Ψ U ∧ MapsTo Φ U (Dom n b.base (R-ρ) (s-σ)) ∧
    MapsTo Ψ U (Dom n b.base (R-ρ) (s-σ)) ∧
    ExtCanonical b.c U Φ ∧
    (∀ z ∈ U, ‖(Φ z).1-z.1‖ ≤ V/ρ ∧ ‖fastAction (Φ z)-fastAction z‖ ≤ V/(Real.exp 1*σ) ∧
      ‖slowPair (Φ z)-slowPair z‖ ≤ b.c*V/ρ) ∧
    (∀ z ∈ U, ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)), z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), Ψ (Φ z) = z ∧ Φ (Ψ z) = z ∧ Φ z ∈ U) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), ∀ v : EC n k,
      scaled ρ σ (fderiv ℂ Φ z v-v) ≤ 2*(V/(ρ*σ))*scaled ρ σ v) ∧
    (extReal (Dom n b.base R s) φ → ∀ z : ER n k, extCx z ∈ U → extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := sorry
```

```lean
theorem iterative (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ K α p δ : ℝ}
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) (Λ : Set (Fin n → ℤ))
    (hR : 0 < ρ) (hR' : 2*ρ < R) (hs : 0 < σ) (hs' : 2*σ < s)
    (hSL : slowLoss b.c ρ σ k) (hα : 0 < α) (hp : 1 < p) (hK : 0 ≤ K)
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/conjExp p))
    (hδ : 0 ≤ δ) (hf : InClass b.base R s f) (hfb : WBound b.base R s f δ)
    (hsmall : δ ≤ 2*Real.pi*α*ρ*σ/(4*conjExp p))
    {N : ℕ} (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ)
    (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j) (hUj : ∀ j, 0 ≤ Uj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j)) :
    let q := conjExp p
    let φ := homGenerator K Λ h f
    let Φ := extFlow b R s ρ σ φ 1
    let g := fun z => ∑ j, gj j z
    let gp := g+projMode Λ (truncate K f)
    DifferentiableOn ℂ Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) ∧
    MapsTo Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) (Dom n b.base (R-ρ) (s-σ)) ∧
    (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2), ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), extFlow b R s ρ σ φ (-1) (Φ z) = z) ∧
    ∃ fp : EC n k → ℂ,
      InClass b.base (R-2*ρ) (s-2*σ) fp ∧
      (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), liftFast h (Φ z)+g (Φ z)+f (Φ z) = liftFast h z+gp z+fp z) ∧
      WBound b.base (R-2*ρ) (s-2*σ) fp
        ((1-2*q*δ/(2*Real.pi*α*ρ*σ))⁻¹*
          (q/(2*Real.pi*α*ρ*σ)*((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)+
            Real.exp (-2*Real.pi*K*σ))*δ) ∧
      ExtCanonical b.c (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) Φ ∧
      Set.InjOn Φ (Dom n b.base (R-2*ρ) (s-2*σ)) ∧
      WBound b.base (R-2*ρ) (s-2*σ) (gp-g) δ ∧
      (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2),
        ‖(Φ z).1-z.1‖ ≤ q*δ/(2*Real.pi*α*ρ) ∧
        ‖fastAction (Φ z)-fastAction z‖ ≤ q*δ/(Real.exp 1*2*Real.pi*α*σ) ∧
        ‖slowPair (Φ z)-slowPair z‖ ≤ q*δ/(16*k*2*Real.pi*α*σ)) ∧
      ((∀ j, j ∈ Λ ↔ -j ∈ Λ) →
        (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
          (h (KAM.realInclusion n I)).im = 0) →
        extReal (Dom n b.base R s) g → extReal (Dom n b.base R s) f →
        extReal (Dom n b.base R s) φ ∧ extReal (Dom n b.base (R-2*ρ) (s-2*σ)) gp ∧
        extReal (Dom n b.base (R-2*ρ) (s-2*σ)) fp ∧
        ∀ z : ER n k, extCx z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2) →
          extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := sorry
```

```lean
theorem real_system (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hR : 0 < R) (hs : 0 < s) (hH : ext_class b R s H) :
    ContDiffOn ℝ ∞ (realHamiltonianExt b R H) (b.realDom R) ∧
    ContDiffOn ℝ 1 (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) ∧
    (∀ z ∈ b.realDom R, extCx (realWfield b.c (realHamiltonianExt b R H) z) = wfield b.c H (extCx z)) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realHamiltonianExt b R H (z.1+(fun i => (ℓ i:ℝ)),z.2) = realHamiltonianExt b R H z) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realWfield b.c (realHamiltonianExt b R H) (z.1+(fun i => (ℓ i:ℝ)),z.2) =
        realWfield b.c (realHamiltonianExt b R H) z) ∧
    (∀ J : Set ℝ, J.OrdConnected → ∀ r, 0 < r → r ≤ R → ∀ y, ExtOrbit b r H J y →
      ∀ t ∈ J, ∀ u ∈ J, realHamiltonianExt b R H (y t) = realHamiltonianExt b R H (y u)) := sorry
```

### F3 — Medium: resonant-gradient target narrows the source to real Hamiltonians

Evidence: C L12 (`real-system` clause (d)) states “g in O(rho,s)^e finite norm” and `Pi_Lambda^perp d_theta g=0`; it does not impose reality. S L507–512 uses `ext_class`, which adds `extReal`, and concludes membership only for the real part of the derivative. The earlier clauses' reality premise for G does not silently impose reality on the separately quantified g in (d).

Refutation recheck: Fourier support forces both real and imaginary derivative vectors into the real resonance span. Multiplying a real resonant Fourier function by i preserves its support and analyticity, while violating the new reality premise. The added premise therefore cannot be recovered from the source assumptions. The actual energy consumer supplies a real g and can use the narrower result, but the standalone source contract still fails the brief's extra-premise and weakened-conclusion checks.

Proposed fix: take `InClass` and export both components, equivalent to the complexified projection assertion. Existing real consumers use the first component.

```lean
theorem real_system_resonant (b : PartialBlock n k) {R s U : ℝ} {g : EC n k → ℂ}
    (hs : 0 < s) (hg : InClass b.base R s g) (hb : WBound b.base R s g U)
    {Λ : Set (Fin n → ℤ)}
    (hsupp : ∀ J ∈ polyNbhd b.base R, ∀ j : Fin n → ℤ, j ∉ Λ → coeff g J j = 0) :
    ∀ z ∈ b.realDom R,
      (fun i => (dtheta i g (extCx z)).re) ∈ KAM.Stability.resSpan Λ ∧
      (fun i => (dtheta i g (extCx z)).im) ∈ KAM.Stability.resSpan Λ := sorry
```

### F4 — Medium: nonexistent qualified Mathlib name in the threshold plan

Evidence: design L117 and L148 name `Real.tendsto_exp_div_rpow_atTop`. The fresh `#check` probe reports `Unknown constant` for exactly that name. The actual declaration in `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:124` is in the root namespace, with type shown below.

Refutation recheck: importing the named asymptotics module does not create a `Real` alias. Repeating the probe with the root name succeeds. This is a concrete API correction for N11-O; it does not invalidate the already elaborated `threshold` statement, whose body is a placeholder.

Proposed replacement API entry:

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
#check tendsto_exp_div_rpow_atTop
-- (s : ℝ) : Filter.Tendsto
--   (fun x : ℝ => Real.exp x / x ^ s) Filter.atTop Filter.atTop
#check tendsto_exp_mul_div_rpow_atTop
-- use this positive-multiple version, or compose with a positive linear rescaling
```

### N1 — Note: upstream Part-8 reconciliation is an actual dispatch gate

The design correctly reserves covering/cutoff names without pretending their concurrent interfaces are fixed. Keep N11-G blocked until the actual owner signatures supply the singleton-base radius bounds, K/sqrt(n) analytic cutoff, strict resonance closeness, and full-rank exclusion. Existing `block_data` alone does not prove those upstream facts. The 12 copied N6–7 definitions match the current delivered NPart67 definitions after whitespace and qualified `polyNbhd` normalization; no mathematical drift was found. Retire these staging definitions when owner modules land.

### N2 — Note: import closure and the real-restriction carrier need explicit attention

The initial API probe intentionally used the delivered signature import list plus FlowRegular/FlowInverse. Besides F4 it could not resolve `Real.exp_one_lt_d9`, the three SupWeighted/Algebra exports, or `gen_continuation`. All those names do exist: adding `Mathlib.Analysis.Complex.ExponentialBounds`, `KAM.Weighted.SupWeighted`, `KAM.Weighted.Algebra`, and `KAM.ODE.Continuation` makes the corrected probe pass. These are required implementation imports, not nonexistent theorems. The package table already names the relevant analytic areas.

`KAM.hamiltonian_real_fderiv` is specialized to equal-size canonical products. Its proof is a valid pattern, but it is not directly applicable to EC n k. The assigned regrouping and local real-system proof must supply the transport; do not introduce an equality assumption to a replacement frozen field. The explicit local real-system/orbit signatures make this a declared implementation obligation rather than an extra source premise.

### N3 — Note: preserve the two reported local source issues

C L31's “complex nu-ball of radius 1/2” must mean an open ball when sigma'=2s; the closed ball would touch the strip boundary. `general_cauchy` was checked to use an open ball, so the stated preimage theorem need not change. The adjoint packet's proof locator B L69–86 overreaches its proof ending at L73 and includes the Taylor lemma. Both issues were already disclosed in the design/handoff. No graph repair was made.

## Consumer, frozen-object, definition and package verdicts

**Consumers: FAIL at intermediate exports (F2), otherwise compatible at design level.** The search for `\Nref{bpN:p3:` in I/P confirms those consumers concern generic ODE/hamiltonian reductions, which this design reuses rather than replaces. Searches for Part-11 labels in I/P and N Part 12 found no direct Part-11 signature consumers. Within N11, NF consumes iterative holomorphy/maps/equivariance, transfer consumes the real field's periodicity, nonresonant/resonant discharge T3, block consumes radius/divisor/strict-closeness data, and the provider consumes only the stopped block theorem and uniform numerical threshold. N Part 7 is upstream: its equal-size energy/no-exit theorem is correctly not applied to the unequal extended system. The N11 fixed-base Fourier and compact-tail arguments are the intended replacements. No whole-window slow-confinement premise or frequency upper bound was added to the provider.

**Frozen objects: PASS.** Read the actual `IsSolutionOn`, `hamiltonianVectorField`, `HasDefiniteFastPart`, `IsPartialPerturbation`, `partialComplexDomain`, `realPart`, `complexifyPhase`, `innerCore`, fast/slow coordinates and degenerate Hamiltonian. `orbit` relates the actual frozen field to the extended weighted field; `domain_field` relates the actual degenerate Hamiltonian to the physical weighted Hamiltonian; `ExtOrbit` uses the existing `KAM.ODE.IsSolutionIn` with two-sided derivatives. The frozen guarded differentiability premise is available to `orbit`. The real restriction's off-domain zero is explicit, and differentiations occur on the open real domain. Provider quantifier order, initial fast erosion, stopped slow prefix, global sign, empty-G branch and unchanged physical time match the frozen contract byte for byte.

**Definitions/structures: PASS as objects, with F1/F3 governing their inappropriate use in two theorem signatures.** Flattened coordinates use ordinary max norms; the projections and append order are I,q,p. `PartialBlock.lam` and c are fixed at the block starting radius. `PartialData` contains actual source data, not a normal-form/stability conclusion; `DefiniteSign` is the selected source witness. `ExtCompose` and `ExtNFHyp` bundle source hypotheses, `ExtConjHyp` bundles the named map contract, and conditional T3 is not smuggled into a source-facing theorem. `IsActionNorm` has the needed zero and homogeneity fields. No global instances are installed. Total derivative/tsum/division definitions are used only under the declared regularity, summability and positive-scale guards; empty bases do not select a fake maximum.

**Packages: PASS structurally, conditional on F2 export repairs and N1 reconciliation.** The 23 packages and ten waves are acyclic. Each proposed module is estimated below 1500 lines, with proof tasks generally 150–800 lines; the maximum listed single-module estimate is 650. EnergyIdentity is independent of NormalForm; Transfer does not import its stability consumers; Threshold depends only on fixed numerical data. The provider remains quarantined. No library rebuild is appropriate for this Markdown-only audit.

**New energy/transfer mathematics:** the displayed energy identity has the correct bracket orientation. The slow half-radius margin, eta <= zeta <= epsilon/e, real fast segment, and two-sided time handling are retained. The resonant consumer derives NF smallness from alpha >= p sqrt(n) M K r and epsilon <= m r²/2^14, and obtains d_star <= rho'/16. Transfer's witnessed slow-tube bound is supplied by the actual compared physical orbit, so it need not assume attainment of distance to an arbitrary S. These checks found no additional signature-level contradiction. They are not a complete proof audit of those new mathematical arguments.

## Definition and structure signature ledger

One row per literal declaration (76); local namespace is shown. These are object/body checks, separate from the theorem-use failures above.

| Lean name | Blueprint/reuse anchor | Verdict | Reason |
|---|---|---|---|
| `KAM.NormalForm.zBall` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.freq` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.dotC` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.conjExp` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.IsNonresonant` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.FreqLipschitz` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.DivisorBound` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.homGenParam` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.homResParam` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.NormalForm.RealOnParam` | Part 6, Revision-2 reuse | PASS | Literal owner staging definition; normalized text matches. |
| `KAM.Nekhoroshev.Ext` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.EC` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.ER` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.fastAction` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.slowPair` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.extCx` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.extRe` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.extReal` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.wfield` | bpN:p11:wfield / symplectic / adjoint | PASS | Coordinate formula or basis-free identity agrees, with nondegeneracy guarded where used. |
| `KAM.Nekhoroshev.realWfield` | bpN:p11:wfield / symplectic / adjoint | PASS | Coordinate formula or basis-free identity agrees, with nondegeneracy guarded where used. |
| `KAM.Nekhoroshev.extBracket` | bpN:p11:wfield / symplectic / adjoint | PASS | Coordinate formula or basis-free identity agrees, with nondegeneracy guarded where used. |
| `KAM.Nekhoroshev.extAd` | bpN:p11:wfield / symplectic / adjoint | PASS | Coordinate formula or basis-free identity agrees, with nondegeneracy guarded where used. |
| `KAM.Nekhoroshev.theta` | bpN:p11:orbit | PASS | Literal period conversion; no time rescaling. |
| `KAM.Nekhoroshev.thetaInv` | bpN:p11:orbit | PASS | Literal period conversion; no time rescaling. |
| `KAM.Nekhoroshev.converted` | bpN:p11:orbit | PASS | Literal period conversion; no time rescaling. |
| `KAM.Nekhoroshev.PartialConstants` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.s` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.m1` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.M1` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.g1` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.r0` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.A` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.eps0` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.R0` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.kappaC` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.cK` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.eps` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.K` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.d` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.kappa` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.rTheta` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialConstants.blockTime` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.PartialBlock` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.PartialBlock.lam` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.PartialBlock.c` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.PartialBlock.base` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.PartialBlock.realDom` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.PartialBlock.SL` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.ext_class` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.slowLoss` | bpN:p11:ext-class | PASS | Declared carrier, projection, fixed block geometry or exact analytic-class reuse. |
| `KAM.Nekhoroshev.scaled` | bpN:p11:scaled | PASS | Max of scaled ordinary coordinate norms. |
| `KAM.Nekhoroshev.liftFast` | bpN:p11:hom / nf | PASS | Fast projection, existing parameter generator or source premise bundle. |
| `KAM.Nekhoroshev.realHamiltonianExt` | bpN:p11:real-system / conj / transfer | PASS | Actual restriction/orbit/map contract; witnessed tube used at actual source point. |
| `KAM.Nekhoroshev.ExtOrbit` | bpN:p11:real-system / conj / transfer | PASS | Actual restriction/orbit/map contract; witnessed tube used at actual source point. |
| `KAM.Nekhoroshev.ExtCanonical` | bpN:p11:wfield / symplectic / adjoint | PASS | Coordinate formula or basis-free identity agrees, with nondegeneracy guarded where used. |
| `KAM.Nekhoroshev.ExtCompose` | bpN:p11:composition | PASS | Source losses/smallness or exact existing generic flow. |
| `KAM.Nekhoroshev.extFlow` | bpN:p11:composition | PASS | Source losses/smallness or exact existing generic flow. |
| `KAM.Nekhoroshev.homGenerator` | bpN:p11:hom / nf | PASS | Fast projection, existing parameter generator or source premise bundle. |
| `KAM.Nekhoroshev.ExtNFHyp` | bpN:p11:hom / nf | PASS | Fast projection, existing parameter generator or source premise bundle. |
| `KAM.Nekhoroshev.reExtMap` | bpN:p11:real-system / conj / transfer | PASS | Actual restriction/orbit/map contract; witnessed tube used at actual source point. |
| `KAM.Nekhoroshev.ExtConjHyp` | bpN:p11:real-system / conj / transfer | PASS | Actual restriction/orbit/map contract; witnessed tube used at actual source point. |
| `KAM.Stability.resSpan` | Part 7 reuse | PASS | Literal span/action-norm carrier; corrected fields present. |
| `KAM.Stability.IsActionNorm` | Part 7 reuse | PASS | Literal span/action-norm carrier; corrected fields present. |
| `KAM.Nekhoroshev.slowTube` | bpN:p11:real-system / conj / transfer | PASS | Actual restriction/orbit/map contract; witnessed tube used at actual source point. |
| `KAM.Nekhoroshev.FastConvex` | bpN:p11:resonant / energy-free | PASS | Correct complex-bound convexity object or dual resonance bound; energy use subject to F1. |
| `KAM.Nekhoroshev.NearResonance` | bpN:p11:resonant / energy-free | PASS | Correct complex-bound convexity object or dual resonance bound; energy use subject to F1. |
| `KAM.Nekhoroshev.PartialData` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.constants` | bpN:p11:constants | PASS | Literal numerical formulas or frozen input fields; no hidden conclusion. |
| `KAM.Nekhoroshev.block_setting` | bpN:p11:block-setting / domain / hessian | PASS | Physical/scaled coordinates, selected source sign or frozen-data specialization. |
| `KAM.Nekhoroshev.signedH` | bpN:p11:block-setting / domain / hessian | PASS | Physical/scaled coordinates, selected source sign or frozen-data specialization. |
| `KAM.Nekhoroshev.signedF` | bpN:p11:block-setting / domain / hessian | PASS | Physical/scaled coordinates, selected source sign or frozen-data specialization. |
| `KAM.Nekhoroshev.slowScale` | bpN:p11:block-setting / domain / hessian | PASS | Physical/scaled coordinates, selected source sign or frozen-data specialization. |
| `KAM.Nekhoroshev.blockPert` | bpN:p11:block-setting / domain / hessian | PASS | Physical/scaled coordinates, selected source sign or frozen-data specialization. |
| `KAM.Nekhoroshev.DefiniteSign` | bpN:p11:block-setting / domain / hessian | PASS | Physical/scaled coordinates, selected source sign or frozen-data specialization. |
| `KAM.Nekhoroshev.physicalDomain` | bpN:p11:block-setting / domain / hessian | PASS | Physical/scaled coordinates, selected source sign or frozen-data specialization. |
| `KAM.Nekhoroshev.extForm` | bpN:p11:wfield / symplectic / adjoint | PASS | Coordinate formula or basis-free identity agrees, with nondegeneracy guarded where used. |

## Verification and limits

All audit Lean invocations use `LEAN_NUM_THREADS=1`, `nice -n 5`, and exclusive acquisition of the two campaign compile slots and three signature slots, except lint which holds both compile slots and signature slots 2–3 and lets its existing wrapper acquire signature slot 1. Thus no two audit Lean/lake commands execute together; waits are gate waits. Other agents' ungated activity cannot be controlled by this audit.

1. Original signatures were copied to the specified scratch path and elaborated exactly once against `/root/code/KAM-inp`'s shared build:

   ```sh
   cd /root/code/KAM-inp
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean /root/code/KAM-inp-design-n11/.drafts/scratch/N11Signatures.lean
   ```

   Result: **exit 0, exactly 44 `declaration uses sorry` warnings, no other diagnostics**. Default heartbeat settings; no resource override.

2. API-name probe: first run exited 1 with the namespace/import diagnostics reported in F4/N2. The corrected import/name probe exited 0. All listed Weighted, Canonical flow a–e, generic ODE, finite-dimensional regularity, derivative-chain and real-power declarations were checked with their elaborated types. In particular flow_e is equal-size-specific, while flow_a–d are generic. Designed Part6/7 and reserved Part8 theorem APIs are not claimed to be existing Mathlib declarations.

3. Proposed replacement-signature probe: **exit 0, exactly 44 sorry warnings and no errors**. This checks typing of proposals only; every theorem still has its deliberate placeholder body.

4. `scripts/lint_sources.sh` ran under the single-process arrangement, using the pre-existing `.drafts/scratch/lint-bin/lake` wrapper to reach the shared build. **Exit 0**:

   ```text
   check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

5. `#print axioms` evidence: the designer's existing `N11-axioms.log` reports `[propext, sorryAx, Classical.choice, Quot.sound]` for nf, energy_free, transfer_conditional and the provider. The correction probe independently printed the same axiom list for those four draft targets, including the corrected energy signature. Neither receipt proves any obligation.

6. `git diff --check` passed. The untracked report was also checked with `git diff --no-index --check /dev/null <report>`; working-tree status lists only the requested report. Temporary audit probes are removed; existing designer scratch and original delivery are preserved.

No pinned-PDF erratum is newly asserted. Source acquisition gaps (Nek77 Part-II proofs) and the missing uniform unbounded-frequency time in the ordinary Pos93 route remain explicit. No deviations were introduced into source or production code; all proposed deviations/repairs are confined to this report. Re-audit F1–F4 after correction before dispatch. This is a completed audit with a FAIL verdict, not proof or root closure.
