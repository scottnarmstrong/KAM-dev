# Track W global root-closure review

Reviewer: `sol-global-W` (fresh independent global review, 2026-10-31).

**Root verdict: FAIL for global source-topology acceptance.** The root's statement correspondence and the frozen-order assembly pass. Findings G1–G3 prevent acceptance of the assembled dependency model under the binding specification; they do not refute W-NLW2 or assert a missing analytic estimate.

## Scope and frozen inputs

Worktree `/root/code/KAM-inp-wgraph`, branch `inp-wgraph`, read-only HEAD `3c54696db828e44a378390eed4927fcdd46a6952`. Scope is the assembled source graph, coverage, eleven pinned W parts, four imported K source statements and their use sites, and the thirteen permitted frozen declarations. Manifest identity fields alone were used. Slice/delta reports were background, not acceptance evidence. No implementation/provider file was opened and no Lean, Lake, build, source lint, or state-changing git command was run. Only this report is written.

Snapshot:

- DEPGRAPH.md SHA-256: `a09a8ae722fbf6e404e1f564fa8594dd8bff5ca845017c2ac60fa6c43f9e9571`.
- DEPGRAPH_COVERAGE.md SHA-256: `7cc6d00d3236dded7f1af6b9af1cac26c9b34aac73d55e2ae3f4a2518141872d`.
- Source bytes are identified by `CORPUS.sha256` and `IMPORTS.sha256`; both checks succeeded.

This is a source correspondence/topology audit, not a claim that every source proof has been independently reproved or that any Lean theorem is closed. Discovery and a separate refutation pass were performed against the current source, including checks for local adaptations, conditional quantifiers, transitive paths and negative/provenance citations.

## Root: four independently reconstructed fields

`bpW:wh:nlw2`, `KAM.Wave.nlw2`, `wave.nlw2.v1`.

**SOURCE_HYPOTHESES:** `m : ℝ`, `hm : 0 < m`. Fixed definitions/conventions: positive actions `Fin 2 → ℝ`; period-one angles `Fin 2 → ℝ`; modes `ℕ+`, tangential `i` represents mode `i+1`; `WaveSpace = lp ℝ 2 × lp ℝ 2` in weighted coordinates with product max norm. Physical coefficients are `coeff y j = y j / (j exp j)`. Set `P={I | ∀ i, 0<I i}`, `r(I)=sqrt(I 0+I 1)` and `B_h=Metric.ball 0 h`. No derived normal-form or KAM conclusion is an additional premise.

**SOURCE_QUANTIFIERS:** For every `m>0`, choose in frozen order `r₀,C,τ : ℝ`, total `η : ℝ → ℝ`, `Γ : Set (Fin 2 → ℝ)`, total `ν : (Fin 2 → ℝ) → Fin 2 → ℝ`, and total `K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace`. Require `r₀>0`, `C>0`, `τ>1`, `η(r)≥0` for `0<r<r₀`, and `η→0` along `nhdsWithin 0 (Ioi 0)`. Require Γ measurable, Γ⊆{I∈P | r(I)<r₀}, `ContinuousOn ν Γ` and joint `ContinuousOn (uncurry K) (Γ ×ˢ univ)`. Only then quantify over `I∈Γ`, angles, mode, time and spatial point. The positive `γ_I` is chosen separately after I. In (3) the binder includes every positive-carrier proof `hI`; `linearTorus` does not depend on that proof. Values of η outside the positive interval and of ν,K outside Γ impose no extra conclusion.

**SOURCE_CONCLUSION:** In the frozen order:

1. `volume(Γ∩B_h)/volume(P∩B_h)→1` in `[0,∞]`, with the positive-sided filter at zero.
2. For each I∈Γ, ∃γ_I>0 with `IsDiophantine γ_I τ (ν I)`; `ν→(lam m hm (i+1)/(2π))_i` along `nhdsWithin 0 Γ`.
3. Each K_I is `IsAnalyticTorusEmbedding`; for every θ at the same angle, `‖K_I θ-linearTorus I hI θ‖≤η(r(I))r(I)` and `‖K_I θ‖≤C r(I)`.
4. For every I∈Γ, θ and j∈ℕ+, the coordinate curves at t=0 have `HasDerivAt` derivatives `lam_j * coeff(K_I θ).2 j` and `-(lam_j * coeff(K_I θ).1 j)-cubicGrad m hm (K_I θ).1 j` respectively.
5. For every θ₀, `u(t,x)=reconU m hm (K_I(θ₀+t•ν(I))).1 x` is analytic at every point of ℝ×[0,π], satisfies the exact frozen `IsClassicalSolution`, and has time derivative `reconV m hm (K_I(θ₀+t•ν(I))).2 x`. For all t and x∈[0,π], the sum of |u|, |`derivWithin (u t) (Icc 0 π) x`| and |reconV| is ≤C r(I).
6. Equality `K_I θ=K_I' θ'` for I,I'∈Γ implies I=I' and ∃k:Fin 2→ℤ with θ−θ' equal to k cast coordinatewise.

**CONSTANT_SCOPE:** All seven witnesses follow m and precede I,θ,θ₀,t,x,j. They can depend on m; there is no uniformity in m. C is one witness common to (3) and (5), and τ is common to all shells. γ_I is per I and may degenerate.

Evidence: `w-headline.tex:19–71`; `KAM/Frozen/Wave/Theorems/Nlw2.lean:43–81` (declaration statement); the permitted frozen definition files. The graph's four fields agree with this reconstruction, interpreting the headline's partial-domain notation by the frozen total functions.

All thirteen anchor paths, exports, manifest IDs, contract versions and ABI hashes match the identity data. `bpW:wh:dioph#IsDiophantine` remains the existing track-K frozen definition transcribed as W's thirteenth anchor, as explicitly ruled in SPEC. All non-anchors, including imports, have empty (`-`) frozen fields.

## Frozen-order assembly and closure spine

The root proof locator is exactly `w8-assembly.tex:552–599`; its single proof-result edge points to `bpW:w8:nlw2-proof` at the theorem's claim `548–550`. Definition-symbol edges remain separate. The complete ordered proof-step list is:

`p-pos`, `p-etapos`, `p-etalim`, `p-meas`, `p-incl`, `p-nucont`, `p-Kcont`, `p-dens`, `p-dioph`, `p-lim`, `p-emb`, `p-close`, `p-size`, `p-inv`, `p-pde`, `p-inj`, `p-assembly`.

There are **16 conjunct-check steps plus one assembly step**, 17 labelled steps total. The brief's “17 conjunct steps plus the assembly step” overcounts by one; positivity of r₀,C and τ>1 is grouped in p-pos. No frozen conjunct is missing.

| Boundary checked | Result on current source/model, apart from findings below |
|---|---|
| W0/W1/W3 normalizations | Weighted coordinates versus coefficients, max versus Hilbert/sum norms and √2 factors, positive-mode indexing, clockwise z rotation, φ=2πθ and ν=ω/(2π), 1/16 quartic prefactor, corrected A/B and K_s,C_m are retained. C_m is independent of m. |
| W2–W3 on W1; W4 on W1/W3 | Trilinear/smoothing and reconstruction interfaces, scalar reduction of Fourier uniqueness/decay, operator ℓ¹ replacement, and the Riesz representation repair have explicit suppliers. See G2–G3 for the imported analytic theorem boundary. |
| W3 normal form → W5 → W8 | W5 action–angle domain check uses c_A(t+r²)<ρ₁² and shifted Dirichlet weights. W8 bounds Ψ in B_{ρ_n} and Z⁻¹Ψ in the real B_{r₁} before Γ^ℝ is used. |
| W4 → W5 modified solve | Guard (G) is satisfied by a=p=1. The modified Q divisors use β=1/4; the stronger Lipschitz condition 2β≤p+1−p_+=1/2 is explicit in the source/quantifier fields. The σ loss is 53 for the preparatory step and 52 for the subsequent iteration. |
| W5 → W6 | Preparatory ε is a positive chosen majorant, so η_P,r₀,ε₀ are positive. The initial full Lipschitz bound and onto property are retained. The unmodified iteration and weak conjugacy are separate from the modified step. |
| W7 constants and W6 interface | (C1)–(C2) precede X and the split Xzones#consts; (C4) uses the definitions of σ_X,c_X, not the conditional zone bound. No cycle through Xzones is present. s,σ_P,M,γ₀,γ₁,γ and θ are fixed before shell α. |
| W6 → W8 | The ε₀ interval is genuinely a parameter: sharp-prep supplies ε^flat_{0,n}≤ε_{0,n}≤γ₁ check α_n. w6-general uses results for that value, and e_tor≤E₅t_n^{1/64} tends to zero. |
| W7 → W8 | q=1/2; α_n=t_n^{95/64}; r_n²=t_n^{3/2}; trimmed Π_n is Borel, lies in the admissible box, and the relative excluded fraction tends to zero as t_n^{1/94}. γ_I=check α_n/(8π)>0, with fixed τ=24. |
| Weak return trip | W8 shell-inv applies transport-tori-weak, not the stronger regularity hypothesis without proof. The invariance equation supplies W⁺ regularity pointwise before Γ conjugacy. |
| Embedding, closeness, injectivity | Cauchy gives ‖DX‖≤1/2; closeness compares at the same θ. Family injectivity uses coefficient-orbit uniqueness, winding and injective frequencies, including cross-shell margins. |
| PDE and common C | W2 orbit/clause5 consume analyticity, coordinate invariance and the C₃ size bound. W8 chooses C=max(1,M_m)C₃ before I, and retains derivWithin at both endpoints. |

The two route nodes of `stepW:w1:tricoord` encode sufficient alternatives, not conjunctive prerequisites. The coefficient bound needed by the selection route is supplied by the signed quartic formula and λ≥j; the cubic-bound route invokes the already stated estimate.

## Findings

### G1 — major: section-data premises are copied into fields but omitted as direct dependencies

GLOBAL-BRIEF §3 requires: “Every node that uses section data (`<section>#data`) must depend on that data node.” The current graph applies this inconsistently. For example:

- `bpW:w3:Lambda` (`DEPGRAPH.md:6651`): SOURCE_HYPOTHESES explicitly imports W3 standing data, and its proof at `w3-birkhoff.tex:209` uses p≥1/2. DEPS reaches `bpW:w3#data` only through `bpW:w3:space`.
- `bpW:w5:w4-modified` (`DEPGRAPH.md:11104`): SOURCE_HYPOTHESES imports W5's fixed weights; the proof uses those weights. DEPS has only transitive access to `bpW:w5#data`.
- `bpW:w8:shells` (`DEPGRAPH.md:17493`): SOURCE_HYPOTHESES names `bpW:w8#data` literally, and its formulas at `w8-assembly.tex:122–124` use c_A,γ,γ₁ from that data. DEPS lists only const and W7 shells.

Refutation check: these are not missing global standing assumptions or claims of false inequalities. The graph contains paths to the packages, and the source fields retain their contents. That does not satisfy the brief's *direct* section-data requirement. Repetition in SOURCE_HYPOTHESES is not the requested direct package edge. The following exhaustive list is restricted to records whose own SOURCE_HYPOTHESES expressly invokes the corresponding standing-data package: 81 W3, 24 W5, 15 W7, 1 W8 (121 total). It does not infer new packages from symbols.

Proposed edge additions follow. For each named consumer, add the target to DEPS, add the complete EDGE line shown, and reopen the record for independent delta review. Existing fields and edges remain. Ownership is stated per group. These are proposal fragments, not changes applied to the database.


#### Owner slice `W-w3`


Consumer `bpW:w3:coords` (`DEPGRAPH.md:6506`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L119-L128 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:omega` (`DEPGRAPH.md:6535`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L139-L145 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:hamfield-def` (`DEPGRAPH.md:6564`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:real-restrict` (`DEPGRAPH.md:6594`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L171-L177 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:forms` (`DEPGRAPH.md:6622`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L189-L197 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:Lambda` (`DEPGRAPH.md:6651`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L200-L206 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:majorant` (`DEPGRAPH.md:6684`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L232-L239 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:quartic` (`DEPGRAPH.md:6716`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L248-L259 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:maj` (`DEPGRAPH.md:6747`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:gradbound` (`DEPGRAPH.md:6775`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:identify` (`DEPGRAPH.md:6803`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:quartic-ident` (`DEPGRAPH.md:6834`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L282-L291 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:Gz` (`DEPGRAPH.md:6871`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:XG` (`DEPGRAPH.md:6900`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:Gnor` (`DEPGRAPH.md:6933`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L312-L313 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:count` (`DEPGRAPH.md:6961`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L314-L318 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:res` (`DEPGRAPH.md:6990`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L319-L321 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:divisor` (`DEPGRAPH.md:7017`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L333 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:sel` (`DEPGRAPH.md:7054`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L339-L342 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:signs` (`DEPGRAPH.md:7080`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L343-L346 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:s0` (`DEPGRAPH.md:7106`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L347-L348 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:s1` (`DEPGRAPH.md:7135`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L349-L353 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:s23` (`DEPGRAPH.md:7165`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L354-L358 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:s1inner` (`DEPGRAPH.md:7194`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L359-L369 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:divconcl` (`DEPGRAPH.md:7225`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L370-L373 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:Fdef` (`DEPGRAPH.md:7256`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L395-L401 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:F` (`DEPGRAPH.md:7284`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L406-L413 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:fcoef` (`DEPGRAPH.md:7313`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L416-L419 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:Fconcl` (`DEPGRAPH.md:7341`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L420-L423 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:homological` (`DEPGRAPH.md:7371`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L427-L432 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:Xfcoord` (`DEPGRAPH.md:7402`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L435-L437 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:euler` (`DEPGRAPH.md:7430`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L438-L443 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:divide` (`DEPGRAPH.md:7461`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L444-L448 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:lie-coeff` (`DEPGRAPH.md:7490`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L461-L466 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:leibniz` (`DEPGRAPH.md:7519`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L470-L480 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:rec` (`DEPGRAPH.md:7551`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L483-L485 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:norms` (`DEPGRAPH.md:7579`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L486-L490 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:Phireal` (`DEPGRAPH.md:7608`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L491-L492 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:leib` (`DEPGRAPH.md:7635`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L493-L496 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:leibid` (`DEPGRAPH.md:7662`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L497-L500 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:flow` (`DEPGRAPH.md:7691`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L504-L527 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:conv` (`DEPGRAPH.md:7726`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L530-L537 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:floweq` (`DEPGRAPH.md:7755`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L538-L541 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:transport` (`DEPGRAPH.md:7784`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L542-L544 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:est` (`DEPGRAPH.md:7812`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L545-L551 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:Greal` (`DEPGRAPH.md:7841`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L552-L553 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:var` (`DEPGRAPH.md:7868`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L554-L557 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:inv` (`DEPGRAPH.md:7897`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L558-L565 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:symplectic` (`DEPGRAPH.md:7928`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L579-L586 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:skew` (`DEPGRAPH.md:7959`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L589-L592 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:constform` (`DEPGRAPH.md:7988`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L593-L597 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:gradtrans` (`DEPGRAPH.md:8018`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L598-L602 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:Yseries` (`DEPGRAPH.md:8047`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L621-L629 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majcalc` (`DEPGRAPH.md:8083`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L633-L644 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majflow` (`DEPGRAPH.md:8111`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L645-L647 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majA` (`DEPGRAPH.md:8140`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L648-L654 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majN` (`DEPGRAPH.md:8170`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L655-L661 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majX` (`DEPGRAPH.md:8200`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L662-L665 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majY` (`DEPGRAPH.md:8229`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majint` (`DEPGRAPH.md:8259`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L672-L675 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majps` (`DEPGRAPH.md:8287`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:majreal` (`DEPGRAPH.md:8316`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L679-L682 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:main` (`DEPGRAPH.md:8345`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L687-L705 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:Kanalytic` (`DEPGRAPH.md:8382`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L710-L713 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:K1` (`DEPGRAPH.md:8412`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L714-L717 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:K2` (`DEPGRAPH.md:8442`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L718-L723 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:XK1` (`DEPGRAPH.md:8474`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L724-L731 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:XK2` (`DEPGRAPH.md:8505`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L732-L741 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:XKconcl` (`DEPGRAPH.md:8537`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L742-L746 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:iii` (`DEPGRAPH.md:8570`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L747-L748 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:conj` (`DEPGRAPH.md:8598`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:gamma-real` (`DEPGRAPH.md:8630`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L780-L794 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:transport-tori` (`DEPGRAPH.md:8664`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L810-L817 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:hamfield-def#hamilton` (`DEPGRAPH.md:8723`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:quartic-sec#data` (`DEPGRAPH.md:8752`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L224-L230 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:main-sec#data` (`DEPGRAPH.md:8781`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L608-L619 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:transport-tori-weak` (`DEPGRAPH.md:8841`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L831-L842 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:wk-lin` (`DEPGRAPH.md:8876`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:wk-reg` (`DEPGRAPH.md:8907`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w3:wk-transport` (`DEPGRAPH.md:8939`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w3:class-remark` (`DEPGRAPH.md:8969`):

```text
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


#### Owner slice `W-w5a`


Consumer `bpW:w5:omega` (`DEPGRAPH.md:10757`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L89-L93 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:ombd` (`DEPGRAPH.md:10787`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L95-L96 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:omnd` (`DEPGRAPH.md:10814`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnd@L97-L99 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:omnorm` (`DEPGRAPH.md:10840`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L100-L101 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w5:class` (`DEPGRAPH.md:10867`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L105-L119 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:g-tail` (`DEPGRAPH.md:10990`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L153-L154 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:g-div` (`DEPGRAPH.md:11017`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L155-L157 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:g-diag` (`DEPGRAPH.md:11044`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L158-L160 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:g-rest` (`DEPGRAPH.md:11072`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L161-L164 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w5:w4-modified` (`DEPGRAPH.md:11104`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L170-L191 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:m-sup` (`DEPGRAPH.md:11139`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L194-L198 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:m-other` (`DEPGRAPH.md:11166`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L199-L200 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:m-lip` (`DEPGRAPH.md:11194`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L201-L204 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:m-act` (`DEPGRAPH.md:11223`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L205-L226 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:m-ass` (`DEPGRAPH.md:11257`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L227-L231 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:m-const` (`DEPGRAPH.md:11289`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L232-L235 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w5:taylor` (`DEPGRAPH.md:11316`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L265-L285 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:t-scale` (`DEPGRAPH.md:11351`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-scale@L287-L290 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:t-disc` (`DEPGRAPH.md:11378`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-disc@L291-L293 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:t-poly` (`DEPGRAPH.md:11404`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-poly@L294-L298 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:t-comp` (`DEPGRAPH.md:11431`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L299-L307 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:t-field` (`DEPGRAPH.md:11466`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L308-L313 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w5:t-est` (`DEPGRAPH.md:11495`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L314-L320 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w5:data` (`DEPGRAPH.md:11524`):

```text
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L328-L348 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


#### Owner slice `W-w7a`


Consumer `bpW:w7:omega0` (`DEPGRAPH.md:14799`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L127-L131 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w7:freqcoords` (`DEPGRAPH.md:14827`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L135-L150 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:inverse` (`DEPGRAPH.md:14859`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:norms` (`DEPGRAPH.md:14888`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:Omegazeta` (`DEPGRAPH.md:14918`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:measure-affine` (`DEPGRAPH.md:14947`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w7:unpert-bounds` (`DEPGRAPH.md:14976`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L172-L181 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:ssize` (`DEPGRAPH.md:15010`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:plus` (`DEPGRAPH.md:15039`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:minus` (`DEPGRAPH.md:15068`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:kappa` (`DEPGRAPH.md:15097`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `stepW:w7:liplOmega` (`DEPGRAPH.md:15126`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w7:constdef` (`DEPGRAPH.md:15155`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w7:Xdef` (`DEPGRAPH.md:15652`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L398-L401 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


Consumer `bpW:w7:constdef#base` (`DEPGRAPH.md:16040`):

```text
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


#### Owner slice `W-w8a`


Consumer `bpW:w8:shells` (`DEPGRAPH.md:17493`):

```text
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L117-L128 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
```


### G2 — major: imported source fields are not copies of their current owner records

SPEC's import policy requires the four source fields to be copied from `docs/graph/K/DEPGRAPH.md`. All four W imports differ in SOURCE_HYPOTHESES; the other three source fields agree. W explicitly adds K's inherited finite-dimensional target/strip conventions, while the owner graph has not incorporated those constraints. The W NOTEs themselves say the upstream correction is still needed. Neither the imports tool nor the structural linter checks this equality.

Evidence: W `DEPGRAPH.md:20408,20434,20460,20486`; K source `blueprint/parts/p1-analysis.tex:24–47,296–312,531–534,757–768,786–789`; corresponding K graph records by ID. The W additions agree with the source. **Do not repair this by dropping the genuine source restrictions from W.**

Refutation check: the extra text is not merely a reordered spelling: it changes the explicit applicability contract (notably finite-dimensional target versus arbitrary Banach target). The explanatory NOTE documents a pending upstream action, not an exception in SPEC. No later SPEC ruling waives exact copying.

Required reconciliation: source-review and update the owner K records, then regenerate/review W imports. G3 proposes removing the proof-only holomorphic-analytic import; the remaining three owner corrections are given as complete K node proposals below. Owner: track K (outside the authorized edit envelope); W integration owner: `W-imports`. These blocks deliberately preserve K's own identity/contract fields and source locators, add only the source's inherited premises, and reopen topology review. They are not applied here.


```text
NODE: bp:p1:decay
KIND: lemma
TITLE: Coefficient decay
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay@L786-L789
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay@L791-L819
CONTRACT_ID: bp:p1:decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1, rho > 0, u takes values in a finite-dimensional complex normed W; u holomorphic, bounded and 1-periodic on T_rho
SOURCE_QUANTIFIERS: rho, u; k in Z^n; rho' with 0<=rho'<rho
SOURCE_CONCLUSION: |hat u_k| <= e^{-2 pi |k|_1 rho'} ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:dec-shift, step:p1:dec-bound, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:dec-shift | blueprint/parts/p1-analysis.tex#bp:p1:decay@L800-L800 | proof step of this result
EDGE: step:p1:dec-bound | blueprint/parts/p1-analysis.tex#bp:p1:decay@L813-L813 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:decay@L787-L787 | strip T_rho used by name
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: norm_torusCoeff_le_of_lt (KAM/Strip/Fourier.lean:229); boundary radius norm_torusCoeff_le (:291)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -
```


```text
NODE: bp:p1:fourier-basic
KIND: lemma
TITLE: Fourier coefficients of periodic functions
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L757-L768
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L770-L784
CONTRACT_ID: bp:p1:fourier-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing convention K p1 L34-L47: n >= 1, Fourier indices in Z^n, period one; v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0
SOURCE_QUANTIFIERS: v; k in Z^n; ell; omega in C^n; r
SOURCE_CONCLUSION: (a) hat(d_ell v)_k = 2 pi i k_ell hat v_k and hat(d_omega v)_k = 2 pi i (k.omega) hat v_k; (b) v(x)=sum hat v_k chi_k(x) for all x, so v=0 if all hat v_k=0; (c) v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:fb-derivative, step:p1:fb-series, step:p1:fb-holomorphic, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:fb-derivative | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L771-L771 | proof step of this result
EDGE: step:p1:fb-series | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L778-L778 | proof step of this result
EDGE: step:p1:fb-holomorphic | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L781-L781 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L765-L765 | strip T_r used by name
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: (a) KAM.torusCoeff_fderiv_real, torusCoeff_fderiv_coordinate_real (FourierDerivative); (b),(c) KAM.hasSum_torusCoeff_mul_character, eq_zero_of_torusCoeff_eq_zero, eq_zero_of_torusCoeff_holomorphic (FourierBasic; scalar, componentwise per the blueprint)
LEAN_NOTE: Zohar Komargodski's Part 1 Fourier layer; retro audit docs/campaign/audits/I-STRIP-2-audit-1.md (PASS for these nodes; part (a) via I-STRIP-3b-audit-1.md)
NOTE: -
```


```text
NODE: bp:p1:strip-identity
KIND: lemma
TITLE: Identity theorem on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L536-L546
CONTRACT_ID: bp:p1:strip-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1 and W a finite-dimensional complex normed space; r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x
SOURCE_QUANTIFIERS: r>0 ; v
SOURCE_CONCLUSION: v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:si-induction, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:si-induction | blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L537-L537 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L532-L532 | strip T_r used by name
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.strip_identity
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -
```


### G3 — major: an adapted Banach-target proof is represented by a theorem-import edge

At `w1-sequences.tex:829–835`, the coefficient argument explicitly replaces K's finite-dimensional W by a complete Banach F. The W step supplies the reasons for transporting the proof: complete-target one-variable Cauchy and Bochner integration. The imported theorem, however, has finite-dimensional W (K source `p1-analysis.tex:24–27,296–312`). `stepW:w1:hacoef` still has a direct theorem dependency `K:bp:p1:holomorphic-analytic`, with rationale “K's Cauchy-coefficient argument ... W replaced by ... F” (`DEPGRAPH.md:4187` and its EDGE lines). This is a proof adaptation, not an application satisfying that imported statement's premises.

SPEC expressly says that a mention that “the proof of K's Lemma ... carries over” is **not an import**: W owns the argument and the K label is provenance. A graph EDGE rationale cannot widen the imported theorem's carrier. This affects the W1 finite-domain analytic toolkit used by W5/W6/W8 and therefore belongs in the root review.

Refutation check: the W text does explain the carrier transfer; this finding does **not** classify that transfer as an unproved mathematical SOURCE_GAP. Its two external suppliers are present, and K's proof at `p1-analysis.tex:319–350` uses the stated Cauchy/geometric-series/Bochner argument. The defect is its classification as a direct theorem import under SPEC. The other three imports are genuine scalar applications and do not have this problem.

Owner `W-w1b`: replace hacoef by the following complete block. K proof provenance remains in NOTE. No finite-dimensional premise is added to W.


```text
NODE: stepW:w1:hacoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L829-L835
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L829-L835
CONTRACT_ID: stepW:w1:hacoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U; local data: F complete
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); within the step: alpha in N^n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: there are c_alpha in F with ¦¦c_alpha¦¦ <= M_1 r_1^{-¦alpha¦} and f(z) = sum_alpha c_alpha (z - z_0)^alpha absolutely on P(z_0,r_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:hamargin, bpW:w1:ext-onevar, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:hamargin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L831-L831 | the radius r_1 and the bound M_1
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L833-L833 | the one-variable Cauchy formula for complete F
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L835-L835 | Fubini and termwise integration of Bochner integrals on the torus
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: W owns the complete-target Cauchy coefficient argument described at L829-L835. The finite-dimensional K theorem is not applied to F; its han-cauchy through han-bounds proof is provenance for this local adaptation. The external Cauchy formula and Bochner integration supply the transfer. This is the SPEC proof-reuse case, not an imported theorem application.
```


Owner `W-imports`: delete `K:bp:p1:holomorphic-analytic` (its only consumer is hacoef). Replace its coverage item completely as follows; this avoids an artificial unreferenced external after the edge correction.

```text
ITEM: K:bp:p1:holomorphic-analytic
KIND: external
SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L296-L312
DISPOSITION: EXCLUDED
REASON: proof provenance only under SPEC import policy: stepW:w1:hacoef owns the Banach-target adaptation of K's finite-dimensional Cauchy argument, with W external suppliers ext-onevar and ext-integral; no W node applies the K theorem with its literal finite-dimensional target premise
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: -
```

## Reachability and coverage findings

- Unreachable nodes in the submitted graph: **none**. All 696 nodes lie in the root closure; acyclicity passes the required gate.
- Unmapped inventory items in the submitted manifest: **none mechanically**; all 1094 items are REVIEWED. The substantive imported-item classification change is G3. G1 concerns missing direct package edges, not unmapped text.
- The excluded rescaling, W0 PDE equivalence theorem with its time/ident/converse steps, formal-birkhoff, Duffing/Lindstedt, W4 k0 and W7 melnikov have no required root application. W2 fcub consumes the retained **force step**, not the excluded whole PDE-equivalence theorem. W6 prep consumes zones(i) directly, not the stronger conditional W7 melnikov corollary.
- The preserved claim nodes for kam-conventions, class-remark and to-w8 cover genuine consumers. Citations that only state what is not used, identify ownership, give source provenance or point forward do not create extra mathematical prerequisites. In particular the negative references to W3 interface in W4 from-w3 do not resurrect that administrative summary.
- No currently unpaid SOURCE_GAP node is present. Two historical NOTE strings say a previous SOURCE_GAP was resolved; those are not open gaps. The ten W4–W6 repairs have explicit source suppliers (Riesz representation, symmetry, triangular integral, principal square root, parameter differences, and the preparatory full Lipschitz/onto/Borel interfaces). No additional analytic gap is claimed by this report.

## Checks and exact outcomes

```text
sha256sum -c docs/graph/W/CORPUS.sha256
# exit 0: all 11 W source files OK

sha256sum -c docs/graph/W/IMPORTS.sha256
# exit 0: blueprint/parts/p1-analysis.tex OK

python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_imports.py docs/graph/W/packets --slice W-imports --root . --owner K=blueprint --owner-graph K=docs/graph/K --self-track W
W-imports: 4 imported nodes present, 4 referenced, 0 missing, 0 unreferenced
# exit 0

python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-reviewed --require-complete-coverage --require-initial-lean-status --require-all-reachable
docs/graph/W/DEPGRAPH.md:12: review gate: missing or placeholder GLOBAL_REVIEWER
docs/graph/W/DEPGRAPH.md:13: review gate: missing or placeholder GLOBAL_REVIEW_REF
# exit 1; exactly the two expected header failures, no other output
```

Additional read-only comparisons: 696 nodes, 48 external leaves (four imports included), no external with prerequisites; all non-anchor FROZEN_* fields are `-`; all four imports have one SOURCE_HYPOTHESES mismatch with their owner and no mismatch in the other three source fields. These checks diagnose G1–G3; mechanical validation alone would miss them. No proof-status/manifest-state inference or axiom probe was used.

## Suspected blueprint defects

None newly established in the pinned W mathematical text by this review. The complete-target analytic argument is explicitly a local adaptation, not a new mathematical erratum (G3). Existing source errata and deviations remain as recorded in W0/W1/W4/W5/W7; their original scanned papers were not independently re-audited here.

One administrative discrepancy: GLOBAL-BRIEF's proof-step count should read “16 conjunct steps plus the assembly step” (the source has 17 total). This does not require changing the graph, the frozen statement or the blueprint proof.

## Unresolved questions and closeout

1. Apply/review the 121 direct section-data additions under the brief's explicit rule (G1); no new mathematical premises are proposed.
2. Reconcile the owner K source fields with the accurate inherited premises before claiming exact-copy imports (G2). The upstream K proposals require their own owner review; none was applied here.
3. Classify the Banach-target proof reuse according to SPEC and remove the theorem-only import as proposed (G3), or obtain an explicit specification ruling if a different graph semantics is intended. The current binding policy provides no such exception.

The statement correspondence and frozen-order assembly pass. Global graph acceptance remains FAIL until these topology/provenance findings are resolved and the affected records receive independent delta review. No Lean proof closure is asserted.
