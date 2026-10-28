# Lean design for planetary Parts 8–10

Design draft, 2026-10-28. Assigned branch `inp-design-p810`, base `081967912d5200ad4711d6d16abde6a8cfafea71`.
This is statement and implementation planning, with no proofs or frozen closures claimed.
The signatures in Appendix A are the exact checked draft, not production dependencies.

## Decisions

1. Use the published graph from `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` (publication reported by the orchestrator at `f21b16a`).
   The scope is **158 nodes**, selected by statement-source file, including proof steps, external facts,
   definition components and both Part 9 alternatives. All three blueprint files are byte-identical to this worktree.
   Published Part 8 edges `bpP:p12:f-unif` and `K:bp:p1:ext-integral` are consumed explicitly.
2. Reuse the delivered Poincare/Newtonian modules; do not copy their objects into a secular representation.
   `secular` is an exposed abbreviation-by-definition of the frozen `secularAverage` at `(I,p,q)=(Lambda,eta,xi)`.
   Its two matched models are selected by one Boolean. All spectral and nondegeneracy data are independent of coupling.
3. Literal coefficient formulas define the halved matrix. `Omega=2*sigma`, with sorted **increasing** eigenvalues;
   this ordering is independent of increasing planet axes. No complex continuation or universal cover is used.
4. Keep Euclidean lengths, induced matrix operator norms and CP09 diagonal tensor norms as explicit scalar functions
   on `Fin n → ℝ`. Mathlib's scoped `Matrix.Norms.Elementwise` supplies the topology for matrix calculus only.
   No new instance is installed on a function or matrix type. The spectral theorem's matrix outputs are used;
   no declaration introduces `EuclideanSpace`.
5. The `rho_*` witness remains existential, shared by all real angles, pairs and both models. It is not an arbitrary
   chosen radius whose admissibility is later assumed. `rho` is the literal `rho_0` formula. Each local expansion may
   shrink the radius. Use the common minimum when assembling outputs.
6. Main nodes get slug names. To resolve the repeated slugs `n2`, `good-set` and `conv#data`, use nested namespaces
   `KAM.Planetary.SecularForm`, `KAM.Planetary.SecularSpectrum`, `KAM.Planetary.Nondegeneracy`.
   `Fc-def`, `Fc-analytic`, `F-nonzero` become `fc_def`, `fc_analytic`, `f_nonzero`.
7. Do not identify Cartesian slow shifts with oscillator angle shifts. Part 9 exports the analytic symplectic lift,
   its fast-angle equivariance and average identity. The **polar chart must be composed before** the Part 1
   `phys_pipeline` period-one transport can be applied. The exact Part 1 interfaces are copied verbatim for
   elaboration only at the end of Appendix A; production imports their owning modules.
8. Internal graph steps are proof cuts of the listed theorem, not separate assumed lemmas. Their exact obligations
   remain the source displays at the table locators; the parent signature is proved from source premises.
   External facts with no applicable Mathlib theorem are owned proof packages, never axioms.


| Blueprint source | SHA-256 |
|---|---|
| `blueprint-P/parts/p8-secular-form.tex` | `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc` |
| `blueprint-P/parts/p9-secular-spectrum.tex` | `19271673e246eed9d444a3f370c479aa13685528e306f9addcddc550cc56da54` |
| `blueprint-P/parts/p10-nondegeneracy.tex` | `a76d868e361ef824a7e4c546719811da97a0d14bba1fd686b3eb61c32ea57124` |

## Carriers and standing structures

| Object | Exact carrier / definition | Guard |
|---|---|---|
| Physical data | `SecularForm.Data n` | `G,m0,m_i>0`, `0<n`; only source standing data |
| Axes | `axes n = {a | (∀ i, 0<a i) ∧ StrictMono a}` | open convex connected cone |
| Actions | `action D a`, inverse `axis D I`, `actionDomain D` | positive actions; source axes-to-actions diffeomorphism |
| Full chart | delivered `Phase (n+n)`, `assemble`, `planetBlock`, `poincareProd` | physical output `Phase (n*2)` |
| Slow tuple | `(Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)` | order `(xi,Lambda,eta)`; no replacement for Phase |
| Slow variation | `(Fin n → ℝ) × (Fin n → ℝ)` | order `(xi,eta)` |
| Complex tuple | the same product over `ℂ` | complex square is bilinear, never Hermitian |
| Matrix | `Matrix (Fin n) (Fin n) ℝ` | literal `qhat`, `coeffs`; symmetry proved, not assumed |
| Spectrum | `sorted M hM i := hM.eigenvalues₀ (Fin.cast ... i.rev)` | reverses Mathlib's antitone list, multiplicities retained |
| Non-resonance | finite set `k4 n`; `nr4`, `good` | all integer vectors `0<sum abs k≤4` |
| R-nondegeneracy | `rnd_def B omega` | every nonzero **real** relation vector, not merely integers |
| Amount | `betaFamily`, `betaMu` | minimum over nonempty compact parameter sphere × compact patch |
| Index | `index_def ... h = Nat.find h` | existence of a positive order with positive amount; no default zero |

The product `Slow` is only notation for the variables in the integral. Every actual Hamiltonian is still on
`Phase`; every model comparison and Birkhoff transfer uses frozen definitions. No structure contains analyticity,
quadratic representability, spectral separation, finite type, a good patch, or a downstream theorem as an assumption.

## Node → declaration table

Owner namespaces in the declaration column are relative to `KAM.Planetary`; explicitly qualified Mathlib and neighbouring-namespace references retain their indicated owner. A “proof cut in” entry means that its source
statement is a local obligation inside the named exported theorem; the source locator is authoritative for that cut.
A slash groups cooperating declarations. Existing Mathlib entries are reuse, not proposed duplicate declarations.
Source and proof locators are transcribed from the published graph, including component labels.

| Graph node | Declaration / disposition | Statement locator | Proof locator |
|---|---|---|---|
| `bpP:p8:e-param` | infrastructure, SecularForm: `e_param` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-param@L26-L26` | `-` |
| `bpP:p8:e-diff` | infrastructure, SecularForm: `e_diff / average_translate` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-diff@L27-L27` | `-` |
| `bpP:p8:e-taylor` | infrastructure, SecularForm: `e_taylor` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-taylor@L28-L28` | `-` |
| `bpP:p8:e-weyl` | infrastructure, SecularForm: `e_weyl` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-weyl@L29-L29` | `-` |
| `bpP:p8:e-poch` | infrastructure, SecularForm: `e_poch` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-poch@L30-L30` | `-` |
| `bpP:p8:conv#data` | export, SecularForm: `Data / secular / polydisc / inclusion` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L17-L22` | `-` |
| `bpP:p8:rho` | export, SecularForm: `rho` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:rho@L33-L35` | `-` |
| `bpP:p8:perturbation-analytic` | export, SecularForm: `perturbation_analytic` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L39-L46` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L47-L52` |
| `stepP:p8:pa-circ` | proof cut in, SecularForm: `perturbation_analytic` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-circ@L48-L48` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-circ@L48-L48` |
| `stepP:p8:pa-unif` | proof cut in, SecularForm: `perturbation_analytic; compact_uniform (published edge bpP:p12:f-unif)` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49` |
| `stepP:p8:pa-hol` | proof cut in, SecularForm: `perturbation_analytic` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50` |
| `stepP:p8:pa-avg` | proof cut in, SecularForm: `perturbation_analytic` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51` |
| `bpP:p8:symmetries` | export, SecularForm: `symmetries` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L58-L66` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L67-L73` |
| `stepP:p8:sy-1` | proof cut in, SecularForm: `symmetries` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-1@L69-L69` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-1@L69-L69` |
| `stepP:p8:sy-2` | proof cut in, SecularForm: `symmetries` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-2@L70-L70` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-2@L70-L70` |
| `stepP:p8:sy-3` | proof cut in, SecularForm: `symmetries` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-3@L71-L71` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-3@L71-L71` |
| `stepP:p8:sy-f` | proof cut in, SecularForm: `symmetries` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-f@L72-L72` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-f@L72-L72` |
| `bpP:p8:evenness` | export, SecularForm: `evenness / evenness_taylor` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L75-L80` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L81-L85` |
| `stepP:p8:ev-inv` | proof cut in, SecularForm: `evenness / evenness_taylor / quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-inv@L82-L82` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-inv@L82-L82` |
| `stepP:p8:ev-tay` | proof cut in, SecularForm: `evenness / evenness_taylor / quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83` |
| `stepP:p8:ev-quad` | proof cut in, SecularForm: `evenness / evenness_taylor / quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-quad@L84-L84` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-quad@L84-L84` |
| `bpP:p8:lemma64` | export, SecularForm: `lemma64 / lemma64_coordinates` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L89-L99` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L100-L106` |
| `stepP:p8:l64-a` | proof cut in, SecularForm: `lemma64 / lemma64_coordinates` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101` |
| `stepP:p8:l64-b` | proof cut in, SecularForm: `lemma64 / lemma64_coordinates; periodic_derivative_integral (published edge K:bp:p1:ext-integral)` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102` |
| `stepP:p8:l64-c` | proof cut in, SecularForm: `lemma64 / lemma64_coordinates` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103` |
| `stepP:p8:l64-d` | proof cut in, SecularForm: `lemma64 / lemma64_coordinates` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104` |
| `stepP:p8:l64-e` | proof cut in, SecularForm: `lemma64 / lemma64_coordinates` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-e@L105-L105` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-e@L105-L105` |
| `bpP:p8:laplace-def` | export, SecularForm: `laplace_def / laplace_fourier` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace-def@L110-L114` | `-` |
| `bpP:p8:laplace` | export, SecularForm: `laplace` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L116-L120` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L121-L124` |
| `stepP:p8:la-exp` | proof cut in, SecularForm: `laplace` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-exp@L122-L122` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-exp@L122-L122` |
| `stepP:p8:la-conv` | proof cut in, SecularForm: `laplace` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-conv@L123-L123` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-conv@L123-L123` |
| `bpP:p8:identities` | export, SecularForm: `identities` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L129-L135` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L136-L140` |
| `stepP:p8:id-1` | proof cut in, SecularForm: `identities` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-1@L138-L138` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-1@L138-L138` |
| `stepP:p8:id-2` | proof cut in, SecularForm: `identities` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-2@L139-L139` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-2@L139-L139` |
| `bpP:p8:coeffs` | export, SecularForm: `coeffs / coeffs_hermitian / coeffs_analytic` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:coeffs@L144-L150` | `-` |
| `bpP:p8:quadratic-form` | export, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L152-L158` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L159-L171` |
| `stepP:p8:qf-pair` | proof cut in, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160` |
| `stepP:p8:qf-scale` | proof cut in, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-scale@L161-L161` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-scale@L161-L161` |
| `stepP:p8:qf-c0` | proof cut in, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162` |
| `stepP:p8:qf-diag` | proof cut in, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L165` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L165` |
| `stepP:p8:qf-cross` | proof cut in, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L168` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L168` |
| `stepP:p8:qf-assembly` | proof cut in, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169` |
| `stepP:p8:qf-diag2` | proof cut in, SecularForm: `quadratic_form` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170` |
| `bpP:p8:identification` | export, SecularForm: `identification` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L182-L189` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L190-L194` |
| `stepP:p8:id-diff` | proof cut in, SecularForm: `identification` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191` |
| `stepP:p8:id-avg` | proof cut in, SecularForm: `identification` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-avg@L192-L192` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-avg@L192-L192` |
| `stepP:p8:id-int` | proof cut in, SecularForm: `identification` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-int@L193-L193` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-int@L193-L193` |
| `bpP:p8:same-jets` | export, SecularForm: `same_jets / same_jets_on / same_jets_transfer` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets@L196-L204` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets@L205-L207` |
| `bpP:p8:same-jets#jets` | export, SecularForm: `same_jets_on` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206` |
| `bpP:p8:same-jets#transfer` | export, SecularForm: `same_jets_transfer` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206` |
| `bpP:p8:quartic` | export, SecularForm: `quartic / quartic_scaling / quartic_pair_scaling` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L216-L229` | `blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L230-L235` |
| `stepP:p8:q4-str` | proof cut in, SecularForm: `quartic / quartic_scaling / quartic_pair_scaling` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231` |
| `stepP:p8:q4-a` | proof cut in, SecularForm: `quartic / quartic_scaling / quartic_pair_scaling` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232` |
| `stepP:p8:q4-b` | proof cut in, SecularForm: `quartic / quartic_scaling / quartic_pair_scaling` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-b@L233-L233` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-b@L233-L233` |
| `stepP:p8:q4-c` | proof cut in, SecularForm: `quartic / quartic_scaling / quartic_pair_scaling` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-c@L234-L234` | `blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-c@L234-L234` |
| `bpP:p9:e-spec` | infrastructure, SecularSpectrum: `Mathlib Matrix.IsHermitian.spectral_theorem / charpoly_eq` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-spec@L20-L20` | `-` |
| `bpP:p9:e-ift` | infrastructure, SecularSpectrum: `Mathlib ContDiffAt.contDiffAt_implicitFunction` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-ift@L21-L21` | `-` |
| `bpP:p9:e-fts` | infrastructure, SecularSpectrum: `Mathlib MvPolynomial.esymmAlgEquiv` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-fts@L22-L22` | `-` |
| `bpP:p9:e-id` | infrastructure, SecularSpectrum: `Nondegeneracy.analytic_zero_null; Mathlib AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-id@L23-L23` | `-` |
| `bpP:p9:e-ibp` | infrastructure, SecularSpectrum: `Mathlib intervalIntegral.integral_mul_deriv_eq_deriv_mul / integral_pos_iff_support_of_nonneg_ae` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-ibp@L24-L24` | `-` |
| `bpP:p9:conv#data` | export, SecularSpectrum: `length2 / op2 / frobenius / sorted / norm_compare` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:conv#data@L15-L16` | `-` |
| `bpP:p9:l75` | export, SecularSpectrum: `l75 / l75_bound` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l75@L70-L75` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l75@L76-L78` |
| `stepP:p9:l75` | proof cut in, SecularSpectrum: `l75 / l75_bound` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l75@L77-L77` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l75@L77-L77` |
| `bpP:p9:l74` | export, SecularSpectrum: `l74` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L80-L85` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L86-L89` |
| `stepP:p9:l74-red` | proof cut in, SecularSpectrum: `l74` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-red@L87-L87` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-red@L87-L87` |
| `stepP:p9:l74-ibp` | proof cut in, SecularSpectrum: `l74` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88` |
| `bpP:p9:definite` | export, SecularSpectrum: `definite` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L91-L98` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L99-L103` |
| `stepP:p9:p73-dom` | proof cut in, SecularSpectrum: `definite` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-dom@L100-L100` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-dom@L100-L100` |
| `stepP:p9:p73-had` | proof cut in, SecularSpectrum: `definite` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101` |
| `stepP:p9:p73-cong` | proof cut in, SecularSpectrum: `definite` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102` |
| `bpP:p9:local-analytic` | export, SecularSpectrum: `local_analytic / local_analytic_unique` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L107-L109` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L110-L115` |
| `stepP:p9:la-ev` | proof cut in, SecularSpectrum: `local_analytic / local_analytic_unique` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111` |
| `stepP:p9:la-adj` | proof cut in, SecularSpectrum: `local_analytic / local_analytic_unique` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112` |
| `stepP:p9:la-vec` | proof cut in, SecularSpectrum: `local_analytic / local_analytic_unique` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-vec@L113-L113` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-vec@L113-L113` |
| `stepP:p9:la-so` | proof cut in, SecularSpectrum: `local_analytic / local_analytic_unique` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114` |
| `bpP:p9:lift` | export, SecularSpectrum: `lift / liftMap / liftInv` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L117-L122` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L123-L132` |
| `stepP:p9:lift-bij` | proof cut in, SecularSpectrum: `lift` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-bij@L124-L124` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-bij@L124-L124` |
| `stepP:p9:lift-anti` | proof cut in, SecularSpectrum: `lift` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-anti@L125-L125` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-anti@L125-L125` |
| `stepP:p9:lift-form` | proof cut in, SecularSpectrum: `lift` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-form@L126-L129` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-form@L126-L129` |
| `stepP:p9:lift-mc` | proof cut in, SecularSpectrum: `lift` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-mc@L130-L130` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-mc@L130-L130` |
| `stepP:p9:lift-concl` | proof cut in, SecularSpectrum: `lift` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131` |
| `bpP:p9:diagonalize` | export, SecularSpectrum: `diagonalize; Part 1 phys_pipeline after polar composition` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L134-L147` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L148-L153` |
| `stepP:p9:d-a` | proof cut in, SecularSpectrum: `diagonalize` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149` |
| `stepP:p9:d-b` | proof cut in, SecularSpectrum: `diagonalize` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150` |
| `stepP:p9:d-c` | proof cut in, SecularSpectrum: `diagonalize` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151` |
| `stepP:p9:d-d` | proof cut in, SecularSpectrum: `diagonalize; upstream isLatticeTorus_periodOne_iff / phys_pipeline after polarMap` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152` |
| `bpP:p9:dict` | export, SecularSpectrum: `diagonalize (oscillatorAction identity)` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L155-L160` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L155-L160` |
| `bpP:p9:good` | export, SecularSpectrum: `k4 / nr4 / discriminant / good` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good@L164-L171` | `-` |
| `bpP:p9:good-set` | export, SecularSpectrum: `good_set / good_characteristic / good_set_dichotomy; Nondegeneracy.generic for (c)` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L173-L179` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L180-L184` |
| `stepP:p9:gs-a` | proof cut in, SecularSpectrum: `good_set` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181` |
| `stepP:p9:gs-b` | proof cut in, SecularSpectrum: `good_set` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-b@L182-L182` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-b@L182-L182` |
| `stepP:p9:gs-c` | proof cut in, SecularSpectrum: `good_set` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183` |
| `bpP:p9:n2` | export, SecularSpectrum: `n2 / n2_global_frame` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L193-L200` | `blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L201-L204` |
| `stepP:p9:n2-mat` | proof cut in, SecularSpectrum: `n2 / n2_global_frame` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202` |
| `stepP:p9:n2-res` | proof cut in, SecularSpectrum: `n2 / n2_global_frame` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-res@L203-L203` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-res@L203-L203` |
| `stepP:p9:gs-c#roots-route` | alternative, SecularSpectrum: `NOT SELECTED: roots-continuity alternative (unpaid); use gs-c#analytic-route` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183` |
| `stepP:p9:gs-c#analytic-route` | proof cut in, SecularSpectrum: `good_set via Nondegeneracy.generic; selected analytic route` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183` | `blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183` |
| `bpP:p10:conv#data` | export, Nondegeneracy: `SecularForm.action / axis; action_diffeomorphism` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:conv#data@L15-L21` | `-` |
| `bpP:p10:generic` | export, Nondegeneracy: `generic / analytic_zero_null` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:generic@L32-L34` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:generic@L35-L38` |
| `stepP:p10:gen-prod` | proof cut in, Nondegeneracy: `generic` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gen-prod@L36-L36` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gen-prod@L36-L36` |
| `stepP:p10:gen-zero` | proof cut in, Nondegeneracy: `generic` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gen-zero@L37-L37` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gen-zero@L37-L37` |
| `bpP:p10:weyl` | export, Nondegeneracy: `weyl` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:weyl@L40-L42` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:weyl@L43-L46` |
| `stepP:p10:weyl-mm` | proof cut in, Nondegeneracy: `weyl` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:weyl-mm@L44-L44` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:weyl-mm@L44-L44` |
| `stepP:p10:weyl-pert` | proof cut in, Nondegeneracy: `weyl` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:weyl-pert@L45-L45` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:weyl-pert@L45-L45` |
| `bpP:p10:laplace-bounds` | export, Nondegeneracy: `laplace_bounds` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:laplace-bounds@L57-L61` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:laplace-bounds@L62-L66` |
| `stepP:p10:lb-series` | proof cut in, Nondegeneracy: `laplace_bounds` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:lb-series@L63-L63` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:lb-series@L63-L63` |
| `stepP:p10:lb-ratio` | proof cut in, Nondegeneracy: `laplace_bounds` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:lb-ratio@L64-L64` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:lb-ratio@L64-L64` |
| `stepP:p10:lb-tail` | proof cut in, Nondegeneracy: `laplace_bounds` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:lb-tail@L65-L65` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:lb-tail@L65-L65` |
| `bpP:p10:formula69` | export, Nondegeneracy: `formula69` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:formula69@L68-L73` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:formula69@L74-L76` |
| `bpP:p10:peel` | export, Nondegeneracy: `peel / peelError / outerData` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:peel@L78-L85` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:peel@L86-L89` |
| `stepP:p10:peel-ent` | proof cut in, Nondegeneracy: `peel` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:peel-ent@L87-L87` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:peel-ent@L87-L87` |
| `stepP:p10:peel-bd` | proof cut in, Nondegeneracy: `peel` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:peel-bd@L88-L88` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:peel-bd@L88-L88` |
| `bpP:p10:n2` | export, Nondegeneracy: `n2` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:n2@L93-L98` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:n2@L99-L103` |
| `stepP:p10:n2-r` | proof cut in, Nondegeneracy: `n2` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:n2-r@L100-L100` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:n2-r@L100-L100` |
| `stepP:p10:n2-t` | proof cut in, Nondegeneracy: `n2` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:n2-t@L101-L101` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:n2-t@L101-L101` |
| `stepP:p10:n2-nr` | proof cut in, Nondegeneracy: `n2` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:n2-nr@L102-L102` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:n2-nr@L102-L102` |
| `bpP:p10:good-point` | export, Nondegeneracy: `good_point` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:good-point@L105-L109` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:good-point@L110-L120` |
| `stepP:p10:gp-base` | proof cut in, Nondegeneracy: `good_point` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-base@L112-L112` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-base@L112-L112` |
| `stepP:p10:gp-choice` | proof cut in, Nondegeneracy: `good_point` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-choice@L113-L115` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-choice@L113-L115` |
| `stepP:p10:gp-loc` | proof cut in, Nondegeneracy: `good_point` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-loc@L116-L116` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-loc@L116-L116` |
| `stepP:p10:gp-nr` | proof cut in, Nondegeneracy: `good_point` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-nr@L117-L119` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:gp-nr@L117-L119` |
| `bpP:p10:f-id` | infrastructure, Nondegeneracy: `Mathlib AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:f-id@L25-L25` | `-` |
| `bpP:p10:f-fts` | infrastructure, Nondegeneracy: `Mathlib MvPolynomial.esymmAlgEquiv over Polynomial ℝ` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:f-fts@L26-L26` | `-` |
| `bpP:p10:f-pol` | infrastructure, Nondegeneracy: `f_pol` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:f-pol@L28-L28` | `-` |
| `bpP:p10:f-leib` | infrastructure, Nondegeneracy: `f_leib` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:f-leib@L29-L29` | `-` |
| `bpP:p10:sorted-analytic` | export, Nondegeneracy: `sorted_analytic` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:sorted-analytic@L48-L50` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:sorted-analytic@L51-L53` |
| `stepP:p10:sa-loc` | proof cut in, Nondegeneracy: `sorted_analytic` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:sa-loc@L52-L52` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:sa-loc@L52-L52` |
| `bpP:p10:good-set` | export, Nondegeneracy: `good_set` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:good-set@L122-L124` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:good-set@L125-L127` |
| `bpP:p10:rnd-def` | export, Nondegeneracy: `rnd_def` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:rnd-def@L137-L140` | `-` |
| `bpP:p10:Fc-def` | export, Nondegeneracy: `fc_def / relation` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:Fc-def@L142-L146` | `-` |
| `bpP:p10:Fc-analytic` | export, Nondegeneracy: `fc_analytic` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:Fc-analytic@L148-L150` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:Fc-analytic@L151-L153` |
| `stepP:p10:Fc-poly` | proof cut in, Nondegeneracy: `fc_analytic` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:Fc-poly@L152-L152` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:Fc-poly@L152-L152` |
| `bpP:p10:F-nonzero` | export, Nondegeneracy: `f_nonzero` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:F-nonzero@L155-L159` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:F-nonzero@L160-L171` |
| `stepP:p10:F-A` | proof cut in, Nondegeneracy: `f_nonzero` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:F-A@L162-L162` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:F-A@L162-L162` |
| `stepP:p10:F-B` | proof cut in, Nondegeneracy: `f_nonzero` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:F-B@L163-L163` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:F-B@L163-L163` |
| `stepP:p10:F-C` | proof cut in, Nondegeneracy: `f_nonzero` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:F-C@L164-L170` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:F-C@L164-L170` |
| `bpP:p10:rnd` | export, Nondegeneracy: `rnd` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:rnd@L173-L180` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:rnd@L181-L185` |
| `stepP:p10:rnd-a` | proof cut in, Nondegeneracy: `rnd / scaling` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:rnd-a@L182-L182` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:rnd-a@L182-L182` |
| `stepP:p10:rnd-b` | proof cut in, Nondegeneracy: `rnd / scaling` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:rnd-b@L183-L183` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:rnd-b@L183-L183` |
| `stepP:p10:rnd-c` | proof cut in, Nondegeneracy: `rnd / scaling` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:rnd-c@L184-L184` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:rnd-c@L184-L184` |
| `bpP:p10:scaling` | export, Nondegeneracy: `scaling / scaling_amount` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:scaling@L191-L193` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:scaling@L191-L193` |
| `bpP:p10:finite-type` | export, Nondegeneracy: `finite_type` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:finite-type@L199-L203` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:finite-type@L204-L208` |
| `stepP:p10:ft-pt` | proof cut in, Nondegeneracy: `finite_type` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:ft-pt@L205-L205` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:ft-pt@L205-L205` |
| `stepP:p10:ft-cover` | proof cut in, Nondegeneracy: `finite_type` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:ft-cover@L206-L206` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:ft-cover@L206-L206` |
| `stepP:p10:ft-min` | proof cut in, Nondegeneracy: `finite_type` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:ft-min@L207-L207` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:ft-min@L207-L207` |
| `bpP:p10:index-def` | export, Nondegeneracy: `index_def / index_amount / betaFamily / betaMu` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:index-def@L210-L213` | `-` |
| `bpP:p10:cp09-lemma1` | export, Nondegeneracy: `cp09_lemma1 / cp09_unsquared / cp09_product` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:cp09-lemma1@L215-L217` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:cp09-lemma1@L218-L220` |
| `bpP:p10:stability` | export, Nondegeneracy: `stability` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:stability@L222-L227` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:stability@L228-L231` |
| `stepP:p10:st-prod` | proof cut in, Nondegeneracy: `stability` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:st-prod@L229-L229` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:st-prod@L229-L229` |
| `stepP:p10:st-diff` | proof cut in, Nondegeneracy: `stability` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:st-diff@L230-L230` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:st-diff@L230-L230` |
| `bpP:p10:interface` | export, Nondegeneracy: `interface` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:interface@L235-L248` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:interface@L249-L254` |
| `stepP:p10:if-a` | proof cut in, Nondegeneracy: `interface` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-a@L250-L250` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-a@L250-L250` |
| `stepP:p10:if-b` | proof cut in, Nondegeneracy: `interface` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-b@L251-L251` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-b@L251-L251` |
| `stepP:p10:if-c` | proof cut in, Nondegeneracy: `interface` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-c@L252-L252` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-c@L252-L252` |
| `stepP:p10:if-d` | proof cut in, Nondegeneracy: `interface` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-d@L253-L253` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:if-d@L253-L253` |
| `stepP:p10:sa-n2` | proof cut in, Nondegeneracy: `sorted_analytic` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:sa-n2@L52-L52` | `blueprint-P/parts/p10-nondegeneracy.tex#stepP:p10:sa-n2@L52-L52` |
| `bpP:p10:sec-rnd#data` | export, Nondegeneracy: `frequency / frequencyAxes` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:sec-rnd@L135-L135` | `-` |
| `bpP:p10:sec-index#data` | export, Nondegeneracy: `jetNorm / scalarJet / jetMax; f_pol` | `blueprint-P/parts/p10-nondegeneracy.tex#bpP:p10:sec-index@L197-L197` | `-` |

The table is exhaustive: 55 Part 8, 42 Part 9 and 61 Part 10 nodes (counts are checked from the actual records;
if a subsequent publication changes counts, refresh rather than trusting this sentence). Every retained graph dependency
is a proof input, not an extra source hypothesis. The checked public signatures are joint where the source shares a
radius, coefficient family or patch; subclauses not repeated as exports are proved in those proof cuts.

## Conventions and exact consumption

`cell` is the closed radian cell `[0,2*pi]^n`; endpoints have zero measure. The average's factor is the frozen
integer power `(2*pi)^(-(n:Z))`. Integrability is carried before subtracting averages. `identification` is deliberately
conditional at its final subtraction, since Bochner integrals of nonintegrable functions are zero. The analytic
neighbourhood supplies integrability, so no such condition is added to a planetary theorem.

`pairA` and `pairB` use min/max indices to implement the source symmetric extension. Diagonal values of those
auxiliaries are unused; `qhat` erases the diagonal from its sums. Literal formulas are total in Lean, but every
analytic/spectral statement is restricted to positive separated axes. No arbitrary zero extension represents a
source object. `constantTerm` has the Newtonian minus sign. `coeffs` divides by `sqrt(Lambda_i)*sqrt(Lambda_j)`.
The secular quadratic form has no prefactor one-half. The one-half resides in frozen `oscillatorAction`, hence
`Omega_j=2*sigma_j`. For one planet the pair sum vanishes; negative definiteness and nondegeneracy require `n≥2`.

`jetNorm` and `scalarJet` have a separate order-zero branch; positive orders are maxima of diagonal evaluation
on the Euclidean unit sphere. Compactness and continuity justify their `sSup`; `f_pol` proves faithfulness on
symmetric tensors. `betaFamily` is a literal infimum on the compact product; the minimum/positivity proof is paid
by `finite_type`, not a theorem-shaped structure. `index_def` uses the **least positive** order; order zero is still
included inside each maximum. `stability` keeps its positive-old-amount guard and the exact factor
`2^mu * theta * (2*M+theta)`; `theta` is not assumed to control full mixed tensor norms.

## Reuse map and upstream interface (to reconcile)

| Supplier | Exact declaration(s) | Inputs supplied here / conclusion consumed |
|---|---|---|
| `KAM/Planetary/Newtonian/Models.lean` | `fMov`, `fFix`, `pairPotential`, `movingHamiltonian_split`, `fixedHamiltonian_split`, `moving_sub_fixed`, `analyticOnNhd_fMov`, `analyticOnNhd_fFix` | positive physical data, collision-free chart points; literal perturbations and analytic real Newtonian formulas |
| `KAM/Planetary/Poincare/Chart.lean` | `poincare`, `poincareDom`, `poincare_facts`, `analyticOnNhd_poincare`, `poincare_periodic` | `D.hm`, `mul_pos D.hG D.hm0`, positive actions; regularity and exact periodicity |
| `KAM/Planetary/Poincare/Symplectic.lean` | `poincare_symplectic`, `poincare_elements`, `poincare_circular`, `poincare_means` | no pair collision needed for the means; source virial and zero-eccentricity values |
| `KAM/Planetary/Poincare/Holomorphic.lean` | `poincareC`, `poincareNbhd`, `poincare_holomorphic` | `Lambda*=action D a`, all real angles; complex extension, real restriction, periodicity |
| `KAM/Planetary/Poincare/Product.lean` | `planetBlock`, `poincareProd`, `poincareProdDom`, `poincareProd_block`, `analyticOnNhd_poincareProd`, `keplerPart_poincareProd`, `poincareProd_symplectic`, `poincareProd_lattice`, `poincareProd_eq_iff`, `poincareProdCast`, `analyticOnNhd_fMov_poincareProd`, `analyticOnNhd_fFix_poincareProd` | product-block identities, analytic composition on preimage of collision-free domain; no parallel product chart |
| `KAM/Kepler/Basic.lean`, `Plane.lean` | `IsSymplecticOn`, `IsSymplecticOn.comp`, `phaseCast`, `phaseCast_symplectic`, `rot`, `planeDot_rot`, `planeLength_rot`, `norm_le_planeLength` | exact frozen form and Fin reindexing; block rotations and physical/max-norm bridge |
| `KAM/Kepler/Equation.lean`, `Mass.lean` | `keplerLong_unique`, `fderiv_keplerLong_vec`, `delaunayMK_position`, `delaunayMK_means` | chart symmetries, first orbit variations, radial change of variables |
| P7 draft definitions; proof now owned by S7-R/S9-T below | **existing exact draft definitions** `polarMap`, `polarDom`; owned theorem `SecularSpectrum.lattice` | positive oscillator actions below fast actions; convert all angle shifts to fast Cartesian shifts before applying physical transport |
| P1 design, `KAM/Planetary/Hamiltonian/Transport.lean` | **existing exact draft** `IsChart`, `IsLatticeTorus`, `IsTwoPiLatticeTorus`, `periodOne`, `isLatticeTorus_periodOne_iff`, `phys_pipeline` | see verbatim signature block; `H∘Phi`, radian torus, analytic chart, Q1/Q2, `gamma>0`, `tau>d-1`, radian Diophantine frequency |
| Published graph external G1 | `IsCompact.uniformContinuousOn_of_continuous` via owned adapter `SecularForm.compact_uniform` | compact angle cell × closed polydisc, continuous separation; one radius for all angles and pairs |
| Published graph external G2 | `intervalIntegral.integral_eq_sub_of_hasDerivAt` via `SecularForm.periodic_derivative_integral` | analytic periodic q gives C1 and q(2*pi)=q(0); exact zero mean momentum |

Part 1's exact `phys_pipeline` returns `IsPhysicalTorus H ((2*pi)^(-1) • omega) (Phi ∘ periodOne kappa)`
and its range identity. This keeps physical time and the original physical Hamiltonian. On a period-one **chart**
route, Part 1 instead uses `chartPullback (2*pi) H (Phi ∘ angleScale (2*pi))`; its Hamiltonian divisor is essential.
These are two correct interfaces, not permission to scale both the torus frequency and time twice.

For the heterogeneous product chart, use `phaseCast (Nat.mul_two n)` on the source (as `poincareProdCast` does).
To include the lift and polar map, conjugate them by that same equivalence before composing with `poincareProdCast`.
The resulting map has source and target `Phase (n*2)` and can enter Part 1 unchanged.
`Phi = Psi ∘ liftInv R ∘ polarMap` (with these casts) has Q1 by the angle-independent lift correction and polar
periodicity; Q2 follows in order from `poincareProd_eq_iff`, injectivity/equivariance of the lift, then the positive-radius
polar injectivity modulo `2*pi`. Only then call `isLatticeTorus_periodOne_iff` and `phys_pipeline`.
The Boolean must be held fixed when choosing the pair `(secular, perturbation)` in `diagonalize`.

### Synced P7 export boundary (orchestrator aa7bc30)

The graph's `bpP:p7:product-chart` and its steps remain NOT_STARTED as complete source nodes despite
available ingredients. **S7-R owns the consumed missing declarations** instead of assuming whole-node status:

| Source node | Owned exact declaration | Source locator / consumption |
|---|---|---|
| `bpP:p7:product-chart` (b) | `SecularForm.product_chart` | p7 L197/L206; analytic `keplerActionHam` built from literal `hProd`, first derivative nu, nonzero second derivative, and explicit decoupled Hamiltonian field; used by l64-a and the action-frequency dictionary |
| `stepP:p7:pc-prod` | `SecularForm.pc_prod` | p7 L195/L205; joint analytic/symplectic chart, image, injectivity modulo fast lattice and analytic local inverse; complete quotient ingredients using existing names |
| `stepP:p7:pc-dec` | `SecularForm.pc_dec` | p7 L197/L206; decoupled Kepler field transport on O_n, **without a pair collision guard**; this is the actual input of l64-a |
| `stepP:p7:pc-share` | `SecularForm.pc_share` | p7 L198–201/L207; source Hamiltonian split and field transport at NoCollision chart points, with one matched-model selector |
| `bpP:p7:lattice` | `SecularSpectrum.lattice` | p7 L223–233; exact polarMap/polarDom draft bodies, radian quotient facts and period-one conformal factor; S9-T builds the lifted physical chart from these |
| `bpP:p7:d25` (e) | no consumption | no D25(e) supplier is assumed; one-body eccentric-anomaly identities use the already named `delaunayMK_position`, `delaunayMK_means` and `poincare_means` instead |

These declarations are in Appendix A. The proof boundary is explicit: `poincareProd_eq_iff` and `poincareProd_localDiffeo`
are individual ingredients, not evidence that `product-chart` as a whole is proved. New downstream code consumes
`product_chart` and `pc_dec` by their own names; `hasDerivAt_nu` alone does not replace either of them.

### Mathlib search and applicability boundaries

Inspected the pinned repository sources, rather than current web documentation:
`Mathlib/Analysis/Matrix/Spectrum.lean` (`eigenvalues₀_antitone`, `spectral_theorem`, `charpoly_eq`,
`sort_roots_charpoly_eq_eigenvalues₀`), `Mathlib/Analysis/Analytic/Uniqueness.lean`
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`),
`Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean` (`MvPolynomial.esymmAlgEquiv`, including
coefficient ring `Polynomial ℝ`), analytic IFT and integral differentiation APIs used in the Kepler design.
The elementary-symmetric algebra equivalence supplies polynomial factorization, not analyticity of labelled roots.
The identity theorem supplies propagation of zero, not the multivariable measure-zero theorem.

The latter is an **owned theorem** `Nondegeneracy.analytic_zero_null` (induction on dimension, one-dimensional
isolated zeros plus Fubini on countably many rational boxes). Likewise `f_pol`, `e_weyl`, `weyl` and the analytic
parameter-integral adapter are proof work, not claimed existing Mathlib closures. `weyl` needs Courant–Fischer or
an equivalent direct spectral subspace argument in explicit Euclidean norms. Do not obtain it by interpreting the
ambient Pi norm as Euclidean. The scalar IFT and spectral theorem are applicable to the finite-dimensional matrix
and polynomial carriers after componentwise analytic closure; sign-normalized adjugate columns give the local SO frame.

## Departures

| Place | Deliberate Lean form | Reason / preserved claim |
|---|---|---|
| p8 rho_* | existential radius, no globally chosen definition | avoids an unjustified arbitrary choice; witnesses shared by both models |
| p8 quadratic remainder | explicit C,r inequality in max norm plus analytic remainder | finite-dimensional equivalence to Euclidean O(u^4); uniformity on a smaller action neighbourhood retained |
| p8 same-jets | `same_jets_on` states full slow tensors and all action derivatives | includes mixed multi-index consequences without inventing a parallel partial-derivative representation |
| p8 quartic | analytic coefficient functions returned jointly; mixed values not specified | source Part 11b obligation retained; exact diagonal derivatives use `radialH` |
| p9 sorted spectrum | reverse Mathlib's antitone `eigenvalues₀` | source increasing order with multiplicity; no choice of eigenvalue branches off the simple locus |
| p9 generic (c) | selected analytic zero-set route | roots-continuity alternative has an unpaid supplier; do not mark its proof complete |
| p9 transport | add polar composition and named Part 1 period conversion | pays the published SOURCE_GAP at L143/L152 without a new frozen premise |
| p10 index | proof-indexed `Nat.find`, least positive order | index has no meaning without positive amount; no fallback zero |
| p10 stability | arbitrary certified upper bounds M,theta instead of forcing compact maxima | strictly stronger: the source maxima instantiate them; exact constants and positivity guards unchanged |
| p10 interface | includes finitely many additional analytic nonzero conditions in the same existential patch | source final sentence, including zero additional functions; constants do not depend on coupling |

For `l75` the algebraic identity is stated without the source off-diagonal sign guard: it holds for every symmetric matrix, so this identity is strictly stronger. The sign guard is still required and supplied for its inequality application in `definite`. The real symmetry statements also extend from the small analytic polydisc to `slowDom`: exact chart invariance and measure-preserving torus substitutions give the same identities, including simultaneous zero total integrals in the nonintegrable case. `same_jets_transfer` consequently needs only its stated whole-disc chart-domain guard, since `identification` supplies the equivalence whenever either average is integrable. These are strictly stronger domain forms, not analytic regularity claims outside the collision-free neighbourhood. No other source premise is dropped. Generic conditional `birkhoff_transfer` has its own name;
its average/integrability premises are discharged by `identification` in `same_jets_transfer` and never passed to a root.
Decompositions supplied as premises of `diagonalize` and `local_analytic` are exactly the source's spectral-data premises;
the planetary application obtains them from `local_analytic`, never from an owner assumption.

## Blueprint issues, source limitations and suspected errata

These are reported, not repaired in the blueprint or ledger. Paper claims below are inherited from the explicitly
quoted blueprint notes; no new independent pinned-PDF audit was performed in this design assignment.

- **Published gap p9 L143/L152**, “satisfies the lattice compatibility (Q1)–(Q2)” and “the torus-transport theorem applies”.
  The calculation is for radian fast shifts while Part 1's torus has period one. The named conversion above is required,
  after the oscillator polar chart; merely asserting lift symplecticity does not pay it. Package S9-T owns the new glue.
- **Inherited p7 L207**, “the proof” of p6:domain provides analyticity. A smooth square-root proof does not establish
  real analyticity. Consume the delivered **analytic** statements `analyticOnNhd_fMov`, `analyticOnNhd_fFix`,
  `analyticOnNhd_*_poincareProd`, whose implementation uses `analyticAt_inv_planeLength` off zero and analytic
  composition. If those imports cease to have this exact property, stop that package; no smooth substitute.
- **Root continuity alternative**, p9 L183 / `stepP:p9:gs-c#roots-route`: “continuity of the roots of a polynomial”.
  No supplier in that route. Use `gs-c#analytic-route` through the symmetric polynomial and analytic zero theorem.
  It is a route choice, not a proof of the unused alternative.
- **p8 L157**, Fej04r p.50 “Le calcul complet est un peu long”: [LR95] is not pinned. Packages S8-D/S8-X/S8-Q
  recompute the diagonal and cross Hessian from the regular orbit map and Laplace series, then assemble. Do not cite
  the quadratic matrix as an assumption or use a numerical ratio as proof.
- **p8 L228**, CP11 quartic coefficients printed without derivation: `quartic` gives the six-invariant structure and
  exact diagonal coefficients; `quartic_scaling` uses the separated domain. Part 11b must compute mixed c3..c6,
  retaining third-order one-body variations in bidegrees (3,1)/(1,3). No torsion determinant is certified here.
- **p9 L146**, plain slow rotation omits its action dependence. `liftMap` includes
  `lambda_l - eta^T (partial_l R) R^T xi`; its inverse has the opposite shift. Package S9-L proves the full
  frozen symplectic-form identity using commuting second derivatives and Maurer–Cartan, not only block orthogonality.
- **p10 L108/L158**, Fej04r p.58 “par un raisonnement analogue”: both inductions must be written. S10-H/S10-F
  explicitly handle the lone surviving secular coefficient (C2), nonzero limiting products (C1), and all mass data
  simultaneously. The n=2 base uses the trace/determinant ratio; no universal cover is invoked.
- **E-P-Fej04r-3**, p8 L174–179, pinned revised (31) already has “sqrt(2 Lambda)” while (35)–(37) retain the old
  matrix coefficients. This yields `Q_F=2 Q_h`; preserve the half and `Omega=2 sigma` throughout.
- **E-P8-Fej50**, p8 L248, Lemma 64 p.50 coefficient “mu_j^3 M_j^2/Lambda_j^3” should have mass power four.
  Exact `p_i=m_i nu_i partial_lambda_i q_i` is used; zero-average proof is unaffected.
- **E-P-CP11-1**, p8 L178/L248, (B.2) C2 lacks “1/2”; reading (B.1) literally doubles its cross term.
  Recompute it via `identities` and the first variations; do not import the printed matrix.
- **E-P-CP11-2**, p8 L238–239, (B.6) printed “37 alpha^4 beta_4^(9)” needs alpha power three. The blueprint's
  integration-by-parts certificate is a polynomial/rational identity still to prove; the design uses `radialR1` as
  exact derivative formula, never printed r1 at finite axis ratio. The mixed r2,r3,r4 remain unchecked.
- **E-P-Fej04r-7**, p10 L269, outer block error “O(a_n^(5/2))” misses its nonzero order-two diagonal correction.
  Keep three separate powers: inner entry 3/2, outer diagonal 2, coupling 11/4. The printed weaker coupling 5/2
  is valid; it is the outer-block claim that is defective.
- **E-P-Fej04r-8 / E-P-Fej04r-2**, p10 L269: omitted induction cases and the claimed simple connectedness of the
  complexified axes domain. The real symmetric-product argument avoids that complex topology.

The blueprint's local SO(n) statement includes n=0 vacuously; if the proof chooses a first column, split n=0 first.
The radius/domain statement for dimensionless quartics must retain `alpha(1+|v_i|)<1-|v_j|`; a full product
`(0,1) × {|v|<1/4}²` includes intersecting ellipses and is not a legitimate analytic domain.

## Modules, import DAG, packages and waves

All new production files are under `KAM/Planetary/`. The table names exact paths relative to that directory,
inputs as package IDs (and specific upstream modules above), and expected proof lines. Each package owns one
module of 150–800 lines. A forecast above 1200 lines triggers splitting before the absolute 1500-line cap.
The import DAG is exactly this table: every non-upstream input comes from an earlier wave; no provider or frozen
theorem is imported. Files defining analytic objects use public imports; proof-only calculus imports stay private.

| Package | Exact module `.lean` | Exports / proof cuts | Inputs | Lines | Wave |
|---|---|---|---|---:|---:|
| S8-B | `SecularForm/Basic` | Data, domains, literal average, rho, inclusion, actions, pairSlowSecular | frozen definitions, Poincare/Product | 250 | 1 |
| S7-R | `SecularForm/ProductInterface` | product_chart, pc_prod, pc_dec, pc_share; polarMap/polarDom exact draft definitions and lattice | S8-B; delivered Poincare ingredients; P1 fullShift definition | 750 | 2 |
| S8-P | `SecularForm/ParameterIntegral` | e_param, e_diff, compact_uniform, periodic_derivative_integral | S8-B; Mathlib dominated calculus, FTC | 650 | 2 |
| S8-L | `SecularForm/Laplace` | laplace_def, poch, e_poch, laplace, laplace_fourier | S8-B; binomial series | 700 | 2 |
| S8-Y | `SecularForm/Symmetry` | symmetries, evenness, evenness_taylor | S8-P; Poincare/Chart, Equation | 500 | 3 |
| S8-A | `SecularForm/Analytic` | perturbation_analytic, pa-circ/unif/hol/avg | S8-P; Poincare/Holomorphic; Models analytic formulas | 600 | 3 |
| S8-M | `SecularForm/Momentum` | lemma64, lemma64_coordinates, identification | S8-P, S7-R; Product, Symplectic, Mass means | 550 | 3 |
| S8-I | `SecularForm/LaplaceIdentities` | identities, radialPhi/radialH | S8-L | 400 | 3 |
| S8-C | `SecularForm/Coefficients` | pairA/B, constantTerm, coeffs, symmetry, analytic coefficients | S8-L, S8-B | 350 | 3 |
| S8-W | `SecularForm/InvariantPolynomial` | e_weyl, quadratic and six quartic invariant reduction | S8-B; MvPolynomial | 750 | 2 |
| S8-D | `SecularForm/DiagonalJet` | qf-scale/c0/diag, exact diagonal derivatives | S8-A, S8-Y, S8-I, S8-C; Mass means | 650 | 4 |
| S8-X | `SecularForm/CrossJet` | qf-cross, first orbit variations and Fourier selection | S8-A, S8-I, S8-C; Equation | 750 | 4 |
| S8-Q | `SecularForm/Quadratic` | quadratic_form, qf-pair/assembly/diag2 | S8-D, S8-X, S8-W, S8-Y | 300 | 5 |
| S8-J | `SecularForm/ModelTransfer` | same_jets_on, same_jets, birkhoff_transfer, same_jets_transfer | S8-A, S8-M; frozen HasSecularBirkhoffForm | 350 | 4 |
| S8-4 | `SecularForm/Quartic` | quartic, quartic_scaling, quartic_pair_scaling, six coefficients, radialR1 | S8-D, S8-W, S8-J; Poincare/Chart | 700 | 5 |
| S9-N | `SecularSpectrum/Norms` | length2, op2, opMax, frobenius, norm_compare, norm_compare_operator | S8-B | 300 | 2 |
| S9-D | `SecularSpectrum/Definiteness` | l74, l75, l75_bound, definite, coercivity | S9-N, S8-C, S8-L | 600 | 4 |
| S9-S | `SecularSpectrum/LocalAnalytic` | sorted, sigma, local_analytic, local_analytic_unique, adjugate projection and SO frame | S8-C, S9-N; matrix spectral theorem, analytic IFT | 750 | 4 |
| S9-L | `SecularSpectrum/Lift` | liftMap, liftInv, lift; bijectivity, Maurer–Cartan | S9-N; Kepler/Basic | 650 | 3 |
| S9-G | `SecularSpectrum/GoodPolynomial` | k4_finite, nr4, good, good_characteristic, good_set(a,b), good_set_dichotomy | S9-S; esymmAlgEquiv | 550 | 5 |
| S9-2 | `SecularSpectrum/TwoPlanets` | n2, n2_global_frame | S9-D, S9-S, S9-G | 450 | 6 |
| S9-Q | `SecularSpectrum/Diagonalize` | diagonalize, matched averages and domain estimates | S8-Q, S8-M, S9-D, S9-S, S9-L | 400 | 6 |
| S9-T | `SecularSpectrum/Transport` | diagonalize_transport, diagonalize_period_one; polar/lift/cast Q1/Q2 | S9-Q, S7-R; P1/Hamiltonian/Transport exact draft | 450 | 7 |
| S10-Z | `Nondegeneracy/AnalyticZeros` | rnd_def, analytic_zero_null, generic, identity/products | S8-B; analytic uniqueness, Fubini | 750 | 2 |
| S10-W | `Nondegeneracy/Weyl` | weyl, min-max subspace helper | S9-N; matrix spectral theorem | 700 | 3 |
| S10-P | `Nondegeneracy/Peel` | laplace_bounds, formula69, peel | S8-C, S9-N, S8-L | 650 | 4 |
| S10-H | `Nondegeneracy/GoodAxes` | n2, good_point, good_set, sorted_analytic | S9-2, S9-G, S10-W, S10-P, S10-Z | 700 | 7 |
| S10-F | `Nondegeneracy/SymmetricRelation` | fc_def, fc_analytic, f_nonzero | S10-H, S10-P, S10-Z; esymmAlgEquiv over R[X] | 750 | 8 |
| S10-R | `Nondegeneracy/Frequency` | action_diffeomorphism, frequency, rnd, scaling | S10-F, S9-S, S10-Z; elementary component calculus | 450 | 9 |
| S10-J | `Nondegeneracy/DiagonalTensor` | jetNorm, scalarJet, jetMax, f_pol, f_leib | S9-N; iteratedFDeriv | 750 | 3 |
| S10-C | `Nondegeneracy/FiniteType` | sphere, squaredForm, betaFamily, betaMu, index_def, finite_type, index_amount, cp09_lemma1, cp09_unsquared, cp09_product | S10-J, S10-Z | 650 | 4 |
| S10-S | `Nondegeneracy/Stability` | stability, scaling_amount | S10-C, S10-J | 500 | 5 |
| S10-I | `Nondegeneracy/Interface` | interface, all simultaneous patch witnesses | S10-R, S10-H, S10-C, S10-S | 450 | 10 |

Proof-cut splitting above does not create extra assumptions: DiagonalJet/CrossJet return identities for the literal
pair average, Quadratic sums them. If the 750-line jobs exceed estimates, split by the named graph proof cuts;
retain the public module as a cheap facade. No patch or coefficient structure may be accepted as an assumed
supplier of its own intended theorem. Every future prover brief repeats the complete hard rules below.

## Provider assembly and consumers

**No frozen theorem is closed by Parts 8–10.** No provider is edited or created. Part 11a consumes `frequency`,
`rnd`, `cp09_lemma1`, `stability` and `interface` in CP09's squared-scalar convention with a fixed positive
finite order. Part 11b consumes `quartic`, `radialR1`, `coeffs` and local rotations; torsion remains unpaid.
Parts 12/13 obtain a good patch inside every prescribed neighbourhood, then may combine its nonzero conditions
with their proved torsion determinant. The finite-family guards in `interface` are facts supplied by those proofs,
not new frozen assumptions. `same_jets_transfer` shares exactly the frozen Omega and beta functions; only P0
changes. General n goes through weak nondegeneracy, while the n=2 trace/determinant exclusion is a distinct helper.

## Risks and stop conditions

- Polynomial invariant theory, multivariable zero-set measure, min-max and diagonal polarization are substantive
  proof packages. Their signatures elaborating does not prove them. Do not replace them by conclusion-shaped assumptions.
- Source expression equality and Mathlib analytic topology need local scalar/matrix adapters; the only matrix norm
  scope is the existing Elementwise scope. Default-heartbeat failure triggers module/proof-cut splitting.
- Unit spheres are nonempty only for positive output dimension. The finite-type theorem has explicit compact
  nonempty C and K; CP09 adds `0<m`. The index's positivity is a guarded definition, not inferred from a zero bound.
- `F_c` induction is for every mass vector at every dimension. Dropping one coefficient does not necessarily leave
  a nonzero relation: C2 must use negative definiteness, not invoke induction on a zero vector.
- Slow rotations preserve Euclidean lengths, not max norm polydiscs. Shrink the slow input radius using sqrt(n);
  never assume the whole polydisc is rotation invariant.
- P1 not-yet-delivered transport modules are exact design interfaces; missing P7 obligations have owned packages below. Reconcile import paths at landing without
  changing their declarations. This signature check includes their exact definitions/transport type, not a fake proof
  of their implementation or an import of another untracked draft.

## Required hard rules for subsequent Lean briefs (verbatim)

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


## Validation receipts

Signature check: prescribed `inp_sig_check.sh /root/code/KAM-inp-design-p810 .drafts/scratch/P810Signatures.lean`
exited **0**, with only `declaration uses 'sorry'` warnings. Signature: **885 lines**, **78 theorem stubs**;
SHA-256 `aa8e13ad5e4e62b40d0f12effde76ce4e643abbcb545cb7a933f666bf6241931`. Published graph snapshot read after status sync:
`7d58c7597a6e498eddaa56d6b062d015a466131dcd2e9abde2bc852f07b6e8ca`. Static coverage: **158/158** distinct records; packages: **33**, in **10 waves**,
each forecast 150–800 lines, every package dependency strictly earlier than its consumer. No direct lake/Lean execution is authorized for this
worktree. Production module builds are not applicable: this assignment writes no production Lean files.
The scratch signature is elaborated only through the prescribed `inp_sig_check.sh` wrapper. All theorem bodies
are `sorry`, so axiom output includes `sorryAx` and is never proof closure.

The gated `.drafts/scratch/P810Axioms.lean` probe exited **0**. It printed axioms of
`quadratic_form`, `same_jets_transfer`, `diagonalize_period_one`, `rnd`, `stability`, and `interface`:
`[propext, sorryAx, Classical.choice, Quot.sound]` for each. These six declarations are unchanged in the final
signature (the subsequent additions are four independent helper signatures). The sampled delivered
`poincareProd_symplectic` and `poincare_holomorphic` printed `[propext, Classical.choice, Quot.sound]` only.
The same probe checked the spectral theorem, antitone eigenvalue order, symmetric-polynomial equivalence,
analytic identity theorem, analytic IFT, `IsCompact.uniformContinuousOn_of_continuous`, and interval FTC names.
This verifies declaration types and dependency receipts, not new theorem proofs.

Source lint: `PATH="/root/code/KAM-inp-design-p810/.drafts/scratch/lint-bin:$PATH" scripts/lint_sources.sh`
exited **0**. The local wrappers preserve the script and route its ABI `lake env lean` invocation through the
prescribed signature gate; checker git calls use `git -C /root/code/KAM-inp-design-p810`.
Exact output:

```text
check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

`git -C /root/code/KAM-inp-design-p810 diff --cached --check` and the explicit new-file whitespace check passed.
No production Lean module build was run: this is a design-only assignment with targeted gated signature elaboration.

## Appendix A. Exact signatures

The following block is byte-identical to the checked untracked `P810Signatures.lean`. Imported production
objects retain their existing exact declarations. The trailing Part 1 definitions are verbatim interface extracts
from the delivered design; future production modules import their owner instead of copying them.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.Poincare.Holomorphic
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm
public import KAM.Frozen.Planetary.Defs.IsPhysicalTorus

/-! # P810 design signatures
Draft only. All theorem bodies are sorry. No frozen theorem or provider is imported.
Part 1 interface definitions below are verbatim extracts, not replacement APIs.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev CVec (n : ℕ) := Fin n → ℂ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Slow (n : ℕ) := Vec n × Vec n × Vec n
abbrev CSlow (n : ℕ) := CVec n × CVec n × CVec n
/-- Source standing physical data; no spectral or analytic conclusions. -/
structure Data (n : ℕ) where
  G : ℝ
  m0 : ℝ
  m : Vec n
  hG : 0 < G
  hm0 : 0 < m0
  hm : ∀ i, 0 < m i
  hn : 0 < n
variable {n : ℕ}
def axes (n : ℕ) : Set (Vec n) := {a | (∀ i, 0 < a i) ∧ StrictMono a}
def action (D : Data n) (a : Vec n) : Vec n := fun i => D.m i * √(D.G * D.m0 * a i)
def axis (D : Data n) (I : Vec n) : Vec n := fun i => I i ^ 2 / (D.m i ^ 2 * (D.G * D.m0))
def actionDomain (D : Data n) : Set (Vec n) := action D '' axes n
def nu (D : Data n) (I : Vec n) : Vec n := fun i => (D.G * D.m0) ^ 2 * D.m i ^ 3 / I i ^ 3
def perturbation (D : Data n) (moving : Bool) (w : Phase (n+n)) : ℝ :=
  if moving then fMov D.G D.m0 D.m (poincareProd D.m (D.G * D.m0) w)
  else fFix D.G D.m (poincareProd D.m (D.G * D.m0) w)
/-- Literally the frozen average: slow order is (xi,Lambda,eta). -/
def secular (D : Data n) (moving : Bool) (x : Slow n) : ℝ :=
  secularAverage (fun _ => perturbation D moving) 0 x.2.1 x.2.2 x.1
def slowSecular (D : Data n) (moving : Bool) (I : Vec n) (u : Vec n × Vec n) : ℝ :=
  secular D moving (u.1,I,u.2)
def slowDom (_D : Data n) : Set (Slow n) :=
  {x | assemble x.2.1 0 x.2.2 x.1 ∈ poincareProdDom n}
def cell (n : ℕ) : Set (Vec n) := Set.pi univ (fun _ => Icc 0 (2 * π))
def avg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec n → E) : E := (2 * π) ^ (-(n : ℤ)) • ∫ t in cell n, f t
def rho (D : Data n) (a : Vec n) : ℝ :=
  ⨅ i, min (action D a i / 2) (√(action D a i) / 16)
def polydisc (D : Data n) (a : Vec n) (r : ℝ) : Set (CSlow n) :=
  {x | ∀ i, ‖x.1 i‖ < r ∧ ‖x.2.1 i - (action D a i : ℂ)‖ < r ∧ ‖x.2.2 i‖ < r}
def inclusion (x : Slow n) : CSlow n :=
  (fun i => (x.1 i : ℂ), fun i => (x.2.1 i : ℂ), fun i => (x.2.2 i : ℂ))
def realDisc (D : Data n) (a : Vec n) (r : ℝ) : Set (Slow n) := inclusion ⁻¹' polydisc D a r
def planetC (D : Data n) (t : Vec n) (x : CSlow n) (i : Fin n) :=
  poincareC (D.m i) (D.G * D.m0) (![t i, x.1 i], ![x.2.1 i,x.2.2 i])
def separationC (D : Data n) (t : Vec n) (x : CSlow n) (i j : Fin n) : ℂ :=
  ∑ c : Fin 2, ((planetC D t x i).1 c - (planetC D t x j).1 c)^2
def perturbationC (D : Data n) (moving : Bool) (t : Vec n) (x : CSlow n) : ℂ :=
  -(D.G : ℂ) * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    (D.m i : ℂ) * D.m j * separationC D t x i j ^ (-1/2 : ℂ) +
  if moving then (∑ c : Fin 2, (∑ i, (planetC D t x i).2 c)^2) / (2 * D.m0) else 0
def secularC (D : Data n) (moving : Bool) (x : CSlow n) : ℂ :=
  (2 * π) ^ (-(n : ℤ)) • ∫ t in cell n, perturbationC D moving t x

theorem perturbation_analytic (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a ∧
    (∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j-a i)^2 / 2) ≤ (separationC D t x i j).re) ∧
    (∀ b : Bool, (∀ t, DifferentiableOn ℂ (perturbationC D b t) (polydisc D a r)) ∧
      ContinuousOn (fun z : Vec n × CSlow n => perturbationC D b z.1 z.2)
        (univ ×ˢ polydisc D a r) ∧
      DifferentiableOn ℂ (secularC D b) (polydisc D a r) ∧
      (∀ x ∈ realDisc D a r, secularC D b (inclusion x) = (secular D b x : ℂ)) ∧
      AnalyticOnNhd ℝ (secular D b) (realDisc D a r) ∧
      (∀ x ∈ realDisc D a r, ∀ t,
        perturbationC D b t (inclusion x) =
          (perturbation D b (assemble x.2.1 t x.2.2 x.1) : ℂ)) ∧
      (∀ x ∈ realDisc D a r,
        IntegrableOn (fun t => perturbation D b (assemble x.2.1 t x.2.2 x.1)) (cell n))) := sorry

/-- Rotation of the slow blocks, using the delivered planar rotation. -/
def rotateSlow (t : ℝ) (x : Slow n) : Slow n :=
  (fun i => (rot t ![x.1 i,x.2.2 i]) 0, x.2.1,
    fun i => (rot t ![x.1 i,x.2.2 i]) 1)
def rotatePhysical (t : ℝ) (z : Phase (n*2)) : Phase (n*2) :=
  (ofBodies (fun i => rot t (bodyVector z.1 i)), ofBodies (fun i => rot t (bodyVector z.2 i)))
theorem symmetries (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) (t : Vec n) (θ : ℝ) :
    poincareProd D.m (D.G*D.m0) (assemble x.2.1 (t + fun _ => π) (-x.2.2) (-x.1)) =
      -poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1) ∧
    poincareProd D.m (D.G*D.m0)
      (assemble x.2.1 (t + fun _ => θ) (rotateSlow θ x).2.2 (rotateSlow θ x).1) =
      rotatePhysical θ (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)) ∧
    poincareProd D.m (D.G*D.m0) (assemble x.2.1 (-t) (-x.2.2) x.1) =
      (ofBodies (fun i => ![(bodyVector (poincareProd D.m (D.G*D.m0)
        (assemble x.2.1 t x.2.2 x.1)).1 i) 0,
        -(bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i) 1]),
       ofBodies (fun i => ![-(bodyVector (poincareProd D.m (D.G*D.m0)
        (assemble x.2.1 t x.2.2 x.1)).2 i) 0,
        (bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).2 i) 1])) := sorry

theorem evenness (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) (b : Bool) (θ : ℝ) :
    secular D b (-x.1,x.2.1,-x.2.2) = secular D b x ∧
    secular D b (x.1,x.2.1,-x.2.2) = secular D b x ∧
    secular D b (-x.1,x.2.1,x.2.2) = secular D b x ∧
    secular D b (rotateSlow θ x) = secular D b x := sorry

def momentum (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) : Fin 2 → ℝ :=
  bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).2 i
def position (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) : Fin 2 → ℝ :=
  bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i
/-- Joint Lemma 64; no pair-collision guard is required. -/
theorem lemma64 (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    (∀ t i, (D.m i * nu D x.2.1 i) •
      deriv (fun s => position D x (Function.update t i s) i) (t i) = momentum D x t i) ∧
    (∀ i, avg (fun t => momentum D x t i) = 0) ∧
    (∀ i j, i ≠ j → avg (fun t => planeDot (momentum D x t i) (momentum D x t j)) = 0) ∧
    (∀ i, avg (fun t => planeSq (momentum D x t i)) =
      D.m i ^ 4 * (D.G*D.m0)^2 / x.2.1 i ^ 2) ∧
    avg (fun t => planeSq (∑ i, momentum D x t i)) =
      ∑ i, D.m i ^ 4 * (D.G*D.m0)^2 / x.2.1 i ^ 2 := sorry

def laplace_def (s : ℝ) (k : ℤ) (α : ℝ) : ℝ :=
  (2*π)⁻¹ * ∫ t in (0 : ℝ)..2*π,
    Real.cos ((k : ℝ)*t) * (1+α^2-2*α*Real.cos t) ^ (-s)
def poch (s : ℝ) (q : ℕ) : ℝ := ∏ j ∈ Finset.range q, (s+j)
def laplaceTerm (s : ℝ) (k q : ℕ) (α : ℝ) : ℝ :=
  poch s (q+k) * poch s q / ((q+k).factorial * q.factorial) * α^(2*q+k)
def laplaceC (s : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∑' q : ℕ, (poch s (q+k) * poch s q / ((q+k).factorial * q.factorial) : ℝ) * z^(2*q+k)
theorem laplace {s : ℝ} (hs : 0 < s) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    HasSum (fun q => laplaceTerm s k q α) (laplace_def s k α) ∧
    laplace_def s (-(k : ℤ)) α = laplace_def s k α ∧
    0 ≤ laplace_def s k α ∧
    (0 < α → 0 < laplace_def s k α) ∧
    laplace_def s k 0 = (if k = 0 then 1 else 0) ∧
    DifferentiableOn ℂ (laplaceC s k) (Metric.ball 0 1) ∧
    laplaceC s k (α : ℂ) = (laplace_def s k α : ℂ) ∧
    AnalyticOnNhd ℝ (laplace_def s k) (Ioo 0 1) := sorry

theorem identities {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    α^2 * iteratedDeriv 2 (laplace_def (1/2) 0) α + 2*α*deriv (laplace_def (1/2) 0) α =
      α * laplace_def (3/2) 1 α ∧
    α * deriv (laplace_def (1/2) 1) α + α^2/2 * iteratedDeriv 2 (laplace_def (1/2) 1) α -
      laplace_def (1/2) 1 α = α/2 * laplace_def (3/2) 2 α := sorry

def pairA (D : Data n) (a : Vec n) (i j : Fin n) : ℝ :=
  D.G * D.m (min i j) * D.m (max i j) * a (min i j) / (4 * a (max i j)^2) *
    laplace_def (3/2) 1 (a (min i j) / a (max i j))
def pairB (D : Data n) (a : Vec n) (i j : Fin n) : ℝ :=
  D.G * D.m (min i j) * D.m (max i j) * a (min i j) / (4 * a (max i j)^2) *
    laplace_def (3/2) 2 (a (min i j) / a (max i j))
def constantTerm (D : Data n) (a : Vec n) : ℝ :=
  -∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    D.G * D.m i * D.m j / a j * laplace_def (1/2) 0 (a i / a j)
def qhat (D : Data n) (a : Vec n) : Mat n :=
  fun i j => if i = j then -∑ k ∈ Finset.univ.erase i, pairA D a i k else pairB D a i j
def coeffs (D : Data n) (a : Vec n) : Mat n :=
  fun i j => qhat D a i j / (√(action D a i) * √(action D a j))
def quad (M : Mat n) (x : Vec n) : ℝ := ∑ i, ∑ j, x i * M i j * x j

theorem coeffs_hermitian (D : Data n) (a : Vec n) : (coeffs D a).IsHermitian := sorry
theorem coeffs_analytic (D : Data n) : AnalyticOnNhd ℝ (coeffs D) (axes n) := sorry
/-- Explicit local uniform O(u^4), and the same analytic remainder. -/
theorem quadratic_form (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r C : ℝ, 0 < r ∧ r < rho D a ∧ 0 < C ∧
    AnalyticOnNhd ℝ (fun x : Slow n => secular D false x - constantTerm D (axis D x.2.1) -
      quad (coeffs D (axis D x.2.1)) x.1 - quad (coeffs D (axis D x.2.1)) x.2.2)
      (realDisc D a r) ∧
    ∀ x ∈ realDisc D a r, |secular D false x - constantTerm D (axis D x.2.1) -
      quad (coeffs D (axis D x.2.1)) x.1 - quad (coeffs D (axis D x.2.1)) x.2.2| ≤
      C * ‖(x.1,x.2.2)‖^4 := sorry

def modelDelta (D : Data n) (I : Vec n) : ℝ :=
  (2*D.m0)⁻¹ * ∑ i, D.m i^4 * (D.G*D.m0)^2 / I i^2
/-- Never subtract total Bochner averages without an integrability guard. -/
theorem identification (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    Continuous (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1)) ∧
    avg (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1) -
      perturbation D false (assemble x.2.1 t x.2.2 x.1)) = modelDelta D x.2.1 ∧
    (IntegrableOn (fun t => perturbation D true (assemble x.2.1 t x.2.2 x.1)) (cell n) ↔
      IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n)) ∧
    (IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n) →
      secular D true x = secular D false x + modelDelta D x.2.1) := sorry

theorem same_jets (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (k : ℕ) (hk : 0 < k) :
    iteratedFDeriv ℝ k (slowSecular D true I) 0 = iteratedFDeriv ℝ k (slowSecular D false I) 0 := sorry
/-- Generic transfer lemma with distinct name; source-specific discharge below. -/
theorem birkhoff_transfer {P Q : ℝ → Phase (n+n) → ℝ} {V : Set (Vec n)} {r0 μ0 : ℝ}
    {P0 : ℝ → Vec n → ℝ} {Ω : ℝ → Vec n → Vec n} {β : ℝ → Vec n → Mat n}
    {δ : Vec n → ℝ}
    (hInt : ∀ μ ∈ Icc 0 μ0, ∀ I ∈ V, ∀ p q : Vec n,
      (∀ j, p j^2+q j^2 < r0^2) →
      (IntegrableOn (fun t => P μ (assemble I t p q)) (cell n) ↔
       IntegrableOn (fun t => Q μ (assemble I t p q)) (cell n)))
    (hAvg : ∀ μ ∈ Icc 0 μ0, ∀ I ∈ V, ∀ p q : Vec n,
      (∀ j, p j^2+q j^2 < r0^2) →
      IntegrableOn (fun t => Q μ (assemble I t p q)) (cell n) →
      secularAverage P μ I p q = secularAverage Q μ I p q + δ I) :
    HasSecularBirkhoffForm P V r0 μ0 P0 Ω β ↔
      HasSecularBirkhoffForm Q V r0 μ0 (fun μ I => P0 μ I - δ I) Ω β := sorry

theorem same_jets_transfer (D : Data n) {V : Set (Vec n)} {r0 μ0 : ℝ}
    {P0 : ℝ → Vec n → ℝ} {Ω : ℝ → Vec n → Vec n} {β : ℝ → Vec n → Mat n}
    (hDom : ∀ I ∈ V, ∀ p q : Vec n, (∀ j, p j^2+q j^2 < r0^2) →
      (q,I,p) ∈ slowDom D) :
    HasSecularBirkhoffForm (fun _ => perturbation D true) V r0 μ0 P0 Ω β ↔
    HasSecularBirkhoffForm (fun _ => perturbation D false) V r0 μ0
      (fun μ I => P0 μ I - modelDelta D I) Ω β := sorry

/-- Pair coefficient functions are functions of their two actions only. -/
def pairSlowSecular (D : Data n) (i j : Fin n) (I J : ℝ)
    (u : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  (2*π)⁻¹ * ∫ s in (0:ℝ)..2*π, (2*π)⁻¹ * ∫ t in (0:ℝ)..2*π,
    -D.G*D.m i*D.m j / planeLength
      ((poincare (D.m i) (D.G*D.m0) (![s,u.1 0], ![I,u.1 1])).1 -
       (poincare (D.m j) (D.G*D.m0) (![t,u.2 0], ![J,u.2 1])).1)
def quarticMonomials (u v : Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![planeSq u^2, planeSq v^2, planeSq u*planeSq v, planeDot u v^2,
    planeSq u*planeDot u v, planeSq v*planeDot u v]
def radialPhi (a b : ℝ) : ℝ := (2*π)⁻¹ * ∫ t in (0:ℝ)..2*π,
  (a^2+b^2-2*a*b*Real.cos t) ^ (-1/2 : ℝ)
def radialH (a b ε : ℝ) : ℝ := radialPhi (a*(1-ε)) b * (1-ε)
def radialR1 (a b : ℝ) : ℝ := -iteratedDeriv 4 (radialH a b) 0 / 32 +
  iteratedDeriv 2 (radialH a b) 0 / 8
/-- Joint six-coefficient existence, analyticity and exact diagonal values. -/
theorem quartic (D : Data n) (hn : 2 ≤ n) :
    ∃ c : Fin n → Fin n → (ℝ × ℝ) → Fin 6 → ℝ,
    (∀ i j, i < j → AnalyticOnNhd ℝ (c i j)
      {IJ | 0 < IJ.1 ∧ 0 < IJ.2 ∧ IJ.1^2/(D.m i^2*(D.G*D.m0)) <
        IJ.2^2/(D.m j^2*(D.G*D.m0))}) ∧
    (∀ I ∈ actionDomain D, ∀ u : Vec n × Vec n,
      iteratedFDeriv ℝ 4 (slowSecular D false I) 0 (fun _ => u) / 24 =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        ∑ k, c i j (I i,I j) k * quarticMonomials ![u.1 i,u.2 i] ![u.1 j,u.2 j] k) ∧
    (∀ I ∈ actionDomain D, ∀ i j, i < j →
      c i j (I i,I j) 0 = -D.G*D.m i*D.m j *
        (iteratedDeriv 4 (radialH (axis D I i) (axis D I j)) 0 / 64 -
         iteratedDeriv 2 (radialH (axis D I i) (axis D I j)) 0 / 16) / I i^2 ∧
      c i j (I i,I j) 1 = -D.G*D.m i*D.m j *
        (iteratedDeriv 4 (radialH (axis D I j) (axis D I i)) 0 / 64 -
         iteratedDeriv 2 (radialH (axis D I j) (axis D I i)) 0 / 16) / I j^2) := sorry
end SecularForm

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}
/-- Euclidean norms as explicit functions on the required Pi carriers. -/
def length2 (x : Vec n) : ℝ := √(∑ i, x i^2)
def op2 (M : Mat n) : ℝ := sSup {r | ∃ x : Vec n, length2 x = 1 ∧ r = length2 (M.mulVec x)}
def frobenius (M : Mat n) : ℝ := √(∑ i, ∑ j, M i j^2)
def sorted (M : Mat n) (hM : M.IsHermitian) (i : Fin n) : ℝ :=
  hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i.rev)
def sigma (D : Data n) (a : Vec n) : Vec n := sorted (coeffs D a) (coeffs_hermitian D a)
def isSO (R : Mat n) : Prop := R.transpose * R = 1 ∧ R.det = 1

theorem norm_compare (x : Vec n) (M : Mat n) :
    ‖x‖ ≤ length2 x ∧ length2 x ≤ √n * ‖x‖ ∧ op2 M ≤ frobenius M := sorry

def dominance (M : Mat n) (j : Fin n) : ℝ := -M j j - ∑ k ∈ Finset.univ.erase j, M j k
/-- Algebraic identity; positivity only needed for its subsequent inequalities. -/
theorem l75 (M : Mat n) (hM : M.IsHermitian) (x : Vec n) :
    quad M x = -(∑ j, dominance M j * x j^2) -
      ∑ j, ∑ k ∈ Finset.univ.filter (j < ·), M j k * (x j-x k)^2 := sorry

theorem l74 {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (hα1 : α < 1) :
    laplace_def s 1 α - laplace_def s 2 α =
      2*s*α/π * ∫ t in (0:ℝ)..π,
        Real.sin t^2 * (1-Real.cos t) * (1+α^2-2*α*Real.cos t)^(-s-1) ∧
    0 < laplace_def s 1 α - laplace_def s 2 α := sorry

def coercivity (D : Data n) (a : Vec n) : ℝ :=
  (⨅ j, ∑ k ∈ Finset.univ.erase j, (pairA D a j k - pairB D a j k)) /
    (⨆ i, action D a i)
theorem definite (D : Data n) (hn : 2 ≤ n) {a : Vec n} (ha : a ∈ axes n) :
    0 < coercivity D a ∧ (∀ x, quad (coeffs D a) x ≤ -coercivity D a * length2 x^2) ∧
    (∀ j, sigma D a j ≤ -coercivity D a) ∧
    ContinuousOn (coercivity D) (axes n) := sorry

/-- Generic local spectral theorem. Sorted branches avoid witness-choice ambiguity. -/
theorem local_analytic {d : ℕ} {W : Set (Vec d)} (hW : IsOpen W)
    {M : Vec d → Mat n} (hM : ∀ x ∈ W, (M x).IsHermitian)
    (hAn : AnalyticOnNhd ℝ M W) {x0 : Vec d} (hx0 : x0 ∈ W)
    (hSimple : Function.Injective ((hM x0 hx0).eigenvalues)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x0 r ⊆ W ∧
    ∃ s : Vec d → Vec n, ∃ R : Vec d → Mat n,
      AnalyticOnNhd ℝ s (Metric.ball x0 r) ∧ AnalyticOnNhd ℝ R (Metric.ball x0 r) ∧
      ∀ x ∈ Metric.ball x0 r, isSO (R x) ∧ StrictMono (s x) ∧
        M x = R x * Matrix.diagonal (s x) * (R x).transpose := sorry

/-- Explicit action-dependent lift; full derivative of R is indispensable. -/
def liftMap (R : Vec n → Mat n) (w : Phase (n+n)) : Phase (n+n) :=
  let I : Vec n := fast w.2
  let ξ : Vec n := slow w.1
  let η : Vec n := slow w.2
  let θ : Vec n := fun l => fast w.1 l -
    ∑ i, η i * ((fderiv ℝ R I (Pi.single l 1) * (R I).transpose).mulVec ξ) i
  assemble I θ ((R I).transpose.mulVec η) ((R I).transpose.mulVec ξ)
def liftInv (R : Vec n → Mat n) (w : Phase (n+n)) : Phase (n+n) :=
  let I : Vec n := fast w.2
  let ξ : Vec n := slow w.1
  let η : Vec n := slow w.2
  let θ : Vec n := fun l => fast w.1 l +
    ∑ i, η i * (((R I).transpose * fderiv ℝ R I (Pi.single l 1)).mulVec ξ) i
  assemble I θ ((R I).mulVec η) ((R I).mulVec ξ)
def liftDomain (W : Set (Vec n)) : Set (Phase (n+n)) := {w | fast w.2 ∈ W}

theorem lift {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) :
    AnalyticOnNhd ℝ (liftMap R) (liftDomain W) ∧
    AnalyticOnNhd ℝ (liftInv R) (liftDomain W) ∧
    IsSymplecticOn 1 (liftMap R) (liftDomain W) ∧
    IsSymplecticOn 1 (liftInv R) (liftDomain W) ∧
    (∀ w ∈ liftDomain W, liftInv R (liftMap R w) = w ∧ liftMap R (liftInv R w) = w ∧
      fast (liftMap R w).2 = fast w.2 ∧
      length2 (slow (liftMap R w).1) = length2 (slow w.1) ∧
      length2 (slow (liftMap R w).2) = length2 (slow w.2)) ∧
    (∀ w ∈ liftDomain W, ∀ c : Vec n,
      liftMap R (w + (Fin.append c 0,0)) = liftMap R w + (Fin.append c 0,0)) := sorry

def k4 (n : ℕ) : Set (Fin n → ℤ) := {k | 0 < ∑ i, |k i| ∧ ∑ i, |k i| ≤ 4}
def nr4 (s : Vec n) : Prop := Function.Injective s ∧
  ∀ k ∈ k4 n, ∑ i, (k i : ℝ)*s i ≠ 0
def discriminant (s : Vec n) : ℝ :=
  ∏ j, ∏ l ∈ Finset.univ.filter (j < ·), (s j-s l)^2
/-- Finite set written as a subtype for product indexing. -/
theorem k4_finite (n : ℕ) : (k4 n).Finite := sorry
/-- Finiteness witness is proved before implementing this product, not an input assumption. -/
def good (s : Vec n) : ℝ := discriminant s *
  ∏ k ∈ (k4_finite n).toFinset, ∏ p : Equiv.Perm (Fin n), ∑ j, (k j : ℝ)*s (p j)
def goodAxes (D : Data n) : Set (Vec n) := {a ∈ axes n | good (sigma D a) ≠ 0}
def simpleAxes (D : Data n) : Set (Vec n) := {a ∈ axes n | discriminant (sigma D a) ≠ 0}

theorem good_set (D : Data n) :
    AnalyticOnNhd ℝ (fun a => good (sigma D a)) (axes n) ∧
    (∀ a ∈ axes n, good (sigma D a) ≠ 0 ↔ nr4 (sigma D a)) ∧
    (∀ p : Equiv.Perm (Fin n), ∀ s : Vec n, good (s ∘ p) = good s) := sorry

/-- Matched model parameter b appears once, in both average and secular function. -/
theorem diagonalize (D : Data n) (hn : 2 ≤ n) {W : Set (Vec n)} (hW : IsOpen W)
    (hWI : W ⊆ actionDomain D) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I))
    (hDiag : ∀ I ∈ W, coeffs D (axis D I) =
      R I * Matrix.diagonal (sigma D (axis D I)) * (R I).transpose) :
    (∀ I ∈ W, ∀ ξ η : Vec n,
      quad (coeffs D (axis D I)) ξ + quad (coeffs D (axis D I)) η =
      ∑ j, (2*sigma D (axis D I) j) *
        oscillatorAction ((R I).transpose.mulVec η) ((R I).transpose.mulVec ξ) j) ∧
    (∀ b : Bool, ∀ I ∈ W, ∃ r : ℝ, 0 < r ∧ ∀ ξ η : Vec n,
      ‖(ξ,η)‖ < r →
      avg (fun t => perturbation D b (liftInv R (assemble I t η ξ))) =
        secular D b ((R I).mulVec ξ,I,(R I).mulVec η)) := sorry

theorem n2 (D : Data 2) {a : Vec 2} (ha : a ∈ axes 2) :
    (coeffs D a).det = ((pairA D a 0 1)^2-(pairB D a 0 1)^2) /
      (action D a 0*action D a 1) ∧
    0 < (coeffs D a).det ∧
    0 < (coeffs D a).trace^2-4*(coeffs D a).det ∧
    sigma D a 0 < sigma D a 1 ∧
    (nr4 (sigma D a) ↔ sigma D a 0/sigma D a 1 ≠ 2 ∧ sigma D a 0/sigma D a 1 ≠ 3) ∧
    (nr4 (sigma D a) ↔
      (2*(coeffs D a).trace^2-9*(coeffs D a).det) *
      (3*(coeffs D a).trace^2-16*(coeffs D a).det) ≠ 0) := sorry

theorem n2_global_frame (D : Data 2) : ∃ R : Vec 2 → Mat 2,
    AnalyticOnNhd ℝ R (axes 2) ∧ ∀ a ∈ axes 2,
      isSO (R a) ∧ coeffs D a = R a * Matrix.diagonal (sigma D a) * (R a).transpose := sorry
end SecularSpectrum

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

theorem generic {r : ℕ} {B : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    {f : Fin r → Vec d → ℝ} (hf : ∀ j, AnalyticOnNhd ℝ (f j) B)
    (hne : ∀ j, ∃ x ∈ B, f j x ≠ 0) :
    IsOpen {x ∈ B | ∀ j, f j x ≠ 0} ∧
    B ⊆ closure {x ∈ B | ∀ j, f j x ≠ 0} ∧
    volume {x ∈ B | ∃ j, f j x = 0} = 0 := sorry

theorem weyl (A E : Mat n) (hA : A.IsHermitian) (hE : E.IsHermitian)
    (hAE : (A+E).IsHermitian) :
    ∀ i, |sorted (A+E) hAE i - sorted A hA i| ≤ op2 E := sorry

theorem sorted_analytic (D : Data n) : AnalyticOnNhd ℝ (sigma D) (simpleAxes D) := sorry

theorem laplace_bounds {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1/2) :
    (3/2)*α ≤ laplace_def (3/2) 1 α ∧
    laplace_def (3/2) 1 α ≤ (3/2)*α*(1+4*α^2) ∧
    (15/8)*α^2 ≤ laplace_def (3/2) 2 α ∧
    laplace_def (3/2) 2 α ≤ (15/8)*α^2*(1+4*α^2) := sorry

theorem formula69 (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j)
    (hα : a i/a j ≤ 1/2) :
    ∃ θ θ' : ℝ, θ ∈ Icc 0 (4*(a i/a j)^2) ∧ θ' ∈ Icc 0 (4*(a i/a j)^2) ∧
      pairA D a i j = (3/8)*D.G*D.m i*D.m j*(a i/a j)^2/a j*(1+θ) ∧
      pairB D a i j = (15/32)*D.G*D.m i*D.m j*(a i/a j)^3/a j*(1+θ') := sorry

def outerData (D : Data (n+1)) (hn : 0 < n) : Data n :=
  ⟨D.G,D.m0,(fun i => D.m i.succ),D.hG,D.hm0,(fun i => D.hm i.succ),hn⟩
def peelError (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) : Mat (n+1) :=
  fun i j => coeffs D a i j - Fin.cases 0
    (fun i' => Fin.cases 0 (fun j' => coeffs (outerData D hn) (fun k => a k.succ) i' j') j) i

theorem peel (D : Data (n+1)) (hn : 0 < n) {a' : Vec n} (ha' : a' ∈ axes n) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → (∀ i, t ≤ a' i/2) →
      let E := peelError D hn (Fin.cons t a')
      op2 E ≤ frobenius E ∧ frobenius E ≤ C*t^(3/2 : ℝ) ∧
      (∀ i j : Fin n, i ≠ j → E i.succ j.succ = 0) ∧
      |E 0 0| ≤ 3*D.G/(4*√(D.G*D.m0))*t^(3/2 : ℝ)*
        ∑ i : Fin n, D.m i.succ * (a' i)^(-3 : ℤ) ∧
      (∀ j : Fin n, |E j.succ j.succ| ≤
        3*D.G*D.m 0/(4*√(D.G*D.m0))*t^2*(a' j)^(-7/2 : ℝ)) ∧
      (∀ j : Fin n, |E 0 j.succ| ≤
        15*D.G*√(D.m 0*D.m j.succ)/(16*√(D.G*D.m0))*t^(11/4 : ℝ)*(a' j)^(-17/4 : ℝ)) := sorry

theorem n2 (D : Data 2) {a : Vec 2} (ha : a ∈ axes 2) :
    (coeffs D a).trace^2/(coeffs D a).det =
      (action D a 0+action D a 1)^2/(action D a 0*action D a 1) /
        (1-(pairB D a 0 1/pairA D a 0 1)^2) ∧
    (coeffs D a).trace^2/(coeffs D a).det > action D a 1/action D a 0+2 ∧
    sigma D a 0/sigma D a 1 ≥ (coeffs D a).trace^2/(coeffs D a).det-3 ∧
    (16*D.m 0^2/D.m 1^2 ≤ a 1/a 0 → nr4 (sigma D a)) := sorry

theorem good_point (D : Data n) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ a ∈ axes n, (∀ i j : Fin n, j.val = i.val+1 → a i/a j < ε) ∧ nr4 (sigma D a) := sorry

theorem good_set (D : Data n) (hn : 2 ≤ n) :
    IsOpen (goodAxes D) ∧ axes n ⊆ closure (goodAxes D) ∧
    volume (axes n \ goodAxes D) = 0 ∧
    ∀ a ∈ axes n, ∀ η : ℝ, 0 < η → ∃ a0 : ℝ, ∃ r : Vec n,
      0 < a0 ∧ Metric.closedBall r (2*a0) ⊆ goodAxes D ∩ Metric.ball a η := sorry

/-- Source definition, not a package of consequences. -/
def rnd_def (B : Set (Vec d)) (ω : Vec d → Vec m) : Prop :=
  ∀ c : Vec m, c ≠ 0 → ∃ y ∈ B, ∑ i, c i*ω y i ≠ 0

def relation (D : Data n) (c : Vec n × Vec n) (p : Equiv.Perm (Fin n)) (a : Vec n) : ℝ :=
  (∑ i, c.1 i*nu D (action D a) i) + ∑ j, c.2 j*sigma D a (p j)
def fc_def (D : Data n) (c : Vec n × Vec n) (a : Vec n) : ℝ :=
  ∏ p : Equiv.Perm (Fin n), relation D c p a

theorem fc_analytic (D : Data n) (c : Vec n × Vec n) :
    AnalyticOnNhd ℝ (fc_def D c) (axes n) := sorry

theorem f_nonzero (D : Data n) (hn : 2 ≤ n) {c : Vec n × Vec n} (hc : c ≠ 0) :
    ∃ a ∈ axes n, fc_def D c a ≠ 0 := sorry

def frequency (D : Data n) (I : Vec n) : Vec (n+n) :=
  Fin.append (nu D I) (fun j => 2*sigma D (axis D I) j)
def frequencyAxes (D : Data n) (a : Vec n) : Vec (n+n) := frequency D (action D a)

theorem rnd (D : Data n) (hn : 2 ≤ n) {B : Set (Vec n)}
    (hB : IsOpen B) (hBc : IsConnected B) (hBS : B ⊆ simpleAxes D) :
    AnalyticOnNhd ℝ (frequencyAxes D) B ∧ rnd_def B (frequencyAxes D) ∧
    AnalyticOnNhd ℝ (frequency D) (action D '' B) ∧ rnd_def (action D '' B) (frequency D) ∧
    rnd_def (action D '' B) (nu D) ∧
    rnd_def B (fun a j => 2*sigma D a j) := sorry

theorem scaling {B : Set (Vec d)} {ω : Vec d → Vec m} (hω : rnd_def B ω)
    {s : Vec m} (hs : ∀ i, 0 < s i) (p : Equiv.Perm (Fin m)) :
    rnd_def B (fun y i => s i * ω y (p i)) := sorry

/-- CP09 diagonal Euclidean tensor norm, with the separate order-zero convention. -/
def jetNorm {m : ℕ} (f : Vec d → Vec m) (ν : ℕ) (y : Vec d) : ℝ :=
  if ν = 0 then length2 (f y) else
    sSup {r | ∃ v : Vec d, length2 v = 1 ∧ r = length2 (iteratedFDeriv ℝ ν f y (fun _ => v))}
def scalarJet (g : Vec d → ℝ) (ν : ℕ) (y : Vec d) : ℝ :=
  if ν = 0 then |g y| else
    sSup {r | ∃ v : Vec d, length2 v = 1 ∧ r = |iteratedFDeriv ℝ ν g y (fun _ => v)|}
def jetMax (g : Vec d → ℝ) (μ : ℕ) (y : Vec d) : ℝ :=
  sSup ((fun ν => scalarJet g ν y) '' {ν | ν ≤ μ})

def betaFamily {C : Type*} (g : C → Vec d → ℝ) (C0 : Set C) (K : Set (Vec d)) (μ : ℕ) : ℝ :=
  sInf ((fun z : C × Vec d => jetMax (g z.1) μ z.2) '' (C0 ×ˢ K))
def sphere (m : ℕ) : Set (Vec m) := {c | length2 c = 1}
def squaredForm (ω : Vec d → Vec m) (c : Vec m) (y : Vec d) : ℝ := (∑ i, c i*ω y i)^2
def betaMu (ω : Vec d → Vec m) (K : Set (Vec d)) (μ : ℕ) : ℝ :=
  betaFamily (squaredForm ω) (sphere m) K μ
/-- No fallback value for an undefined index. -/
def index_def {C : Type*} (g : C → Vec d → ℝ) (C0 : Set C) (K : Set (Vec d))
    (h : ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily g C0 K μ) : ℕ := Nat.find h

theorem finite_type {C : Type*} [MetricSpace C] {C0 : Set C} (hC : IsCompact C0) (hCn : C0.Nonempty)
    {B K : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B) {g : C → Vec d → ℝ}
    (hAn : ∀ c ∈ C0, AnalyticOnNhd ℝ (g c) B)
    (hNe : ∀ c ∈ C0, ∃ y ∈ B, g c y ≠ 0)
    (hCont : ∀ ν : ℕ, ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2) (C0 ×ˢ B)) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily g C0 K μ ∧
      ∀ c ∈ C0, ∀ y ∈ K, betaFamily g C0 K μ ≤ jetMax (g c) μ y := sorry

theorem index_amount {C : Type*} [MetricSpace C] {g : C → Vec d → ℝ} {C0 : Set C}
    (hC : IsCompact C0) (hCn : C0.Nonempty) {K : Set (Vec d)}
    (hK : IsCompact K) (hKn : K.Nonempty)
    (hCont : ∀ ν : ℕ, ContinuousOn (fun z : C × Vec d => iteratedFDeriv ℝ ν (g z.1) z.2) (C0 ×ˢ K))
    (h : ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily g C0 K μ) :
    0 < index_def g C0 K h ∧ 0 < betaFamily g C0 K (index_def g C0 K h) ∧
    Monotone (betaFamily g C0 K) ∧
    (∀ μ : ℕ, 0 < μ → (0 < betaFamily g C0 K μ ↔ index_def g C0 K h ≤ μ)) := sorry

theorem cp09_lemma1 (hm : 0 < m) {B K : Set (Vec d)}
    (hB : IsOpen B) (hBc : IsConnected B) (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (hR : rnd_def B ω) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaMu ω K μ ∧
      ∀ c ∈ sphere m, ∀ y ∈ K, betaMu ω K μ ≤ jetMax (squaredForm ω c) μ y := sorry

/-- Bounds are explicit on the source tensors; M,theta can be chosen as their compact maxima. -/
theorem stability (hm : 0 < m) {B K : Set (Vec d)} (hB : IsOpen B)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω ω' : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (hAn' : AnalyticOnNhd ℝ ω' B)
    (μ : ℕ) {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 ≤ θ)
    (hBound : ∀ ν ≤ μ, ∀ y ∈ K, jetNorm ω ν y ≤ M)
    (hDiff : ∀ ν ≤ μ, ∀ y ∈ K, jetNorm (fun z => ω' z - ω z) ν y ≤ θ) :
    (∀ c ∈ sphere m, ∀ y ∈ K, ∀ ν ≤ μ,
      |scalarJet (squaredForm ω' c) ν y - scalarJet (squaredForm ω c) ν y| ≤
        2^ν*θ*(2*M+θ)) ∧
    betaMu ω K μ - 2^μ*θ*(2*M+θ) ≤ betaMu ω' K μ ∧
    (0 < betaMu ω K μ → 2^μ*θ*(2*M+θ) ≤ betaMu ω K μ/2 →
      betaMu ω K μ/2 ≤ betaMu ω' K μ ∧ 0 < betaMu ω' K μ) := sorry

/-- Joint good patch: all witnesses precede every coupling parameter (none occurs). -/
theorem interface (D : Data n) (hn : 2 ≤ n) {aStar : Vec n} (ha : aStar ∈ axes n)
    {η : ℝ} (hη : 0 < η) {r : ℕ} (f : Fin r → Vec n → ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) (axes n)) (hne : ∀ j, ∃ a ∈ axes n, f j a ≠ 0) :
    ∃ a0 : Vec n, ∃ r0 α β : ℝ, ∃ μ0 : ℕ,
      0 < r0 ∧ 0 < α ∧ 0 < β ∧ 0 < μ0 ∧
      Metric.closedBall a0 (2*r0) ⊆ goodAxes D ∩ Metric.ball aStar η ∧
      (∀ a ∈ Metric.closedBall a0 (2*r0), ∀ j, f j a ≠ 0) ∧
      α = sInf {q : ℝ | ∃ a ∈ Metric.closedBall a0 r0, ∃ k ∈ k4 n,
        q = |∑ j, (k j : ℝ)*(2*sigma D a j)|} ∧
      (∀ a ∈ Metric.closedBall a0 r0, ∀ k ∈ k4 n,
        α ≤ |∑ j, (k j : ℝ)*(2*sigma D a j)|) ∧
      (let B := action D '' Metric.ball a0 (2*r0)
       let K := action D '' Metric.closedBall a0 r0
       IsOpen B ∧ IsConnected B ∧ IsCompact K ∧ K ⊆ B ∧ 0 < volume K ∧
       AnalyticOnNhd ℝ (frequency D) B ∧ rnd_def B (frequency D) ∧
       β = betaMu (frequency D) K μ0 ∧
       (∀ μ, 0 < μ → 0 < betaMu (frequency D) K μ → μ0 ≤ μ) ∧
       (∀ μ, μ0 ≤ μ → β ≤ betaMu (frequency D) K μ) ∧
       ∀ c ∈ sphere (n+n), ∀ I ∈ K, β ≤ jetMax (squaredForm (frequency D) c) μ0 I) := sorry
end Nondegeneracy


namespace SecularForm
variable {n d : ℕ}
/-- Own the finite-dimensional parameter-integral adapter, not an external axiom. -/
theorem e_param {U : Set (CVec d)} (hU : IsOpen U) {f : Vec n → CVec d → ℂ}
    (hCont : ContinuousOn (fun z : Vec n × CVec d => f z.1 z.2) (cell n ×ˢ U))
    (hHol : ∀ t ∈ cell n, DifferentiableOn ℂ (f t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in cell n, f t z) U := sorry

theorem e_diff {U : Set (Vec d)} (hU : IsOpen U) {f : Vec n → Vec d → ℝ}
    (hCont : ∀ k : ℕ, ContinuousOn
      (fun z : Vec n × Vec d => iteratedFDeriv ℝ k (f z.1) z.2) (cell n ×ˢ U))
    (hSmooth : ∀ t ∈ cell n, ContDiffOn ℝ ⊤ (f t) U) (k : ℕ) {x : Vec d} (hx : x ∈ U) :
    iteratedFDeriv ℝ k (fun y => ∫ t in cell n, f t y) x =
      ∫ t in cell n, iteratedFDeriv ℝ k (f t) x := sorry

theorem average_translate {f : Vec n → ℝ} (hCont : Continuous f)
    (hPer : ∀ i (x : Vec n), Function.Periodic (fun t : ℝ => f (Function.update x i t)) (2*π)) (c : Vec n) :
    avg (fun t => f (t+c)) = avg f := sorry

theorem e_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (N : ℕ) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ h : E, ‖h‖ < r →
      |f (x+h) - ∑ k ∈ Finset.range (N+1),
        iteratedFDeriv ℝ k f x (fun _ => h) / k.factorial| ≤ C*‖h‖^(N+1) := sorry

/-- Simultaneous orthogonal invariance implies generation by dot products. -/
theorem e_weyl (P : MvPolynomial (Fin n × Fin 2) ℝ)
    (hInv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose*R = 1 →
      ∀ u : Fin n → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => (R.mulVec (u ic.1)) ic.2) P =
        MvPolynomial.eval (fun ic => u ic.1 ic.2) P) :
    ∃ Q : MvPolynomial (Fin n × Fin n) ℝ, ∀ u : Fin n → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => u ic.1 ic.2) P =
        MvPolynomial.eval (fun ij => planeDot (u ij.1) (u ij.2)) Q := sorry

theorem e_poch {s : ℝ} (hs : 0 < s) :
    (∀ q : ℕ, poch s (q+1) = poch s q * (s+q)) ∧
    (∀ z : ℝ, |z| < 1 → HasSum (fun q : ℕ => poch s q / q.factorial * z^q) ((1-z)^(-s))) ∧
    (fun q : ℕ => poch s q / q.factorial) =O[atTop] (fun q : ℕ => (q : ℝ)^(s-1)) := sorry

/-- The radius uniformization input named by global review G1. -/
theorem compact_uniform {E F : Type*} [MetricSpace E] [MetricSpace F]
    {K : Set E} (hK : IsCompact K) {f : E → F} (hf : ContinuousOn f K) :
    UniformContinuousOn f K := sorry
/-- G2, instantiated with the analytic periodic position map. -/
theorem periodic_derivative_integral {q : ℝ → (Fin 2 → ℝ)}
    (hq : ContDiff ℝ 1 q) (hp : Function.Periodic q (2*π)) :
    ∫ t in (0:ℝ)..2*π, deriv q t = 0 := sorry

/-- Exact dimensionless separated pair average. -/
def unitPosition (t : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let F := keplerLong t v
  let k := √(1-planeSq v)
  k • orbitalUnit F - v + (planeDot v (orbitalUnit F)/(1+k)) • v

def separatedDomain : Set (ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  {z | 0 < z.1 ∧ z.1 < 1 ∧ planeLength z.2.1 < 1/4 ∧ planeLength z.2.2 < 1/4 ∧
    z.1*(1+planeLength z.2.1) < 1-planeLength z.2.2}
def dimensionlessPair (z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  (2*π)⁻¹ * ∫ s in (0:ℝ)..2*π, (2*π)⁻¹ * ∫ t in (0:ℝ)..2*π,
    (planeLength (z.1 • unitPosition s z.2.1 - unitPosition t z.2.2))⁻¹

theorem quartic_scaling : AnalyticOnNhd ℝ dimensionlessPair separatedDomain := sorry
end SecularForm

namespace Nondegeneracy
variable {d m : ℕ}
/-- Polarization pays the diagonal-tensor-norm faithfulness obligation. -/
theorem f_pol {ν : ℕ} (T : (Fin d → ℝ) [×ν]→L[ℝ] ℝ)
    (hSym : ∀ (p : Equiv.Perm (Fin ν)) (v : Fin ν → (Fin d → ℝ)), T (v ∘ p) = T v) :
    T = 0 ↔ ∀ v : Fin d → ℝ, T (fun _ => v) = 0 := sorry

theorem f_leib {B : Set (Fin d → ℝ)} (hB : IsOpen B) {f g : (Fin d → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f B) (hg : AnalyticOnNhd ℝ g B)
    {y : Fin d → ℝ} (hy : y ∈ B) (v : Fin d → ℝ) (ν : ℕ) :
    iteratedFDeriv ℝ ν (fun z => f z*g z) y (fun _ => v) =
      ∑ k ∈ Finset.range (ν+1), (ν.choose k : ℝ) *
        iteratedFDeriv ℝ k f y (fun _ => v) * iteratedFDeriv ℝ (ν-k) g y (fun _ => v) := sorry

open SecularForm SecularSpectrum in
theorem scaling_amount {B K : Set (Vec d)} (hB : IsOpen B)
    (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B) (hm : 0 < m)
    {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) {s : Vec m} {lo hi : ℝ}
    (hlo : 0 < lo) (hs : ∀ i, lo ≤ s i ∧ s i ≤ hi) (μ : ℕ) :
    lo^2*betaMu ω K μ ≤ betaMu (fun y i => s i*ω y i) K μ ∧
    betaMu (fun y i => s i*ω y i) K μ ≤ hi^2*betaMu ω K μ := sorry
end Nondegeneracy

/-! ## Verbatim upstream Part 1 interfaces, for checking only.
These keep their exact owner names and bodies. Production imports their owner modules. -/
variable {d : ℕ}
def IsChart (c : ℝ) (Ψ : Phase d → Phase d) (O : Set (Phase d)) : Prop :=
  AnalyticOnNhd ℝ Ψ O ∧ IsSymplecticOn c Ψ O

def fullShift (k : Fin d → ℤ) : Phase d := (fun i => 2 * π * (k i : ℝ), 0)
def IsLatticeTorus (L : (Fin d → ℤ) → Phase d) (G : Phase d → ℝ) (O : Set (Phase d))
    (w : Fin d → ℝ) (K : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ K univ ∧ ∀ θ, K θ ∈ O ∧ DifferentiableAt ℝ G (K θ)) ∧
  (∀ θ (k : Fin d → ℤ), K (θ + fun i => (k i : ℝ)) = K θ + L k) ∧
  (∀ θ θ', K θ = K θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ∧
  (∀ θ, Injective (fderiv ℝ K θ)) ∧
  (∀ θ u v, symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) = 0) ∧
  (∀ θ t, HasDerivAt (fun s : ℝ => K (θ + s • w))
    (hamiltonianVectorField G (K (θ + t • w))) t)

def periodOne (κ : (Fin d → ℝ) → Phase d) : (Fin d → ℝ) → Phase d := fun θ => κ ((2 * π) • θ)

/-- The `2π`-convention torus of CP09 Thm. 3 (`bpP:p1:phys-pipeline`): (L1)-(L5) with period
`2π` (`τ_k = fullShift k`) and the flow clause with the angular frequency `ω̃`. -/
def IsTwoPiLatticeTorus (G : Phase d → ℝ) (O : Set (Phase d)) (ω : Fin d → ℝ)
    (κ : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ κ univ ∧ ∀ ϑ, κ ϑ ∈ O ∧ DifferentiableAt ℝ G (κ ϑ)) ∧
  (∀ ϑ (k : Fin d → ℤ), κ (ϑ + fun i => 2 * π * (k i : ℝ)) = κ ϑ + fullShift k) ∧
  (∀ ϑ ϑ', κ ϑ = κ ϑ' → ∃ k : Fin d → ℤ, ϑ' = ϑ + fun i => 2 * π * (k i : ℝ)) ∧
  (∀ ϑ, Injective (fderiv ℝ κ ϑ)) ∧
  (∀ ϑ u v, symplecticForm (fderiv ℝ κ ϑ u) (fderiv ℝ κ ϑ v) = 0) ∧
  (∀ ϑ t, HasDerivAt (fun s : ℝ => κ (ϑ + s • ω))
    (hamiltonianVectorField G (κ (ϑ + t • ω))) t)

theorem isLatticeTorus_periodOne_iff (G : Phase d → ℝ) (O : Set (Phase d)) (ω : Fin d → ℝ)
    (κ : (Fin d → ℝ) → Phase d) :
    IsLatticeTorus fullShift G O ((2 * π)⁻¹ • ω) (periodOne κ) ↔ IsTwoPiLatticeTorus G O ω κ :=
  sorry
theorem phys_pipeline {H : Phase d → ℝ} {Φ : Phase d → Phase d} {O₀ : Set (Phase d)}
    (hΦ : IsChart 1 Φ O₀)
    (hQ1 : ∀ z ∈ O₀, ∀ k : Fin d → ℤ, z + fullShift k ∈ O₀ ∧ Φ (z + fullShift k) = Φ z)
    (hQ2 : ∀ z ∈ O₀, ∀ z' ∈ O₀, Φ z' = Φ z → ∃ m : Fin d → ℤ, z' = z + fullShift m)
    {κ : (Fin d → ℝ) → Phase d} {ω : Fin d → ℝ} (hκ : IsTwoPiLatticeTorus (H ∘ Φ) O₀ ω κ)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : (d : ℝ) - 1 < τ) (hω : IsDiophantine γ τ ω) :
    IsPhysicalTorus H ((2 * π)⁻¹ • ω) (Φ ∘ periodOne κ) ∧
      range (Φ ∘ periodOne κ) = Φ '' range κ := sorry

namespace SecularForm
variable {n : ℕ}
theorem lemma64_coordinates (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) :
    (∀ t i j, i ≠ j → deriv (fun s => position D x (Function.update t j s) i) (t j) = 0) ∧
    (∀ t i, (2*π)⁻¹ • (∫ s in (0:ℝ)..2*π, momentum D x (Function.update t i s) i) = 0) ∧
    (∀ t i, (2*π)⁻¹ * (∫ s in (0:ℝ)..2*π, planeSq (momentum D x (Function.update t i s) i)) =
      D.m i^2*(D.G*D.m0)/axis D x.2.1 i) := sorry

theorem evenness_taylor (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (b : Bool) (k : ℕ) :
    iteratedFDeriv ℝ (2*k+1) (slowSecular D b I) 0 = 0 := sorry

theorem same_jets_on (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a ∧ ∀ x ∈ realDisc D a r, ∀ k : ℕ, 0 < k → ∀ l : ℕ,
      iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D true I) (x.1,x.2.2)) x.2.1 =
      iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D false I) (x.1,x.2.2)) x.2.1 := sorry
end SecularForm

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {d m : ℕ}
theorem analytic_zero_null {B : Set (Vec d)} (hB : IsOpen B) (hBc : IsConnected B)
    {f : Vec d → ℝ} (hf : AnalyticOnNhd ℝ f B) (hne : ∃ x ∈ B, f x ≠ 0) :
    volume {x ∈ B | f x = 0} = 0 := sorry

theorem action_diffeomorphism {n : ℕ} (D : Data n) :
    IsOpen (axes n) ∧ Convex ℝ (axes n) ∧ IsConnected (axes n) ∧
    IsOpen (actionDomain D) ∧
    AnalyticOnNhd ℝ (action D) (axes n) ∧ AnalyticOnNhd ℝ (axis D) (actionDomain D) ∧
    (∀ a ∈ axes n, axis D (action D a) = a) ∧
    (∀ I ∈ actionDomain D, action D (axis D I) = I) := sorry
end Nondegeneracy

/-! ## P7 obligations not exported as complete graph results (aa7bc30).
These are owned by the present design, rather than assumed. -/
namespace SecularForm
variable {n : ℕ}
def keplerActionHam (D : Data n) (I : Vec n) : ℝ := hProd (D.G*D.m0) D.m (assemble I 0 0 0)
theorem product_chart (D : Data n) :
    AnalyticOnNhd ℝ (keplerActionHam D) {I | ∀ i, 0 < I i} ∧
    (∀ I : Vec n, (∀ i, 0 < I i) → ∀ i,
      fderiv ℝ (keplerActionHam D) I (Pi.single i 1) = nu D I i ∧
      fderiv ℝ (fun J => nu D J i) I (Pi.single i 1) = -3*(D.G*D.m0)^2*D.m i^3/I i^4 ∧
      -3*(D.G*D.m0)^2*D.m i^3/I i^4 ≠ 0) ∧
    (∀ w ∈ poincareProdDom n,
      hamiltonianVectorField (hProd (D.G*D.m0) D.m) w = (Fin.append (nu D (fast w.2)) 0,0)) := sorry

theorem pc_prod (D : Data n) :
    AnalyticOnNhd ℝ (poincareProd D.m (D.G*D.m0)) (poincareProdDom n) ∧
    IsSymplecticOn 1 (poincareProd D.m (D.G*D.m0)) (poincareProdDom n) ∧
    poincareProd D.m (D.G*D.m0) '' poincareProdDom n = regionProd D.m (D.G*D.m0) ∧
    (∀ w ∈ poincareProdDom n, ∀ w' ∈ poincareProdDom n,
      poincareProd D.m (D.G*D.m0) w = poincareProd D.m (D.G*D.m0) w' ↔
      ∃ k : Fin n → ℤ, w' = w + fastShift (a := n) (b := n) k) ∧
    (∀ w ∈ poincareProdDom n,
      ∃ φ : OpenPartialHomeomorph (Phase (n+n)) (Phase (n*2)), w ∈ φ.source ∧
        (φ : Phase (n+n) → Phase (n*2)) = poincareProd D.m (D.G*D.m0) ∧
        AnalyticOnNhd ℝ φ.symm φ.target) := sorry

/-- Source field transport, obtained from the frozen form, not assumed in Lemma 64. -/
theorem pc_share (D : Data n) (b : Bool) (μ : ℝ) {w : Phase (n+n)}
    (hw : w ∈ poincareProdDom n) (hW : NoCollision (poincareProd D.m (D.G*D.m0) w).1) :
    let H := if b then movingHamiltonian D.G D.m0 D.m μ else fixedHamiltonian D.G D.m0 D.m μ
    H (poincareProd D.m (D.G*D.m0) w) = hProd (D.G*D.m0) D.m w + μ*perturbation D b w ∧
    fderiv ℝ (poincareProd D.m (D.G*D.m0)) w
      (hamiltonianVectorField (H ∘ poincareProd D.m (D.G*D.m0)) w) =
      hamiltonianVectorField H (poincareProd D.m (D.G*D.m0) w) := sorry

/-- Collision-free Kepler version needed by p8:l64-a; no pair guard. -/
theorem pc_dec (D : Data n) {w : Phase (n+n)} (hw : w ∈ poincareProdDom n) :
    fderiv ℝ (poincareProd D.m (D.G*D.m0)) w
      (hamiltonianVectorField (hProd (D.G*D.m0) D.m) w) =
      hamiltonianVectorField (keplerPart (D.G*D.m0) D.m) (poincareProd D.m (D.G*D.m0) w) := sorry
end SecularForm

/-! P7's exact existing definitions (KeplerSignaturesP.lean), still unimplemented here. -/
variable {n : ℕ}
def polarDom (n : ℕ) : Set (Phase (n + n)) := {z | ∀ i, 0 < fast z.2 i ∧ 0 < slow z.2 i ∧ slow z.2 i < fast z.2 i}
def polarMap (z : Phase (n + n)) : Phase (n + n) :=
  assemble (fast z.2) (fast z.1) (fun i => √(2 * slow z.2 i) * Real.cos (slow z.1 i))
    (fun i => √(2 * slow z.2 i) * Real.sin (slow z.1 i))
def angleScale (c : ℝ) (z : Phase d) : Phase d := (c • z.1, z.2)
namespace SecularSpectrum
open SecularForm
/-- The missing radian/polar quotient statements, on the literal existing polar map. -/
theorem lattice (D : Data n) :
    AnalyticOnNhd ℝ (polarMap (n := n)) (polarDom n) ∧
    IsSymplecticOn 1 (polarMap (n := n)) (polarDom n) ∧
    MapsTo (polarMap (n := n)) (polarDom n) (poincareProdDom n) ∧
    (∀ z ∈ polarDom n, ∀ k : Fin (n+n) → ℤ,
      z + fullShift k ∈ polarDom n ∧
      poincareProd D.m (D.G*D.m0) (polarMap (z+fullShift k)) =
        poincareProd D.m (D.G*D.m0) (polarMap z)) ∧
    (∀ z ∈ polarDom n, ∀ z' ∈ polarDom n,
      poincareProd D.m (D.G*D.m0) (polarMap z') = poincareProd D.m (D.G*D.m0) (polarMap z) →
      ∃ k : Fin (n+n) → ℤ, z' = z+fullShift k) ∧
    IsSymplecticOn (2*π) (poincareProd D.m (D.G*D.m0) ∘ polarMap ∘ angleScale (2*π))
      (angleScale (2*π) ⁻¹' polarDom n) := sorry

def rotatedPhysicalChart (D : Data n) (R : Vec n → Mat n) : Phase (n*2) → Phase (n*2) :=
  poincareProd D.m (D.G*D.m0) ∘ liftInv R ∘ polarMap ∘ phaseCast (Nat.mul_two n)
def rotatedDomain (R : Vec n → Mat n) (W : Set (Vec n)) : Set (Phase (n*2)) :=
  {z | let w := phaseCast (Nat.mul_two n) z
    w ∈ polarDom n ∧ fast w.2 ∈ W ∧ liftInv R (polarMap w) ∈ poincareProdDom n}

theorem diagonalize_transport (D : Data n) {W : Set (Vec n)} (hW : IsOpen W)
    {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) :
    IsOpen (rotatedDomain R W) ∧ IsChart 1 (rotatedPhysicalChart D R) (rotatedDomain R W) ∧
    (∀ z ∈ rotatedDomain R W, ∀ k : Fin (n*2) → ℤ,
      z+fullShift k ∈ rotatedDomain R W ∧
      rotatedPhysicalChart D R (z+fullShift k) = rotatedPhysicalChart D R z) ∧
    (∀ z ∈ rotatedDomain R W, ∀ z' ∈ rotatedDomain R W,
      rotatedPhysicalChart D R z' = rotatedPhysicalChart D R z →
      ∃ k : Fin (n*2) → ℤ, z' = z+fullShift k) := sorry

theorem diagonalize_period_one (D : Data n) {W : Set (Vec n)} (hW : IsOpen W)
    {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I))
    (H : Phase (n*2) → ℝ) (κ : (Fin (n*2) → ℝ) → Phase (n*2)) (ω : Fin (n*2) → ℝ)
    (hκ : IsTwoPiLatticeTorus (H ∘ rotatedPhysicalChart D R) (rotatedDomain R W) ω κ)
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : ((n*2 : ℕ) : ℝ)-1 < τ) (hω : IsDiophantine γ τ ω) :
    IsPhysicalTorus H ((2*π)⁻¹ • ω) (rotatedPhysicalChart D R ∘ periodOne κ) ∧
      range (rotatedPhysicalChart D R ∘ periodOne κ) = rotatedPhysicalChart D R '' range κ := sorry
end SecularSpectrum

namespace SecularForm
variable {n : ℕ}
theorem quartic_pair_scaling (D : Data n) {i j : Fin n} (hij : i < j)
    {L1 L2 : ℝ} (hI : 0 < L1) (hJ : 0 < L2) (u v : Fin 2 → ℝ)
    (hu : (![0,u 0],![L1,u 1]) ∈ poincareDom)
    (hv : (![0,v 0],![L2,v 1]) ∈ poincareDom)
    (hSep : (L1^2/(D.m i^2*(D.G*D.m0))/(L2^2/(D.m j^2*(D.G*D.m0))),
      poincareV (![0,u 0],![L1,u 1]), poincareV (![0,v 0],![L2,v 1])) ∈ separatedDomain) :
    pairSlowSecular D i j L1 L2 (u,v) = -D.G*D.m i*D.m j/(L2^2/(D.m j^2*(D.G*D.m0))) *
      dimensionlessPair (L1^2/(D.m i^2*(D.G*D.m0))/(L2^2/(D.m j^2*(D.G*D.m0))),
        poincareV (![0,u 0],![L1,u 1]), poincareV (![0,v 0],![L2,v 1])) := sorry
end SecularForm

namespace SecularSpectrum
open SecularForm
variable {n d : ℕ}
def opMax (M : Mat n) : ℝ := sSup {r | ∃ x : Vec n, ‖x‖ = 1 ∧ r = ‖M.mulVec x‖}
theorem norm_compare_operator (M : Mat n) :
    opMax M ≤ √n * op2 M ∧ op2 M ≤ √n * opMax M := sorry

theorem good_characteristic (n : ℕ) : ∃ P : MvPolynomial (Fin n) ℝ,
    ∀ M : Mat n, ∀ hM : M.IsHermitian,
      good (sorted M hM) = MvPolynomial.eval (fun i => M.charpoly.coeff i.val) P := sorry

theorem good_set_dichotomy (D : Data n) {B : Set (Vec n)} (hB : IsOpen B)
    (hBc : IsConnected B) (hBA : B ⊆ axes n) :
    (∀ a ∈ B, good (sigma D a) = 0) ∨
    (IsOpen {a ∈ B | good (sigma D a) ≠ 0} ∧
      B ⊆ closure {a ∈ B | good (sigma D a) ≠ 0} ∧
      volume {a ∈ B | good (sigma D a) = 0} = 0) := sorry

/-- Uniqueness includes constant column signs on a connected patch. -/
theorem local_analytic_unique {W : Set (Vec d)} (hW : IsOpen W) (hWc : IsConnected W)
    {s t : Vec d → Vec n} {R S : Vec d → Mat n}
    (hR : AnalyticOnNhd ℝ R W) (hS : AnalyticOnNhd ℝ S W)
    (hDiag : ∀ x ∈ W, isSO (R x) ∧ isSO (S x) ∧ StrictMono (s x) ∧ StrictMono (t x) ∧
      R x * Matrix.diagonal (s x) * (R x).transpose = S x * Matrix.diagonal (t x) * (S x).transpose) :
    EqOn s t W ∧ ∃ e : Vec n, (∀ i, e i = 1 ∨ e i = -1) ∧
      (∏ i, e i) = 1 ∧ ∀ x ∈ W, S x = R x * Matrix.diagonal e := sorry
end SecularSpectrum
namespace SecularSpectrum
open SecularForm
variable {n : ℕ}
theorem l75_bound (M : Mat n) (hM : M.IsHermitian)
    (hOff : ∀ i j, i ≠ j → 0 ≤ M i j) {c : ℝ}
    (hc : ∀ j, c ≤ dominance M j) (x : Vec n) :
    quad M x ≤ -c * length2 x^2 := sorry
end SecularSpectrum

namespace SecularForm
variable {n : ℕ}
theorem laplace_fourier {s α : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hα1 : α < 1) (t : ℝ) :
    HasSum (fun k : ℤ => (laplace_def s k α : ℂ) * Complex.exp ((k : ℂ)*(t : ℂ)*Complex.I))
      ((1+α^2-2*α*Real.cos t)^(-s) : ℝ) := sorry
end SecularForm

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {d m : ℕ}
theorem cp09_unsquared (hm : 0 < m) {B K : Set (Vec d)}
    (hB : IsOpen B) (hBc : IsConnected B) (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω : Vec d → Vec m} (hAn : AnalyticOnNhd ℝ ω B) (hR : rnd_def B ω) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily (fun c y => ∑ i, c i*ω y i) (sphere m) K μ := sorry

theorem cp09_product {r : ℕ} {dims : Fin r → ℕ} (hm : ∀ l, 0 < dims l) {B K : Set (Vec d)}
    (hB : IsOpen B) (hBc : IsConnected B) (hK : IsCompact K) (hKn : K.Nonempty) (hKB : K ⊆ B)
    {ω : (l : Fin r) → Vec d → Vec (dims l)}
    (hAn : ∀ l, AnalyticOnNhd ℝ (ω l) B) (hR : ∀ l, rnd_def B (ω l)) :
    ∃ μ : ℕ, 0 < μ ∧ 0 < betaFamily
      (fun (c : (l : Fin r) → Vec (dims l)) y => ∏ l, ∑ i, c l i*ω l y i)
      {c | ∀ l, c l ∈ sphere (dims l)} K μ := sorry
end Nondegeneracy

end KAM.Planetary
end
```
