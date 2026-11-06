Audited commit: `66b14c836abbb606364723aac48a50a53e142d5e` (`inp-sjsu-g2`).

Verdict: **PASS WITH NOTES**.

The proposed mathematical statement and Hamiltonian data definition pass this independent, refute-first
statement audit. No false binder, empty initial set, coefficient mismatch, sign error, time rescaling, or
conclusion-shaped premise was found. The documentation overstates the status of the eccentricity enclosure
(N1). The fixed-reference eccentricities should be labelled explicitly as secular-model observables (N2).
This verdict approves neither a confinement proof nor a completed numerical certificate.

## Scope and revision record

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the audit brief, the proposal, dataset and application
README, nominal-point JSON, rigor plan §1.1, phase-1 gates report, both frozen definitions, and the frozen
Hénon–Heiles precedent. D74 and D75 are absent from this checkout's decision file; both were read from
`git show main:docs/DECISIONS.md`, with `main` at `22f7dd4b58a880bdaa5347130809d34dd0972a10`.
D75 explicitly selects the complex form and supersedes the plan's real-form wording.

There was already one tracked working-tree modification on entry: `scripts/sjsu/rigor/gen_t2conf.py`
replaces `import Mathlib` in the generated scratch check with three specific Mathlib imports (two inserted
lines, one deleted line). I did not change it. Its working-tree SHA256 is
`88429a70534b87e3471598e560c368ff6c4e8921b41d134e7f43bce57de162ee`; the committed generator's SHA256 is
`8c82b8c9f975a433fdd20b54552bed11bd5981fd6bb43b5ad8691d7ea2846749`.
The typecheck below uses that pre-existing import-only modification. All generated declaration texts,
including the theorem docstring, were independently compared with the pinned proposal. This distinction
does not change the audited declarations, but the passing scratch import configuration is not the
committed generator's configuration.

Only this report was added to the repository. Generated audit artifacts are in
`/tmp/g2-stmt-audit-1-66b14c836/`. Frozen files, manifests, roots and application sources were not edited.

## Findings

### N1 — The proposal calls an unenclosed float calculation rigorous

**Location:** `docs/explorations/sjsu-g2-t2conf-proposal.md:48–49`.

**Quoted text:** “they contain the rigorous tube ranges [0.0267, 0.0611], [0.0093, 0.0845],
[0.0066, 0.0621] (SR-4 (e)).”

**Why it is wrong:** The cited report explicitly says at
`docs/explorations/sjsu-g2-gates.md:149`: “The float evaluation in (e) is not enclosed; the Lean enclosure
is N6.” Its actual reported ranges at lines 139–141 are `[0.02668, 0.06112]`, `[0.00932, 0.08454]`,
and `[0.00658, 0.06206]`. Some shortened endpoints in the proposal round inward. Neither the word
“rigorous” nor an interpretation of these shortened pairs as established enclosures is supported.
The bracket ball-mirror calculation elsewhere in SR-4 does not certify this separate eccentricity step.

**Suggested fix:** Replace the sentence with: “The proposed intervals contain the phase-1 float estimates
of the tube ranges, [0.02668, 0.06112], [0.00932, 0.08454] and [0.00658, 0.06206] (SR-4(e)); these
estimates are not interval enclosures. The required eccentricity enclosure remains the phase-2 N6 proof.”
Keep the proposed Lean interval endpoints: they have positive margins over all the reported estimates.
This is a documentation correction and an explicit remaining proof obligation, not a refutation of the
candidate theorem.

### N2 — Clarify what the eccentricities mean after the secular transformations

**Location:** theorem docstring at proposal lines 26–28 and conventions at lines 109–110.

**Quoted text:** “the eccentricities … of Jupiter, Saturn and Uranus” and
“`Γ_j = Λ*_j (1 − √(1 − e_j²))`.”

**Why clarification is needed:** The general Poincaré identity uses the actual fast action `Λ_j`.
The dataset says its secular variables are *after* the near-identity transformations at `L = 0`, and are
not the osculating Poincaré variables (`conventions.secular_variables`; application README lines 101,
106). The proposed theorem correctly uses fixed `parameters.Lambda_star`, not a nonexistent evolving
fast-action component of its six-dimensional state. Thus its displayed expression is a precisely defined
fixed-reference secular eccentricity observable. It does not, without inverse transformations and error
bounds, bound actual osculating eccentricities of the full planetary problem. The explicit formula and
“secular confinement” title make the mathematical statement acceptable, but this limitation should travel
with the frozen docstring rather than depend on the application README.

**Suggested fix:** Say “the fixed-reference secular-model eccentricities of Jupiter, Saturn and Uranus,
defined by … using the dataset's `Λ*` at `L = 0`.” Add that no bound on the full problem's osculating
elements is asserted. Do not substitute actual `Λ_j` or add an unprovided dynamical phase variable.

## Required checks and mathematical assessment

1. **Binders, existence, uniqueness and non-vacuity — PASS.** For each `z₀` satisfying the only premise,
   the statement chooses one `T₁ > 5·10⁹ > 0` and one path `z`, before quantifying over times and competing
   solutions. Since `|t| ≤ 5·10⁹ < T₁`, the entire closed claimed horizon, including both endpoints, lies
   in the open ODE interval `Set.Ioo (-T₁) T₁`. `z` being a function on all real times imposes no ODE or
   uniqueness claim outside that interval. Each `j` is inferred as `Fin 3`, so all three planets occur.

   The competing interval is any `OrdConnected` set containing zero, and agreement is asserted precisely
   on its intersection with the exhibited interval. `HasDerivAt`, as in the Hénon–Heiles precedent,
   requires an ordinary derivative even at a competing interval's endpoints; usual solutions on open
   intervals are included. No hypothesis assumes the desired bound, a tube, an approximate integral,
   a certificate, or existence. This matches the precedent's quantifier structure.

   Setting `z₀.2` to the three nominal ξ literals and `z₀.1` to the three nominal η literals satisfies
   `hz₀` exactly. In fact Q is a closed six-dimensional box of positive radius and positive volume.
   Independent exact-rational evaluation at this point gave zero imaginary Hamiltonian part and six
   nonzero real gradient components. In order `(∂ξ_J, ∂ξ_S, ∂ξ_U, ∂η_J, ∂η_S, ∂η_U)`, their approximate
   displays are `(-1.580105595e-6, 1.735583075e-6, 1.299782970e-7, -7.905146543e-7,
   2.382858799e-6, -3.570227205e-8)`. The constant nominal path cannot witness the ODE conclusion.

2. **Time units — PASS.** Dataset and README specify AU, year, `G = 1`, and `m₀ = 4π²`; setting the
   gravitational constant to one here does not change years into a `2π`-rescaled time. The recorded
   Kepler angular frequencies give periods `2π/n` approximately `(11.8603, 29.5288, 84.2273)` years.
   The specified Hamilton equations use these units without an extra scaling factor. Accordingly the
   literal `5 * 10 ^ 9` is five billion model years. This says nothing about approximation error relative
   to the full N-body problem.

3. **Coordinate, complex-variable and column conventions — PASS.** The frozen vector field is
   `(∂H/∂x.2, −∂H/∂x.1)`. With `x = (η, ξ)` this gives precisely the dataset's
   `η̇ = ∂H/∂ξ`, `ξ̇ = −∂H/∂η`. Hence `z = (ξ − iη)/√2` has `{z, z̄} = −i` and
   `ż = −i∂H/∂z̄`. The right-associated tuple constructor and projections select, in order,
   `aJ, bJ, aS, bS, aU, bU, c`; the Hamiltonian assigns these to the six advertised factors correctly.

   Independently checked all rows: unique exponent tuples, total degrees exactly among `2,4,…,18`,
   zero charge, rational real coefficients, and exact equality of every coefficient with its conjugate
   partner obtained by swapping all three exponent pairs. Conjugating the sum therefore merely
   permutes its terms. It is exactly real for every real state; taking `Re` discards no Hamiltonian
   information. Even degree supplies the rational factor `2^(−degree/2)` upon expansion into ξ and η;
   reality follows from the conjugate pairing, not from even degree alone.

4. **Eccentricity formula and domain — PASS with N2.** The frozen `oscillatorAction ξ η j` is exactly
   `(ξ_j² + η_j²)/2 = Γ_j`. Inverting `Γ = Λ*(1 − √(1 − e²))` on the physical branch
   `0 ≤ Γ ≤ Λ*`, `0 ≤ e ≤ 1`, gives the displayed square root. `Λ*` is the appropriate fixed reference
   of this secular observable; the theorem contains no actual fast action. All three literals are positive.

   Exact rational endpoint calculations on the entire initial box establish `0 < Γ_j < Λ*_j` and
   put each initial eccentricity strictly inside its proposed interval. Nominal eccentricities are
   approximately `(0.04848729, 0.05475852, 0.04705978)`. There is no immediate contradiction at `t = 0`.
   The totalized real square root cannot make the conclusion vacuous: each required lower bound is
   positive, ruling out a nonpositive radicand. Moreover, continuity from the initial physical branch
   and the asserted upper bounds below one exclude crossing `Γ_j = Λ*_j` during the claimed horizon.

5. **Decimal literals — PASS.** Parsed the nominal JSON with decimal tokens retained as strings and
   compared all six lexemes with the theorem, ξ first in `z₀.2`, η second in `z₀.1`. Both appearances of
   the three `Λ*` entries match `parameters.Lambda_star` verbatim. All coefficients have explicit type
   `ℚ`; the initial state, radius, horizon and eccentricity literals have type `ℝ` from their context.
   Scientific notation in these characteristic-zero fields denotes decimal rationals exactly, with
   exact rational casts into `ℂ`; there is no floating-point conversion. This also agrees with the local
   Mathlib `Data/Rat/Cast/OfScientific.lean` and `Rat.cast_ofScientific` implementation/lemmas.

6. **Dataset regeneration and independent re-parse — PASS.** Ran:

   ```sh
   python3 scripts/sjsu/rigor/gen_t2conf.py --out /tmp/g2-stmt-audit-1-66b14c836 --roundtrip
   sha256sum applications/sjsu/data/sjsu18-o2.json
   ```

   Output: `roundtrip OK: 7941 rows byte-identical to complex_form.terms` and dataset SHA256
   `702b0b3a3c7c713d48cc3044f90bd13795b79f255550275cc7937c5d8a067772`.

   A separate Python parser then read the six generated `.txt` part files from disk, required every
   list-body line to match a complete `sjsuTerm` row, and compared the concatenated six exponent integers
   and untouched coefficient strings against every JSON row in order. It did not call or reuse the
   generator's parser. All 7,941 rows matched. Counts were `1324,1324,1324,1324,1324,1321`.
   SHA256 of each definition text, excluding the generator's one appended newline, matched every entry
   in the proposal's hash table:

   | Part | SHA256 |
   |---|---|
   | 0 | `6d39b3be7706097ab81b20247b2d22211a145253f23daec5df8806604a9e997b` |
   | 1 | `1d64722ff317478ba69bb2991177eafb3bc61631914a95374c8d8a46eb207de9` |
   | 2 | `5b2ccffe12002514218f8ff98b5123872b75ab1520d24ce9aa1bd7b8da22a8c7` |
   | 3 | `c6e58527b1d9dd7806d931825ecdcd2ee34c2a40aa0f32b974bcd15a127ccd63` |
   | 4 | `a26f0b35939a67d27a9616f96ad8ba6d82de23000602ccbca572218136aa39f5` |
   | 5 | `10cc55d4d29374655ef89e4fd71b943d25d4cb69250aafafc6ba99f715deb43b` |

   The generated theorem plus docstring, Hamiltonian, terms concatenation and row constructor also
   match their proposal code blocks verbatim. Each prospective data declaration occupies 1,328 lines
   (part 5: 1,325), leaving room for the required module wrapper below the 1,500-line file limit.

7. **Exactly the prescribed Lean check — PASS.** With no other Lean invocation active, ran once:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean /tmp/g2-stmt-audit-1-66b14c836/Check.lean
   ```

   Exit status **0**. Only diagnostic:

   ```text
   /tmp/g2-stmt-audit-1-66b14c836/Check.lean:8002:5: warning: Variable name `hz₀` is not explicitly referenced.
   ```

   This is expected in a check of the universally quantified statement as a proposition: its conclusion
   does not depend on the proof term of `hz₀`. It is not a discarded initial-set assumption in a proof.
   Lean also printed its standard hint for suppressing this warning; no suppression or `set_option`
   was used. `Check.lean` SHA256:
   `94dbea1cf97c023529b7b22d2aa0faa0380e3c03dd6ea13bab471742e331257c`.
   This generated scratch aggregate has 8,015 lines, as required by the brief's bundled check; it is not
   a proposed repository module. No options or proof escapes were added.

8. **Conclusion-shaped content and enclosure plausibility — PASS with N1/N2.** The docstring's initial
   box, ODE, open existence interval, local uniqueness and finite-time eccentricity bounds agree with the
   formal proposition. The only premise is the initial box. No torus existence, all-time stability,
   closeness to the original N-body flow, or bound on missing planets is concluded. The chosen intervals
   contain all three full-precision SR-4(e) float ranges, with lower/upper margins respectively
   `(0.00068,0.00088)`, `(0.00032,0.00046)`, `(0.00058,0.00094)`. They plausibly repair the plan's
   narrower Saturn/Uranus examples, but their enclosure remains to be proved.

## Handoff, remaining checks, errata and deviations

- **Files:** only `docs/explorations/sjsu-g2-audits/STMT-AUDIT-1.md` added; the pre-existing generator
  import change was preserved. No commit or freeze was made.
- **Approach:** compare literal source contracts and owner decisions; independent exact-data parsing,
  rational symmetry/initial-domain/value checks; one capped elaboration of the generated statement.
- **Axioms/proof status:** `sjsu_secular_confinement` has no theorem body in the audited proposal. The
  generated check establishes `example : (proposed statement) → True`, and separately kernel-checks
  `terms_length`; it does not establish the proposed statement. No `#print axioms` result for the
  proposed confinement theorem exists in this audit. Its eventual provider must be audited and checked
  for axioms before sealing. No confinement proof or N6 enclosure was accepted by this typecheck.
- **Lint/build scope:** did not run `scripts/lint_sources.sh`, a targeted Lake build, or a separate axiom
  probe. The specific brief permits only the displayed generated-check Lean invocation and says
  “no other lean/lake commands.” Full source lint calls `scripts/abi_hashes.py`, which itself invokes
  `lake env lean` and writes an ABI scratch file. The brief's narrower instruction therefore supersedes
  the general pre-handoff build/lint rule for this report-only audit. No repository Lean was edited.
- **Uncertainties:** no phase-1 producer or arb computation was rerun; the tube-eccentricity and Q-radius
  feasibility numbers remain phase-1 evidence, not newly certified bounds. The reported SR-7 computation
  itself acknowledges float summation without directed rounding. The eventual proof must establish
  initial-box inclusion, enclosure and all confinement hypotheses without using those numbers as axioms.
- **Suspected source defects:** no new defect found in either frozen definition or the pinned dataset.
  N1 is an overclaim in our proposal, not an erratum in SLG13/GLS17. The plan's stale exact-real-form
  choice and insufficient Saturn/Uranus tube examples are already identified by SR-1/SR-4(e) and are
  superseded here by D75 and the proposal's wider intervals. No new primary-literature erratum is asserted.
- **Deviations introduced:** none to the statement, definitions, data, normalizations or sources.

READY g2-stmt-audit-1
