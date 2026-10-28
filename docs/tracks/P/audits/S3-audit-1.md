# S3 independent package audit 1

Date: 2026-10-28. **Overall verdict: FAIL — slice completeness and literal node contract (F1–F2).**
The submitted public definition and theorem have the exact signed contracts, and their
proofs pass the checks recorded below. The assigned graph slice is incomplete: one
quantitative internal obligation is absent, and the signed export is narrower than its
literal blueprint node. This is not a counterexample to `sb_s`.

## Scope and authority

- Worktree: `/root/code/KAM-inp-p14-s3`; HEAD
  `b1f2c0aead0d35981535db61e86918a86275dea6`; comparison `inp` at
  `d1a02150c8e815febce9e0fade2dd194d5ee7795`.
- Audited only `KAM/Planetary/SecularBox/Region.lean` (174 lines), SHA-256
  `6cc03cebc12ad40bafaf7bbc29bc98294e9e6cce675ab6907704200c8d59a600`.
  The full `git diff inp...HEAD` also adds `SecularBox/Chart.lean` (143 lines).
  Chart/S1 and Numerics/S0 are dependencies, not newly audited packages here.
- Read `AGENTS.md`, PLAN, DECISIONS, the package audit brief, `S3-handoff.md`,
  track-P statement (especially lines 578–638), relevant frozen definitions and the
  two downstream secular-box theorem anchors; P14 design row S3, node table,
  signature appendix and both design audits; blueprint p14b lines 175–193 and
  the corresponding graph packet records.
- Compared the live `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`,
  SHA-256 `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.
  `sb_sdef` is at lines 371–377 and `sb_s` at lines 435–440.
- The user's exact report destination overrides the generic brief's main-worktree
  destination. No repository source, frozen file, manifest, generated file or git
  state was changed. The pre-existing untracked handoff was preserved.

S3 is an ordinary infrastructure slice, not a provider or seal package. Provider/frozen
export equality and frozen seal-body probes are therefore not applicable. Neither
`secularBoxSafety` nor `secularBoxAtCitedMasses` is proved or seal-ready by this slice.
Both remain outside this audit's proof-closure claim.

## F1 — Medium, blocking: quantitative radicand obligation missing

Blueprint `blueprint-P/parts/p14b-secular-box.tex:186` states:
“the radicand of $\rho_i$ exceeds $\frac{99}{100\,\Lambda_i}$.”
Line 190 (`stepP:p14:sb-S-1`) also requires
`1 - Γ_i / (2 Λ_i) > 99/100`. The graph packet
`docs/graph/P/packets/P-p14b.nodes.md`, records `bpP:p14:sb-S` and
`stepP:p14:sb-S-1`, retains these literal conclusions. The downstream
`stepP:p14:sb-sm-2` edge from `sb-S` explicitly cites the radicand bound.

Both design audits deliberately allow the narrow exported signature only with the
qualification “quantitative intermediate radii/radicand are internal Region obligations”
(`DESIGN-P14-design-audit-1.md:215`; `DESIGN-P14-design-audit-2.md:77`).
The design's node table maps both nodes to Region (lines 226–227).

Region lines 107–109 apply `sb_chart` and immediately discard its first conjunct,
which gives only *positive* radicand. Lines 111–114 establish Γ/Λ < 1/50 and
k > 49/50, but never establish the 99/100 numerator margin or its division by Λ.
Neither the private helper's result (lines 96–103), the rest of its proof, nor
`sb_s` (lines 126–172) contains either missing inequality. The separately established
radii at lines 144–155 do satisfy the intended internal radii obligations.

Thus exact signature agreement passes, while full graph-node completion fails under
AUDIT FOCUS (b). This is an omitted proof obligation, not a false inequality or a
pinned-source erratum. Positivity from S1 is strictly weaker than the quantitative bound;
its round-2 addition does not discharge F1.

Requested repair: retain an internal proof, under the existing S membership premises, of

```lean
(99 / 100 : ℝ) < 1 - secularGamma w i / (2 * fast w.2 i)
(99 : ℝ) / (100 * fast w.2 i) <
  (1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i
```

Use `0 < fast w.2 i` and `50 * secularGamma w i < fast w.2 i` to clear
positive denominators. Preserve the signed public signatures; no added premise,
resource override or source edit is required. A source inequality being easily derivable
does not constitute a Lean receipt for an assigned internal obligation.

## F2 — Medium, blocking under the current literal-node audit focus

The exported `sb_s` at Region lines 126–130 exactly matches the signed contract, but
it does not state the literal conclusion of `bpP:p14:sb-S` at blueprint line 186:
it omits the quantitative radii, the radicand margin, and the explicit ellipticity
clauses. The radii are genuinely proved internally, while F1 identifies the missing
quantitative radicand proof. Those facts are distinct from what the export states.

The design audits expressly accepted keeping intermediate radii/radicand internal.
The current AUDIT FOCUS (b) is stricter: “an exported lemma named after a graph node
must state that node's literal conclusion”; permission for internal *steps* does not
make the exported parent node's literal clauses available. Hence exact-signature
requirement (a) and literal-node requirement (b) conflict for the supplied `sb_s`
contract. The implementation has not changed the signature; this is a design-contract
mismatch exposed by the current audit, not a prover-introduced premise or a false theorem.

The orchestrator must reconcile the signed export/node mapping with the full source
conclusion (for example, approve a full geometry companion contract and map the node
accordingly). Do not silently enlarge or replace the signed declaration in an audit.
Even if the earlier design's internal-clause convention is explicitly retained, F1
still independently prevents a complete-slice verdict. No consumer may project the
omitted clauses from the current `sb_s` export.

## Node and declaration ledger

Names below are in `KAM.Planetary`; private names are source-level spellings.

| Node / role | Declaration | Verdict | Evidence |
|---|---|---|---|
| `bpP:p14:sb-smooth#data` | `sb_sdef` parameter, `sb_s` section data | PASS | Exact Saturn parameter; theorem assumes the prescribed closed interval. No μ premise needed for geometry. |
| `bpP:p14:sb-Sdef` | `sb_sdef` | PASS | Exact inequalities and whole-carrier definition; openness proved by `sbRegion_isOpen`. |
| `bpP:p14:sb-S` | `sb_s` | FAIL | Exact signed type and sound proof; missing internal radicand (F1), narrower exported node conclusion (F2). |
| `stepP:p14:sb-S-1` | internal `sbRegion_planet` | FAIL (incomplete) | Γ≥0, Γ<Λ, k>49/50 proved; numerator margin >99/100 absent. |
| `stepP:p14:sb-S-2` | internal `sbRegion_planet` | PASS | Squared eccentricity identity and strict k bound give e<1/5; Jacobian >4/5. |
| `stepP:p14:sb-S-3` | internal `sb_s` | PASS | Explicit upper/lower radii, reverse triangle inequality, both index orders and positive individual radii. |
| Continuity | `sbRegion_continuous_fast` | PASS | Coordinate projection. |
| Continuity | `sbRegion_continuous_slow_snd` | PASS | Coordinate projection. |
| Continuity | `sbRegion_continuous_slow_fst` | PASS | Coordinate projection. |
| Continuity | `sbRegion_continuous_gamma` | PASS | Polynomial oscillator action. |
| Continuity | `sbRegion_continuous_axis` | PASS | Division by fixed mass, followed by squaring; continuous for every fixed mass, including zero under Lean's total division. |
| Openness | `sbRegion_isOpen` | PASS | Exact finite-intersection identity over Fin 2 and strict continuous inequalities. |
| Physical-coordinate bridge | `sbRegion_bodyVector_ellipsePhase` | PASS | Literal frozen flattening/unflattening identity, componentwise. |
| Pointwise geometry helper | `sbRegion_planet` | PASS for its stated type | Valid mass/action premises, ordinary S1 supplier, eccentricity/Jacobian/radius conclusions. F1 is missing assigned work, not an unsound helper. |

The short name `sb_s` denotes the prescribed signed helper. No additional public
theorems, instances, structures, abbreviations or auxiliary definitions are introduced.

## Definition classification and proof review

`sb_sdef` is the sole new definition: an exposed noncomputable set predicate on all
`Phase (2+2)`. Its body is byte-for-byte the signature definition. It constrains precisely
positive fast actions, 50Γ<Λ and the four strict semimajor-axis endpoints, and imposes
no condition on the fast angles. It uses the frozen `secularGamma`, `secularAxis` and
`jupiterSaturnWeights`, without a chart replacement, selected branch or junk fallback.
At Saturn zero the Saturn axis is zero by total division, so the region is empty;
the body remains the exact specified inequalities. The geometry theorem uses only the
positive Saturn interval, where all relevant masses and actions are positive.

The other new declarations are theorems. Their hypotheses supply source data and
standing geometry, not the sought conclusions. In particular Γ≥0 is proved from
squares; ellipticity is derived before invoking S1; positivity of the axis is proved
from positive action/mass; and `NoCollision` is the literal frozen predicate. The
finite two-planet case split covers both off-diagonal pairs. No dimension, norm,
carrier, quantifier order or constant dependence is changed in either public signature.
The upper Saturn endpoint and some axis bounds need not be used in the proof; this
neither strengthens premises nor changes the signed result.

## Independent validation receipts

All Lean/Lake commands below ran serially in this worktree with
`LEAN_NUM_THREADS=1`; `nice -n 5` applied to each Lean invocation, including the
build wrapper's child and lint's inherited subprocess priority. No heartbeat,
recursion-depth or synthesis-budget override was used. The compile gate wait was
allowed to finish.

1. Targeted gate build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s3 KAM.Planetary.SecularBox.Region
   [inp-gate] slot 2 acquired 18:25:36 for KAM.Planetary.SecularBox.Region
   ✔ [9099/9099] Built KAM.Planetary.SecularBox.Region (36s)
   Build completed successfully (9099 jobs).
   exit 0
   ```

   This is the targeted Lake job graph, not a clean/full-library rebuild. No warnings.

2. Signature, definition, axiom and root-shadow probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S3Audit1.lean
   'KAM.Planetary.sb_sdef' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_s' depends on axioms: [propext, Classical.choice, Quot.sound]
   root sb_sdef: false
   root sb_s: false
   exit 0
   ```

   The probe copied the live signed definition under `expectedRegion`, checked
   `expectedRegion saturn = sb_sdef saturn` by `rfl`, copied the exact signed theorem
   telescope under a fresh name and proved it by `exact KAM.Planetary.sb_s saturn hs`.
   Independent text extraction also returned `True` for definition-body and full
   theorem-telescope identity. No admitted signature file was imported. The root-name
   test queried Lean's actual environment. An initial probe without that test also
   exited 0 with the same two axiom lists. The reported stale Covariance artifact did
   not recur in these independent runs.

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Region
   replaying KAM.Planetary.SecularBox.Region
   exit 0
   ```

   One invocation, auditing the sole in-scope lemma module; there is no provider.
   Output was captured in scratch and copied here before cleanup.
4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (824 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole diagnostic is the generated-root exception explicitly permitted by the
   audit brief. No regeneration was performed. The lint's ABI probe ran only after
   kernel replay had terminated; all other source checks passed.


5. Static/protected checks:

   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   - `git diff --check inp...HEAD`: empty, exit 0.
   - Forbidden-token/override/EuclideanSpace scan of Region: no matches (`rg` exit 1).
   - Unicode line scan: 174 total lines, maximum 98 characters; no line exceeds 100.
     Module header, copyright, public imports, module docstring and exposed public
     section are present; no file-cap issue.
   - `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-p14-s3 KAM.Planetary.SecularBox.Region`:
     `short-name check OK (no reused public short name)`, exit 0. An independent
     `rg` scan found no other KAM declarations of `sb_sdef` or `sb_s`.
   - Recursive source import traversal: 53 KAM modules, no provider or frozen theorem
     import. All 48 imported frozen modules are definitions marked `SEALED` in the
     manifest. Thus no DRAFT_SORRY theorem supplies a proof premise.

## Uncertainties, errata and deviations

No counterexample to the submitted Lean theorem, invalid axiom dependency, or suspected
pinned mathematical-source defect was found. F1 is the implementation's deviation from
the complete blueprint/graph obligations and contradicts the handoff's “none” claim
for deviations. F2 records the earlier design convention's mismatch with the current
literal-node audit requirement; the original signed interface itself was preserved.
F1 needs an internal proof receipt; F2 needs explicit contract/mapping reconciliation.
S0/S1's independent audit status is inherited from the scope instructions rather than
re-certified here. This report makes no downstream regularity, flow or frozen theorem
closure claim.

Workflow memory was consulted only to orient the report/scratch-only audit and serialized
validation; all package facts and receipts above were independently checked live.

Final cleanup: removed the audit probe and its two captured logs from `.lake/abi-scratch/`.
Final report validation found no pending checks; `git diff --check` passed. The only
untracked repository files are this report and the pre-existing S3 handoff.
