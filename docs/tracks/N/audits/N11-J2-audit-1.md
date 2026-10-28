# N11-J2 independent package audit 1

Verdict: **PASS WITH NOTES** for `KAM.Nekhoroshev.transfer_conditional` and **PASS** for
`KAM.Nekhoroshev.slowTube`, with the verification receipts below. The complete assigned
transfer slice is implemented. This is an infrastructure conditional-helper audit, not a seal
of `partialConvex_nekhoroshev` or a proof of the downstream stability propositions.

## Scope and immutable inputs

Audited on 2026-10-28 in `/root/code/KAM-inp-n11j2`, at HEAD
`27261da549f3dd9c8d18d45c9ea2ca66eee65c9f`. Comparison ref `inp` resolved to
`b8e023179635e643629844d102983e478c955c1e`. `git diff inp...HEAD` warns of multiple merge
bases and selects `eedc66febf1e2749337a502351ab1515c1779c15`; the other merge base is
`c198ff11a966d692e9ba3fd91709b4de7a6740d5`. The literal requested comparison was used.
Its complete file/declaration inventory contains Flow (133 added lines), Preimage (327),
Symplectic (400), SymplecticLinear (356), and Transfer (407). Only Transfer receives a mathematical
package verdict, as explicitly required by AUDIT FOCUS; the E1/J1 files are upstream context.

Read the external package-audit brief, AGENTS.md, PLAN.md, DECISIONS.md, the untracked handoff,
both N11 design audits, the current design and signed declarations, Part 11c transfer and its
nonresonant/resonant consumers, the N partial-stability statement and frozen root, and relevant
Setting, RealSystem, Continuation and ODE interfaces. The explicit user report destination overrides
the generic brief's main-worktree destination. No production, frozen, manifest or generated file
was edited. Temporary probes are confined to `.lake/abi-scratch/` and removed after verification.

| Input | SHA-256 |
|---|---|
| `KAM/Nekhoroshev/Partial/Transfer.lean` | `1a0bd2ad9af3ce824c702b3ed5bbe6456451a7a1872ad27aba86a3f637f16d13` |
| `/root/code/KAM-inp/.drafts/design/N11Signatures.lean` | `fe33b7d1689fdfb8ea66242b975d2b44002039fc4aa25378313afc4bd59a8aeb` |
| `docs/tracks/N/design/N11-LEAN-DESIGN.md` | `f48f720851c9b81326f9f6a24d5a42c8346283c41cf1d6a48285ce0e311fdafb` |
| `blueprint-N/parts/p11c-partial-stability.tex` | `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea` |

The design's N11-J2 row is line 366; node allocation is lines 237–243. Design audit 1's
missing field-periodicity finding was resolved at design level by audit 2. Transfer now actually
consumes the field-periodicity conjunct of `real_system` (351–352, 390–393), rather than scalar
periodicity. Earlier design PASS receipts were not treated as proof receipts.

## Declaration and node ledger

All Lean locators below refer to the fixed Transfer file unless another path is named.

| Source node / object | Lean implementation | Verdict | Evidence |
|---|---|---|---|
| Signed `slowTube` | `KAM.Nekhoroshev.slowTube`, 144–145 | PASS | Entire declaration and body equal signatures 518–519 after whitespace normalization. |
| `bpN:p11:transfer` | `KAM.Nekhoroshev.transfer_conditional`, 331–403 | PASS | Entire statement equals signatures 531–552 after whitespace normalization; no added binder or changed conclusion. |
| `stepN:p11:tr-orbit` | private `transfer_core`, 180–184 | PASS | T2 supplies actual preimage, then `gen_maximal` produces the inner orbit. |
| `stepN:p11:tr-E` | 185–193 | PASS | Nonempty, downward-closed set of prefixes. Explicit outer membership is derivable from conjugation. |
| `stepN:p11:tr-bounds` | 195–210 | PASS | T1 plus actual stopped slow-coordinate witness supplies T3; absolute time bound follows from prefix bound. |
| `stepN:p11:tr-open` | 212–242 | PASS | Actual C1 outer field, local domain membership and `gen_uniqueness` extend each nonterminal good prefix. |
| `stepN:p11:tr-closed` | 244–306, helpers 37–141 | PASS | Compact transverse tail lies strictly in the actual open real domain; periodic continuation rules out finite obstruction; continuity closes endpoint equality. |
| `stepN:p11:tr-concl` | 307–325; 359–403 | PASS | Supremum reaches queried endpoint; three-term norm inequality gives `a+2*d`; negative-time branch preserves all hypotheses. |

There are exactly two new public declarations: the signed definition and theorem above. All
nine other declarations are private proof helpers. There is no unsigned public export pretending
to be a graph-node result, reused public HELPER name or new root-namespace declaration.
The stronger abstract private `transfer_core` omits unused signed assumptions `hd`, `ha`, `hT`;
the public signed surface retains them exactly.

## Binder and semantic audit

Source references: C43–52 means Part 11c transfer statement; C53–61 its proof; C20–25 the
conjugation lemma. Design departures 308–309 explicitly authorize ENNReal time and witnessed
closed slow tubes. TYPING carries source data only; SOURCE means a literal source premise;
there are no STANDING, RULED or EXCESS premises in the expanded theorem inventory.

| Binder or expanded logical input | Bin | Source / meaning |
|---|---|---|
| `n` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `k` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `b` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `R` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `s` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `r` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `t` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `d` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `dx` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `a` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `T` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `H` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `Ht` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `Ψ` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `Nrm` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `F` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `J` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `y` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `t1` | TYPING | C43–52, extended coordinates and source data; `T : ENNReal` as design 308. |
| `hbR` | SOURCE | Positive block radius; C43–44 and fixed block geometry. |
| `hbw` | SOURCE | Positive slow width; C43–44 and fixed block geometry. |
| `hc.R_pos` | SOURCE | C44 imports the conjugation domains, C20–25. |
| `hc.r_pos` | SOURCE | C44 imports the conjugation domains, C20–25. |
| `hc.s_pos` | SOURCE | C44 imports the conjugation domains, C20–25. |
| `hc.t_pos` | SOURCE | C44 imports the conjugation domains, C20–25. |
| `hc.r_le` | SOURCE | C44 imports the conjugation domains, C20–25. |
| `hc.t_le` | SOURCE | C44 imports the conjugation domains, C20–25. |
| `hc.outer.InClass.differentiableOn` | SOURCE | C44 imports real holomorphic periodic Hamiltonians, C20–25; Setting 96–97; Weighted/Norm 42–44. |
| `hc.outer.InClass.periodic` | SOURCE | C44 imports real holomorphic periodic Hamiltonians, C20–25; Setting 96–97; Weighted/Norm 42–44. |
| `hc.outer.extReal` | SOURCE | C44 imports real holomorphic periodic Hamiltonians, C20–25; Setting 96–97; Weighted/Norm 42–44. |
| `hc.inner.InClass.differentiableOn` | SOURCE | C44 imports real holomorphic periodic Hamiltonians, C20–25; Setting 96–97; Weighted/Norm 42–44. |
| `hc.inner.InClass.periodic` | SOURCE | C44 imports real holomorphic periodic Hamiltonians, C20–25; Setting 96–97; Weighted/Norm 42–44. |
| `hc.inner.extReal` | SOURCE | C44 imports real holomorphic periodic Hamiltonians, C20–25; Setting 96–97; Weighted/Norm 42–44. |
| `hc.hol` | SOURCE | C44 imports the actual holomorphic, real canonical conjugating map, C20–25; Setting 131–147. |
| `hc.maps` | SOURCE | C44 imports the actual holomorphic, real canonical conjugating map, C20–25; Setting 131–147. |
| `hc.real` | SOURCE | C44 imports the actual holomorphic, real canonical conjugating map, C20–25; Setting 131–147. |
| `hc.canon` | SOURCE | C44 imports the actual holomorphic, real canonical conjugating map, C20–25; Setting 131–147. |
| `hc.identity` | SOURCE | C44 imports the actual holomorphic, real canonical conjugating map, C20–25; Setting 131–147. |
| `hN.continuous` | SOURCE | C44: a norm dominating the max norm; Stability/Setting 132–138. |
| `hN.map_zero` | SOURCE | C44: a norm dominating the max norm; Stability/Setting 132–138. |
| `hN.add_le` | SOURCE | C44: a norm dominating the max norm; Stability/Setting 132–138. |
| `hN.neg` | SOURCE | C44: a norm dominating the max norm; Stability/Setting 132–138. |
| `hN.smul` | SOURCE | C44: a norm dominating the max norm; Stability/Setting 132–138. |
| `hN.norm_le` | SOURCE | C44: a norm dominating the max norm; Stability/Setting 132–138. |
| `hd` | SOURCE | C45–48: nonnegative displacement bound. |
| `hdx` | SOURCE | C45–48: nonnegative slow displacement bound. |
| `hdxr` | SOURCE | C46: strict slow margin dx < inner radius. |
| `ha` | SOURCE | C48: positive a priori drift radius. |
| `hgap` | SOURCE | C48: d+a < inner radius. |
| `hT` | SOURCE | C48: positive finite or infinite time. |
| `hdisp.fast` | SOURCE | C46 (T1): fast displacement in the chosen norm. |
| `hdisp.slow` | SOURCE | C46 (T1): slow displacement in max norm. |
| `hpre` | SOURCE | C47 (T2): exact real preimage with initial fast bound. |
| `hT3` | SOURCE | C48 (T3): only the explicitly conditional helper assumes normal-form confinement. |
| `hF` | SOURCE | C50: arbitrary extension agreeing on the actual outer open domain. |
| `hJ` | SOURCE | C50: source interval is order connected. |
| `h0` | SOURCE | C50: source interval contains zero. |
| `hy` | SOURCE | C50: two-sided derivative equals the supplied extension at every source time. |
| `hI` | SOURCE | C50: initial fast action is the fixed centre. |
| `hx` | SOURCE | C50: initial scaled slow coordinates lie in S. |
| `ht1` | SOURCE | C50: queried endpoint is in the supplied interval. |
| `htT` | SOURCE | C50: absolute queried time is at most T. |
| `hstop` | SOURCE | C50: slow membership only between zero and the queried endpoint. |

Expanded row counts: TYPING 19, SOURCE 44, STANDING 0, RULED 0, EXCESS 0.
Structure-parameter data are included in the typing rows. `hc.outer` and `hc.inner` are each
expanded into holomorphy, unit-angle periodicity and reality; `hc.canon` is the literal
all-linear-functionals bracket identity (Setting 107–110), not a confinement claim.
`ExtOrbit` expands to `IsSolutionIn` of the actual `realWfield` and indicator-restricted real
Hamiltonian, whose two conjuncts are domain membership and the two-sided derivative equation.
`hT3` retains universal scope over every interval and every qualifying inner orbit; its initial
bound and slow-tube premise are antecedents of that source obligation, not extra premises on the
physical orbit. `hpre` supplies an actual preimage, not an arbitrary choice of a formal orbit.
No typeclass parameter or other hidden project assumption is introduced.

Definition classification: `slowTube` is a **literal existential predicate**, not a choice-defined
object or a theorem-shaped substitute for confinement. On its whole carrier, including empty S,
it means exactly `∃ v ∈ b.S, ‖x - b.lam⁻¹ • v‖ ≤ a`. No fallback value or off-domain branch is
introduced. The block scale is the fixed `b.w/b.rB`; positive block inputs make it nonzero in the proof.

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

## Refutation checks and consumer limits

1. **Compactness and domain margin.** The tail is centred at `fastAction x`, not at the wrong
   physical initial action. `IsActionNorm.norm_le` controls the max norm; the fast transverse
   ball has radius `a`, and the slow factor is `cthickening dx Y`, where Y is the continuous image
   of the actual physical interval. This is compact without assuming S closed or bounded.
   At 267–279, every tail point has fast distance at most `a+d < r`, and slow distance at most
   `dx < r` from an actual point of scaled S. Thus the entire compact tail lies in the true
   transverse `polyNbhd b.base r`, not merely a weaker closure. This discharges continuation's
   literal compact-subset obligation.
2. **No assumed physical confinement.** The good set omits an explicit `y ∈ realDom R` clause
   because `hconj` proves it from equality with the inner orbit. At openness, continuity gives
   membership near a good time before uniqueness is applied. There is no circular use of `hF`
   away from its agreement domain.
3. **Supremum and endpoint.** The proof uses right extension and membership of the supremum;
   it does not claim to have independently proved arbitrary topological closedness of E.
   Assuming `Tp ≤ τs`, every time below Tp belongs to a good prefix, so continuation forces
   `Tp = ⊤`, contradicting the finite supremum. Endpoint equality uses continuous functions
   on the closed interval and density of its half-open prefix. The `τs=0` case is separate.
4. **Time reversal.** At 365–403 both fields are negated, T3 is transported through the
   preimage of interval negation, the interval remains order connected and contains zero,
   and the absolute time bound is unchanged. No symmetry of S or Hamiltonian evenness is assumed.
   The zero-time case also follows from the nonnegative branch.
5. **Intended consumers.** C70–73 nonresonant T3 uses integration of the actual remainder field;
   C118–120 resonant T3 uses energy_free. Witnessed `slowTube` gives the strict half-radius
   condition for energy_free when `dx < inner_radius/2`, by its same witness; no closedness of S
   is needed. The final consumer arithmetic uses exactly `a+2*d` in the max norm or `euclid`.
   There are no current production consumers of `transfer_conditional` in this worktree.
   Actual downstream assembly is therefore not certified; T3 must be proved at each later call,
   never forwarded to the frozen root.

Import traversal finds 87 project modules, 23 frozen imports, all 23 individually matched by
manifest path with state SEALED; none is a frozen theorem. There are no provider imports or
DRAFT_SORRY imports in this closure. The D25 root
`nekhoroshev.d25.partialConvex_nekhoroshev.v1` remains DRAFT_SORRY, untouched and unimported by
Transfer; its proof/seal check is outside this helper package and is not marked seal-ready.

## Notes, source defects and deviations

- **N1, nonblocking, expected generated root:** source lint's stale `KAM.lean` exception is
  permitted explicitly by the audit brief. The orchestrator owns regeneration; this audit does
  not edit the generated root.
- **N2, minor blueprint wording:** C56 says “if τ∈E and τ′≤τ then τ′∈E”. Read literally over
  all real τ′ this is false: 0∈E but −1∉E. The missing restriction is `0≤τ′`, or equivalently
  downward closure relative to `[0,t1]`. Independent refutation recheck: E is explicitly
  restricted to `[0,t1]`, so this is a context omission, not a gap in the interval argument.
  Lean 191–193 supplies `0 ≤ τ′` explicitly. Report to the orchestrator; no source repair made.
- **N3, declared design departure:** a witness at distance ≤dx is stronger than mere
  infimum-distance ≤dx when S is not closed. Do not claim these predicates equivalent.
  Design 309 explicitly chooses the witnessed version. Transfer constructs the required witness
  from `b.lam • slowPair (y u)` at 203–205, and intended energy consumption retains that witness.
  Thus no consumer obligation in this slice is lost.
- Unused `hd`, `ha`, `hT` are retained to match the signed statement; they cause ordinary warnings.
  No new pinned-PDF erratum is asserted; pinned-source PDFs and upstream E1/J1 proof packages
  were not independently re-audited here. No implementation deviation beyond the recorded
  witnessed-tube design and internal equivalent good-set formulation was found.

## Independent verification receipts

All audit Lean/Lake invocations use `LEAN_NUM_THREADS=1` and `nice -n 5`, serialized with
no overlap between this audit's build, probe, kernel replay and lint/ABI elaboration.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11j2 KAM.Nekhoroshev.Partial.Transfer
   ```

   Exit **0**. Gate output: `[inp-gate] slot 1 acquired 21:31:39 for KAM.Nekhoroshev.Partial.Transfer`.
   Final output: `Build completed successfully (3241 jobs).` Transfer was replayed successfully;
   its only diagnostics were unused `hd` at 335:5, `ha` at 335:49 and `hT` at 335:79.
   The build also replayed inherited Gradient, Coordinates and RealSystem linter warnings;
   those are not additional Transfer failures.

2. Exact signed-type and definition-body probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11J2Audit.lean
   ```

   Exit **0**, no warnings. The probe copies the entire signed theorem command from the pinned
   signature file, changes only the name to `audit_transfer_signature`, and supplies this body:

   ```lean
   exact transfer_conditional b hbR hbw hc Nrm hN hd hdx hdxr ha hgap hT
     hdisp hpre hT3 F hF hJ h0 hy hI hx ht1 htT hstop
   ```

   A separate `Iff.rfl` checks the full signed `slowTube` defining formula. Mechanical comparison
   independently prints `slowTube whitespace-normalized exact match: True` and
   `transfer_conditional whitespace-normalized exact match: True`, including binder names/order,
   implicit groups and all statement clauses. All explicit theorem arguments are supplied in order.
   The two public declarations and the copied exact-signature theorem print:

   ```text
   'KAM.Nekhoroshev.transfer_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.slowTube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.audit_transfer_signature' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   No `sorryAx` or project axiom appears. No root-provider seal probe applies to this helper-only
   package; the actual D25 frozen root is not claimed proved.

3. Kernel replay, exactly one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.Transfer
   ```

   Exit **0**. Exact output: `replaying KAM.Nekhoroshev.Partial.Transfer`.
   This replays Transfer's private helper proofs as well as its public declarations; upstream
   modules retain their separate audit scopes.

4. Full source lint, including frozen guard and elaborated ABI hashes:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the explicitly permitted stale generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (953 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint failure occurred. No root regeneration was performed. Lint/ABI ran only after
   the probe and leanchecker exited; the environment and lowered priority were inherited by
   lint's internal `lake env lean` invocation.

5. Mechanical hygiene and artifact checks:

   - `git diff --check inp...HEAD`: exit **0**, no whitespace errors (only the recorded
     multiple-merge-base warning). `git diff --check`: exit **0**.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit **0**, empty diff
     (only the recorded multiple-merge-base warning).
   - Full Transfer token scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
     `EuclideanSpace` or `set_option`; 407 total lines, maximum line length **100**.
     Module header, public imports, module docstring and exposed public section are present.
   - Repository-wide declaration lookup finds each public name only in Transfer.
   - Final Transfer SHA-256 is unchanged from the immutable-input table.
   - Temporary `N11J2Audit.lean` was deleted. Final status has only the new audit report and the
     pre-existing untracked `N11-J2-handoff.md`; no tracked edits.
   - Report whitespace check:
     `git diff --no-index --check /dev/null /root/code/KAM-inp-n11j2/docs/tracks/N/audits/N11-J2-audit-1.md`:
     exit **1**, with no diagnostics (the report is a new file versus `/dev/null`).

Closeout: signed type/body fidelity, all seven assigned graph nodes, logical-input audit,
private continuation argument, allowed axioms, targeted build, kernel replay and protected-path
checks pass. Source lint passes all substantive checks and retains only its authorized generated
root exception. **N11-J2: PASS WITH NOTES.** No claim is made that the D25 root is seal-ready.
