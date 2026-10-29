# P5-LO independent package audit 1

Overall verdict: **PASS WITH NOTES** for the P5-LO slice in
`KAM/Planetary/PGAssembly/Lower.lean`. No statement, definition, proof, or local hygiene defect
was found. The generated-root lint exception and the scope of the graph-step implementation
are recorded below. This is an infrastructure-package verdict, not a seal of
`KAM.Planetary.properlyDegenerateKAM`: that frozen anchor remains `DRAFT_SORRY`.

## Scope and authority

Audited HEAD `789cf69a429ae4c70335f70955db28ce9be7eb87`, compared with branch `inp`
(`bea4e8e486c920ad0f51758913e31756dd9e9554`) using `git diff inp...HEAD`.
Git reports multiple merge bases and selects
`b5e58ec5e766134ead4e306f3ed3c4dc0da81acd`; this audit uses that requested three-dot
comparison without silently substituting a two-dot diff. The full diff contains nine new
Lean files, 1,499 lines: Lower, six ActionBudget modules, and two CellTransfer modules.
The dependency diffs were inspected as context; the implementation verdict covers **only
Lower.lean**, as the handoff's AUDIT FOCUS requires. P5-CT and P5-BU are separate packages.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, P5-LO handoff, the P45 design
(in particular rows 206–209, 224, 508 and the assembly/consumer discussion), design audits
1–4, the shared signatures, P Part 5 lines 290–298 and the corresponding P-p5 graph packet,
the track-P statement, frozen P-G and its relevant definitions. Read the actual upstream
interfaces and definitions used by Lower, including PGData, admissible, checkedCore,
pgActionDomain, pgD0, rawUnion, kset, outputRepresentative, cell_transfer, budget,
volume_pgActionDomain, and disc_measure.

The user's exact report destination overrides the generic brief's MAIN-worktree destination.
Only this report was added to tracked-source locations; temporary checks/logs were confined
to this worktree's `.lake/abi-scratch/` and removed after recording the results. No git
state-changing command, generated-root repair, frozen edit, or dependency edit was made.
The untracked handoff present at entry was left alone.

Input SHA256:

| Input | SHA256 |
|---|---|
| Lower.lean | `e8347a4324d4a97ec4447d96e25376775d511537757c85d5c165414825da8ed7` |
| P45-LEAN-DESIGN.md | `a1d2cd226b6b2f6b668f2712e66d6191a9fd6ab4c03ddc5183539f92c72d5dbf` |
| `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` | `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304` |

## Declarations and node coverage

All names in the table are in `KAM.Planetary`. Locators refer to Lower.lean unless stated.
The two definition declarations including bodies, and the complete lower theorem telescope
and conclusion before `:=`, are byte-identical to shared signatures lines 1225–1234.
Fresh elaboration also checked their definitional equality and theorem-type agreement.
There is no unsigned public export named after a graph node.

| Node / role | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p5:lower#constant` | `pgLoss`, 34–36 | PASS | Exact printed three-term loss, depending only on d; no r or mu dependence. |
| `bpP:p5:lower` | `lower`, 120–245 | PASS | Exact signed conclusion, full admissible range, positive data-only loss constant; no extra premises. |
| `stepP:p5:lo-setup` | local `hvol`, `hcell`, 148–160 | PASS, route note | Uses cell_transfer with B=pgD0, proved sigma compactness and identity inclusion; disc_measure supplies the exact factor and disc volume. Direct lower-bound route avoids the complement identity and its separate location argument. |
| `stepP:p5:lo-bad` | private `lo_core_bad`, 43–89; `lo_ell_pow`, 96–118; local `hm`, `hXm`, `hDvol`, 186–213 | PASS | Collar plus one-scale Diophantine bound supplies the checked-core loss; shell width is exactly r²/2−3λ₁, yielding 6bκ₁√r by Bernoulli. These bounds are combined locally rather than exported as a graph-named theorem. |
| `stepP:p5:lo-lost` | local `hQvol`, `hsplit`, `hDR`, 164–184; `hRlow`, `hprod`, `hfin`, 215–245 | PASS | The unit angle cell has volume one. budget bounds the missed portion; the covering inclusion yields the representative lower bound. Nonnegative-factor multiplication yields exactly the sum of the three losses. |
| `bpP:p5:rstar`, final measure shrink; `bpP:p5:order` | `finalRadius`, 247 | PASS | Exact signed minimum of the preliminary radius and the squared reciprocal loss bound, chosen from d alone. Positivity and finalRadius≤pgRstar were independently elaborated. The remaining preliminary-radius/assembly responsibilities belong to their owners. |
| angle-volume helper | private `lo_volume_unitCube`, 38–40 | PASS | Actual product Lebesgue measure of the half-open unit cube, including dimension zero. |
| elementary combination helper | private `lo_prod_ge`, 92–94 | PASS | Nonnegative losses whose sum is at most one give the required product bound; all guards are discharged in lower. |

The assigned slice is complete under the design's local-step convention (design line 436).
The source proof's complement-based setup is replaced by the direct lower-bound calculation;
its unused intermediate complement identity is not separately formalized. The two cell-volume
identities, checked-core loss, shell loss, and lost-tori budget needed for the literal signed
conclusion are all present. Graph bookkeeping should describe this route instead of claiming
that the complement identity itself was exported. No assigned unsigned export weakens a
literal source conclusion.

The blueprint's lower bound is preserved; the signature additionally asserts positivity of
pgLoss and holds already below the preliminary pgRstar. Downstream signed strictness uses
this bound after r<finalRadius, and signed Main uses finalRadius as its final data-only
radius. The shrink preserves admissibility via finalRadius≤pgRstar and makes the relative
lower coefficient positive. There is no consumer mismatch introduced by these declarations.
Strictness/Main implementation files are absent here; their future proofs and frozen
assembly are outside this audit.

## Definition and hypothesis classification

There are exactly two new public definitions and no new abbrev, structure, instance, or
public helper theorem besides lower.

- `pgLoss`: intended arithmetic constant on its entire carrier PGData a b. Connected,
  nonempty open V and boundedness give 0<(volume V).toReal<∞ through volume_V_pos and
  d.hVb; division by zero or ENNReal.toReal's infinity fallback is not used. The selected
  analytic/scaling constants come from existing proved existence theorems, not added inputs.
- `finalRadius`: intended data-only numerical minimum on the entire PGData carrier.
  lower proves pgLoss>0, so its reciprocal denominator is positive; rstar proves the
  preliminary radius positive. No junk branch, surrogate object, or circular dependence
  on this radius is introduced.

PGData contains the frozen source data, geometry and analytic hypotheses, not a KAM
conclusion. lower takes only d, followed by arbitrary r,mu and their existing admissible
proof. The latter contains the original five smallness inequalities and no measure bound.
The private helpers take only typing/scalar data and their advertised elementary guards,
or PGData/admissibility. All hard estimates are proved or supplied by upstream theorems;
none is assumed as a local instance or extra bundled field.

The real/ENNReal conversions were checked explicitly: volume V, volume checkedCore and
volume D have finiteness proofs before conversion. An infinite representative is handled
separately, as is a negative lower-bound coefficient (ofReal=0). In the remaining branch,
C√r≤1 bounds all three nonnegative losses so the multiplication directions are valid.
The final common factor is exactly (2π)^(a+b), and the disc action radius is r²/2.
No norm change, carrier substitution, or missing period factor was found.

## Independent validation

All Lean/Lake invocations initiated by this audit were serialized, with LEAN_NUM_THREADS=1
and nice -n 5. No heartbeat, recursion-depth or synthesis-budget override was used.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5lo KAM.Planetary.PGAssembly.Lower
   ```

   Exit **0**. Output began `[inp-gate] slot 1 acquired 22:05:06 for KAM.Planetary.PGAssembly.Lower`
   and ended `Build completed successfully (9396 jobs).` Dependency warnings were replayed;
   no Lower.lean diagnostic was emitted.

2. Exact signed-type/body and consumer-radius probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5LOAudit1.lean
   ```

   Exit **0**. Probe imported only Lower, copied the signed theorem under a fresh name
   with body `by exact KAM.Planetary.lower d`, and checked
   `example : type_of% @copied_lower := @KAM.Planetary.lower`.
   Copied signed definitions were compared with pgLoss/finalRadius by rfl.
   Additional examples proved 0<finalRadius and finalRadius≤pgRstar.
   This is an infrastructure package, so a provider=frozen-type probe and frozen seal-body
   probe are **not applicable**; lower is not presented as a replacement for frozen P-G.

   Complete axiom output from the same probe:

   ```text
   'KAM.Planetary.pgLoss' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lower' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.finalRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation for the only assigned lemma module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Lower
   ```

   Exit **0**. Complete output: `replaying KAM.Planetary.PGAssembly.Lower`.

4. Full source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the generated-root exception expressly permitted by the audit brief.
   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (961 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No substantive lint failure occurred. KAM.lean was not regenerated.

5. Static/protected-path checks:

   ```sh
   git diff --check inp...HEAD
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   ```

   Both exit **0**, with no diff/check output; both repeat the multiple-merge-base warning
   recorded above. Frozen and generated protected paths are unchanged.
   Lower has **251 lines**, maximum **100 Unicode characters** per line. Module header,
   copyright/authors, public imports, docstring, public section and exposed definition bodies
   are present. No banned token/override or EuclideanSpace occurs. Its public names are
   unique project declarations, scoped under KAM.Planetary; no reused helper short name or
   harmful root shadow was found.

   A recursive local-import scan found 350 KAM modules, **no provider module and no frozen
   theorem module**. All 55 imported frozen-definition anchors have manifest state SEALED.
   In particular no DRAFT_SORRY theorem is imported directly or transitively.

## Notes, errata and remaining scope

No new suspected pinned-source or blueprint defect was found in this slice. The known
CP10 normalization correction is retained rather than reintroduced: Part 5 line 334(5)
quotes “replacing epsilon by sqrt(2 check-c2) epsilon”; the current frozen normalization
uses the disc action radius r²/2 and hence the shell-loss coefficient 6bκ₁. Lower uses
precisely that coefficient. This is a previously documented correction, not a new source
claim independently checked against the PDF in this audit.

The alternate direct measure argument described above is the only local proof-route
variation. It does not change a signed statement or add a hypothesis. The source graph's
NOT_STARTED labels are bookkeeping, not evidence against the proof; no graph updates were
made in this report-only audit. Dependency-package acceptance (including P5-CT round 2),
strict upper measure, whole-torus deletion, Main and provider completion remain separate
obligations. Nothing here seals the still-unproved frozen headline.
