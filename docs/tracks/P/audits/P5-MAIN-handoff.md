# P5-MAIN prover handoff (branch inp-p5main, a454ffb6; contains P5-ST (in audit), P5-LO, P5-CT, P5-BU, P5-FAM; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/PGAssembly/Main.lean` (~150 lines). Nothing else touched.

**Declarations**
- `KAM.Planetary.main` (signed, verbatim telescope; nodes `bpP:p5:main`, `stepP:p5:mn-const/-given/-set/-meas`,
  and `bpP:p5:order` which needs no theorem).
- `KAM.Planetary.main_of_data (d : PGData a b)` (unsigned helper, same conclusion for bundled data; `main` is
  `main_of_data ⟨…all binders…⟩`).
- `KAM.Planetary.ofReal_mul_lt_of_slack` (unsigned: ENNReal strict lower slack).

**Approach:** rStar = `finalRadius d`, C = `max (pgLoss d + 1) Cw` (Cw from `frequency_bounds`), c = `2*pgTau a b+2`.
Given r, mu: `admissible d (pgRstar d) r mu` via `finalRadius ≤ pgRstar`. S = `kset d r mu h (pgD0 d r mu \ B)`
with B from `strictness`. Measurability and cylinder inclusion from `cell_transfer`; torus data from
`torus_conv` (`PGFamilySpec`), Diophantine clause from `cp10_isDiophantine` (gamma1, gamma2 > 0, tau = n+1 > n),
frequency bounds from `frequency_bounds` (blockFast/blockSlow = fast/slow by rfl). Strict lower bound: the
coefficient `1-(pgLoss+1/2)√r` > `1-C√r`, via `ofReal_mul_lt_of_slack` (case split on sign inside).

**Checks**
- Gate build `KAM.Planetary.PGAssembly.Main`: success, no warnings in Main.lean.
- `#print axioms KAM.Planetary.main`: `[propext, Classical.choice, Quot.sound]` (same for the two helpers).
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; only note is
  "KAM.lean is out of date" (generated, not edited per rules).
- No lines > 100 columns; no heartbeat options; no sorry.

**Provider term (P5-PROV):** import `KAM.Planetary.PGAssembly.Main` (not the frozen theorem) and state
`theorem KAM.Provider.Planetary.properlyDegenerateKAM` with the frozen telescope verbatim (inside namespace
`KAM.Planetary`-style opens as in the frozen file); proof body: `KAM.Planetary.main ha hb V hV hVc hVb W hW hVW
hboundary r0 mu0 B hr0 hmu0 hB H0 P P0 Omega beta hP hperiod hfreq hBNF htorsion hsymm` (equivalently
`@KAM.Planetary.main`; `{a b}` implicit match). Types are identical.

**Uncertainties:** none. **Errata / deviations:** none new.

AUDIT FOCUS (SEAL-KEY AUDIT for the frozen anchor KAM.Planetary.properlyDegenerateKAM, manifest id planetary.properlyDegenerateKAM.v1, frozen file KAM/Frozen/Planetary/Theorems/ProperlyDegenerateKAM.lean; provider stub KAM/Provider/Planetary/ProperlyDegenerateKAM.lean, design row P5-PROV 'provider wrapper to the exact frozen type; no theorem anchor import'): design docs/tracks/P/design/P45-LEAN-DESIGN.md row P5-MAIN (main, literal telescope, ENNReal strict lower slack; P5-ST, P5-FAM, P5-CT, frozen Kolmogorov definition) and its node table incl. bpP:p5:main, stepP:p5:mn-*, bpP:p5:order; P45 design audits; signatures /root/code/KAM-inp/.drafts/design/P45Signatures.lean. (1) Compile an exact-type probe in a scratch file outside KAM/: example : type_of% @KAM.Planetary.properlyDegenerateKAM := @KAM.Planetary.main, and report the result. (2) PROSPECTIVE seal: in a scratch copy only (never edit frozen files, provider stubs or the manifest), copy the complete frozen telescope and replace the body with the handoff's term (by exact KAM.Planetary.main ...), confirm it elaborates and #print axioms shows only propext, Classical.choice, Quot.sound. (3) Confirm main's binders match the frozen telescope exactly and in order, no added premise, and the import chain of Main contains no provider or frozen-theorem module. (4) Audit Main.lean in full; Strictness.lean (P5-ST) has its own audit. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
