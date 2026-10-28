# Independent package audit: N89-P2

**Overall verdict: PASS WITH NOTES.** All nine public declarations in
`KAM/Nekhoroshev/Poschel/Frequency.lean` satisfy the Revision-2 design contract.
The targeted build, fresh theorem-application probes, axiom checks, and kernel replay pass.
Lint's sole failure is the expressly permitted stale generated root. No mathematical or
implementation blocker was found.

**Frozen-anchor verdict: not applicable.** This package proves infrastructure, exports no
`KAM.Provider` theorem, and seals no frozen anchor. This verdict does not certify N-HEAD-C,
Part 9's full theorem, or campaign/root closure.

## Scope and authority

Audited worktree: `/root/code/KAM-inp-n89p2`, HEAD
`d43b6518984ca2e0523666176c4b0643b0ddc98f`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local N89-P2 handoff.
The user's explicit output location supersedes the generic brief's main-worktree destination.
Only this report is a repository edit; the temporary probe was confined to `.lake/abi-scratch/`.

Read the N track statement, blueprint Part 9 (especially lines 54–68), the Revision-2
`docs/tracks/N/design/N89-LEAN-DESIGN.md` (P2 ownership, local restriction warning,
maximum semantics, Appendix A), and both design audits under `docs/tracks/N/design/`.
The handoff's `audits/DESIGN-N89-...` paths are stale; the reports are under `design/`.
The external signature file is
`/root/code/KAM-inp/.drafts/design/N89Signatures.lean`, SHA-256
`01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88`,
matching design audit 2's reviewed revision.

Examined the required `git diff inp...HEAD`: it reports multiple merge bases and selects
`46bfbcb5e40e5540583d781ad736c36bd2abd4ab`. Its four added files are the inherited
P1 CoverParams/Setting/Elementary and P2 Frequency. Also examined
`git diff inp-n89p1...HEAD -- KAM/Nekhoroshev/Poschel/Frequency.lean`:
Frequency is the sole P2 target and adds 414 lines. The unrestricted comparison against
`inp-n89p1` also includes unrelated intervening base development; it is not attributed to P2.
P1 and unrelated packages were not re-audited.

Read the actual frozen `frequencyMap` and `realPart` bodies, local tube/Hessian/quasi-convexity
predicates, Euclidean norm comparisons, and the holomorphic-regularity bridge used here.
The real map is genuinely the frozen real gradient, with complex derivatives identified by
proof, not by a new assumed bridge.

## Declaration and node verdicts

Names below have prefix `KAM.Nekhoroshev`; line numbers refer to Frequency.lean.
The five public theorem headers, structure fields, and three definition bodies were
mechanically compared with the signature file: **9/9 identical**. This includes omega0's
entire conclusion after its local `let B := ...`.

| Node / component | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| `bpN:p9:m-le-M` | `m_le_M` (197) | PASS | No assumed m≤M; nonempty P and n≥2 give a nonzero transverse vector. Nonnegative ell excludes the strict QC alternative. Positive squared length permits cancellation. |
| `stepN:p9:om-max#local-real-regularity` | `local_real_regularity` (245) | PASS | C² and continuous frequency on the arbitrary real tube; exact real/complex Hessian identity. No frozen global-action-ball Data premise. |
| `bpN:p9:omega0`, compact domain | `FrequencyBall` (263) | PASS | Center membership and nonnegative radius strictly below r0 are typing/domain guards, not maximum or continuity assumptions. |
| Same | `FrequencyBall.points` (270) | PASS | Exact closed Euclidean ball, including its boundary and radius zero. |
| Same | `FrequencyBall.maximum` (273) | PASS | Supremum of exactly the Euclidean frequency lengths on points; attainment is subsequently proved. |
| `bpN:p9:ext-compact`, `stepN:p9:om-incl`, `stepN:p9:om-max` | `frequency_maximum` (333) | PASS | Inclusion, compactness, nonemptiness, attained supremum, every-point bound, center lower bound, and M-radius upper bound are all conclusions. |
| `bpN:p9:omega0`, radius guard | `omega0_radius` (379) | PASS | Derives 11≤A from hm and hmM, then 0≤r0/A<r0; no epsilon-dependent premise. |
| Same | `omega0Ball` (391) | PASS | Actual center I0 and radius r0/A, carrying proved guards. |
| `bpN:p9:omega0` | `omega0` (395) | PASS | Exact attained maximum and both stated bounds, with the source constant M r0/A and unchanged quantifiers. |

`m_le_M` is deliberately stronger than blueprint p9:54–56: it omits m>0 and M>0 and
allows ell=0. This is disclosed in Revision 2 and design audit 2, not a silent change.
The proof does not use `Theorem1Setting.hmM` or the positivity of m or M.
No extra premise, widened constant dependence, weakened conclusion, or substituted norm
was found. No `blockBall` declaration appears here; that belongs to P3.

## Definition classification and proof review

- `FrequencyBall`: faithful guarded domain record. Its S parameter fixes the intended
  setting; the record supplies no proof of a hard analytic conclusion.
- `FrequencyBall.points`: faithful explicit Euclidean closed ball on `Fin n → ℝ`.
  The ambient function norm remains the maximum norm.
- `FrequencyBall.maximum`: faithful noncomputable supremum. Every inhabitant supplies
  a nonempty compact ball strictly inside the real tube. Continuity yields a greatest
  image element; `IsGreatest.csSup_eq` identifies the real supremum with that value.
  No empty/unbounded supremum fallback is used, including at radius zero or zero frequency.
- `omega0Ball`: faithful specialization to r0/(11 M/m), with both radius guards proved.

There are no new abbreviations or other user-written definitions. All definitions are
inside the exposed public noncomputable section. Structure-generated operations are ordinary
record constructors/projections.

Reviewed all private proof helpers as well. Holomorphy on the open complex tube gives
real C∞ regularity after scalar restriction and composition with real inclusion; taking
the real part gives C². Local reality is obtained using the zero real angle and s>0.
`real_fderiv` proves equality with the complex derivative using eventual equality on the
open real tube and uniqueness of derivatives. Applied to the coordinate derivatives,
with mixed-partial symmetry, it gives both complex and real Hessian formulas for Dω.
This avoids applying the specialized Part-1 `holo_real_b/c` theorems to arbitrary P.

The m≤M proof explicitly constructs a nonzero vector perpendicular to ω, transfers the
complex Hessian bound to real vectors, applies Cauchy–Schwarz, and cancels its positive
squared Euclidean length. Neither positivity being omitted is smuggled into the proof.

Compactness uses closedness in the actual ambient topology and boundedness via
max norm≤Euclidean length; no EuclideanSpace instance is installed. The M-radius bound
uses a scalar mean-value argument for F·ω along the center-to-point segment, where
F=ω(I)−ω(center). The segment stays in the guarded ball, so local differentiability and
the Hessian bound apply throughout. The F=0 case is separate; cancellation in the other
case uses strictly positive Euclidean length. Thus the bound has M, with no dimension loss.

## Independent checks and exact receipts

Checks were run sequentially with no overlapping Lean checks. The final lint run, build,
probe, and kernel replay used `LEAN_NUM_THREADS=1`; Lean invocations were at nice priority 5.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89p2 KAM.Nekhoroshev.Poschel.Frequency
   ```

   The gate itself executes `nice -n 5 lake build`. Exit **0**:

   ```text
   [inp-gate] slot 2 acquired 07:28:56 for KAM.Nekhoroshev.Poschel.Frequency
   Build completed successfully (3219 jobs).
   ```

2. Fresh probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89P2Audit.lean
   ```

   Exit **0**. Copied all five public theorem headers under fresh names and supplied bodies
   applying the actual exports to their explicit binders in order. No assumptions or options
   were added. Provider/frozen type equality and seal-body probes are inapplicable: no provider
   or frozen theorem is implemented by this package.

   Exact axiom output (one line per public declaration, including the definitions):

   ```text
   'KAM.Nekhoroshev.m_le_M' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.local_real_regularity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.FrequencyBall' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.FrequencyBall.points' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.FrequencyBall.maximum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.frequency_maximum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.omega0_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.omega0Ball' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.omega0' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   An initial audit-harness attempt split omega0's header at the `:=` in `let B := ...` and
   failed to parse. Correcting the scratch extraction to retain the full header resolved it;
   no production change or resource override was needed. The final probe is deleted.

3. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Poschel.Frequency
   ```

   Exit **0**, exact output:

   ```text
   replaying KAM.Nekhoroshev.Poschel.Frequency
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (452 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This is PASS subject to the brief's explicit generated-root exception. The root was not
   regenerated. No overlength, forbidden-token, module, errata-rendering, or anchor error appears.
   A preliminary plain `sh scripts/lint_sources.sh` invocation produced the same output and
   exit 1; the command above is the final resource-constrained rerun.

5. Hygiene and quarantine:

   - Frequency.lean: **414 lines**, maximum line width **100 characters**, no line over 100.
     Copyright, `module`, public interface imports, docstring, and exposed public section present.
   - Token/option scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`,
     or `set_option` in the audited file. No heartbeat/recursion/synthesis overrides.
   - Recursive KAM import inspection: **64 modules**, **no provider**, **no frozen theorem**.
     All **27** imported frozen declarations are manifest-kind `definition`, status `SEALED`.
     Thus no DRAFT_SORRY anchor or other provider is imported, directly or transitively.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**, apart from
     Git's multiple-merge-base warning. These protected paths were not modified.
   - `git diff --check`: exit **0**, no output.
   - `git diff --no-index --check /dev/null docs/tracks/N/audits/N89-P2-audit-1.md`:
     exit **0**, no output.

## Notes, suspected defects, and limitations

No new suspected mathematical source defect, frozen-statement defect, or implementation
deviation was found. No source PDF was independently fetched or re-audited; this is an
implementation-versus-pinned-blueprint/design audit. The stronger m≤M lemma is an already
reviewed, disclosed improvement, not an erratum.

The blueprint p9:67 says “h_R is C² ... (Lemma bpN:p1:holo-real)”. That Part-1 API is
specialized to the frozen global action ball. Revision-2 design lines 120–124 explicitly
warn against applying it on arbitrary P. This implementation supplies the needed local
restriction argument correctly, so there is no unpaid analytic premise here. Treat the
blueprint citation as the mathematical local argument, not literal applicability of that
specialized Lean export.

The handoff's stale design-audit directory locators and moving-branch comparison breadth
are documentation notes only. The permitted root regeneration remains an orchestrator task.
Inherited source deviations in the larger Part-9 setting (including the stronger radius
hypothesis) are recorded in the design; this package neither changes nor resolves those
source-level issues. No claim about Part-8 lattice packages, P3 blockBall, full stability,
or consumer assembly follows from this P2-only audit.

Final ownership: authored only this report at the requested absolute worktree path.
The pre-existing untracked N89-P2 handoff was preserved. No tracked file was edited,
no state-changing Git command was used, and the audit scratch probe was removed.
