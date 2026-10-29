# Independent audit: P11A-P5W

**Verdict: PASS WITH NOTES for the assigned FastSigned wrapper slice.** No blocking
proof, statement, carrier, or consumer defect was found in the audited module.
No frozen anchor is delivered by this package; this verdict does not seal P-FIXED.

## Scope and snapshot

User-specified destination and handoff AUDIT FOCUS control this report, overriding the
generic brief's destination and broader provider checklist. Audited only
`KAM/Planetary/Preparation/FastSigned.lean`, in full, against the signed API and
its imported contracts. P2f and P5 internals are dependencies, not independently
reaudited proof packages here.

- Worktree: `/root/code/KAM-inp-p11ap5w`.
- HEAD: `6f5b73405fbb114f2c7b8a1f6e41bbe2a1f93189`.
- `inp`: `ce5bc0c09a78b36777a59cdb8b93c5e544d380e6`.
- Assigned source SHA-256: `d9fe8930d8ac22d2d4def8c80b58f6cedd961b80cc5855ee9558e4f547fa2afb`.
- Signed authority: `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`,
  SHA-256 `fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the supplied package brief and handoff;
P11A design node table and registry; track-P statement; blueprint
`p11-cp09-preparation.tex:96–114,181`; the amended secular specification,
fast specification and upstream exports; P-FIXED and its phase, Hamiltonian and
Kolmogorov-set definitions. No source repair or git mutation was made.

## Declaration and coverage table

All names below are in `KAM.Planetary`.

| Node / obligation | Declaration and location | Verdict | Reason |
|---|---|---|---|
| Discharge the core's realness premise | `p11SecularHReal_of_spec`, FastSigned:26 | PASS | Only `P11SecularSpec D C` is assumed. Selects its amended h-realness conjunct after the exact real-inclusion ball/norm conversion. Distinct helper name. |
| `bpP:p11:avg-fast`, signed result | `avg_fast`, FastSigned:33 | PASS | Literal signed statement, including all binders, threshold dependence, S1 constants, and existential `P11FastSpec`. No added premise. |
| Selected fast data | `p11FastData`, FastSigned:42 | PASS | Entire definition, including dependent choice and default branch, matches the signature; independently checked by `rfl`. |
| `stepP:p11:af-apply`, `af-o1`, `af-o2`, `af-concl` | Imported `avg_fast_of_spec` (Fast:390), through FastSigned:38–39 | PASS for wrapper integration | Instantiated with the actual chosen secular datum and both required proofs; no local assertion of these steps as assumptions. Their internal proofs remain P5's audit responsibility. |
| Blueprint closing eta rate, needed by `as-osc` | Imported `p11eta1_source_rate` (Fast:406) | PASS for availability | Export applies to any `P11SecularSpec`, hence to `(holo_chart D).choose_spec.1`; amended `p11d1 = min (s1*sigma) (rz^2)` is present. No rate needs to be extracted from the signed existential or tied to a particular fast witness. |
| P-FIXED frozen anchor | `fixedSunPlanetaryKAM` | Not assessed for sealing | Still `DRAFT_SORRY`; no provider or seal is supplied by P5W. |

The original design maps this slice and the four af steps to `Preparation/Fast`
(design:156–160,346–355). The explicit later split assigns only the final signed
wrappers to FastSigned. That assigned slice is complete: the previously conditional
core now yields the signed result from physical data alone. This report does not
reclassify P5's source proofs or P2f's chart assembly as independently audited here.

## Statement, proof, and definition checks

The signed `avg_fast` declaration at signature:822–827 matches FastSigned:33–37
exactly modulo whitespace. An independent probe copied that signed declaration
under `audit_signed_avg_fast`, replacing only its proof with
`@KAM.Planetary.avg_fast n D`; elaboration passed. It preserves `let C :=
p11SecularData D`, `eps1` before `eps`, both strict threshold bounds, and the
literal S1 inequality and existential fast specification.

The imported `P11SecularSpec` body (Holomorphic:73 onward) and `P11FastSpec` body
(Fast:43–76) also match their live signed bodies modulo whitespace. In particular,
Holomorphic:80–83 explicitly contains `(C.h (realInclusion n J)).im = 0` under
`‖J-C.J0‖ < 2*C.rC`. FastSigned:28–31 takes precisely that conjunct:
`mem_ball_iff_norm`, `← map_sub`, and `KAM.norm_realInclusion` convert the core's
ball membership to the signed real norm premise. There is no smaller real domain,
positivity assumption, assumed fast map, or conclusion-shaped hypothesis.

`holo_chart D` proves `∃ C, P11SecularFullSpec D C`; its chosen datum is definitionally
`p11SecularData D` (HoloAssembly:180–181). `.choose_spec.1` supplies the secular
specification used twice by the wrapper, and the unsigned helper discharges
`P11SecularHReal`. Thus the extra premise of the parametric core does not survive
in `avg_fast`.

There is exactly one new definition, no new structure or abbreviation:
`p11FastData` is the signed total classical selector on all physical data and real
epsilons. On the existence branch it chooses a witness of the full `P11FastSpec`;
on the nonexistence branch it returns the specified `default`. No theorem in this
slice relies on that fallback satisfying a fast specification. The signed theorem
supplies existence on a positive small-epsilon interval. The probe separately
proved `P11FastSpec C eps (p11FastData D eps)` from an existence witness by unfolding
the selector and using the chosen witness's specification. Outside that interval
no analytic property of the default is asserted.

`P11FastSpec` retains holomorphy, injectivity, reality, symplecticity, lattice
translation, image domain, exact Hamiltonian identity, cubic remainder supremum
and weighted bound, the G-minus-mean estimate, and all three displacement bounds.
The planned slow-stage consumer at blueprint:181 obtains its additional eta rate
from the imported P5c export. The original P5 audit's squared-minimum finding has
been addressed by the explicit 23:20 ruling and corrected imported definition;
P5W introduces no silent signature change. A source search found no other
production declaration of any of the three exported names and no current Lean
consumer of `p11FastData` outside this module. Names remain under the intended
namespace with no harmful root shadow.

## Independent verification

All Lean/Lake commands were serialized and run with `LEAN_NUM_THREADS=1` and
`nice -n 5`; no heartbeat or recursion override was used. Scratch files lived only
under this worktree's `.lake/abi-scratch/` and are removed after recording results.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap5w KAM.Planetary.Preparation.FastSigned
```

Exit **0**. Output begins and ends:

```text
[inp-gate] slot 3 acquired 23:33:42 for KAM.Planetary.Preparation.FastSigned
Build completed successfully (9380 jobs).
```

Intervening output consists of replayed dependency warnings (unused variables,
and an existing `if_neg` deprecation in BasePoint:73), including HoloAssembly:220,225.
There is no error or warning attributed to FastSigned. The build's job count
includes cached dependencies; this was the single targeted gate, not a clean build.

### Independent signed-target and selector probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP5WAudit.lean
```

Exit **0**. In addition to the signed theorem application, this probe copied the
signed selector body under a fresh name and proved equality to `p11FastData` by
`rfl`; it checked the witness-selection property described above. A deprecation
warning about `dif_pos` belongs only to this disposable probe. Axiom output:

```text
'KAM.Planetary.p11SecularHReal_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avg_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11FastData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_signed_avg_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Frozen/provider type and seal-body probes are inapplicable: this package exports
no provider or proposed frozen seal. The independently copied signed target is
the applicable statement probe.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.FastSigned
```

Exit **0**; complete output:

```text
replaying KAM.Planetary.Preparation.FastSigned
```

### Hygiene and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the brief-permitted stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1105 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Thus the source/module, frozen-anchor and elaborated ABI gates pass; the repository
lint command is not reported as an unconditional exit-0 success. `KAM.lean` was not
regenerated or edited.

The assigned file has 47 lines, maximum line length 94 Unicode characters, and the
required copyright, `module`, public imports, module docstring, public section,
and exposed noncomputable definitions. A forbidden-token/resource-override scan
of the assigned file returned no matches. Recursive project-import inspection
found 334 KAM modules, no provider module, and 64 frozen definition modules, all
marked `SEALED`; no frozen theorem or `DRAFT_SORRY` anchor is in that closure.

The full `git diff inp...HEAD` comparison was enumerated (85 changed files;
14,130 diff lines), and the complete assigned-file diff and protected-path diff
were read. It is not a single-package diff: Git warns
`inp...HEAD: multiple merge bases, using efc785f37e88ea6c13df230a568a02bb3506f489`.
The other merge base is `2d009059bbfb14a40c7d98e3f65765e3a6a9bc5b`.
Full-diff SHA-256 at this snapshot:
`76ae196ff603566ccb8f62c0e383b5f87d928353d7a33f4f9ef6e4853df4b1c3`.

The literal brief check
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
it includes the inherited ProperlyDegenerateKAM proof-body seal, its manifest
state transition, and generated root imports. This whole-history protected-path
check therefore does not pass as an empty diff. Crucially,
`git diff --quiet inp HEAD -- KAM/Frozen` and the corresponding manifest command
both exit **0**: these frozen/manifest bytes already agree with current `inp`.
The endpoint root still differs. The actual P5W commit `4fadef49` changes only
FastSigned (`git show --stat 4fadef49`; 47 insertions). These inherited changes
are disclosed here rather than attributed to this wrapper or silently excluded
from the requested comparison. No broad branch or inherited seal audit is claimed.

`git diff --check inp...HEAD` exits **0**, with only the merge-base warning.

## Notes, errata, and limits

1. **N1 — stale graph metadata.** `docs/graph/P/packets/P-p11.nodes.md:599–601`
   still records `LEAN_STATUS: NOT_STARTED`, `LEAN_REF: -`, `LEAN_NOTE: -` for
   `bpP:p11:avg-fast`. The signed export is now present. Updating that ledger is
   outside this report-only audit; the receipt distinguishes proved API delivery
   from registry maintenance.
2. **N2 — inherited comparison noise.** The protected-path three-dot difference
   above prevents a blanket claim that the entire branch satisfies the brief's
   empty-diff check. It is not a blocking source change in the assigned wrapper.
3. **Existing blueprint wording.** Blueprint:112 says “eps_1 is the largest value”.
   The signed theorem and actual consumer need any positive threshold; neither
   the signed result nor this proof claims a maximum. No existence of a largest
   admissible threshold is established. This is a pre-existing source-proof
   overstatement, not a weakened signed result or a new pinned-source erratum.

No new suspected pinned-source defect or implementation deviation was found.
The only persistent audit edit is this report, at the exact user-specified path;
the pre-existing untracked handoff is untouched. No frozen anchor is seal-ready
on the strength of this wrapper audit alone.
