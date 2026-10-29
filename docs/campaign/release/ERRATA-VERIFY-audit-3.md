# ERRATA-VERIFY audit 3

**Verdict: PASS WITH NOTES.** All round-2 required corrections are resolved. The two revised mathematical transcriptions match the pinned PDFs, the corrected analytic approximation and physical-wrapper citations are supported by the Lean bodies, and the ledger changes exactly the two authorized `printed` fields. No further record revision is required for this delta. The notes below preserve the precise budget dependency and the separate lint/ABI limitation; this verdict does not certify library elaboration or kernel replay.

Audited `inp-errata` at `346e6d31` (writer revision `0ee968fd`), 2026-10-29, solely in `/root/code/KAM-inp-errata`. Initial working tree clean. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the complete verification handoff including Round 3, and the complete round-2 report. This is an independent, refute-first delta review, not a repetition of all round-1 mathematical investigations. No delegation or process termination was used.

## Inputs and scope

| Input | SHA-256 |
|---|---|
| docs/ERRATA-AND-DEVIATIONS.md | `f1af270bf33f66a2b04fdad1688dbbc2a5f1ed9ec1869799dae187a228d30946` |
| docs/errata/ledger.json | `f5568324278a6f1e7902fb20c6edbf6cc8a53b6ee45c0cf077e7d35bd5ccbe01` |
| docs/errata/working-record.md | `6341202a58523e4fc195f791d3883931209d04669a9cb33aaa2b799a36a58162` |
| docs/campaign/release/ERRATA-VERIFY-handoff.md | `4dc6b5c9886a130676791a26a4ae08d5a4b07bbd0d37824f9dd4224f06022bee` |

Only this report is authored and committed. Draft, ledger, working record, Lean, frozen, manifest and generated files are unchanged by this audit. PDF text and comparison data were held in memory; no scratch artifact was authored. Lint may create its own temporary probe.

## Round-2 findings

| Finding | Round-3 result | Independent evidence |
|---|---|---|
| R1: distinguish analytic approximation from real frequency extension | Resolved | Record line 453 now describes finite Fourier truncation and first-order action Taylor truncation, with the correct remainder and separate real cutoff. Bodies and consumer details below. |
| R2a: E-GJLV05-5 was a summary under a transcription label | Resolved | Record line 96 and the ledger now give the actual two formulas at printed 889 / PDF 35. Both erroneous source symbols are retained faithfully. |
| R2b: E-P-CP11-2 silently normalized notation | Resolved | Record line 395 and the ledger now retain the source's beta notation, with its definition explicitly attributed to CP11 p. 61. The alpha exponent and r1-only scope are unchanged. |
| R3: cite the actual quantitative physical consumer | Resolved | Record line 425 gives the call at Preparation/Wrapper.lean:83 and declaration at Quantitative/AssemblyK6.lean:31; body lines 48–51 call the three stated results. See the dependency note below. |
| Item 8: two internal-history remnants | Resolved | Line 179 removes the abandoned-draft sentence. Line 359 states the absence of a factor-four restriction without recounting an earlier project proposal or attributing it to Fej04r. |

No new division-of-work authorship credit, unnumbered theorem assurance, status promotion or broader source-refutation claim is introduced by these edits. Earlier unresolved mathematical allegations retain their unverified status.

## Lean citation and body checks

D-P-APPROX is supported at source-body level:

- `KAM/Planetary/MaximalStep/FourierCutoff.lean:37`: `p11Cut_eq_sum` is a **private** theorem expressing `p11Cut` as a finite sum over `modeCutoff n ceil(T)`, with the additional mode-size test. It is a valid source locator, not a claim of an exported interface. Its proof reduces the infinite sum to finite support.
- The same file at line 143: `fourier_cutoff` supplies admissibility, the tail bound `p11Error n T d * M`, the retained-part bound and reality. Its body uses `p11Cut_eq_sum` and `cutoff_tail`.
- `KAM/Planetary/MaximalStep/Cutoff.lean:80`: `p11_cutoff` states the smaller-domain remainder `eps * (q^2/(1-q) + 2*p11Error n T d)`. Lines 90–92 call `taylor_cutoff` and `fourier_cutoff`; the last calculation adds the Taylor and Fourier errors. This is genuinely the claimed analytic construction.
- `KAM/Planetary/WeakKAM/IterationIncrement.lean:31`: `cutoff_delta` obtains the increment bounds through **`p11_cutoff_coeff`**, called at line 38. It does not directly call the scalar remainder theorem `p11_cutoff`. The coefficient theorem is at `MaximalStep/StepCoeff.lean:272`; its body calls `fourier_cutoff` on the zeroth and first action coefficient families at lines 306–308 and exports their bounds and affine decomposition. Thus “consumes the resulting estimate” is acceptable at construction level; it should not be read as a direct call to the scalar remainder bound.
- `KAM/Planetary/WeakKAM/Cutoff.lean:97`: `smooth_cutoff` returns a real C^mu function, equal to one on the compact action set, with support and derivative control. The proof constructs the convolution of an indicator with `selectionKernel`.
- `KAM/Planetary/WeakKAM/Extension.lean:134–147`: the body chooses these cutoffs, calls `smooth_cutoff` at line 141, then multiplies the real frequency increments by them. The record now correctly separates this extension from holomorphic approximation.

D-P-WEAK-KAM is supported by the actual consumer:

- `KAM/Planetary/Preparation/Wrapper.lean:83` calls `weak_kam_quantitative_full` with the prepared datum's parameters, then uses its quantitative family and threshold output.
- `KAM/Planetary/Quantitative/AssemblyK6.lean:31` declares that theorem. Lines 48–51 call `weak_kam_quantitative`, `displacement_power_flat` and `qb_beta`, exactly as stated. Its remaining body constructs the valid datum with beta replaced and composes the two displacement inequalities.
- **Dependency precision note:** `Quantitative/Budget.lean:149` proves the beta threshold estimate using `qb_poly`. The displacement estimate instead calls **`qbPoly_gamma_lower` at line 177**, specializing the gamma lower bound to the beta rates and inverting it. The record's “polynomial bounds ... specializations of qb_poly” is a broad description of the budget route, not a literal direct dependency for both inequalities. Adding “and qbPoly_gamma_lower” would be more precise; this does not reopen R3 or invalidate the route. These distinctions also delimit what was checked: source bodies, not fresh elaboration or a complete downstream constant audit.

## Pinned quotation checks

Both PDFs were freshly hashed against `docs/sources.json` before reading their cited pages with `pdftotext -layout`; paths are inside this worktree.

| Source | Pinned file and SHA-256 | Check |
|---|---|---|
| GJLV05 | `sources/pdf/gjlv.pdf`, `eec921dc45889c6a7148d12653d84f6994d395811ccf40f2bdfd6057d119a9ee` | MATCH. Printed 889 / PDF 35, Proposition 18 displays the sum over j with derivative theta_i, and the bound with the norm of v on the right. The new formulas retain precisely those symbols and powers. |
| CP11 | `sources/pdf/cp11_planetary_invent.pdf`, `9b525c5896cfd006b813e79ce56df0b33fcdc55595c972e5090f4a839de4c30f` | MATCH. Printed/PDF 63, (B.6), r1 ends in `37 alpha^4 beta_4^(9)(alpha)`. Printed/PDF 61 defines `beta_k^(r) := b_(r/2),k`. Both new fields agree. |

These are faithful linearized **mathematical transcriptions**, as the record explicitly labels them, not byte-verbatim PDF typography. The CP11 definition and page locator are explanatory metadata; the ledger brackets mark them separately. No new prose quotation or changed mathematical verdict needs certification in this delta.

## Exact delta and inventories

Compared the full diff `4bbaeacc..346e6d31`, not merely the supplied mapping. The writer commit changes exactly the record, ledger, rendered working record and `.drafts/handoff-ERRATA-R3.md`; the subsequent request commit changes only the verification handoff. There is no Lean, frozen, manifest, README or KAM.lean delta.

The reader record has exactly six changed entry lines: the two quotations, two internal-history edits, approximation route, and quantitative consumer locator. No other record text changes. The rendered working record changes exactly the two quotations.

Recursive parsed-JSON comparison against `4bbaeacc:docs/errata/ledger.json` finds exactly:

- `/entries/19/printed`, E-GJLV05-5;
- `/entries/100/printed`, E-P-CP11-2.

All top-level keys, entry keys, array lengths, order, IDs and every other field are identical, including every `status`, `checked_by`, deviation, claim, location, effect and evidence field. Serialization remains exactly `indent=1`, `ensure_ascii=False`, without a terminal newline.

Counts remain **84 CONFIRMED, 13 CANDIDATE, 16 DROPPED, 32 ADOPTED, 32 PLANNED**. Record coverage is **163 occurrences, 163 unique IDs**, exactly the non-DROPPED ledger IDs plus the two newly withdrawn allegations; missing and extra sets are empty. The unchanged reader totals **82 current defects + 2 historical reports + 13 unverified + 64 deviations**, with **2 withdrawn**, reconcile. No round-1 verdict is independently upgraded by this review.

## Checks and handoff

- `python3 scripts/render_errata.py --check`: exit 0, no output.
- `git diff --check`: exit 0, no output before report creation; report whitespace and final commit scope checked before handoff.
- Inline Python pinned-hash, exact-ledger-delta, serialization and ID comparisons: exit 0, all assertions passed.
- An exploratory glob for `MaximalStep/Coeff*.lean` returned exit 2 because that filename does not exist; a directory search located `StepCoeff.lean`, whose actual declaration and body were then read. No missing citation remains.
- `LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: **exit 1**. Output: `check_lean_modules: PASS (1362 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; then `.lake/abi-scratch/tmp49jy8xzo.lean:1:0: error: unknown module prefix 'KAM'`, with no KAM directory/olean in the configured search paths. This reproduces the earlier worktree ABI limitation and is **not a passing lint/ABI receipt**.
- Targeted build: not applicable; no Lean module authored or changed. No full build, cache reconstruction, generated-root regeneration or resource override attempted.
- Main-result axioms / `#print axioms`: not applicable to this documentation-only report; no new Lean result. No fresh axiom assurance is issued. The release owner still needs a separate successful ABI/axiom/kernel receipt.

Uncertainties retained: the 13 unverified allegations, unpinned historical originals, and the absence of fresh Lean elaboration/kernel certification. No new suspected pinned-source defect or Lean deviation was established or introduced. The sole authored and committed path is `docs/campaign/release/ERRATA-VERIFY-audit-3.md`.
