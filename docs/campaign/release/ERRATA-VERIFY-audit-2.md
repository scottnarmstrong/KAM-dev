# ERRATA-VERIFY audit 2

**Verdict: RETURN FOR REVISION.** The ledger transition is exact, and most round-1 corrections are resolved. D-P-APPROX now identifies the wrong approximation construction. Correct that mathematical route description before publication. Two quotation-label issues and small remnants of internal history also remain; none changes the round-1 erratum verdicts.

Audited `inp-errata` at `365b183c` (writer revision `d3c4cc3b`), 2026-10-29, solely in `/root/code/KAM-inp-errata`. Initial working tree clean. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the complete verification handoff including Round 2, and audit 1. This is a delta audit of the record, not a new certification of the Lean library or a repetition of all 99 mathematical investigations. No delegation or process termination was used.

## Inputs and mutation boundary

| Input | SHA-256 |
|---|---|
| docs/ERRATA-AND-DEVIATIONS.md | `6a910bba54c6e27826e134de144df0036569c730148b783289e2e60a55aa116c` |
| docs/errata/ledger.json | `fa83d574683c2a21c2649068cf34f4dfdec3cb7888bc6533bf79655960203229` |
| docs/errata/working-record.md | `77b83f41e1ce67bb07787c3aad8fbabe05ea3063cd3ec77263ef8a0f7b1796e7` |
| docs/campaign/release/ERRATA-VERIFY-handoff.md | `29e3fc83ec4a40c5a64ac3a31f8912986e4fa8a25946c75b9f36eb324b796b33` |

Only this report is authored and committed. Draft, ledger, rendered working record, Lean files, frozen files, manifest and generated files remain unchanged. No scratch file was authored: PDF text and rendered images were held in memory. Lint generates its own temporary ABI probe.

## The ten required corrections

| Audit-1 item | Round-2 result | Evidence and remaining action |
|---|---|---|
| 1. Withdraw the two wrong allegations | Resolved | Lines 467–472 withdraw E-FdlLS09-1 and E-HL19-7 with the correct reasons. They no longer enter verified counts. |
| 2. Preserve 13 UNCLEAR allegations | Resolved | All 13 retain CANDIDATE in the ledger and explicit unverified text in the record. Convention/proof-supplement qualifications are retained; no failing source-admissible example is newly claimed. |
| 3. Separate historical reports | Resolved | E-Pos01-1 and E-P-Fej07e occupy historical subsections; the table separates 82 current defects and 2 historical reports. Arn63b explicitly lacks a pinned original and remains unverified. |
| 4. Quotations and pagination | Substantially resolved; two labels remain | All eight former P entries and all 65 former M entries are accounted for below. The live P placeholders have been replaced. Pos01 PDF 24–25, GJLV05 printed 864, CP09 Lemma 7 variables and H⁵ location, Pos93's 1/2, and both HL19 A.3 strictness qualifications check out. GJLV05-5 remains a verbal summary under a transcription label; CP11-2 silently changes Laplace-coefficient notation. |
| 5. Accurate deviations and current proof routes | Partial; revision required | Sup norms, action-coordinate extension, approved averaging, fast inverse/collar distinctions and planar attribution are corrected. The partial theorem and averaging locators are supported by bodies. D-P-APPROX confuses the frequency extension cutoff with analytic Fourier–Taylor approximation; see finding R1. D-P-WEAK-KAM would benefit from the actual downstream quantitative assembly locator. |
| 6. Remove claims beyond ledger | Resolved at record scope | The universal guard assertions, five convention items, six internal proof repairs, global corrected-reading assurance and all-22 axiom assurance are removed. The remaining mathematical additions explain individual identified entries rather than introduce an unnumbered theorem/consumer claim. |
| 7. Remove unaudited theorem/axiom assurance | Resolved | Lines 12–14 link to STATEMENTS.md without repeating its proof/axiom claim. This report does not certify the linked document or the release axiom/kernel gate. |
| 8. Remove internal campaign language | Partial, minor | Package/Part/question/provider instructions and broken “written proof-P” locators are removed. Line 179 retains an abandoned project-draft narrative; line 359 retains the rejected earlier project proposal. Remove those sentences or move them to internal provenance, preserving the mathematical scope and correct source attribution. |
| 9. No division-of-work authorship credits | Resolved | No formalization author or author's team is credited with a subset of the work. Literature citations and attribution of the historical author corrections are legitimate. |
| 10. Scoped mathematical conclusions | Resolved | CP11 certifies only r₁; CP10-12/13 do not refute properly-degenerate KAM; Nei76's identity does not refute averaging; Rus05 concerns constructed multipliers only. CP10-ANNULUS explicitly retains the signed-ball/positive-shell issue as well as the exponent. |

## Remaining findings

### R1: D-P-APPROX describes a different mathematical operation (required)

At `docs/ERRATA-AND-DEVIATIONS.md:453`, the replacement for Rüssmann's analytic approximation is described as a smooth cutoff constructed by tensor-kernel convolution, citing WeakKAM/Cutoff, CutoffBump, CutoffTensor and CutoffConv.

Those files do construct a cutoff, but its role is extension of real frequency increments on action sets. `KAM/Planetary/WeakKAM/Cutoff.lean:97` (`smooth_cutoff`) returns a real C^μ function equal to one on a compact set, with controlled support and derivatives. Its actual consumer `KAM/Planetary/WeakKAM/Extension.lean:134` chooses such functions; lines 147 onward multiply the frequency increments by them. This is not the holomorphic approximation of a Hamiltonian on a thinner complex strip. A nontrivial compactly supported smooth action cutoff cannot itself be a holomorphic cutoff on a connected complex neighbourhood.

The analytic replacement is visible in `KAM/Planetary/MaximalStep/FourierCutoff.lean:37` (`p11Cut_eq_sum`) and `:143` (`fourier_cutoff`): finite Fourier truncation with its own tail bound. `KAM/Planetary/MaximalStep/Cutoff.lean:80` (`p11_cutoff`) composes first-order action Taylor truncation with that Fourier truncation, proving the remainder bound `eps * (q^2/(1-q) + 2*p11Error n T d)` on the smaller domain. Its body calls `taylor_cutoff` and `fourier_cutoff` at lines 90–92. `KAM/Planetary/WeakKAM/IterationIncrement.lean:31` (`cutoff_delta`) consumes the corresponding coefficient estimate.

Required replacement: describe elementary Fourier truncation and action Taylor estimates, with their own constants, and cite these MaximalStep declarations. Describe the convolution cutoff separately as the real frequency-extension supplement if retaining it in this same deviation. The broad claim that source multipliers are replaced is consistent; the claimed mechanism is not. This is a documentation defect introduced in the revision, not a new defect in a frozen statement or in Rüssmann's paper.

### R2: two remaining quotation-label mismatches (required editorial corrections)

- `docs/ERRATA-AND-DEVIATIONS.md:96`, E-GJLV05-5: “a sum over j differentiated in θ_i, and the solution bounded by its own norm” is a prose description, not a displayed expression transcribed from the PDF. The source at printed 889 (PDF 35) actually displays `Σ_(j=1)^n ω_j ∂v/∂θ_i = h` and `‖v‖_(ρ−δ) ≤ c δ^(−σ) γ^(−1) ‖v‖_ρ`. Supply those formulas or label the existing field as a summary. The two source typos remain confirmed.
- `docs/ERRATA-AND-DEVIATIONS.md:395`, E-P-CP11-2: printed B.6 uses `37 α⁴ β₄^(9)(α)`, whereas the record gives `37 α⁴ b_(9/2)^(4)(α)`. CP11 printed 61 explicitly defines `β_k^(r) := b_(r/2),k`; the conversion is mathematically sound. It is a change of notation, not merely linearized typesetting. Retain the source β notation in “Printed”, or explicitly say “normalized notation using CP11's definition on p. 61”. The exponent allegation and r₁-only scope stand.

The new prose excerpts for Pos01, CCdlL13, FdlLS09 and CP09-11 were found in the pinned text; no replacement prose quotation was found to reverse its source meaning. Whitespace, line wrapping and mathematical glyphs inside prose excerpts are not byte-for-byte PDF strings. The FdlLS09 entry explicitly discloses the text-layer `7→` rendering; formula-bearing excerpts should consistently use the stated transcription convention.

### R3: strengthen the current-route citation without overstating the audit (note)

D-P-WEAK-KAM at line 425 correctly names real declarations `adm_budget`, `adm_budget_beta` and `displacement_power` in WeakKAM/PolynomialBudget.lean (lines 140, 224, 286). However, the physical wrapper's actual call is `weak_kam_quantitative_full` at `KAM/Planetary/Preparation/Wrapper.lean:83`. Its body in `KAM/Planetary/Quantitative/AssemblyK6.lean:48` uses `weak_kam_quantitative`, `displacement_power_flat` and `qb_beta`; Quantitative/Budget.lean traces the polynomial bounds to `qb_poly`. Add this assembly locator to show what the final consumer uses. Importing PolynomialBudget or finding its named declarations alone would not establish that they are the exact route at that consumer.

D-P-LOCAL-WRAPPER is supported at source-body level: `Preparation/Wrapper.lean:158` discharges the conditional wrapper with `data_star D`; `Preparation/Datum.lean:177` discharges its conditional result with `amount D hnu`; `FixedAssembly/General.lean:87` supplies the actual wrapper to the physical set transfer. The wrapper conclusion keeps `Set.range K ⊆ S` and positive finite volume. D-NAVG-3 agrees with `Averaging/Mean.lean:44` (`mean_family`) and `:88` (`averaging_mean_core`), including maximal-flow identification and the stopped-error/Markov argument. D-N-PARTIAL-ROUTE's threshold is actually consumed in `Provider/Nekhoroshev/PartialConvexNekhoroshev.lean:99`; ThresholdExplicit exports the stated block-time exponent. These are source checks, not fresh successful elaboration or kernel receipts.

## Ledger transition and inventories

Compared parsed JSON at `986fbdc8` (pre-revision ledger) with the current file, preserving array order and IDs. All top-level fields and all entry keys were compared; the only changed fields are `status` and `checked_by`.

- Exactly 99 `checked_by` fields changed, each preserving its old text as a prefix.
- Exactly 86 statuses changed: 84 CORRECT entries to CONFIRMED; E-FdlLS09-1 and E-HL19-7 to DROPPED. All 13 UNCLEAR entries remain CANDIDATE.
- Every change agrees with audit 1's per-ID verdict. The other 14 dropped entries and all 64 deviations are identical in every field. No printed text, claim, location, effect, source, type or evidence field changed. No entry was added, deleted or reordered.
- Current totals: **84 CONFIRMED, 13 CANDIDATE, 16 DROPPED, 32 ADOPTED, 32 PLANNED**. Thus the reader's **82 current defects + 2 historical reports + 13 unverified + 64 deviations**, plus **2 withdrawn**, reconciles exactly.
- Record coverage: **163 occurrences, 163 unique IDs**, equal to the pre-revision non-DROPPED set; missing and extra sets empty. The two newly withdrawn IDs are deliberately retained for traceability.
- The writer revision changes exactly three files: the record, ledger, and regenerated working record. It changes no Lean, frozen or manifest file. The ledger is byte-identical to its JSON serialization with `indent=1`, `ensure_ascii=False`, no terminal newline.

## Changed former P/M fields: pinned-source spot checks

Every former P/M row changed (8 P, 65 M). The table covers all 73, including the two withdrawn allegations. “Located” for M means that the relevant expression is present and the field is acceptable as mathematical transcription/excerpt; it does not mean verbatim prose or a fresh proof of the entire erratum. R2 identifies the exceptions. The live former P entries now contain actual prose excerpts, labels or formulas. Page numbers below are the audit-1 locators except for the corrections explicitly recorded.

| ID | Former class | Current line | Delta check |
|---|---|---:|---|
| E-Pos01-2 | P | 72 | Located on PDF 24–25; both initial-choice prose excerpts and h₀ formula checked. |
| E-Pos01-5 | M | 75 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-GJLV05-1 | M | 92 | Located on printed 864 / PDF 10; γ² in both bounds. |
| E-GJLV05-2 | M | 93 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-GJLV05-3 | M | 94 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-GJLV05-4 | M | 95 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-GJLV05-5 | M | 96 | Source located on PDF 35; field remains a summary, see R2. |
| E-FdlLS09-1 | M | 471 | Withdrawn correctly; no new printed-quote claim needed. |
| E-FdlLS09-2 | P | 108 | Prose located on PDF 43; disclosed arrow transcription; remains unverified supplement. |
| E-CCdlL13-1 | P | 120 | All three ℓ sentences located on PDF 31–32. |
| E-HL19-1 | M | 132 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-2 | M | 133 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-3 | M | 134 | A.1/A.3 located on PDF 55; both strictness qualifications match. |
| E-HL19-4 | P | 135 | Formulas (5.15)/(5.18) located on PDF 33; surrounding strict bounds checked, also PDF 43. |
| E-HL19-6 | M | 137 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-7 | P | 472 | Withdrawn correctly; PDF 44 weaker sentence versus stronger (5.73). |
| E-HL19-8 | M | 138 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-9 | M | 139 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-10 | M | 140 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-12 | M | 142 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-13 | M | 143 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-HL19-14 | M | 144 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-A-N77-1 | P | 168 | Labels 12.3.A / 12.4.A located on printed 56 / 58. |
| E-P-A-N77-2 | M | 169 | Rendered printed 56 confirms both factors 1/2. |
| E-P-A-LP17-1 | M | 187 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-Chi05-1 | M | 200 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-N-BM-2 | M | 226 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-N-BM-5 | M | 229 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-N-GCB-1 | M | 252 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-N-GCB-2 | M | 247 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-N-GCB-3 | M | 248 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-Pos93-1 | M | 265 | Rendered printed 194 confirms positive exponent at end of Case B. |
| E-Pos93-2 | M | 270 | Rendered printed 195 confirms 1/2 and W⁻¹; remains unverified. |
| E-Pos93-4 | M | 271 | Rendered printed 199 confirms displayed 5δ/4 estimate; remains unverified. |
| E-Pos93-7 | M | 266 | Rendered printed 214 confirms single ζ kernel. |
| E-NAVG-NEI-17 | M | 288 | PDF 4 / printed 1298 identity located; same scoped claim. |
| E-P-CP10-BOUNDARY | M | 303 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-CP10-ANNULUS | M | 304 | PDF 17 / printed 561 exponent located; shell normalization warning retained. |
| E-P-CP10-WHOLE | M | 318 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-1 | M | 305 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-2 | M | 306 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-3 | M | 307 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-4 | M | 319 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-5 | M | 320 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-8 | M | 310 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-9 | M | 311 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-10 | M | 312 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP10-13 | M | 314 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-Fej04r-1 | M | 341 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-Fej04r-3 | M | 343 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-Fej04r-6 | M | 344 | Printed 53–54 matrix assumptions and eigenvalue expansion located. |
| E-P-Fej04r-7 | M | 345 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P7-Fej48 | M | 348 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P8-Fej50 | M | 349 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-Fej04r-12 | M | 351 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-Fej04r-13 | M | 352 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-Fej04r-14 | M | 353 | Printed 38 a/b and printed 39 membership signs located. |
| E-P-Fej04r-16 | M | 355 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-CP11-1 | M | 394 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-P-CP11-2 | M | 395 | B.6 located on printed 63; normalized b notation needs disclosure, see R2. |
| E-CP09-1 | M | 418 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP09-2 | M | 407 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP09-3 | M | 408 | PDF 14 Lemma 7 has (x̃, ỹ), as revised. |
| E-CP09-4 | P | 409 | PDF 14–15 separated quadratic term and Q⋆ polynomial located. |
| E-CP09-5 | M | 410 | PDF 15 prose substring located, including 2p × 2p. |
| E-CP09-6 | M | 411 | PDF 15 H⁵ has repeated ρ₀j; (27) correctly has ρ_j. |
| E-CP09-7 | M | 412 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP09-9 | M | 419 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP09-10 | M | 414 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-CP09-11 | P | 420 | PDF 22 “regular and non influential” prose located; remains unverified. |
| E-Rus01-1 | M | 434 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-Rus01-2 | M | 435 | Located; mathematical transcription/excerpt, not verbatim typography. |
| E-Rus05-2 | M | 448 | Printed 30–31 cutoff rescaling and (46)–(47) located; constructed-multiplier scope retained. |

Additional surrounding passages and the historical author reports were read; the former V-class entries were not all independently re-investigated in this delta round. All 23 PDFs used in audit 1 were freshly hashed against docs/sources.json: **23/23 match**, using the actual registered paths (including incoming-directory aliases). Arn63b still has no pinned original. Local `pdftotext -layout` was used, with direct in-memory page rendering for Pos93 printed 194, 195, 199, 214 and Nek77 printed 56. CP11's printed notation was also compared with its definition on p. 61. An initial optional `fitz` rendering attempt failed because that module is unavailable; `pdftoppm` succeeded without installing anything or writing image files.

## Checks, limits and handoff

- `python3 scripts/render_errata.py --check`: **exit 0**, no output.
- Inline Python ledger/ID/hash comparisons: **exit 0** for the completed comparisons above; no unexpected JSON changes, missing IDs or extra IDs. An initial PDF-path resolver failed on an incoming-path record; the corrected resolver checked all 23 paths successfully.
- `LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: **exit 1**. Output: `check_lean_modules: PASS (1362 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; then ABI scratch `error: unknown module prefix 'KAM'`. No KAM compiled directory/olean is available in the configured search paths. This is not a passing lint/ABI receipt.
- Fresh axiom probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean --stdin`, importing `KAM.Frozen.Theorems.AposterioriKam` and requesting `#print axioms KAM.aposteriori_kam`: **exit 1**, unknown module prefix `KAM`; no axiom set printed. No new theorem was authored, so main-result axioms are not applicable to this report; all-library axiom/kernel certification remains outside this failed probe.
- Targeted build: **not applicable**, documentation-only delta and no changed Lean module. No cache reconstruction, full-library build, heartbeat override, generated-root regeneration or out-of-worktree action was attempted.
- Final report-only whitespace, ID-table coverage, unchanged input hashes and commit scope are checked before handoff. The sole commit path is `docs/campaign/release/ERRATA-VERIFY-audit-2.md`.
- Uncertainties retained: all 13 unverified allegations and unpinned historical originals; no new complete consumer audit, constant audit, Lean elaboration or kernel replay. Round 1's 84/2/13 mathematical verdicts are unchanged by this delta review.

Required record-owner action is to correct R1, finish the two R2 labels, and remove or relocate the two internal-history sentences. R3 supplies better evidence for the accurate current-route claims. No ledger status change or frozen-statement change is requested. No new pinned-source erratum or Lean deviation was established or introduced by this report.
