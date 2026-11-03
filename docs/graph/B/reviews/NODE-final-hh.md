# NODE final recheck (sonnet-review-B-hh-nodes), HEAD e2eb1de8b; changed nodes/items only
b:3.2#lie-identity: ACCEPT (STATEMENT_SOURCE L343-354 now covers the B/(m+1)! bound; ext:ode#local dropped, correct since the flow is a hypothesis; bracket edge L347-349 states d/ds F o Phi^s = {F,chi} o Phi^s).
b:3.2#chart-composition: ACCEPT (lie-identity dep with edge L355-356 correct; NOTE records L316-318/L321/L398-402 sources and that "reversed flows" is an inference; ode#local kept for flow uniqueness, justified).
b:3.2#oscillator-drift: ACCEPT (chart-composition dep with edge L399-402; eta_poly L378-379 and tail w_j E(1/dq_j+1/dp_j) L383-384 recorded correctly; cauchy edge L382-384 correct; no cycle: chart-composition -> lie-identity only).
ext:analysis#cauchy: ACCEPT (hypotheses/conclusion are the standard estimate E/delta; leaf with no deps; STATEMENT_SOURCE form matches ext:ode#local; EXTERNAL_POLICY header updated consistently).
b:3.1#checker-soundness: ACCEPT (transfer dep with edge L322 and conclusion L329-331 now consistent; B1-E edge cites L197-198; NOTE records polynomial/oscillator scope, torus excluded, and the divisor-witness deviation with its corpus justification L317/L337 plus OD-B12; quantifiers/open interval unchanged and correct).
b:4#model-identification: ACCEPT (HVF edge now cites F23-26, the inlined H).
b:4#certificate-accepted: ACCEPT (wording "normalized chart" L546; edge L546; conclusion lists forward displacement on closed E_b, inverse on the physical disc and the initial-set inclusion L321; literals unchanged and correct). Note only: the specific domains (closed E_b, physical disc) are modeling of P553 "their required domains" via the P145/P154 analogs, already flagged in inverse-chart NOTE.
b:4#inverse-chart: ACCEPT (soundness dep with edge L321 and oscillatorAction dep with edge L553 added; analogy NOTE present; no cycle since soundness does not depend on it).
b:2.3#transfer: ACCEPT (hypotheses now include z0 = Psi(w0), I_j(w0) <= a_j).
b:4#physical-bounds: ACCEPT (forward displacement on closed E_b; chain unchanged and correct).
b:4#HH: ACCEPT (oscillatorAction edge now F21-36 covering premise and conclusion).
Coverage b:2.2#transfer: ACCEPT (NODE b:2.3#transfer, b:4#inverse-chart; PROPOSED).
Coverage b:2.3#transfer: ACCEPT (reset to PROPOSED/-).
Coverage b:3.1#certificate-table: ACCEPT (dispositions widened, consistent with node sources).
Coverage b:3.1#soundness: ACCEPT (adds b:4#certificate-accepted for L338-340).
Coverage b:3.2#tail: ACCEPT (L387-397 EXCLUDED with corpus-based reason).
Coverage b:3.2#propagation: ACCEPT (L398-402 -> oscillator-drift, chart-composition; contiguous with L387-397 and L404 onward).
Coverage ext:cauchy: ACCEPT (L382-384 -> ext:analysis#cauchy). Note: its range overlaps b:3.2#oscillator L373-385; same pattern as the existing ext:* items, so acceptable if the graph tool allows overlaps (run the generator/validator to confirm; I did not).
Coverage b:3.3#divisors: ACCEPT (reason now stands on L317/L337).
No new omissions.
