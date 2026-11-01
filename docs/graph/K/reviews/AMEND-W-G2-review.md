# Track-K AMEND review for W global finding G2

Reviewer: `sol-kamend-W` (GPT-6.1-Sol, codex-1), independent of `claude-suborch-W` and `sol-global-W`. Date: 2026-10-31.

**PASS: K-A045, K-A046, K-A047 and K-A048.** All four staged records preserve the old mathematical premises and add only typing/convention data already inherited from the source. No replacement records are required. No target is a frozen anchor; no contract-version bump is needed.

## Scope and frozen inputs

Focused source-correspondence audit (manuscript-audit tier 2). The user's brief supplies the permission envelope: write only this report; do not apply amendments, run Lake/builds or state-changing git, or inspect implementation Lean/providers. AGENTS.md, PLAN.md and DECISIONS.md were read. No Lean brief or proof task is issued. Discovery and a separate adversarial reread were performed by this independent reviewer; no delegation was used.

Read-only HEAD: `b7fd0f9bed269b08039f140efb2a463e122804cd`. The byte snapshot below controls the verdict, including staged/uncommitted input text. SHA-256:

| File | SHA-256 |
| --- | --- |
| `AGENTS.md` | `9895b2a777dd546170f6c0f40ee15bc7330c377d70485c25b38c318eb3e8e804` |
| `docs/PLAN.md` | `3efa6ab0e8da45cf578fcd9c294f330d6db4372fed34c07729e9ba6f6e1fb71f` |
| `docs/DECISIONS.md` | `27b7abea7a24c8347156515cfb2f4179472f528338ee863e02fa0e898d69ae08` |
| `docs/graph/K/SPEC.md` | `4ec0d98fb6c070dec2c57cc8243b85e1d4dcc88cdc472d7a98c49f9d7832e0a9` |
| `docs/graph/K/AMENDMENTS.md` | `8b12b7b43469782e10c6b58b90d163a4f935e2a6b2736212671c9d56af987b23` |
| `docs/graph/K/AMENDMENTS-W-PENDING.md` | `2f412d8ae000bad0aa8cbbd6f0728f5e343ce360724242de012c8484ef28ab4f` |
| `docs/graph/K/DEPGRAPH.md` | `bf82bf0146405c6c0c2c9a5cf2f87fbaa1afa120dc502d103a4806698415e574` |
| `blueprint/parts/p1-analysis.tex` | `2afd058105b3de64042c142ec1c4eeba063b3c973e26ab980e7b668bc0232407` |
| `docs/graph/W/reviews/GLOBAL-review.md` | `e182cb31ff9ebe11cda06abcea2c6c7ea32217881dbc44a5671dd657d497a256` |
| `docs/graph/W/SPEC.md` | `a3b732ba5c43c80435a4bcc3eea3b01d9d96424304ab0fffe7d8d40401ec244a` |
| `docs/graph/W/DEPGRAPH.md` | `3f35f1ac2ced6c0584f638329d2572ae2d7b6144265c165e7ddcff47fccaf425` |
| `docs/graph/W/reviews/W-imports-review-1.md` | `dfc89a92c4c52a32eb49365a94b0a807253e2c555eb3702233e5f49bdd07e257` |
| `docs/graph/W/reviews/W-imports-review-2.md` | `a4bb07f0be2be3cb6d56399aa1bb695b6af9007f45bee08ad958e53f7d54d330` |

## Record verdicts

| Record / target | Verdict | Exact source and effective-record comparison |
| --- | --- | --- |
| K-A045-w-findim-decay / `bp:p1:decay` | PASS | L26 fixes finite-dimensional complex normed W; L37-L39 supplies n >= 1 and rho > 0. L786-L789 retains holomorphic, bounded, 1-periodic u on T_rho. The proof's L792 explicitly identifies u's values as W. Existing n/rho constraints remain; only W's inherited typing is newly exposed. |
| K-A046-w-conventions-fourier-basic / `bp:p1:fourier-basic` | PASS | L36-L47 supplies period-one characters and Fourier indices in Z^n, with n >= 1 at L37-L39. The complete scalar/componentwise clause and all (a)/(b)/(c) premises at L757-L768 remain verbatim after the convention prefix. No boundedness premise is introduced into (c), and vanishing coefficients remain conditional on that clause. |
| K-A047-w-findim-holomorphic-analytic / `bp:p1:holomorphic-analytic` | PASS | L26 fixes finite-dimensional complex normed W; L29-L32 types holomorphic F on open U in C^m. The natural-number dimension m is the existing finite coordinate dimension, not an added positivity condition. The entire old field, including the local polydisc and maximum data (a) and the conditional real-valued subclause (b), remains verbatim. These agree with L296-L312. No n >= 1 or m >= 1 is added. |
| K-A048-w-findim-strip-identity / `bp:p1:strip-identity` | PASS | L26 supplies finite-dimensional complex normed W, L37-L39 supplies n >= 1, and L531-L534 states r > 0, holomorphic v:T_r -> W and vanishing at every real point. All old premises remain. Neither periodicity nor boundedness is added. |

The effective old fields returned by the requested JSON command, before applying any pending record, are:

- `bp:p1:decay`: `n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); u holomorphic, bounded and 1-periodic on T_rho`
- `bp:p1:fourier-basic`: `n >= 1 (standing, p1-analysis.tex L37-L39); v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0`
- `bp:p1:holomorphic-analytic`: `U in C^m open; F:U->W holomorphic; (a) z_0 in U, r>0 with P-bar(z_0,r) in U, A=max_{P-bar(z_0,r)}|F|; (b) U_R=U cap R^m, x_0 in U_R; W=C^p and F(U_R) in R^p for the real clause`
- `bp:p1:strip-identity`: `n >= 1 (standing, p1-analysis.tex L37-L39); r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x`

For A045/A046/A048 the already explicit n/width convention prefix is restated rather than duplicated byte-for-byte. The suffix after that old prefix is preserved verbatim, and its n/width constraints are retained in the new prefix. A047 preserves the whole old field as a verbatim suffix. Thus the NOTEs' “convention prefix plus the old premises” is accurate mathematically; it is not a claim that every replacement starts with the old prefix unchanged.

## Frozen identity, contracts and format

All four effective records are `KIND: lemma`, with their own node ID as CONTRACT_ID and CONTRACT_VERSION `1`. Each has `FROZEN_FILE`, `FROZEN_DECL`, `FROZEN_ANCHOR_ID` and `FROZEN_ABI_SHA256` equal to `-`. K SPEC identifies the theorem anchors and frozen-definition anchors in Part 0; these Part 1 lemma nodes are not among them. No frozen file or provider was opened.

The four pending records use the same field schema as K-A001..K-A044. Only SET_SOURCE_HYPOTHESES is non-placeholder among the mutation fields: every dependency/route addition or removal and every other SET field is `-`. Existing source quantifiers, conclusions, constant scopes, statement/proof locators, dependencies and contract identities therefore stay unchanged. K-A001/A003/A008 are the direct precedents for exposing inherited n/width conventions on these same targets while leaving the version unchanged. Exposing W's already specified finite dimensionality similarly corrects an incomplete source-field summary; it does not alter the source theorem or authorize a Banach-target theorem. Version `1` is appropriate for all four.

The staged REVIEWER placeholders are expected staging metadata. This report supplies the requested independent PASS; the writer's later append/reassembly and replacement of those placeholders by `sol-kamend-W` are not performed here.

## NOTE citation checks and adversarial reread

All four statement ranges and convention citations are accurate. L26 says “W denotes a finite-dimensional complex normed space”; L37-L39 says widths are positive and “n >= 1 wherever a strip occurs.” A046's L36-L47 reference contains the period-one definition, characters indexed by Z^n and the coefficient integral/entrywise convention. A047's L29-L32 contains open U in C^m, holomorphicity and derivative operator norms. None of these citations licenses infinite-dimensional targets or changes a result's conclusion.

G2 at GLOBAL-review.md L940-L947 identifies all four owner/import hypothesis mismatches and explicitly requires source review of K before regenerating exact-copy imports. The current W SPEC change log records root-b8 option (a) and stages precisely these four amendments. That is the repository evidence for the ruling citation; no external conversation is independently certified.

Each proposed hypothesis string equals the corresponding complete reviewed import record in W-imports-review-1.md, including A047 at L95. W-imports-review-2.md gives PASS for all four corrected imports. The three remaining imports in the current W DEPGRAPH have the same strings. Under G3, holomorphic-analytic has since been removed as an import and retained only as proof provenance, as documented by the W SPEC change log. A047's NOTE refers accurately to the reviewed import record, not to a currently retained W import. Its K correction remains source-faithful independently of that removal.

The adversarial reread tested whether the changes silently strengthen applicability beyond the actual source, drop the n/positive-width restrictions, assert boundedness for Fourier uniqueness/identity, impose m >= 1, or promote the real-valued special clause to an unconditional hypothesis. None does. G2's warning about an explicit applicability mismatch is compatible with retaining the source contract version: the omitted source restriction is made explicit; the mathematical source is unchanged. G3's Banach-target proof adaptation is not validated or restored by these amendments.

## Verification and closeout

Read-only commands:

```text
git rev-parse HEAD
python3 -I scripts/proof_depgraph.py --db docs/graph/K/DEPGRAPH.md --json
```

Both exited 0; the JSON command produced no stderr. Its effective nodes, rather than unamended packet text, supplied the old fields above. A read-only Python comparison checked all four records for preservation of the old-premise suffix, empty frozen identity fields, unchanged non-hypothesis mutation fields, and exact reviewed-import hypothesis equality. Output:

```text
K-A045-w-findim-decay: PASS old-premise suffix; PASS non-anchor; PASS other fields unchanged; PASS reviewed-import equality
K-A046-w-conventions-fourier-basic: PASS old-premise suffix; PASS non-anchor; PASS other fields unchanged; PASS reviewed-import equality
K-A047-w-findim-holomorphic-analytic: PASS old-premise suffix; PASS non-anchor; PASS other fields unchanged; PASS reviewed-import equality
K-A048-w-findim-strip-identity: PASS old-premise suffix; PASS non-anchor; PASS other fields unchanged; PASS reviewed-import equality
```

All four requested records are classified PASS; no FAIL replacement blocks, new suspected source errata, introduced deviations or unresolved source-correspondence questions remain in this scope. Only this report is written. No Lake, build, source lint, Lean elaboration, axiom inspection, provider/implementation read, amendment application or state-changing git was performed. This verdict does not certify implementation proofs, W consumer closure, graph reassembly or final W global acceptance. Reassembly/import synchronization remains the integration owner's work.
