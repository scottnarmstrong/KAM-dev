# W-w8a: slice review 1

Reviewer: sol-review-W-w8a. Verdict: **FAIL**.

Read w8-assembly.tex L1-L410 in full, plus all cited W1/W2/W3/W5/W6/W7 statement suppliers and the W6 analyticity step. Checked shell margin >= 4 r_n^2, the positive sharp majorant, eps_0 admissibility, Cauchy strip loss, the max-norm/sqrt2 conversions and weak-invariance discharge. Phase phi in se-der is not sineMode, and lambda=alpha_n/M is not lam.

Source-only topology review. PASS does not assert mathematical proof completion or Lean closure. No implementation Lean was read, and no Lean, Lake, build, source lint or state-changing git command was run.

The eleven corpus hashes were checked with sha256sum -c docs/graph/W/CORPUS.sha256: all OK. The permitted read-only slice checker returned zero problems for this packet.

Packet snapshot SHA-256: nodes d24c10e439ec0b8f8ba86e0efa5bc43790aa4c959c703b753d833b0cf636ffc1; coverage 08b85ed59b579bf9c3761fd0a9e91f17ce5f4d1021613bdee1e15d92b6b113a8.

## Node verdicts

| Node | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w8:ext-inner | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-inner@L59-L64 |
| bpW:w8:ext-mono | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-mono@L65-L68 |
| bpW:w8:ext-compact | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-compact@L69-L71 |
| bpW:w8:ext-exp | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-exp@L72-L76 |
| bpW:w8:ext-sqrt | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-sqrt@L77-L78 |
| bpW:w8:ext-dist | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-dist@L79-L81 |
| bpW:w8:ext-rpow | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-rpow@L82-L86 |
| bpW:w8:ext-local | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-local@L87-L92 |
| bpW:w8:const | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:const@L100-L113 |
| bpW:w8:shells | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L117-L128 |
| bpW:w8:shell-data | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L132-L148; blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L149-L172 |
| stepW:w8:sd-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L150-L153; blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L150-L153 |
| stepW:w8:sd-trim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L154-L159; blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L154-L159 |
| stepW:w8:sd-init | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L160-L167; blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L160-L167 |
| stepW:w8:sd-prep | FAIL | The last bound uses (i) eps^sharp <= gamma alpha, separately from the initial perturbation estimate (iii); its supplying step is missing. |
| bpW:w8:sharp-prep | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L178-L185; blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L186-L194 |
| stepW:w8:sp-step | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-step@L187-L188; blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-step@L187-L188 |
| stepW:w8:sp-cmp | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L189-L193; blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L189-L193 |
| bpW:w8:shell-iter | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L198-L209 |
| bpW:w8:w6-general | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L212-L217; blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L218-L227 |
| stepW:w8:g-app | FAIL | The admissible starting-size interval is a parameter of wave-iteration; the direct use of that definition is missing. The to-w8 reference occurs only in the source note L228-L229, so its provenance edge is removed. |
| stepW:w8:g-freq | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-freq@L222-L223; blueprint-W/parts/w8-assembly.tex#stepW:w8:g-freq@L222-L223 |
| stepW:w8:g-excl | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224; blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224 |
| stepW:w8:g-tori | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-tori@L225-L226; blueprint-W/parts/w8-assembly.tex#stepW:w8:g-tori@L225-L226 |
| bpW:w8:etor | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L231-L234; blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L235-L244 |
| stepW:w8:e-tor | FAIL | The estimate substitutes the shell-iteration error formula and uses alpha_n,kappa_n <= 1, without those suppliers. |
| stepW:w8:e-om | FAIL | The proof uses eps_{0,n} <= gamma_1 check alpha_n and lambda_i > i without direct supplier edges. |
| bpW:w8:freq-shell | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L248-L257; blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L258-L269 |
| stepW:w8:fs-lim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L259-L261; blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L259-L261 |
| stepW:w8:fs-low | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L262-L263; blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L262-L263 |
| stepW:w8:fs-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L265; blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L265 |
| stepW:w8:fs-reg | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L268; blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L268 |
| bpW:w8:torus-shape | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L275-L289; blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L290-L310 |
| stepW:w8:ts-bd | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L293; blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L293 |
| stepW:w8:ts-real | FAIL | The positivity argument uses e <= 1, established by etor, without an edge. |
| stepW:w8:ts-per | FAIL | The integer-valued phase difference is zero because 2e < 1; etor supplies that bound but is absent. |
| stepW:w8:ts-cauchy | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L303-L306; blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L303-L306 |
| stepW:w8:ts-ball | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L307-L309; blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L307-L309 |
| bpW:w8:Kshell | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L314-L319 |
| bpW:w8:shell-embedding | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L323-L325; blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L326-L350 |
| stepW:w8:se-per | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-per@L328-L328; blueprint-W/parts/w8-assembly.tex#stepW:w8:se-per@L328-L328 |
| stepW:w8:se-an | FAIL | The analyticity transfer consumes the continuous linear tau_E from the standing data, without an edge. |
| stepW:w8:se-inj | FAIL | The proof uses tau_E injective and Z bijective, and its local equality premise is omitted. |
| stepW:w8:se-der | FAIL | The kernel argument omits its local premise fderiv R K theta h = 0 and the tau_E/Z identifications. |
| bpW:w8:shell-close | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L355-L358; blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L359-L378 |
| stepW:w8:sc-tan | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L362-L365; blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L362-L365 |
| stepW:w8:sc-dist | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L366-L369; blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L366-L369 |
| stepW:w8:sc-gamma | FAIL | The final radius-to-t_n estimate consumes shell-data(i) directly. |
| stepW:w8:sc-close | FAIL | The proof uses tau_E's isometry and the definition E_7 = 162 E_5 + E_6 without edges. |
| stepW:w8:sc-size | FAIL | The size estimate consumes the bound from sc-gamma, the torus radius and tau_E isometry. |
| bpW:w8:shell-inv | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L383-L392; blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L393-L407 |
| stepW:w8:si-weak | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L397; blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L397 |
| stepW:w8:si-tr | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L399; blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L399 |
| stepW:w8:si-frozen | FAIL | The local proof explicitly identifies the inverse transport with coeff but lacks the frozen coeff edge. |
| stepW:w8:si-cont | FAIL | The continuity proof explicitly uses Z^{-1} and tau_E continuous linear, without a standing-data edge. |
| bpW:w8#data | FAIL | The data paragraph directly uses the W5 constants c_F,c_F^natural,C_2^natural,t^natural but no edge supplies their defining data block. |

## Coverage verdicts

| Coverage item | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w8:ext-inner | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-inner@L59-L64 |
| bpW:w8:ext-mono | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-mono@L65-L68 |
| bpW:w8:ext-compact | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-compact@L69-L71 |
| bpW:w8:ext-exp | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-exp@L72-L76 |
| bpW:w8:ext-sqrt | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-sqrt@L77-L78 |
| bpW:w8:ext-dist | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-dist@L79-L81 |
| bpW:w8:ext-rpow | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-rpow@L82-L86 |
| bpW:w8:ext-local | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-local@L87-L92 |
| bpW:w8:const | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:const@L100-L113 |
| bpW:w8:shells | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L117-L128 |
| bpW:w8:shell-data | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L132-L148 |
| stepW:w8:sd-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L150-L153 |
| stepW:w8:sd-trim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L154-L159 |
| stepW:w8:sd-init | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L160-L167 |
| stepW:w8:sd-prep | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171 |
| bpW:w8:sharp-prep | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L178-L185 |
| stepW:w8:sp-step | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-step@L187-L188 |
| stepW:w8:sp-cmp | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L189-L193 |
| bpW:w8:shell-iter | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L198-L209 |
| bpW:w8:w6-general | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L212-L217 |
| stepW:w8:g-app | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L221 |
| stepW:w8:g-freq | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-freq@L222-L223 |
| stepW:w8:g-excl | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224 |
| stepW:w8:g-tori | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-tori@L225-L226 |
| bpW:w8:etor | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L231-L234 |
| stepW:w8:e-tor | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L239 |
| stepW:w8:e-om | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L243 |
| bpW:w8:freq-shell | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L248-L257 |
| stepW:w8:fs-lim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L259-L261 |
| stepW:w8:fs-low | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L262-L263 |
| stepW:w8:fs-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L265 |
| stepW:w8:fs-reg | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L268 |
| bpW:w8:torus-shape | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L275-L289 |
| stepW:w8:ts-bd | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L293 |
| stepW:w8:ts-real | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L299 |
| stepW:w8:ts-per | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L302 |
| stepW:w8:ts-cauchy | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L303-L306 |
| stepW:w8:ts-ball | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L307-L309 |
| bpW:w8:Kshell | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L314-L319 |
| bpW:w8:shell-embedding | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L323-L325 |
| stepW:w8:se-per | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-per@L328-L328 |
| stepW:w8:se-an | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L330 |
| stepW:w8:se-inj | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L331-L337 |
| stepW:w8:se-der | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L338-L349 |
| bpW:w8:shell-close | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L355-L358 |
| stepW:w8:sc-tan | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L362-L365 |
| stepW:w8:sc-dist | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L366-L369 |
| stepW:w8:sc-gamma | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L372 |
| stepW:w8:sc-close | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L375 |
| stepW:w8:sc-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377 |
| bpW:w8:shell-inv | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L383-L392 |
| stepW:w8:si-weak | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L397 |
| stepW:w8:si-tr | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L399 |
| stepW:w8:si-frozen | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L403 |
| stepW:w8:si-cont | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L406 |
| heading:bpW:w8 | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8@L1-L1 |
| heading:bpW:w8:ext | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:ext@L55-L55 |
| heading:bpW:w8:shell-sec | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-sec@L96-L96 |
| heading:bpW:w8:iter-sec | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:iter-sec@L176-L176 |
| heading:bpW:w8:tori-sec | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:tori-sec@L273-L273 |
| w8-assembly:source-L114 | PASS | blueprint-W/parts/w8-assembly.tex#source@L114-L114 |
| w8-assembly:source-L129 | PASS | blueprint-W/parts/w8-assembly.tex#source@L129-L129 |
| w8-assembly:source-L173 | PASS | blueprint-W/parts/w8-assembly.tex#source@L173-L173 |
| w8-assembly:source-L195 | PASS | blueprint-W/parts/w8-assembly.tex#source@L195-L195 |
| w8-assembly:source-L210 | PASS | blueprint-W/parts/w8-assembly.tex#source@L210-L210 |
| w8-assembly:source-L228 | PASS | blueprint-W/parts/w8-assembly.tex#source@L228-L228 |
| w8-assembly:source-L245 | PASS | blueprint-W/parts/w8-assembly.tex#source@L245-L245 |
| w8-assembly:source-L270 | PASS | blueprint-W/parts/w8-assembly.tex#source@L270-L270 |
| w8-assembly:source-L311 | PASS | blueprint-W/parts/w8-assembly.tex#source@L311-L311 |
| w8-assembly:source-L320 | PASS | blueprint-W/parts/w8-assembly.tex#source@L320-L320 |
| w8-assembly:source-L351 | PASS | blueprint-W/parts/w8-assembly.tex#source@L351-L351 |
| w8-assembly:source-L379 | PASS | blueprint-W/parts/w8-assembly.tex#source@L379-L379 |
| w8-assembly:source-L408 | PASS | blueprint-W/parts/w8-assembly.tex#source@L408-L408 |
| w8-assembly:prose-L5-L11 | PASS | blueprint-W/parts/w8-assembly.tex#prose@L5-L11 |
| w8-assembly:prose-L13-L34 | PASS | blueprint-W/parts/w8-assembly.tex#prose@L13-L34 |
| w8-assembly:prose-L36-L53 | PASS | blueprint-W/parts/w8-assembly.tex#prose@L36-L53 |
| w8-assembly:prose-L57-L58 | PASS | blueprint-W/parts/w8-assembly.tex#prose@L57-L58 |
| w8-assembly:prose-L93-L94 | PASS | blueprint-W/parts/w8-assembly.tex#prose@L93-L94 |
| w8-assembly:prose-L98-L98 | PASS | blueprint-W/parts/w8-assembly.tex#prose@L98-L98 |

all other coverage items PASS.

## Complete replacement fragments

These are proposals only. Existing packet records are unchanged. New and revised records remain PROPOSED for an independent delta reviewer.

```text
NODE: stepW:w8:sd-prep
KIND: step
TITLE: Lemma~\ref{bpW:w6:prep-step}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171
CONTRACT_ID: stepW:w8:sd-prep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-data: Definitions bpW:w8:const and bpW:w8:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-data (for every n >= 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w5:initial, stepW:w8:sd-init, bpW:w6:to-w8, stepW:w8:sd-size
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L168 | its hypotheses
EDGE: bpW:w5:initial | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L170-L170 | P real periodic in S_{p+1}
EDGE: stepW:w8:sd-init | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L171-L171 | (iii)
EDGE: bpW:w6:to-w8 | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L146-L146 | its conditions
EDGE: stepW:w8:sd-size | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L171-L171 | (i) supplies eps^sharp_n <= gamma alpha_n
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:g-app
KIND: step
TITLE: Applicability
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L221
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L221
CONTRACT_ID: stepW:w8:g-app
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:w6-general: the shell iteration (Definition bpW:w8:shell-iter)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:w6-general (for every n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lemma bpW:w6:applicable for the value eps_{0,n}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:applicable, bpW:w8:sharp-prep, bpW:w6:wave-iteration
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:applicable | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L219 | applicability
EDGE: bpW:w8:sharp-prep | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L221-L221 | eps_{0,n} admissible
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L220-L220 | the allowed parameter interval for eps_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:e-tor
KIND: step
TITLE: $e_{\rm tor}$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L239
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L239
CONTRACT_ID: stepW:w8:e-tor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:etor: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:etor (for every n); within the step: n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: e^(n)_tor <= E_5 t_n^{1/64} <= 7/256
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:const, bpW:w8:shell-iter, bpW:w8:shell-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L238-L238 | E_4, E_5, t_0
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L238 | the formula for e_tor and eps_{0,n}
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L238-L238 | alpha_n and kappa_n <= 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:e-om
KIND: step
TITLE: $\varepsilon_\omega$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L243
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L243
CONTRACT_ID: stepW:w8:e-om
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:etor: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:etor (for every n); within the step: n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: eps^(n)_omega <= alpha_n/(70 L_A) <= alpha_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants, bpW:w7:constdef, bpW:w7:freqcoords, bpW:w0:basis#lam, bpW:w8:sharp-prep, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L242-L242 | gamma, gamma_1
EDGE: bpW:w7:constdef | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L242-L242 | (C4) theta_0
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L243-L243 | (ii) L_A
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L243-L243 | lambda occurs directly here (frozen lam)
EDGE: bpW:w8:sharp-prep | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L240 | the upper bound on eps_{0,n}
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L243-L243 | lambda_1 > 1 and lambda_2 > 2 yield L_A > 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:ts-real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L299
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L299
CONTRACT_ID: stepW:w8:ts-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:torus-shape: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:torus-shape (theta (complex or real as stated)); within the step: real theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w3:coords, bpW:w8:shell-data, bpW:w8:ext-exp, stepW:w8:ts-bd, bpW:w8:etor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L294 | (i), (iv)
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L295-L295 | rho
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L297-L297 | (i), (ii)
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L299-L299 | complex exponential
EDGE: stepW:w8:ts-bd | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L297-L297 | (i)
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L297-L297 | e <= 7/256 <= 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:ts-per
KIND: step
TITLE: Periodicity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L302
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L302
CONTRACT_ID: stepW:w8:ts-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:torus-shape: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:torus-shape (theta (complex or real as stated)); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:ext-exp, stepW:w8:ts-real, bpW:w8:etor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L300 | (i) periodicity
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L301-L301 | integer-valued continuous functions
EDGE: stepW:w8:ts-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L300 | (ii)
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L302-L302 | 2e <= 14/256 < 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:se-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L330
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L330
CONTRACT_ID: stepW:w8:se-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-embedding: n >= 0, xi in Gamma_n
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-embedding (for every n, xi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: AnalyticOnNhd R K univ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:ext-local, bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L329 | (v)
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L330-L330 | continuous linear maps preserve AnalyticOnNhd
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L330-L330 | tau_E is a continuous linear isometric bijection
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:se-inj
KIND: step
TITLE: Injectivity modulo $\Z^2$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L331-L337
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L331-L337
CONTRACT_ID: stepW:w8:se-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-embedding: n >= 0, xi in Gamma_n; local implication premise K(theta) = K(theta'); local definitions Psi = tilde Psi^(n)_xi, x = Z^{-1} Psi, K = K^(n)_xi
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-embedding (for every n, xi); within the step: theta, theta'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: injectivity modulo Z^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:gamma-real, bpW:w8:torus-shape, bpW:w8:ext-exp, bpW:w8#data, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L332-L332 | (iii) injectivity
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L333-L333 | (ii)-(v)
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L335-L335 | e^z = 1
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L332-L332 | tau_E is injective
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L333-L333 | Z is bijective
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:se-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L338-L349
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L338-L349
CONTRACT_ID: stepW:w8:se-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-embedding: n >= 0, xi in Gamma_n; local kernel premise fderiv R K theta h = 0; Psi = tilde Psi^(n)_xi, x = Z^{-1} Psi, K = K^(n)_xi
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-embedding (for every n, xi); within the step: theta, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: fderiv R K theta is injective
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:torus-analytic, stepW:w6:t-an, bpW:w8:ext-local, bpW:w3:flow, bpW:w8:torus-shape, bpW:w8#data, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:torus-analytic | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L339-L339 | fderiv via the complex derivative
EDGE: stepW:w6:t-an | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L339-L339 | holomorphy
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L340-L340 | chain rule
EDGE: bpW:w3:flow | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L342-L342 | (iii) invertible, (iv) real
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L345-L345 | (ii), (iv)
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L340-L340 | the inverse transport tau_E^{-1} and its linearity
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L341-L344 | Z^{-1} identifies fixed real points and is injective
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:sc-gamma
KIND: step
TITLE: Birkhoff map
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L372
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L372
CONTRACT_ID: stepW:w8:sc-gamma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Gamma^R(x) - x¦¦_E <= E_6 t_n^{3/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:gamma-real, bpW:w1:embed, bpW:w8:torus-shape, bpW:w8:shell-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L370 | (ii)
EDGE: bpW:w1:embed | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L370 | norm comparison
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L372-L372 | (v)
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L372-L372 | rho_n^2 <= 2 c_A t_n
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:sc-close
KIND: step
TITLE: Closeness
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L375
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L375
CONTRACT_ID: stepW:w8:sc-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the closeness bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:sc-dist, stepW:w8:sc-gamma, bpW:w8:etor, bpW:w0:periodone#linearTorus, bpW:w8#data, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:sc-dist | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L374 | distance
EDGE: stepW:w8:sc-gamma | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L374 | Birkhoff map
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L375-L375 | e
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L374 | the linear torus K^0_I occurs directly here (frozen linearTorus)
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L374 | tau_E is isometric
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L375 | E_7 = 162 E_5 + E_6
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:sc-size
KIND: step
TITLE: Size
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377
CONTRACT_ID: stepW:w8:sc-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦K^(n)_xi(theta)¦¦ < 2 rho_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:gamma-real, stepW:w8:sc-gamma, bpW:w8:torus-shape, bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L376 | rho_1^2 = 1/(160 C_F)
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L376 | (ii)
EDGE: stepW:w8:sc-gamma | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377 | the cubic bound on Gamma^R(x)-x
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377 | ¦¦x¦¦ < rho_n <= r_1 = rho_1/sqrt2
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L377-L377 | tau_E preserves the norm
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:si-frozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L403
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L403
CONTRACT_ID: stepW:w8:si-frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-inv: n >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-inv ((i) for xi in Gamma_n, theta in R^2, j in N_+); within the step: theta, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) in the frozen form
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:coordinatewise, bpW:w1:cubic-analytic, stepW:w8:si-tr, bpW:w8#data, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L402-L402 | coordinates of the derivative
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L402-L402 | (iv)
EDGE: stepW:w8:si-tr | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L400 | the coefficient system
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L400 | tau_E and coeff
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L403-L403 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L402-L402 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L402 | kappa_{1,1} of each component of K is its frozen coeff
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w8:si-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L406
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L406
CONTRACT_ID: stepW:w8:si-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-inv: n >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-inv ((i) for xi in Gamma_n, theta in R^2, j in N_+); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) continuity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:w6-general, bpW:w8:torus-shape, bpW:w3:gamma-real, bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L404 | (ii)
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L404 | transfer
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L405-L405 | (v)
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L406-L406 | (i) Gamma^R analytic
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L405-L406 | Z^{-1} and tau_E are continuous linear
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w8#data
KIND: definition
TITLE: W8 standing data and notation
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8@L36-L53
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: m > 0 and the W0 conventions, a = p = 1; max norms on R^2, C^2; Leb = volume on Fin 2 -> R; Fin 2 index i is mode i+1; shells indexed by n, W6's iteration index mu; the exponent 52 of W5-W6; W3's rho_1, C_*, C'_K, C_F, Z, Gamma, Gamma^R, r_1 = rho_1/sqrt2; W5's c_A and A_xi; W6's s, sigma_P, s_0, sigma_0, M, gamma_0, gamma_1, gamma, c_F, c^natural_F, C^natural_2, t^natural = 53; W7's tau = 24, theta_0, alpha_0, C_7, L_A, N_A, omega^0, Omega^0; W2's M_m; the transport tau_E = tau_{1,1} x tau_{1,1} : E_{1,1} -> WaveSpace, a linear isometric bijection with inverse coeff in each factor; r(I) = sqrt(I_1 + I_2); linearTorus I hI = tau_E o K^0_I (independent of hI)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:mass, bpW:w3:main, bpW:w3:gamma-real, bpW:w3:coords, bpW:w5:action-angle, bpW:w6:constants, bpW:w7:constdef, bpW:w7:omega0, bpW:w7:freqcoords, bpW:w2:curve, bpW:w1:space, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace, bpW:w0:periodone#linearTorus, bpW:w3:majorant, bpW:w3:F, bpW:w5:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w8-assembly.tex#bpW:w8@L36-L36 | m > 0
EDGE: bpW:w3:main | blueprint-W/parts/w8-assembly.tex#bpW:w8@L42-L42 | Gamma
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#bpW:w8@L42-L42 | Gamma^R
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#bpW:w8@L41-L41 | Z
EDGE: bpW:w5:action-angle | blueprint-W/parts/w8-assembly.tex#bpW:w8@L43-L43 | c_A, A_xi
EDGE: bpW:w6:constants | blueprint-W/parts/w8-assembly.tex#bpW:w8@L45-L45 | W6's constants
EDGE: bpW:w7:constdef | blueprint-W/parts/w8-assembly.tex#bpW:w8@L47-L47 | W7's constants
EDGE: bpW:w7:omega0 | blueprint-W/parts/w8-assembly.tex#bpW:w8@L47-L47 | omega^0, Omega^0
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#bpW:w8@L48-L48 | L_A, N_A
EDGE: bpW:w2:curve | blueprint-W/parts/w8-assembly.tex#bpW:w8@L48-L48 | M_m
EDGE: bpW:w1:space | blueprint-W/parts/w8-assembly.tex#bpW:w8@L50-L50 | (iv) tau_E isometric with inverse coeff
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w8-assembly.tex#bpW:w8@L50-L50 | coeff
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w8-assembly.tex#bpW:w8@L49-L49 | WaveSpace
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#bpW:w8@L52-L52 | linearTorus = tau_E o K^0_I
EDGE: bpW:w3:majorant | blueprint-W/parts/w8-assembly.tex#bpW:w8@L40-L40 | C_*
EDGE: bpW:w3:F | blueprint-W/parts/w8-assembly.tex#bpW:w8@L40-L40 | C_F
EDGE: bpW:w5:data | blueprint-W/parts/w8-assembly.tex#bpW:w8@L45-L46 | the ordinary and preparatory step constants, summarized in the W5 ledger
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled 'Standing data and notation' paragraph (SPEC hypothesis packages).
```

## Suspected blueprint errata and deviations

No new suspected blueprint defect. The missing premises and edges identified above are graph extraction defects.

Review deviations: none. No packet, frozen file, manifest, blueprint, generated file or implementation file was edited.
