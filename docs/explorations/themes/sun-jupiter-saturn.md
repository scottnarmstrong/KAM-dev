# Sun–Jupiter–Saturn

[← Back to the catalogue](../README.md)

Three studies from 30 October 2026 on certifying a KAM torus of a Sun–Jupiter–Saturn model, written after
[striking-applications](../striking-applications.md) §9 called the full planar problem infeasible in the kernel. The
feasibility study found two levers that could close the gap and recommended the secular LG00 model as the first
milestone. The LG00 scout became a running side campaign. The costed plan for the full planar problem corrects several
numbers of the feasibility study and waits for eight owner decisions. For lifetimes (rather than tori) of Sun–Jupiter–
Saturn–Uranus secular models, see [effective stability](effective-stability.md).

| Document | Status | One line |
|---|---|---|
| [sjs-feasibility](../sjs-feasibility.md) | scouted; partly superseded by sjs-plan | Route B plus packed kernel arithmetic would make the full planar torus checkable |
| [sjs-lg00-scout](../sjs-lg00-scout.md) | scouted; running as the LG00 side campaign | LG00's secular torus is checkable at lunar-class cost |
| [sjs-plan](../sjs-plan.md) | proposed (8 owner decisions) | A synodic chart and a packed layer: 15–300 CPU-h per torus, 8–15k Lean lines |

**The running LG00 campaign** (from [`lg00-status.json`](../../campaign/side/lg00-status.json), reviewed 31 October
2026, 04:45 UTC; 47 % by weighted stages). Done: the scout; Lean Diophantine lemmas for the two frequency directions;
the certificate-data generator with the exact square-root Hamiltonian, whose exact dry runs pass all seven landed
sub-checks at L = 20 and L = 21; a kernel pilot on representative shards, each under 6.1 GB (budget gate passed: route A
refined at L = 20, about 26 CPU-h projected, range 13–40). In progress (15 %): the kernel certificate of the torus T′
and the closed theorem; the final statement is written and independently audited, and the Hamiltonian identity,
positivity and physical-ODE corollary are proved on a side branch. Not started: the second torus T″ (confinement between
two tori), an independent audit and a separate repository. The certificate data live on branch `lg00-cert` and never
enter KAM-dev's default build.

## Can we certify a KAM torus of the planar Sun–Jupiter–Saturn system? (SJS-FEAS)

**[sjs-feasibility.md](../sjs-feasibility.md)** · 30 October 2026 · feasibility study (Python, literature, small kernel
probes) · status: **scouted**, **partly superseded** by [sjs-plan](../sjs-plan.md)

The study re-examines the scout's verdict on Figueras–Haro's planar Sun–Jupiter–Saturn torus (FH25, a 3-torus of the
reduced three-degree-of-freedom problem). It concludes that the gap can be closed, but only with two things that did not
exist then: the v2 theorem in its route-B form (Figueras–Haro's modified Newton step, split derivative bounds, measured
torsion, frequency-specific small-divisor constants) and kernel arithmetic that keeps Fourier models packed in big
integers. It explains where the six orders go: route B gains 68 orders over v1 on FH's data; the d'Alembert structure and
reversibility cut the support from about 10⁸ to 3.6–4.7·10⁶ coefficients; and the measured kernel cost is interpretive
overhead (0.2–1.5 ms per coefficient), not big-integer arithmetic. It recommends LG00's secular model as the first
milestone, then route B, then a packed-arithmetic prototype as the decision point.

- **Numbers.** Kernel CPU-hours per torus: v1 with the landed checker about 10⁷; route B with a per-slot checker
  1.0–3.3·10⁴ and 1–3.5 TB of advice; route B with packed (GMP-resident) arithmetic 34–351; hybrid plus packed 6–19 (an
  estimate). Numerical Diophantine constant 1.85·10⁻⁵ against FH25's certified 1.69·10⁻⁶. Measured landed packed
  product: about 1.3·10⁻⁴ S^1.9 s.
- **Suspected defects in landed SO code** (reported, not changed): `foldr` norms fail near 10⁴ terms, `toMants` is
  superlinear, `intSlotsBound` has a cliff near 6,000 slots, `liveSet` is quadratic.
- **Superseded or stale.** [sjs-plan](../sjs-plan.md) §8 corrects nine of its claims: the hybrid gives no kernel gain (so
  "6–19 CPU-h" is wrong); charts do reduce the support (2.7×) and the constants; the d'Alembert factor of 7 does not hold
  on the torus (3.7 at L = 10 and falling); the operation count is 252–657 products, not 60–150; the data ledger is
  80–560 GB, not 3–4 GB; its unexplained 11–22× gap between modelled and measured lunar cost is closed. Route B has
  since been proved in Lean (README; D45).
  The "129 monomials" for LG00 was corrected to 69 in the document after the [LG00 scout](../sjs-lg00-scout.md).
  [ambition](../ambition.md) and programs [A](../program-a-plan.md)–[D](../program-d-plan.md) quote its per-slot figure of
  10,000–33,000 CPU-h and do not cite sjs-plan, which prices the current checker (after CSPLIT) at 7·10⁴–5·10⁵ CPU-h per
  torus and finds the earlier per-slot constants 3–5× optimistic.

## Scouting the first formally verified KAM torus of a planetary model: LG00 (SJS-LG00)

**[sjs-lg00-scout.md](../sjs-lg00-scout.md)** · 30 October 2026 · scouting study (Python, two small kernel probes) ·
status: **scouted**; **running** as the LG00 side campaign (see the status box above)

The scout transcribes Locatelli–Giorgilli's (2000) secular Sun–Jupiter–Saturn polynomial (eq. (11): 69 monomials,
exact rationals; it reproduces the paper's energy to 5·10⁻¹⁶ and finds no misprint), computes the invariant torus T′ with
LG00's noble frequency ratio on LG00's energy level, and evaluates every available a-posteriori theorem on it. Verdict:
feasible with the then-landed sharp certifier, at 36 digits and about 2.5·10³ Fourier coefficients, less than the lunar
certificate. It needs a Lean Diophantine lemma for the noble direction and a representation of √(I₁I₂). Proposed claim:
"to our knowledge, the first formally verified KAM torus of a planetary model", a formal reproduction of one of LG00's
two confining tori, not new mathematics.

- **Numbers.** Required invariance error on T′: sealed theorem 10⁻¹³², sharp 10⁻³¹, route A 10⁻¹⁴ (10⁻¹²·² with
  frequency-specific constants; 16–18 digits, 545–680 coefficients, 3–75 CPU-h). Sharp route: 7–150 CPU-h per torus with
  the D34 packing fix, 54–71 on the code of the time. Diophantine constant 0.2251 for τ = 1, seven times LG00's
  conservative value. One landed kernel shard of a 3,025-term product: 14.1 s, 4.96 GB.
- **Beyond LG00.** Tori at two and three times LG00's eccentricities converge and would need 48–54 digits and 30–50 CPU-h.
  LG00's own KAM step had a 3 % margin (0.840 against 0.868), so these "would plausibly be new results about the model;
  that was not established".
- **Stale details.** The `sqrt` node has since landed (D45) and route A is wired into the v2 certifier; the running
  campaign uses route A refined at L = 20 with the exact square-root Hamiltonian, not the sharp route at L = 36.
- **Disagreement.** The scout calls the confinement between T′ and T″ "a topological argument outside our certificates"
  and does not propose it. The campaign's status file now lists "second torus T″ (confinement between two tori)" as a
  stage, and [ambition](../ambition.md) notes that two suitably placed tori on one energy surface give confinement.

## A costed plan to certify a KAM torus of the Sun–Jupiter–Saturn system (SJS-PLAN)

**[sjs-plan.md](../sjs-plan.md)** · 30 October 2026 · planning study with small experiments; every number labelled
measured, model or estimate · status: **proposed** (eight owner decisions); not started

The plan recomputes FH25's torus in Python (it reproduces |⟨T⟩⁻¹| = 354.077 and ⟨Ĝ⟩ = 2.176574188839) and finds that the
chart is the largest lever, which the feasibility study did not have. On a Delaunay polydisc the box contains e = 0, so
the landed ball arithmetic cannot work there at all; in a synodic chart built from polar coordinates in the secular
normal modes, the second-derivative majorant falls from 5·10¹⁰ to about 1.65·10³ and the required invariance error rises
from 10⁻⁴⁶·³ to 10⁻³⁸·⁰ (FH units; majorants sampled, not enclosed). With a packed big-integer kernel layer (one `Nat`
per block of a Fourier model), one torus costs about 15–300 CPU-h and a ledger of 80–560 GB; a rented 48-core machine
checks it in 1–20 hours for under USD 200. The cost is Lean work: 8–15k lines and about 4–6 weeks (×2 either way).

- **Claim it could make.** A formally verified KAM torus of the planar three-body problem with the real Sun–Jupiter–Saturn
  masses and eccentricities, at a frequency within 10⁻⁸ of the ephemeris. FH25 list their computer-assisted proof as in
  progress; if it has not appeared this would be new mathematics. The literature was not checked.
- **Numbers.** Current checker: 7·10⁴–5·10⁵ CPU-h per torus. Kernel limits found: the kernel refuses a `Nat` above
  2²⁷ bytes unless `LEAN_NAT_MAX_SIZE` is raised, and `Nat.shiftLeft` with exponent ≥ 2³² ends the process with an
  internal panic. An explicit cubic frequency within 10⁻⁸ of FH's has certified γ = 2.8·10⁻⁷, τ = 2. Largest
  uncertainty: support measured up to 10 digits and used at 45 (a factor 3 in cost).
- **Decisions asked of the owner.** Build the packed layer (6–10k lines); adopt the synodic chart with a new trusted
  node for the regular Kepler equation; allow `LEAN_NAT_MAX_SIZE`; rent hardware for the final run (lemma.farm has 43 GB
  of free disk); the cubic frequency; route B isoenergetic; the sequence LG00 → packed gate → planar SJS, with secular
  SJSU optional; a separate data repository.
- **Disagreements.** It replaces the infeasibility verdict of [striking-applications](../striking-applications.md) §9
  and corrects [sjs-feasibility](../sjs-feasibility.md) in nine rows (listed in that entry). It makes a
  secular Sun–Jupiter–Saturn–Uranus model optional for the torus campaign, whereas programs
  [B](../program-b-plan.md), [C](../program-c-plan.md) and [D](../program-d-plan.md) propose such a model (GLS17) as the
  first planetary lifetime target. The goals differ (a torus here, a lifetime there); sjs-plan and programs B and D all
  note that GLS17's full coefficient data are not printed and would have to be recovered or rebuilt.

[← Back to the catalogue](../README.md)
