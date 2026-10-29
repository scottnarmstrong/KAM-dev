# Lunar spin–orbit certificate project: plan (track SO)

Owner decision 2026-10-29 (D30): start now; target band **|p(t) − 1| ≤ 33/1000** with the proposal's frequencies
ν± = 1 ± 1/(40 + g), g = (√5 − 1)/2. Sources: `docs/explorations/lunar-spin-orbit-certificate-proposal.md` (the
proposal) and `docs/explorations/lunar-spin-orbit-feasibility-report.md` (the pilot; the 3% band fails numerically,
the tori reach 0.968007 and 1.031992; 3.3% leaves about 0.001 of headroom).

## Deliverables

1. **The certificate black box (the reusable core).** A Lean checker `checkTorusCertificate : TorusCertificate → Bool`
   and a soundness theorem `checkTorusCertificate_sound : checkTorusCertificate c = true → CertifiedTorusWithBounds c`,
   proved once. Any external numerical candidate that passes the kernel-evaluated check yields an exact invariant torus
   with explicit error bounds, through the sealed isoenergetic a-posteriori theorem `KAM.Iso.Apost.g1_explicit`.
   Scope of the first version: see "Open scope decision" below.
2. **The lunar application.** Two concrete certificates (ν− and ν+), proofs that both checks pass, the barrier and
   confinement theorems (proposal §3) with the 3.3% band, reproduction data, axiom audit.

## Adopted refinements (review of the proposal, 2026-10-29)

- **Replay gate first.** Kernel replay of a 10⁻¹⁰³-precision certificate is the dominant risk (no `native_decide`;
  trust boundary = kernel only). Package SO-REPLAY measures it before the checker is built.
- **π-free arithmetic.** Work with v = 2πu: the scalar residual is 2π × (an expression with rational Fourier data),
  so π is needed only coarsely (strip weights). Frequencies are exact in ℚ(√5).
- **A-posteriori composition.** The certificate ships the coefficients of E = exp(2iv) and the checker verifies the
  identity ∂E = 2i(∂v)E with a remainder bound, instead of a long Taylor series in the kernel.
- **Headline graphs are continuous.** Confinement needs continuous invariant graphs; real-analyticity of the graphs and
  the analytic conjugacy (proposal Theorem A items 1 and 3) become a later corollary.
- **Global existence** from the globally Lipschitz periodic force; the barrier argument gives confinement.
- **Constants lever.** If replay is too slow, a sharper explicit-constants theorem for n = 2, τ = 1 (new, unfrozen; the
  frozen G1 is untouched) and rotated angle coordinates are the two levers.

## Workflow

Unfrozen helper code first, in new directories `KAM/Certificate/` and `KAM/SpinOrbit/`, generator in
`scripts/spin_orbit/`, data in `certificates/lunar-spin-orbit/`. Packages run through the inp offload workflow
(prover, independent audit, sub-orchestrator landing). The final public statements are frozen only after the owner
approves their exact Lean text. Existing KAM/Fourier and KAM/Diophantine modules (Zohar's area) are used read-only.

## Waves

- **W0 (now):** SO-GEN (Python generator, exact data, π-free normalization, reproduces the pilot), SO-REPLAY (kernel
  replay-cost prototype: go/no-go), SO-MODEL (exact model, period-one normalization, scalar embedding identities),
  SO-DIO (quadratic Diophantine bounds γ = 1/21, 1/42).
- **W1 (after the replay gate):** arithmetic backend, finite Fourier algebra with correctness proofs, strip-norm
  bounds, composition, Gram and averaged-torsion inverse certificates.
- **W2:** certificate ⇒ every hypothesis of `g1_explicit`; clock lemma; graph inversion and error transport; barrier
  and global solutions. The black-box soundness theorem closes here.
- **W3:** lunar data, passing checks, final theorems; statement review and freeze; seal and audit.

## Scope decision (owner, 2026-10-29): fully general black box

The first black box is **fully general**: any dimension n, analytic Hamiltonians given as finite expressions, and
general Fourier embeddings in all coordinates, all running through `g1_explicit`. The spin–orbit class and the lunar
data are its first client. Consequences:

- **SO-DESIGN** (Opus, before wave 1): an exact-signature Lean design for the general checker and its soundness theorem
  (`docs/tracks/SO/design/SO-LEAN-DESIGN.md`, draft signatures in `.drafts/design/SOSignatures.lean`), then an
  independent design audit. The arithmetic representation is fixed after the replay gate (SO-REPLAY).
- The Diophantine hypothesis enters the general theorem as a proved `IsDiophantine` input; the quadratic-field module
  (SO-DIO) discharges it for n = 2 and the lunar frequencies.
- Estimated size: about 21–37k hand-written lines (the 13–22k spin–orbit estimate plus 8–15k for generality), plus
  generated certificate data.
