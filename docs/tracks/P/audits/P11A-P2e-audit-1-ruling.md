# P11A-P2e audit 1: orchestrator ruling (OVERNIGHT 23:15)

Audit 1 failed P2e only on F1: `p11_hc_mean` / `p11_mean_real_bound` take the premise hOmega (Omega real on real
actions), which P2b's `p11_holo_data` (exporting only `Nonempty (P11HoloData D)`) did not supply. The audit found the
mean clause otherwise exact. By ruling (OVERNIGHT 22:46) the closeout was assigned to P11A-P2f, which added a proved
`Omega_real` field to `P11HoloData` and discharges hOmega from it when it applies `p11_hc_mean` in `holo_chart`.
The P11A-P2f audit (docs/tracks/P/audits/P11A-P2f-audit-1.md on inp-p11ap2f) reports "P2e audit F1 is closed at the
assembled public interface". Ruling: P2e is accepted; merge it before (or together with) P11A-P2f.
