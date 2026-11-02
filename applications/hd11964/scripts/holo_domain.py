import sys, math, numpy as np
sys.path.insert(0, "scripts")
import holo_margin as H, hd11964_model as HM, prod2_hp as PH
cells = PH.plan_cells("validation/cover2-plan-k0.2-d2e-3.json")
etab = max(abs(float(c["c"][3])) + float(c["h"][3]) for c in cells)
print("eta_c bar over the plan's cells: %.5f" % etab)
m = HM.Model(dps=30); nu = [float(x) for x in m.nu]
d = 1/500; Cmax = 1/100 + 2*d
Llo = [116621/2000000 - d, 4454241/2500000 - d]; Lhi = [292553/5000000 + d, 3575393/2000000 + d]
rho = [float(x) for x in sys.argv[1].split(",")]; Y = [2*math.pi*r for r in rho]
rng = np.random.default_rng(1)
N = 1500
# AMD split, planet c rotation-reduced (|eta_c| <= etab), planet b any orientation
f = np.concatenate([rng.random(N), np.array([1.0, 0.0, 0.5, 0.9, 0.99])])
Gc, Gb = f*Cmax, (1-f)*Cmax
Lc = np.where(rng.random(len(f)) < .5, Llo[0], Lhi[0]); Lb = np.where(rng.random(len(f)) < .5, Llo[1], Lhi[1])
etc = np.clip(rng.uniform(-etab, etab, len(f)), -np.sqrt(2*Gc), np.sqrt(2*Gc))
xic = np.sqrt(np.maximum(2*Gc - etc**2, 0)) * np.where(rng.random(len(f)) < .5, 1, -1)
tb = rng.uniform(0, 2*math.pi, len(f)); xib, etb = np.sqrt(2*Gb)*np.cos(tb), np.sqrt(2*Gb)*np.sin(tb)
kc, _, v0c, v1c = H.chart_parts(Lc.astype(complex), xic.astype(complex), etc.astype(complex))
kb, _, v0b, v1b = H.chart_parts(Lb.astype(complex), xib.astype(complex), etb.astype(complex))
Ac = float((abs(v0c)+abs(v1c)).max()); Ab = float((abs(v0b)+abs(v1b)).max())
nx = 40; xs = np.linspace(0, 2*np.pi, nx, endpoint=False); dmin = np.inf
for sc in (-1, 1):
  for sb in (-1, 1):
    lc = (xs + 1j*sc*Y[0])[:, None, None]; lb = (xs + 1j*sb*Y[1])[None, :, None]
    Fc, rc = H.kepler(np.broadcast_to(lc, (nx, 1, len(f))).copy(), v0c, v1c)
    Fb, rb = H.kepler(np.broadcast_to(lb, (1, nx, len(f))).copy(), v0b, v1b)
    q0c, q1c, *_ = H.qp(nu[0], Lc, kc, v0c, v1c, Fc); q0b, q1b, *_ = H.qp(nu[1], Lb, kb, v0b, v1b, Fb)
    d2 = (q0c - q0b)**2 + (q1c - q1b)**2
    dmin = min(dmin, float(d2.real.min())); assert rc < 1e-9 and rb < 1e-9
print("rho %s: R(1/500) with |eta_c| <= %.4f: max l1 ecc c %.4f b %.4f; min Re d2 = %.3f" % (rho, etab, Ac, Ab, dmin))
