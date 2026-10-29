import numpy as np, pickle, math, time
from norms import Cand, sup_package, torsion_inverse
cands = {w: Cand(w) for w in ['lower', 'upper']}
lams = [0.5, 0.7, 1.0, 1.4, 2.0]
rhos = {'theta': list(np.geomspace(0.002, 0.04, 22)), 'rot': list(np.geomspace(0.003, 0.08, 22))}
out = {'lams': lams, 'rhos': rhos, 'sup': {}, 'tors': {}}
t0 = time.time()
for frame in ['theta', 'rot']:
    for lam in lams:
        out['tors'][(frame, lam)] = max(torsion_inverse(cands[w], frame, lam, 1.0)[0] for w in cands)
        for rho in rhos[frame]:
            res = [sup_package(cands[w], frame, rho, lam) for w in cands]
            sK = max(r[0] for r in res); sB = max(r[1] for r in res)
            imX = np.maximum(res[0][2], res[1][2]); pmax = max(r[3] for r in res)
            out['sup'][(frame, lam, rho)] = (sK, sB, imX, pmax)
        print(frame, lam, "tors %.4f" % out['tors'][(frame, lam)], "sup@first", out['sup'][(frame, lam, rhos[frame][0])][:2],
              "sup@last", out['sup'][(frame, lam, rhos[frame][-1])][:2], round(time.time()-t0), flush=True)
pickle.dump(out, open('normgrid.pkl', 'wb'))
