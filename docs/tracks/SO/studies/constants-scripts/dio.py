import mpmath as mp
mp.mp.dps = 40
al = (79 - mp.sqrt(5))/3118
for which, nu in [('lower', 1-al), ('upper', 1+al)]:
    for frame, om in [('theta', (nu, 1)), ('rot', (nu-1, 1))]:
        best = (mp.inf, None)
        K = 4000
        for k1 in range(0, K):
            # best k2 near -k1*om0
            x = k1*om[0]
            for k2 in {int(mp.floor(-x)), int(mp.ceil(-x)), int(mp.floor(-x))-1, int(mp.ceil(-x))+1}:
                if k1 == 0 and k2 == 0: continue
                if k1 == 0 and k2 < 0: continue
                v = abs(x + k2)*(abs(k1)+abs(k2))
                if v < best[0]: best = (v, (k1, k2))
            # also negative k1 handled by symmetry (k -> -k)
        print(which, frame, mp.nstr(best[0], 10), best[1], " 1/21=%.6f 1/42=%.6f alpha=%s" % (1/21, 1/42, mp.nstr(al, 8)))
