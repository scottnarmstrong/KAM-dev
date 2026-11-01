#!/bin/bash
# V2-PACKED-GEN: one LG00 torus through a packed route, generated and run in the kernel (untrusted driver).
#
# Usage: run_tree.sh TREE ROUTE LOGDIR [CAP]
#   TREE   TP (LG00's T') or TPP (T'')
#   ROUTE  gate   the A gate on LG00's real certificate: the packed frame tests at the claims, LG00's own
#                 `Final.RefinedCore` (the certified sharp sites), the one-ulp attacks;
#          b3b    the B3b route on LG00's real certificate (`torsRBase` + `routeARefinedPackedS`), with the tree's
#                 landed `cfgLow` composition (its `Low` chain, reused from LG00's run) and the tree's statement;
#          jet    the production route on kamx-packed's certificate copy (`jetBase` + `routeARefinedPackedSJ`):
#                 run from the integration worktree (its core has the jet API, the consumers, RouteSharpJ,
#                 JetFront); needs kamx-packed's built package (PROD_PKG) and mirror caches JET_LOW_CACHE,
#                 JET_FULL_CACHE (env), and a kam-lg00 package with LG00's built modules (LG00_PKG).
#   CAP    the memory cap per Lean process (default 4G)
# Environment: PKG (default <core>/.lake/lg00-packed), LG00_APP (default lg00-app's applications/lg00).
# Every Python step runs under the 8 GB cap (py_capped.sh); every Lean process alone under CAP (run_packed.py).
set -eu
tree=$1; route=$2; logdir=$3; cap=${4:-4G}
here=$(cd "$(dirname "$0")" && pwd)
core=$(cd "$here/../.." && pwd)
pkg=${PKG:-$core/.lake/lg00-packed}
app=${LG00_APP:-/home/scott/KAM-dev-worktrees/lg00-app/applications/lg00}
py="bash $here/py_capped.sh"
case $route in
  gate)
    $py "$here/gen_pkg.py" --pkg "$pkg" "LG00.$tree.Data.Cert" "LG00.$tree.Final.RefinedCore"
    $py "$here/gen_packed.py" --tree "$tree" --pkg "$pkg" --stages frames,sharp
    targets="LG00Packed.$tree.GateA $(ls "$pkg/LG00Packed/$tree/Gate" | sed "s/\.lean$//; s/^/LG00Packed.$tree.Gate./")"
    ;;
  b3b)
    $py "$here/gen_pkg.py" --pkg "$pkg" "LG00.$tree.Data.Cert" "LG00.$tree.Final.RefinedCore" \
      "LG00.$tree.Final.HamClaim" "LG00.$tree.Final.Static" "LG00.$tree.Final.Embedding" \
      "LG00.$tree.Final.Invariance" "LG00.$tree.Balls.HamBounds" "LG00.$tree.Low.T1931" "LG00.$tree.Low.Ckpt" \
      "LG00.$tree.Final.Freq" LG00.Physical.HamIdentity LG00.JetBridge LG00.Kernel.StageTwo
    $py "$here/gen_packed.py" --tree "$tree" --pkg "$pkg" --stages assembly
    targets="LG00Packed.$tree.Main"
    ;;
  jet)
    # The integration recipe (handoff, "The T' jet route PROVED"): a package mirroring kamx-packed's `kam-lg00p`
    # (their certificate copy and chains reused read only), which requires a `kam-lg00` package holding LG00's own
    # built modules (the Hamiltonian bounds and the disc pass are imported, not re-proved), the port of LG00's
    # chain-free proof, and the packed modules. The core at $core must contain v2-packed-prod's and v2-packed-cons'
    # Lean, RouteSharpJ and JetFront (the integration branch v2-packed-gen-int).
    pkg=${PKG:-$core/.lake/lg00p}
    theirs=${PROD_PKG:-/home/scott/KAM-dev-worktrees/v2-packed/.lake/v2-packed-prod/pkg}
    lg00pkg=${LG00_PKG:-/home/scott/KAM-dev-worktrees/v2-packed-gen/.lake/lg00-packed}
    pg=${PROD_GEN:-/home/scott/KAM-dev-worktrees/v2-packed/scripts/packed/prod_cert_gen.py}
    mods=$(cd "$theirs" && find LG00P -name '*.lean' | sed 's|\.lean$||; s|/|.|g' | tr '\n' ' ')
    $py "$here/gen_pkg.py" --pkg "$pkg" --like "$theirs" --core "$core" --lg00 "$theirs" $mods
    $py "$here/gen_pkg.py" --pkg "$lg00pkg" "LG00.$tree.Balls.HamBounds" "LG00.$tree.Final.HamClaim"
    $py "$here/gen_pkg.py" --pkg "$pkg" --keep-config --require-lg00 "$lg00pkg"
    $py "$here/gen_port.py" "$pkg" --app="$app" --tree="$tree" --prefix=LG00P --prod-gen="$pg"
    $py "$here/gen_packed.py" --tree "$tree" --prefix LG00P --pkg "$pkg" --stages jet \
      --jet-low "$JET_LOW_CACHE" --jet-full "$JET_FULL_CACHE"
    targets="LG00P.$tree.PK.MainJ"
    ;;
  *) echo "unknown route $route"; exit 2;;
esac
CORE_DIR=$core bash "$here/run_core_frontier.sh" KAM.CertificateSharp.Packed.RouteSharp
python3 -I "$here/run_packed.py" "$logdir" "$cap" $targets --pkg "$pkg"
python3 -I "$here/run_packed.py" --summary "$logdir"
