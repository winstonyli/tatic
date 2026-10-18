# serve_shadow.sh <exe> <salts...>: why the bounded join joins no more of serving's laws. Per salt, SWEEP=cold:cmp3d
# (extras on, 2 lanes) with patches/serve_shadow.patch's shadow (JOIN_SHADOW, JOIN_SHADOW_SERVE=1: every join search
# of the serving worker, none of the miner's, both terms logged; budget JOIN_BUDGET, default 4); then over the salts
# the shadow's outcome against the real join's, and for the real failures their larger side's size and the shadow's
# terms reached. A watchdog stops the exe past 8 GB in all.
exe=$1; shift
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
name=$(basename "$exe" | sed 's/\.[Ee][Xx][Ee]$//')
for s in "$@"; do
  o="$d/s$s"; mkdir -p "$o"; rm -f "$o/exit"; t0=$(date +%s)
  ( JOIN_SHADOW_SERVE=1 JOIN_SHADOW="$(cygpath -w "$o")\\shadow" MACHINE_STATE=0 SWEEP=cold:cmp3d SALT=$s SWEEP_OUT="$(cygpath -w "$o")" "$exe" driver::sweep --exact --ignored --nocapture > "$o/log.txt" 2>&1; echo $? > "$o/exit" ) &
  while [ ! -f "$o/exit" ]; do
    mb=$(powershell -NoProfile -Command "[int]((Get-Process $name -EA 0 | Measure-Object WorkingSet64 -Sum).Sum/1MB)" | tr -d '\r')
    [ "${mb:-0}" -gt 8192 ] && { echo "salt $s: over 8 GB ($mb MB), stopped"; taskkill //F //IM "$name.exe" > /dev/null; }
    ping -n 4 127.0.0.1 > /dev/null
  done
  echo "salt $s: exit $(cat "$o/exit") wall $(( $(date +%s) - t0 )) s, $(cat "$o"/shadow.* | wc -l) serving searches"
done
cat "$d"/s*/shadow.* > "$d/serve_pairs.tsv"
awk -F'\t' '{ n[($1 ? "met" : "fail") "->" $3]++ } END { for (k in n) printf "real %s: %d\n", k, n[k] }' "$d/serve_pairs.tsv" | sort
awk -F'\t' '$1 == 0 { f++; sz += $7; r += $4; if ($7 > mx) mx = $7 } END { if (f) printf "real failures %d: larger side mean %.1f nodes (max %d), shadow reached mean %.0f\n", f, sz / f, mx, r / f }' "$d/serve_pairs.tsv"
