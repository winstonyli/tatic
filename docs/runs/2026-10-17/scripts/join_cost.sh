# join_cost.sh <exe> <sweep dir> <salt>...: `search::proof_cost_split` on every served cmp3d batch of a sweep's loops
# (<sweep dir>/ab_b_<salt>/<stage>_cmp3d_<phase>_*/laws_serve_<skip>.txt, under that loop's final rules.txt), with the
# join on and with `ABLATE=join`, one run at a time, the arms' order alternating, $REPS (default 2) times each. Into
# kk.sh's directory ($RUN_DIR under run.ps1): cost.tsv, one row per run and COST line: salt, loop, skip, arm, rep, what, n,
# build ms, check ms, nodes. A law joined with the join on is a machine proof with it off, so (off machine - on machine)
# is the cost of the machine proofs the joined laws replace.
exe=$1; sw=$2; shift 2
d=$(bash "$(dirname "$0")/../../2026-10-12/scripts/kk.sh")
out="$d/cost.tsv"; : > "$out"
for s in "$@"; do
  for loop in "$sw"/ab_b_$s/*_cmp3d_*; do
    for laws in "$loop"/laws_serve_*.txt; do
      skip=$(basename "$laws" .txt); skip=${skip#laws_serve_}
      for rep in $(seq 1 "${REPS:-2}"); do
        arms="on off"; [ $((rep % 2)) = 0 ] && arms="off on"
        for arm in $arms; do
          log="$d/run.log"
          ( [ $arm = off ] && export ABLATE=join
            CHECK_FAMILY=cmp3d CHECK_RULES="$(cygpath -w "$loop/rules.txt")" CHECK_LAWFILE="$(cygpath -w "$laws")" "$exe" search::proof_cost_split --exact --ignored --nocapture > "$log" 2>&1 < /dev/null ) || echo "fail $s $loop $skip $arm" >&2
          grep '^COST [a-z-]*:' "$log" | sed -E 's/COST ([a-z-]+): n=([0-9]+) build=([0-9.]+)ms check=([0-9.]+)ms nodes=([0-9]+).*/\1\t\2\t\3\t\4\t\5/' | while IFS= read -r row; do
            printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$s" "$(basename "$loop")" "$skip" "$arm" "$rep" "$row" >> "$out"
          done
        done
      done
    done
  done
done
# per arm and kind: laws, build ms, check ms, nodes (each run's figures, summed over batches, the faster rep per batch)
awk -F'\t' '{k=$1 FS $2 FS $3 FS $4 FS $6; if (!(k in b) || $8 < b[k]) {b[k]=$8; c[k]=$9}; n[k]=$7; z[k]=$10}
  END {for (k in b) {split(k, f, FS); a=f[4] " " f[5]; N[a]+=n[k]; B[a]+=b[k]; C[a]+=c[k]; Z[a]+=z[k]}
       for (a in N) printf "%s: laws %d build %.0f ms check %.1f ms nodes %d\n", a, N[a], B[a], C[a], Z[a]}' "$out" | sort
