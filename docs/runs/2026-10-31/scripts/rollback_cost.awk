# per log: simulate round times; on a rollback to round r, the rounds r.. played so far are waste
function flush() {
  if (!seen) return
  logs++; rounds += cur_total; rt += roundtime
  if (nrb > 0) { wlogs++; wr += waste_rounds; wt += waste }
  nrb_all += nrb
  tot_other += other
}
FNR==1 { if (NR>1) flush(); seen=1; cur=0; cur_total=0; roundtime=0; nrb=0; waste=0; waste_rounds=0; other=0; delete t }
/RULEMINER time round over/ { s=$NF; sub(/s$/,"",s); t[cur]=s+0; roundtime+=s; cur++; cur_total++; last=cur-1; next }
/RULEMINER time rule-set evaluation/ { s=$NF; sub(/s$/,"",s); if (last>=0) { t[last]+=s; roundtime+=s } next }
/RULEMINER time / { s=$NF; sub(/s$/,"",s); other+=s; next }
/RULEMINER rolled back to round/ { r=$6+0; nrb++; for (i=r;i<cur;i++) { waste+=t[i]; waste_rounds++ ; delete t[i] } cur=r; last=cur-1; next }
END { flush(); printf "logs %d, with rollback %d, rollbacks %d\nround time %.1fs over %d rounds; wasted %.1fs over %d rounds (%.2f%% of round time)\nnon-round mine time lines %.1fs\n", logs, wlogs, nrb_all, rt, rounds, wt, wr, 100*wt/rt, tot_other }
