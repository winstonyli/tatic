# cols: 1 salt 2 loop 3 mine 4 round 5 pos 6 nalts 7 rival 8 gain 9 insample 10 oracle(-M) 11 kept 12 lsize 13 rsize 14 maxvar 15 rule
BEGIN{FS="\t"}
{g=$1 FS $2 FS $3 FS $4; n[g]++; if($11==1) kp[g]=$5; om[g,$5]=$10; ins[g,$5]=$9; gn[g,$5]=$8; if(!(g in ord)){ord[g]=++G; key[G]=g}}
END{
 for(i=1;i<=G;i++){g=key[i]; if(kp[g]>0){sw++; d+=om[g,kp[g]]-om[g,0]}
   b=0; for(a=1;a<n[g];a++) if(ins[g,a]>ins[g,b]) b=a; if(b==kp[g]) agree++; if(b>0) insw++; if(b>0 && b==kp[g]) both++; dm+=om[g,b]-om[g,0]
   # by gain (first is rival when present): does max gain pick the oracle choice?
   bg=0; for(a=1;a<n[g];a++) if(gn[g,a]>gn[g,bg]) bg=a; if(bg>0 && bg==kp[g]) gboth++; if(bg>0) gsw++; gm+=om[g,bg]-om[g,0]
 }
 printf "groups %d; oracle switched %d, next-batch M saved summed over rounds %d\n", G, sw, d
 printf "in-sample finished value: switches %d, same as oracle %d of oracle's %d switches, next-batch M change %+d\n", insw, both, sw, dm
 printf "max round gain: switches %d, same as oracle %d, next-batch M change %+d\n", gsw, gboth, gm
}
