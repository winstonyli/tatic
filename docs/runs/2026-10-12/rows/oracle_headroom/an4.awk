# rounds where the in-sample finished value prefers another alternative, by its margin over position 0 (stragglers = /1000)
BEGIN{FS="\t"}
{g=$1 FS $2 FS $3 FS $4; n[g]++; om[g,$5]=$10; ins[g,$5]=$9; if($11==1) kp[g]=$5}
END{for(g in n){ b=0; for(a=1;a<n[g];a++) if(ins[g,a]>ins[g,b]) b=a; if(b==0) continue; m=ins[g,b]-ins[g,0];
  k=(m<1000)?"<1 straggler":(m<2000)?"1-2 stragglers":">=2 stragglers"; N[k]++; D[k]+=om[g,b]-om[g,0]; W[k]+=(om[g,b]>om[g,0]); L[k]+=(om[g,b]<om[g,0])}
 for(k in N) printf "%-15s rounds %4d  better next batch %3d  worse %3d  net M %+d\n", k, N[k], W[k], L[k], -D[k]}
