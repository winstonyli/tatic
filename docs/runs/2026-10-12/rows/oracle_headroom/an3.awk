# within rounds where the oracle switched: alternatives at positions > 0; "good" = oracle value equal to the round's best
BEGIN{FS="\t"; nf=split("gain|insample|-lsize|lsize|-rsize|rsize|shrink|-shrink|vars|-vars|-pos",F,"|")}
{g=$1 FS $2 FS $3 FS $4; n[g]++; om[g,$5]=$10; if($11==1) kp[g]=$5;
 x[g,$5,"gain"]=$8; x[g,$5,"insample"]=$9; x[g,$5,"-lsize"]=-$12; x[g,$5,"lsize"]=$12; x[g,$5,"-rsize"]=-$13; x[g,$5,"rsize"]=$13;
 x[g,$5,"shrink"]=$12-$13; x[g,$5,"-shrink"]=$13-$12; x[g,$5,"vars"]=$14; x[g,$5,"-vars"]=-$14; x[g,$5,"-pos"]=-$5}
END{for(g in n){ if(!(kp[g]>0)) continue; R++; best=om[g,kp[g]]; good=0; for(a=1;a<n[g];a++) good+=(om[g,a]==best); chance+=good/(n[g]-1)
  for(f=1;f<=nf;f++){ b=1; for(a=2;a<n[g];a++) if(x[g,a,F[f]]>x[g,b,F[f]]) b=a; hit[f]+=(om[g,b]==best)} }
 printf "switched rounds %d; chance of a good pick %.2f\n", R, chance/R; for(f=1;f<=nf;f++) printf "  %-9s %.2f\n", F[f], hit[f]/R}
