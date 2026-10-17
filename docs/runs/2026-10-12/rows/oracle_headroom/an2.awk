# per non-first alternative: feature means for kept (oracle switched to it) vs not kept; features relative to position 0
BEGIN{FS="\t"}
{g=$1 FS $2 FS $3 FS $4; if($5==0){g0[g]=$8; l0[g]=$12; r0[g]=$13; v0[g]=$14; i0[g]=$9; next}
 c=$11; N[c]++; 
 S[c,"gain ratio"]+=$8/g0[g]; S[c,"lhs size"]+=$12; S[c,"lhs size - pos0"]+=$12-l0[g]; S[c,"rhs-lhs size"]+=$13-$12;
 S[c,"vars"]+=$14; S[c,"in-sample - pos0 (x1000)"]+=($9-i0[g])/1000; S[c,"position"]+=$5; S[c,"first is rival"]+=($7==1||0);
 S[c,"lhs smaller than pos0"]+=($12<l0[g]); S[c,"rhs shrinks"]+=($13<$12)}
END{split("gain ratio|lhs size|lhs size - pos0|lhs smaller than pos0|rhs-lhs size|rhs shrinks|vars|in-sample - pos0 (x1000)|position",F,"|");
 printf "%-26s %10s %10s\n","feature","kept("N[1]")","other("N[0]")"; for(i=1;i in F;i++) printf "%-26s %10.3f %10.3f\n",F[i],S[1,F[i]]/N[1],S[0,F[i]]/N[0]}
