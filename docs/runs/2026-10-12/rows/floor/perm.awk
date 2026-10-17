function bag(s,   n,a,i,out) { gsub(/[(),]/," ",s); n=split(s,a," "); asort(a); out=""; for(i=1;i<=n;i++) out=out a[i] " "; return out }
BEGIN{FS="\t"} { p=(bag($8)==bag($9)); key=$1 " " ($5>0?"cut":"nocut"); n[key]++; m[key]+=p }
END{ for(k in n) print k, n[k], "same symbols", m[k] }
