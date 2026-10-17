# rename x,y,z by first appearance, so laws equal up to a variable renaming get the same key; also key the swapped law
function canon(s,   out,i,c,m,k) { delete m; k=0; out=""; for(i=1;i<=length(s);i++){c=substr(s,i,1); if(c ~ /[xyz]/ && substr(s,i-1,1) !~ /[a-z]/ && substr(s,i+1,1) !~ /[a-z0-9]/){ if(!(c in m)) m[c]=substr("abc",++k,1); c=m[c] } out=out c } return out }
function key(l,   p) { split(l,p," = "); a=canon(p[1] " = " p[2]); b=canon(p[2] " = " p[1]); return a<b?a:b }
FNR==1{f++} f==1{ex[key($0)]=1; next} { n++; if(key($0) in ex) hit++ } END{print n, hit+0}
