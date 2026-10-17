# files: twin-free machine laws, with-twins machine laws, with-twins extras, served laws; per served law: machine in each arm, twin in extras
function canon(s,   out,i,c,m,k) { delete m; k=0; out=""; for(i=1;i<=length(s);i++){c=substr(s,i,1); if(c ~ /[xyz]/ && substr(s,i-1,1) !~ /[a-z]/ && substr(s,i+1,1) !~ /[a-z0-9]/){ if(!(c in m)) m[c]=substr("abc",++k,1); c=m[c] } out=out c } return out }
function key(l,   p) { split(l,p," = "); a=canon(p[1] " = " p[2]); b=canon(p[2] " = " p[1]); return a<b?a:b }
FILENAME==ARGV[1]{t[$0]=1; next} FILENAME==ARGV[2]{d[$0]=1; next} FILENAME==ARGV[3]{ex[key($0)]=1; next}
{ tw = (key($0) in ex); print (($0 in t) ? "Tm" : "Tf") " " (($0 in d) ? "Dm" : "Df") " " (tw ? "twin" : "none") }
