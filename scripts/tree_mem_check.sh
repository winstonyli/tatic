#!/bin/bash
# tree_mem_check.sh: tree_mem.ps1 counts and stops only the tree it matches. Starts two trees of the same images
# (cmd -> ping), one marked as the target and one as a decoy; -Kill on the target must leave the decoy. Prints PASS or FAIL.
here="$(cd "$(dirname "$0")" && pwd)"; t="TREE_MEM_TARGET_$$"; d="TREE_MEM_DECOY_$$"
tm() { powershell -NoProfile -File "$(cygpath -w "$here/tree_mem.ps1")" -Match "$@" < /dev/null | tr -d '\r'; }
for m in $t $d; do cmd //c "echo $m > nul & ping -n 30 127.0.0.1 > nul" < /dev/null > /dev/null 2>&1 & done
deadline=$(( $(date +%s) + 20 )); until [ "$(tm $t)" -gt 0 ] && [ "$(tm $d)" -gt 0 ] || [ $(date +%s) -ge $deadline ]; do :; done
tm $t -Kill > /dev/null
deadline=$(( $(date +%s) + 20 )); until [ "$(tm $t)" = 0 ] || [ $(date +%s) -ge $deadline ]; do :; done
target=$(tm $t); decoy=$(tm $d)
tm $d -Kill > /dev/null
if [ "$target" = 0 ] && [ "${decoy:-0}" -gt 0 ]; then echo "PASS target 0 MB after -Kill, decoy $decoy MB"; else echo "FAIL target $target MB, decoy $decoy MB"; exit 1; fi
