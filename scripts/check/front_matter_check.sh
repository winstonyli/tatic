#!/bin/bash
# front_matter_check.sh [root]: every tracked spec and plan (docs/superpowers/{specs,plans}/*.md) opens with front matter whose
# status is draft, active, done or "superseded-by: <file>" (CLAUDE.md), and a superseded-by file exists.
cd "${1:-$(dirname "$0")/../..}" || exit 2
bad=$(git ls-files 'docs/superpowers/specs/*.md' 'docs/superpowers/plans/*.md' | while read -r f; do
  [ "$(sed -n 1p "$f" | tr -d '\r')" = --- ] || { echo "$f: no front matter"; continue; }
  s=$(tr -d '\r' < "$f" | awk 'NR==1 {next} /^---$/ {print s; exit} /^status:/ && s=="" {s=$0; sub(/^status: */,"",s)}')
  case $s in
    draft|active|done) ;;
    '"superseded-by: '*'"') t=${s#'"superseded-by: '}; t=${t%'"'}; [ -f "$(dirname "$f")/$t" ] || [ -f "$t" ] || echo "$f: superseded by a missing file: $t" ;;
    *) echo "$f: bad status: ${s:-none}" ;;
  esac
done)
[ -z "$bad" ] || { echo "front_matter_check:"; echo "$bad"; exit 1; }
echo "front_matter_check: ok"
