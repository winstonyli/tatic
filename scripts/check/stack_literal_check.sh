#!/bin/bash
# stack_literal_check.sh [root]: no tracked .rs file under crates/ spells the 256 MB check stack as a number (256 << 20,
# 256 * 1024 * 1024, 268435456); a thread that checks takes tatic_kernel::CHECK_STACK (CLAUDE.md). No allowlist.
cd "${1:-$(dirname "$0")/../..}" || exit 2
bad=$(git ls-files 'crates/*.rs' | xargs -r grep -nE '(^|[^0-9_])(256 *<< *20|256 *\* *1024 *\* *1024|268_?435_?456)([^0-9_]|$)' /dev/null)
[ -z "$bad" ] || { echo "stack_literal_check: use tatic_kernel::CHECK_STACK"; echo "$bad"; exit 1; }
echo "stack_literal_check: ok"
