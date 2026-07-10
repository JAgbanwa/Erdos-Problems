#!/usr/bin/env bash
# Independent Gate-H build (attempt 2): short root + git longpaths via env (non-invasive).
set -x
cd "C:/Users/jtrav/l" || exit 2
export GIT_CONFIG_COUNT=1
export GIT_CONFIG_KEY_0=core.longpaths
export GIT_CONFIG_VALUE_0=true
date
echo "=== longpaths check (child git inherits env) ==="
git config --show-origin core.longpaths 2>&1 | tail -2
echo "=== STEP 1: cache get (uses local ~/.cache/mathlib; clones mathlib source w/ longpaths) ==="
lake exe cache get 2>&1 | tail -20
echo "cache-get exit: ${PIPESTATUS[0]}"
echo "=== STEP 2: build PaperI.PaperI_Statement (prints #print axioms at end) ==="
lake build PaperI.PaperI_Statement 2>&1
echo "=== BUILD EXIT: $? ==="
date
echo "=== DONE ==="
