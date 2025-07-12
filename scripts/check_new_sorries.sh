#!/usr/bin/env bash
# check_new_sorries.sh
# Fails (exit 1) if the current branch introduces any NEW `sorry` placeholders
# relative to the baseline stored in SORRY_BASELINE.txt.

set -euo pipefail

BASELINE="SORRY_BASELINE.txt"

if [[ ! -f "$BASELINE" ]]; then
  echo "❌ Baseline file $BASELINE not found."
  exit 1
fi

# Temporary file for current sorries
CURRENT_SORRIES=$(mktemp)

# Collect current list of sorries (sorted)
git grep -n "\\bsorry\\b" -- "*.lean" | sort > "$CURRENT_SORRIES" || true

# Compare with baseline
diff_output=$(comm -23 "$CURRENT_SORRIES" <(sort "$BASELINE")) || true

if [[ -n "$diff_output" ]]; then
  echo "❌ New \`sorry\` placeholders detected (compared to baseline):"
  echo "$diff_output"
  exit 1
else
  echo "✅ No new \`sorry\` placeholders introduced."
fi

# Clean up
test -f "$CURRENT_SORRIES" && rm "$CURRENT_SORRIES" 