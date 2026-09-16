#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
scripts/check_resources.sh --strict
lock_file=scripts/comparator-tools.lock.json
[[ $(< lean-toolchain) == "$(jq -r '.lean_toolchain' "$lock_file")" ]]
comparator_revision=$(jq -r '.comparator.revision' "$lock_file")
tool_dir="$PWD/.lake/comparator-tools-$comparator_revision"
comparator_source="$tool_dir/comparator-$comparator_revision"
comparator_binary="$comparator_source/.lake/build/bin/comparator"
exporter_binary="$comparator_source/.lake/packages/lean4export/.lake/build/bin/lean4export"
sandbox_binary="$tool_dir/landrun"
sandbox_adapter="$PWD/scripts/run_landrun.py"
comparator_memory_max="${COMPARATOR_MEMORY_MAX:-56G}"
comparator_swap_max="${COMPARATOR_SWAP_MAX:-0}"
comparator_threads="${LEAN_NUM_THREADS:-1}"
comparator_stage_export="${COMPARATOR_STAGE_EXPORT:-1}"
for tool_binary in "$comparator_binary" "$exporter_binary" "$sandbox_binary"; do
  if [[ ! -x "$tool_binary" ]]; then
    echo "Run bash scripts/prepare_comparator_tools.sh first." >&2
    exit 1
  fi
done
if [[ ! -x "$sandbox_adapter" ]]; then
  echo "Missing executable Landrun argument adapter: $sandbox_adapter" >&2
  exit 1
fi
if [[ $(id -u) == 0 ]]; then
  echo "The official comparator must run as an unprivileged user." >&2
  exit 1
fi

# The pinned official README requires this Linux UNIX-socket mitigation.
# A oneshot service treats SIGTERM as failure, not successful verification.
set +e
systemd-run --user --wait --pipe --collect \
  --property=Type=oneshot --property=TimeoutStartSec=infinity \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --property=CPUQuota=200% --property=MemoryMax="$comparator_memory_max" --property=MemorySwapMax="$comparator_swap_max" \
  --working-directory="$PWD" \
  --setenv=PATH="$PATH" \
  --setenv=LEAN_NUM_THREADS="$comparator_threads" \
  --setenv=COMPARATOR_STAGE_EXPORT="$comparator_stage_export" \
  --setenv=COMPARATOR_LANDRUN="$sandbox_adapter" \
  --setenv=COMPARATOR_LEAN4EXPORT="$exporter_binary" \
  lake env "$comparator_binary" Comparator/config.json
comparator_status=$?
set -e
scripts/check_resources.sh --strict
exit "$comparator_status"
