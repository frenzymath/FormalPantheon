#!/usr/bin/env bash
set -euo pipefail

mode="report"
if [[ "${1:-}" == "--strict" ]]; then
  mode="strict"
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--strict]" >&2
  exit 2
fi

min_disk_gib="${PRD_MIN_DISK_GIB:-12}"
min_memory_gib="${PRD_MIN_MEMORY_GIB:-6}"

read -r disk_kib disk_available_kib < <(
  df -Pk . | awk 'NR == 2 { print $2, $4 }'
)
read -r memory_kib memory_available_kib swap_kib swap_free_kib < <(
  awk '
    /^MemTotal:/ { mt = $2 }
    /^MemAvailable:/ { ma = $2 }
    /^SwapTotal:/ { st = $2 }
    /^SwapFree:/ { sf = $2 }
    END { print mt, ma, st, sf }
  ' /proc/meminfo
)

gib=$((1024 * 1024))
disk_available_gib=$((disk_available_kib / gib))
memory_available_gib=$((memory_available_kib / gib))
swap_used_kib=$((swap_kib - swap_free_kib))

awk -v total="$disk_kib" -v available="$disk_available_kib" \
  'BEGIN { printf "disk: %.1f GiB total, %.1f GiB available\n", total / 1048576, available / 1048576 }'
awk -v total="$memory_kib" -v available="$memory_available_kib" \
  'BEGIN { printf "memory: %.1f GiB total, %.1f GiB available\n", total / 1048576, available / 1048576 }'
awk -v total="$swap_kib" -v used="$swap_used_kib" \
  'BEGIN { printf "swap: %.1f GiB total, %.1f GiB used\n", total / 1048576, used / 1048576 }'
du -sh . | awk '{ print "repository: " $1 }'

failed=0
if ((disk_available_gib < min_disk_gib)); then
  echo "warning: disk availability is below ${min_disk_gib} GiB" >&2
  failed=1
fi
if ((memory_available_gib < min_memory_gib)); then
  echo "warning: memory availability is below ${min_memory_gib} GiB" >&2
  failed=1
fi

if [[ "$mode" == "strict" && $failed -ne 0 ]]; then
  echo "resource gate failed; this check did not invoke the Lean compiler" >&2
  exit 1
fi
