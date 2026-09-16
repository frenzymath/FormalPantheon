#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
scripts/check_resources.sh --strict
lock_file=scripts/comparator-tools.lock.json
expected_toolchain=$(jq -r '.lean_toolchain' "$lock_file")
[[ $(< lean-toolchain) == "$expected_toolchain" ]]
comparator_revision=$(jq -r '.comparator.revision' "$lock_file")
landrun_revision=$(jq -r '.landrun.revision' "$lock_file")
tool_dir="$PWD/.lake/comparator-tools-$comparator_revision"
mkdir -p "$tool_dir/tmp"

check_hash() {
  local file=$1 expected=$2 actual
  read -r actual _ < <(sha256sum "$file")
  if [[ "$actual" != "$expected" ]]; then
    printf 'verification tool checksum mismatch: %s\n' "$file" >&2
    exit 1
  fi
}

for tool_name in comparator landrun go; do
  tool_url=$(jq -r --arg name "$tool_name" '.[$name].url' "$lock_file")
  tool_sha=$(jq -r --arg name "$tool_name" '.[$name].sha256' "$lock_file")
  tool_archive="$tool_dir/$tool_name.tar.gz"
  if [[ ! -f "$tool_archive" ]]; then
    curl --fail --location --silent --show-error "$tool_url" --output "$tool_archive"
  fi
  check_hash "$tool_archive" "$tool_sha"
  case "$tool_name" in
    comparator) tool_source="$tool_dir/comparator-$comparator_revision" ;;
    landrun) tool_source="$tool_dir/landrun-$landrun_revision" ;;
    go) tool_source="$tool_dir/go" ;;
  esac
  if [[ ! -d "$tool_source" ]]; then
    tar --extract --gzip --file="$tool_archive" --directory="$tool_dir"
  fi
  archive_options=()
  [[ "$tool_name" != comparator ]] || archive_options+=(--allow-lake)
  python3 scripts/verify_tool_archive.py "$tool_archive" "$tool_source" "${archive_options[@]}"
done

comparator_source="$tool_dir/comparator-$comparator_revision"
landrun_source="$tool_dir/landrun-$landrun_revision"
check_hash "$comparator_source/lake-manifest.json" \
  "$(jq -r '.comparator.manifest_sha256' "$lock_file")"
check_hash "$landrun_source/go.sum" "$(jq -r '.landrun.go_sum_sha256' "$lock_file")"

(
  cd "$landrun_source"
  export GOPATH="$tool_dir/go-work" GOCACHE="$tool_dir/go-cache"
  export GOMODCACHE="$tool_dir/go-modules" GOTMPDIR="$tool_dir/tmp" TMPDIR="$tool_dir/tmp"
  export XDG_CONFIG_HOME="$tool_dir/xdg-config" XDG_CACHE_HOME="$tool_dir/xdg-cache"
  export GOENV=off GOWORK=off GOFLAGS= GOTOOLCHAIN=local GOMAXPROCS=2
  "$tool_dir/go/bin/go" telemetry off
  [[ $("$tool_dir/go/bin/go" env GOTELEMETRY) == off ]]
  [[ $("$tool_dir/go/bin/go" env GOTELEMETRYDIR) == "$tool_dir/xdg-config/go/telemetry" ]]
  "$tool_dir/go/bin/go" build -mod=readonly -trimpath -o "$tool_dir/landrun" ./cmd/landrun
)
(
  cd "$comparator_source"
  LEAN_NUM_THREADS=2 elan run "$expected_toolchain" lake --no-cache --wfail build comparator lean4export
)

check_hash "$comparator_source/lake-manifest.json" \
  "$(jq -r '.comparator.manifest_sha256' "$lock_file")"
check_hash "$landrun_source/go.sum" "$(jq -r '.landrun.go_sum_sha256' "$lock_file")"
for package_name in lean4export Lean4Checker; do
  if [[ "$package_name" == lean4export ]]; then
    revision_key=lean4export_revision
  else
    revision_key=lean4checker_revision
  fi
  [[ $(git -C "$comparator_source/.lake/packages/$package_name" rev-parse HEAD) == \
    "$(jq -r --arg key "$revision_key" '.comparator[$key]' "$lock_file")" ]]
  [[ -z $(git -C "$comparator_source/.lake/packages/$package_name" status --porcelain) ]]
done
python3 scripts/verify_tool_archive.py "$tool_dir/comparator.tar.gz" "$comparator_source" --allow-lake
python3 scripts/verify_tool_archive.py "$tool_dir/landrun.tar.gz" "$landrun_source"
python3 scripts/verify_tool_archive.py "$tool_dir/go.tar.gz" "$tool_dir/go"
scripts/check_resources.sh --strict
printf 'pinned verification tools prepared: %s\n' "$tool_dir"
