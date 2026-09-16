#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

bash -n scripts/*.sh
scripts/build_project.sh
lake --wfail build Comparator

scripts/check_resources.sh --strict
