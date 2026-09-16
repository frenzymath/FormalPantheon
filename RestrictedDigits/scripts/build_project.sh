#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Bound Lake's worker pool when a cold certificate closure is exposed.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

mkdir -p .lake
exec 9>.lake/prd-build.lock
if ! flock -n 9; then
  echo "build already running through scripts/build_project.sh" >&2
  exit 1
fi

report_resources_on_failure() {
  local status=$?
  if ((status != 0)); then
    scripts/check_resources.sh || true
  fi
}
trap report_resources_on_failure EXIT

scripts/check_resources.sh --strict

# Lake 5 schedules independent imports without a job-count limit. Each of
# these kernel checks can use about 4 GiB, so populate them serially before
# exposing the full import graph.
vector_bound_targets=(
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit0
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit1
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit2
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit3
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit4
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit0
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit0
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit1
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit1
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit2
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit2
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit3
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit3
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit4
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit4
)

for target in "${vector_bound_targets[@]}"; do
  PRD_MIN_MEMORY_GIB=8 scripts/check_resources.sh --strict
  lake --wfail build "$target"
done

# Populate each row family in two stages before exposing the full import graph.
# Each stage has at most eight independent chains; their measured combined
# peak fits below the documented 56 GiB build limit.
build_certificate_stage() {
  PRD_MIN_MEMORY_GIB="${PRD_BUILD_MIN_MEMORY_GIB:-18}" \
    scripts/check_resources.sh --strict
  lake --wfail build "$@"
}

build_certificate_stage \
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit0 \
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit1 \
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit2 \
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit3Group12Result \
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit4Group12Result
build_certificate_stage \
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit3 \
  PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit4
build_certificate_stage \
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit0 \
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit1 \
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit2 \
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group12Result \
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit4Group12Result
build_certificate_stage \
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3 \
  PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit4

PRD_MIN_MEMORY_GIB="${PRD_BUILD_MIN_MEMORY_GIB:-18}" \
  scripts/check_resources.sh --strict
lake --wfail build

scripts/check_resources.sh --strict
trap - EXIT
