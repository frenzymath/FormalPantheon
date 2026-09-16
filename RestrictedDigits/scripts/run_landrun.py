#!/usr/bin/env python3
"""Preserve sandbox arguments and stage large exports on disk."""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def command_arguments(args):
    prefix = []
    index = 0
    while index < len(args):
        token = args[index]
        if token == "--":
            index += 1
            break
        if token in {"--best-effort", "-ldd", "-add-exec"}:
            prefix.append(token)
            index += 1
        elif token in {"--ro", "--rw", "--rox", "--rwx", "--env"}:
            if index + 1 == len(args):
                raise ValueError(f"missing value for {token}")
            prefix.extend(args[index:index + 2])
            index += 2
        elif token.startswith("-"):
            raise ValueError(f"unsupported sandbox option: {token}")
        else:
            break
    if index == len(args) or not args[index]:
        raise ValueError("missing child command")
    return prefix, args[index:]


def forward_bounded_threads(prefix):
    """Pass the wrapper's bounded Lake worker count into the sandbox."""
    threads = os.environ.get("LEAN_NUM_THREADS")
    if not threads:
        return prefix
    if any(prefix[index:index + 2] == ["--env", "LEAN_NUM_THREADS"]
           for index in range(len(prefix) - 1)):
        return prefix
    return prefix + ["--env", "LEAN_NUM_THREADS"]


def staged_export(binary, args, directory):
    if directory.resolve(strict=True) != directory or not directory.is_dir():
        raise ValueError("export staging requires a regular repository-local .lake directory")
    # Keep the exporter and the Comparator's large stdout buffer out of memory together.
    with tempfile.TemporaryFile(mode="w+b", prefix="comparator-export-", dir=directory) as output:
        with subprocess.Popen([str(binary), *args], stdout=output) as child:
            status = child.wait()
        if status != 0:
            return status if status > 0 else 128 - status
        output.seek(0)
        shutil.copyfileobj(output, sys.stdout.buffer, length=1024 * 1024)
        sys.stdout.buffer.flush()
    return 0


def main():
    try:
        prefix, child = command_arguments(sys.argv[1:])
        args = forward_bounded_threads(prefix) + ["--"] + child
        root = Path(__file__).resolve().parent.parent
        lock = json.loads((root / "scripts/comparator-tools.lock.json").read_text())
        revision = lock["comparator"]["revision"]
        if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
            raise ValueError("invalid pinned Comparator revision")
        binary = root / ".lake" / f"comparator-tools-{revision}" / "landrun"
        if binary.resolve(strict=True) != binary or not binary.is_file():
            raise ValueError("pinned Landrun must be a regular nonsymlink file")
        if not os.access(binary, os.X_OK):
            raise ValueError("pinned Landrun is not executable; prepare tools first")
        stage = os.environ.get("COMPARATOR_STAGE_EXPORT", "0")
        if stage not in {"0", "1"}:
            raise ValueError("COMPARATOR_STAGE_EXPORT must be 0 or 1")
        exporter = binary.parent / f"comparator-{revision}" / ".lake/packages/lean4export/.lake/build/bin/lean4export"
        if stage == "1" and child[0] == str(exporter):
            if exporter.resolve(strict=True) != exporter or not exporter.is_file():
                raise ValueError("pinned exporter must be a regular nonsymlink file")
            if not os.access(exporter, os.X_OK):
                raise ValueError("pinned exporter is not executable; prepare tools first")
            return staged_export(binary, args, root / ".lake")
        os.execv(binary, [str(binary), *args])
    except (KeyError, TypeError, ValueError, OSError) as error:
        print(f"Landrun argument adapter: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
