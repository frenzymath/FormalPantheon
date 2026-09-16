#!/usr/bin/env python3
"""Check extracted pinned tool sources, ignoring archive ownership and times."""

import argparse
import hashlib
import os
from pathlib import Path, PurePosixPath
import stat
import tarfile


def digest(stream):
    result = hashlib.sha256()
    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
        result.update(chunk)
    return result.digest()


def verify(archive_path, source_root, allow_lake):
    if source_root.is_symlink() or not source_root.is_dir():
        raise ValueError(f"not an ordinary source directory: {source_root}")
    source_root = source_root.resolve(strict=True)
    expected = set()
    with tarfile.open(archive_path, "r:gz") as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            if (name.is_absolute() or ".." in name.parts or not name.parts
                    or name.parts[0] != source_root.name or name in expected):
                raise ValueError(f"invalid or duplicate archive member: {member.name}")
            expected.add(name)
            target = source_root.parent.joinpath(*name.parts)
            if not target.resolve(strict=True).is_relative_to(source_root):
                raise ValueError(f"source path leaves the tool directory: {target}")
            mode = target.lstat().st_mode
            if member.isdir():
                if not stat.S_ISDIR(mode):
                    raise ValueError(f"source directory type differs: {target}")
            elif member.isfile():
                if not stat.S_ISREG(mode) or (mode & 0o111) != (member.mode & 0o111):
                    raise ValueError(f"source file type or executable bits differ: {target}")
                with archive.extractfile(member) as archived, target.open("rb") as actual:
                    if digest(archived) != digest(actual):
                        raise ValueError(f"source content differs: {target}")
            else:
                raise ValueError(f"unsupported pinned archive member type: {member.name}")

    for directory, subdirs, files in os.walk(source_root, followlinks=False):
        if allow_lake and Path(directory) == source_root and ".lake" in subdirs:
            build_dir = source_root / ".lake"
            if build_dir.is_symlink():
                raise ValueError(f"build directory is a symlink: {build_dir}")
            subdirs.remove(".lake")
        for entry in subdirs + files:
            target = Path(directory) / entry
            name = PurePosixPath(target.relative_to(source_root.parent).as_posix())
            if name not in expected:
                raise ValueError(f"unexpected tool source entry: {target}")
    print(f"verified {len(expected)} archive members: {source_root.name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("--allow-lake", action="store_true")
    args = parser.parse_args()
    try:
        verify(args.archive, args.source, args.allow_lake)
    except (OSError, ValueError, tarfile.TarError) as error:
        parser.exit(1, f"tool archive verification failed: {error}\n")


if __name__ == "__main__":
    main()
