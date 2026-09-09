#!/usr/bin/env python3
"""Collect reproducible lexical metrics for repository-owned Lean sources.

This is intentionally a lexical fallback rather than a Lean parser. It
removes line and nested block comments while preserving strings and plausible
Lean character literals. In particular, a prime following an identifier is
not a character-literal opener: Lean permits primed identifiers such as
``mkNR'`` and ``h''``.

The collector can measure either the current working tree (``--source-root``)
or an exact Git commit/ref (``--git-ref``), without checking out the ref.
Every result records the collector version/hash and a deterministic manifest
of the measured Lean source bytes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
from typing import Callable

ROOT = pathlib.Path(__file__).resolve().parents[1]
KEYS = ["simp", "simpa", "rw", "have", "linarith", "omega", "grind", "by_cases", "cases"]
EXCLUDED_PARTS = {".lake", "generated", "vendor"}
COLLECTOR_VERSION = 2


def _git(root: pathlib.Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=root, text=True)


def _included(path: str) -> bool:
    return path.endswith(".lean") and not any(part in EXCLUDED_PARTS for part in pathlib.PurePosixPath(path).parts)


def working_tree_files(root: pathlib.Path) -> list[str]:
    output = _git(root, "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean")
    return sorted(path for path in output.splitlines() if path and _included(path))


def git_ref_files(root: pathlib.Path, ref: str) -> tuple[str, list[str]]:
    commit = _git(root, "rev-parse", f"{ref}^{{commit}}").strip()
    # Filter ourselves instead of relying on ls-tree's pathspec semantics:
    # ``*.lean`` is not recursive there unless the glob magic is requested.
    output = _git(root, "ls-tree", "-r", "--name-only", commit)
    return commit, sorted(path for path in output.splitlines() if path and _included(path))


def _is_identifier_continuation(c: str) -> bool:
    return bool(c) and (c == "_" or c == "'" or c.isalnum())


def _character_literal_end(text: str, start: int) -> int | None:
    """Return the exclusive end of a plausible Lean character literal."""
    i = start + 1
    if i >= len(text) or text[i] in "\r\n'":
        return None
    if text[i] == "\\":
        i += 1
        if i >= len(text) or text[i] in "\r\n":
            return None
        if text[i] == "x":
            i += 1
            if i + 2 > len(text) or any(c not in "0123456789abcdefABCDEF" for c in text[i:i + 2]):
                return None
            i += 2
        elif text[i] == "u" and i + 1 < len(text) and text[i + 1] == "{":
            close = text.find("}", i + 2)
            if close < 0 or close == i + 2 or any(c not in "0123456789abcdefABCDEF" for c in text[i + 2:close]):
                return None
            i = close + 1
        else:
            i += 1
    else:
        i += 1
    return i + 1 if i < len(text) and text[i] == "'" else None


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_char = False
    escaped = False
    while i < len(text):
        c = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if depth:
            if c == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif c == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append(c)
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if in_char:
            out.append(c)
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == "'":
                in_char = False
            i += 1
            continue
        if c == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
        elif c == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            if c == '"':
                in_string = True
            elif c == "'":
                previous = text[i - 1] if i else ""
                end = _character_literal_end(text, i)
                if not _is_identifier_continuation(previous) and end is not None:
                    in_char = True
            out.append(c)
            i += 1
    return "".join(out)


def count_source(file_name: str, raw: str) -> dict:
    clean = strip_comments(raw)
    original_lines = raw.splitlines()
    clean_lines = clean.splitlines()
    blank = sum(not line.strip() for line in original_lines)
    comment_only = sum(bool(raw_line.strip()) and not clean_line.strip()
                       for raw_line, clean_line in zip(original_lines, clean_lines))
    active_code = sum(bool(line.strip()) for line in clean_lines)
    decl = r"(?m)^\s*(?:private\s+)?"
    result = {
        "file": file_name,
        "physical_loc": len(original_lines),
        "total_nonblank_loc": len(original_lines) - blank,
        "blank_loc": blank,
        "comment_only_loc": comment_only,
        "active_code_loc": active_code,
        "defs_abbrev": len(re.findall(decl + r"(?:def|abbrev)\b", clean)),
        "lemmas_theorems": len(re.findall(decl + r"(?:lemma|theorem)\b", clean)),
        "private_lemmas_theorems": len(re.findall(r"(?m)^\s*private\s+(?:lemma|theorem)\b", clean)),
        "tokens": {},
    }
    for key in KEYS:
        result["tokens"][key] = len(re.findall(
            r"(?<![A-Za-z0-9_?])" + re.escape(key) + r"(?![A-Za-z0-9_?])", clean
        ))
    return result


def _manifest(entries: list[dict]) -> str:
    encoded = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _source_data(root: pathlib.Path, git_ref: str | None) -> tuple[list[str], Callable[[str], bytes], dict]:
    if git_ref is not None:
        commit, files = git_ref_files(root, git_ref)
        tree = _git(root, "rev-parse", f"{commit}^{{tree}}").strip()

        def read(path: str) -> bytes:
            return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=root)

        identity = {"mode": "git-ref", "requested_ref": git_ref, "resolved_commit": commit, "resolved_tree": tree}
    else:
        files = working_tree_files(root)

        def read(path: str) -> bytes:
            return (root / path).read_bytes()

        commit = _git(root, "rev-parse", "HEAD").strip()
        tree = _git(root, "rev-parse", "HEAD^{tree}").strip()
        identity = {"mode": "working-tree", "base_commit": commit, "base_tree": tree}
    # Read each source once so the manifest and the metrics describe the same
    # snapshot even if a working-tree file is edited while collection runs.
    source_bytes = {path: read(path) for path in files}
    read = source_bytes.__getitem__
    entries = []
    for path in files:
        data = read(path)
        entries.append({"file": path, "sha256": hashlib.sha256(data).hexdigest(), "size": len(data)})
    identity["source_bytes_manifest_sha256"] = _manifest(entries)
    identity["source_bytes_manifest"] = entries
    return files, read, identity


def collect(root: pathlib.Path, git_ref: str | None) -> dict:
    files, read, identity = _source_data(root, git_ref)
    rows = [count_source(path, read(path).decode("utf-8")) for path in files]
    scalar_keys = ["physical_loc", "total_nonblank_loc", "blank_loc", "comment_only_loc",
                   "active_code_loc", "defs_abbrev", "lemmas_theorems", "private_lemmas_theorems"]
    return {
        "collector": "scripts/phase0_metrics.py",
        "collector_version": COLLECTOR_VERSION,
        "collector_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        "method": "comment-aware lexical fallback; see script module docstring",
        "source_root": str(root),
        "source_identity": identity,
        "files": rows,
        "totals": {key: sum(row[key] for row in rows) for key in scalar_keys},
        "token_totals": {key: sum(row["tokens"][key] for row in rows) for key in KEYS},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--source-root", type=pathlib.Path, default=ROOT,
                        help="repository working tree to scan (default: collector repository)")
    source.add_argument("--git-ref", metavar="REF", help="scan Lean files from this Git ref without checkout")
    parser.add_argument("-o", "--output", type=pathlib.Path, help="write JSON here instead of stdout")
    args = parser.parse_args()
    root = ROOT if args.git_ref is not None else args.source_root.resolve()
    result = json.dumps(collect(root, args.git_ref), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
