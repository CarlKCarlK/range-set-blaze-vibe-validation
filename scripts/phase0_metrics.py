#!/usr/bin/env python3
"""Collect the small, reproducible Phase 0 Lean source metrics.

This deliberately uses a lexical fallback, not Lean's parser. It scans tracked
Lean files selected by git, excluding .lake/generated/vendor paths. The scanner:
  * removes -- comments through the newline;
  * removes nested /- ... -/ comments;
  * preserves strings and character literals, including escaped characters;
  * treats every splitlines() element as one physical line. Thus a final line
    without a newline still counts as one physical line;
  * counts declarations only when private? followed by def/abbrev or
    lemma/theorem begins a line in the comment-stripped source; and
  * counts whole tokens using the boundary [A-Za-z0-9_?], so simp only counts
    as simp and simpa is counted separately.

Comment-only means a nonblank original line whose comment-stripped remainder is
blank. Active-code is the remaining nonblank comment-stripped lines. The JSON
schema is intentionally simple and should be kept stable for later phases.
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
KEYS = ["simp", "simpa", "rw", "have", "linarith", "omega", "grind", "by_cases", "cases"]


def source_files() -> list[pathlib.Path]:
    out = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=ROOT, text=True,
    )
    return sorted(
        ROOT / line for line in out.splitlines()
        if line and not any(part in {".lake", "generated", "vendor"} for part in pathlib.Path(line).parts)
    )


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
                in_char = True
            out.append(c)
            i += 1
    return "".join(out)


def count_file(path: pathlib.Path) -> dict:
    raw = path.read_text()
    clean = strip_comments(raw)
    original_lines = raw.splitlines()
    clean_lines = clean.splitlines()
    blank = sum(not line.strip() for line in original_lines)
    comment_only = sum(bool(raw_line.strip()) and not clean_line.strip()
                       for raw_line, clean_line in zip(original_lines, clean_lines))
    active_code = sum(bool(line.strip()) for line in clean_lines)
    decl = r"(?m)^\s*(?:private\s+)?"
    result = {
        "file": str(path.relative_to(ROOT)),
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


def main() -> None:
    rows = [count_file(path) for path in source_files()]
    scalar_keys = ["physical_loc", "total_nonblank_loc", "blank_loc", "comment_only_loc",
                   "active_code_loc", "defs_abbrev", "lemmas_theorems", "private_lemmas_theorems"]
    result = {
        "collector": "scripts/phase0_metrics.py",
        "method": "comment-aware lexical fallback; see script module docstring",
        "files": rows,
        "totals": {key: sum(row[key] for row in rows) for key in scalar_keys},
        "token_totals": {key: sum(row["tokens"][key] for row in rows) for key in KEYS},
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
