"""Generate Lean differential cases from PySnpTools `IntRangeSet._internal_add`.

Run with a Python environment in which `pysnptools` is importable, e.g.:

    /home/carlk/programs/PySnpTools/.venv/bin/python \
        scripts/generate_py_intrangeset_cases.py

For every base set and every `(start, length)` in a window around it, and
for seeded random sequences of calls starting from `IntRangeSet()`, the
script calls the real `_internal_add` and records the resulting state three
ways: the half-open `ranges()`, the `_start_items` list, and the
`_start_to_length` dictionary.  It writes
`RangeSetBlaze/PyIntRangeSetCases.lean`, which `RangeSetBlaze/Regression.lean`
checks with `native_decide` against both the list model
(`RangeSetBlaze/PyIntRangeSet.lean`) and the two-field state model
(`RangeSetBlaze/PyIntRangeSetState.lean`).  Line tracing reports which Python
branches the cases reach.
"""

import inspect
import pathlib
import random
import sys

from pysnptools.util.intrangeset import IntRangeSet

BASES = [
    "",
    "0:5",
    "0:5,10:15,20:25",
    "0:5,6:10,12,20:25",
    "-10:-4,-3,0:8",
]

# Distinctive source text for each Python branch of `_internal_add`.
BRANCH_MARKERS = {
    "exact start, covered (return)": "if length <= self._start_to_length[start]:",
    "exact start, lengthen": "index += 1  # index should point to the following range",
    "index == 0, insert": "elif index == 0:",
    "touch previous": "if start <= stop:",
    "previous covers (return)": "if new_length < self._start_to_length[previous]:",
    "lengthen previous": "self._start_to_length[previous] = new_length",
    "gap after previous, insert": "else:  # after previous range",
    "merge loop body": "new_stop = max(stop, next + self._start_to_length[next])",
}


def branch_lines():
    source, first = inspect.getsourcelines(IntRangeSet._internal_add)
    lines = {}
    for name, marker in BRANCH_MARKERS.items():
        hits = [first + i for i, text in enumerate(source) if marker in text]
        assert len(hits) == 1, (name, hits)
        # For a condition/else line, count the line after it (the taken branch).
        code_part = source[hits[0] - first].split("#")[0].rstrip()
        lines[name] = hits[0] + (1 if code_part.endswith(":") else 0)
    return lines


SEQUENCE_COUNT = 300
SEQUENCE_LENGTH = 8
SEQUENCE_SEED = 20260923


def state(int_range_set):
    """`ranges | _start_items | _start_to_length`, flattened; the dictionary
    is listed by key."""
    return " | ".join(
        [
            ints(int_range_set.ranges()),
            " ".join(str(k) for k in int_range_set._start_items),
            ints(sorted(int_range_set._start_to_length.items())),
        ]
    )


def run_case(int_range_set, start, length, code, executed):
    def tracer(frame, event, _arg):
        if frame.f_code is code:
            if event == "line":
                executed.add(frame.f_lineno)
            return tracer
        return None

    sys.settrace(tracer)
    try:
        int_range_set._internal_add(start, length)
    finally:
        sys.settrace(None)
    return state(int_range_set)


def ints(pairs):
    return " ".join(f"{a} {b}" for a, b in pairs)


def count_branches(lines, executed, counts):
    for name, line in lines.items():
        if line in executed:
            counts[name] += 1


def main():
    code = IntRangeSet._internal_add.__code__
    lines = branch_lines()
    counts = {name: 0 for name in lines}
    out = []
    total = 0
    for base_index, base in enumerate(BASES):
        base_ranges = list(IntRangeSet(base).ranges())
        lo = min([a for a, _ in base_ranges], default=0)
        hi = max([b for _, b in base_ranges], default=0)
        cases = []
        for start in range(lo - 3, hi + 3):
            for length in range(1, hi - start + 4):
                executed = set()
                result = run_case(IntRangeSet(base), start, length, code, executed)
                count_branches(lines, executed, counts)
                cases.append(f"{start} {length} | {result}")
        total += len(cases)
        out.append(
            f"/-- Base `IntRangeSet({base!r})`. -/\n"
            f'def pyBase{base_index} : String := "{state(IntRangeSet(base))}"\n\n'
            f"/-- Cases for base {base_index}, one per line. -/\n"
            f'def pyCases{base_index} : String := "\n'
            + "\n".join(cases)
            + '"\n'
        )
    rng = random.Random(SEQUENCE_SEED)
    steps = []
    for _ in range(SEQUENCE_COUNT):
        int_range_set = IntRangeSet()
        steps.append("new")
        for _ in range(SEQUENCE_LENGTH):
            start = rng.randint(-20, 20)
            length = rng.randint(1, 8)
            executed = set()
            result = run_case(int_range_set, start, length, code, executed)
            count_branches(lines, executed, counts)
            steps.append(f"{start} {length} | {result}")
    total += SEQUENCE_COUNT * SEQUENCE_LENGTH
    out.append(
        f"/-- {SEQUENCE_COUNT} seeded random sequences of {SEQUENCE_LENGTH} calls, each from\n"
        "`IntRangeSet()` (a `new` line); every call line applies to the state\n"
        "left by the previous line. -/\n"
        'def pySequences : String := "\n' + "\n".join(steps) + '"\n'
    )
    header = (
        "/-!\n"
        "Generated by `scripts/generate_py_intrangeset_cases.py` from the real\n"
        "PySnpTools `IntRangeSet._internal_add`; do not edit by hand.  A state is\n"
        "`ranges | items | dict`: the half-open `ranges()` as flattened\n"
        "`start stop` pairs, `_start_items`, and `_start_to_length` as flattened\n"
        "`key length` pairs in key order.  Each case line is `start length | `\n"
        "followed by the state after `_internal_add(start, length)`.  The\n"
        f"integers are parsed at run time to keep elaboration cheap.  {total} cases.\n\n"
        "Python branch coverage (cases reaching each branch):\n"
        + "".join(f"* {name}: {count}\n" for name, count in counts.items())
        + "-/\n\nnamespace RangeSetBlaze.PyIntRangeSetCases\n\n"
    )
    footer = "\nend RangeSetBlaze.PyIntRangeSetCases\n"
    target = (
        pathlib.Path(__file__).resolve().parent.parent
        / "RangeSetBlaze"
        / "PyIntRangeSetCases.lean"
    )
    target.write_text(header + "\n".join(out) + footer)
    print(f"wrote {total} cases to {target}")
    for name, count in counts.items():
        print(f"  {name}: {count}")
        assert count > 0, f"branch not covered: {name}"


if __name__ == "__main__":
    main()
