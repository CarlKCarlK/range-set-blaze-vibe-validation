"""Mutation testing for `RangeSetBlaze/PyIntRangeSetState.lean`.

Run from the repository root after `lake build`:

    python3 scripts/mutate_py_intrangeset_state.py

Each mutant makes one textual change to the two-field Python model (or to
its abstraction).  The script appends the `python-differential` region of
`RangeSetBlaze/Regression.lean` to the mutated module, compiles the result
with `lake env lean` in a temporary directory, and reports whether the mutant
was killed by the proofs (an error inside the module), by the differential
tests (a failed `native_decide` in the appended region), by both, or by
neither.  The source tree is never modified.

The unmutated module is checked first and must compile with no errors.
"""

import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
MODULE = ROOT / "RangeSetBlaze" / "PyIntRangeSetState.lean"
REGRESSION = ROOT / "RangeSetBlaze" / "Regression.lean"

# (name, expectation, old text, new text).  `old` must occur exactly once.
# `expectation` records the analysis of what kills the mutant: "both" (a real
# bug), or "proof" alone.  A "proof" mutant is marked either
# [equivalent]: it computes the same result on every represented state and
#   in-contract call, so the theorems remain true and the tests cannot kill
#   it; the proof *script* rejects it because it follows Python's branch
#   structure branch by branch; or
# [statement]: the theorem statements themselves become false.
MUTANTS = [
    (
        "loop: merge only overlapping, not touching (`stop > next`)",
        "both",
        "    if next ≤ stop then do",
        "    if next < stop then do",
    ),
    (
        "loop: keep the absorbed key (`del _start_to_length[next]` dropped)",
        "both",
        """          startToLength :=
            Function.update
              (Function.update py.startToLength previous (some (newStop - previous)))
              next none }""",
        """          startToLength :=
            Function.update py.startToLength previous (some (newStop - previous)) }""",
    ),
    (
        "loop: new length measured from `next`",
        "both",
        "(some (newStop - previous)))",
        "(some (newStop - next)))",
    ),
    (
        "loop: new stop ignores the current stop",
        "both",
        "      let newStop := max stop (next + nextLength)",
        "      let newStop := next + nextLength",
    ),
    (
        "loop: lengthen `next` instead of `previous`",
        "both",
        "(Function.update py.startToLength previous (some (newStop - previous)))",
        "(Function.update py.startToLength next (some (newStop - previous)))",
    ),
    (
        "exact start: merge loop starts at `index` (the range itself)",
        "both",
        """    if py.startItems[index]? = some start then do
      let existingLength ← py.startToLength start
      if length ≤ existingLength then some py
      else
        mergeLoop start (index + 1)""",
        """    if py.startItems[index]? = some start then do
      let existingLength ← py.startToLength start
      if length ≤ existingLength then some py
      else
        mergeLoop start index""",
    ),
    (
        "[equivalent] exact start: `length < existing` returns (equal lengths re-merge)",
        "proof",
        "      if length ≤ existingLength then some py",
        "      if length < existingLength then some py",
    ),
    (
        "index == 0: dictionary updated but `_start_items` not",
        "both",
        """  if index = 0 then
    mergeLoop start (index + 1) (start + length)
      { startItems := py.startItems.insertIdx index start""",
        """  if index = 0 then
    mergeLoop start (index + 1) (start + length)
      { startItems := py.startItems""",
    ),
    (
        "previous: touching start treated as a gap (`start < stop`)",
        "both",
        "    if start ≤ stop then",
        "    if start < stop then",
    ),
    (
        "[equivalent] previous: `new_length <= length` returns (equal lengths re-merge)",
        "proof",
        "      else if newLength < previousLength then some py",
        "      else if newLength ≤ previousLength then some py",
    ),
    (
        "gap insert: `_start_items` updated but dictionary not",
        "both",
        """    else
      mergeLoop start (index + 1) (start + length)
        { startItems := py.startItems.insertIdx index start
          startToLength := Function.update py.startToLength start (some length) }""",
        """    else
      mergeLoop start (index + 1) (start + length)
        { startItems := py.startItems.insertIdx index start
          startToLength := py.startToLength }""",
    ),
    (
        "[equivalent] bisect_right: an exact start is then handled as `previous`",
        "proof",
        "  (items.takeWhile (· < start)).length",
        "  (items.takeWhile (· ≤ start)).length",
    ),
    (
        "[equivalent] assert `length >= 0`: zero length is outside the contract",
        "proof",
        "  if length ≤ 0 then none  -- `assert length > 0`",
        "  if length < 0 then none  -- `assert length > 0`",
    ),
    (
        "[statement] abstraction: dictionary stores `stop` instead of length",
        "proof",
        "  | r :: rs => Function.update (startToLengthOf rs) r.val.lo (some r.length)",
        "  | r :: rs => Function.update (startToLengthOf rs) r.val.lo (some r.stop)",
    ),
    (
        "[statement] invariant: stored ranges may touch, so it no longer implies `Represents`",
        "proof",
        """  stop_lt_later_start : py.startItems.Pairwise fun start next =>
    ∀ length, py.startToLength start = some length → start + length < next""",
        """  stop_lt_later_start : py.startItems.Pairwise fun start next =>
    ∀ length, py.startToLength start = some length → start + length ≤ next""",
    ),
]

ERROR = re.compile(r"^[^:]+:(\d+):\d+: error")


def differential_region():
    text = REGRESSION.read_text()
    begin = text.index("-- BEGIN python-differential")
    end = text.index("-- END python-differential")
    return text[begin:end]


def assemble(module_text, region):
    """Module text with the cases import added, followed by the region."""
    lines = module_text.splitlines(keepends=True)
    imports = [line for line in lines if line.startswith("import ")]
    body = [line for line in lines if not line.startswith("import ")]
    header = imports + ["import RangeSetBlaze.PyIntRangeSetCases\n"]
    module = "".join(header + body)
    wrapper = (
        "\nnamespace RangeSetBlaze\n\nopen IntRange\nopen IntRange.NR\n"
        "open scoped IntRange.NR\n\n"
    )
    return module, module + wrapper + region + "\nend RangeSetBlaze\n"


def classify(module_text, region, workdir):
    module, full = assemble(module_text, region)
    module_lines = module.count("\n")
    path = workdir / "Mutant.lean"
    path.write_text(full)
    result = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    output = result.stdout + result.stderr
    proof = tests = broken = False
    for line in output.splitlines():
        match = ERROR.match(line)
        if not match:
            continue
        if int(match.group(1)) <= module_lines:
            proof = True
        elif "native_decide` evaluated" in line:
            tests = True
        else:
            # The region itself failed to elaborate (e.g. a mutated definition
            # was rejected), so the tests did not run.
            broken = True
    return proof, tests, broken, output


def verdict(proof, tests):
    if proof and tests:
        return "both"
    if proof:
        return "proof"
    if tests:
        return "tests"
    return "neither"


def main():
    source = MODULE.read_text()
    region = differential_region()
    with tempfile.TemporaryDirectory() as tmp:
        workdir = pathlib.Path(tmp)
        proof, tests, broken, output = classify(source, region, workdir)
        if proof or tests or broken or ": error" in output:
            print(output)
            sys.exit("unmutated module or differential region does not compile cleanly")
        print("unmutated: proofs and differential tests pass\n")
        mismatches = 0
        for name, expected, old, new in MUTANTS:
            count = source.count(old)
            assert count == 1, (name, count)
            proof, tests, broken, _ = classify(source.replace(old, new), region, workdir)
            got = verdict(proof, tests) + (" (tests did not run)" if broken else "")
            flag = "" if got == expected else f"   <-- expected {expected}"
            mismatches += got != expected
            print(f"{got:8} {name}{flag}")
        print(f"\n{len(MUTANTS)} mutants; {mismatches} differ from the recorded expectation")
        sys.exit(1 if mismatches else 0)


if __name__ == "__main__":
    main()
