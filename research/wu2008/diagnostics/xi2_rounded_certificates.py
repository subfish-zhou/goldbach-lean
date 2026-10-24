"""Generate exact downward-rounded first-column certificate sources.

Python is not trusted by the proof: each generated piece equality is checked
with `decide +kernel`. Splitting at the nine original supports bounds compiler
memory without changing the 512-panel partition or the Gamma5 budget.

Use --check DIR to compare with existing sources, or --write DIR to emit them.
Without either option, print the four rows of integer payment numerators.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path

from xi2_rectangle_candidate import debit, panel_payments, rows, sigma_payment, target

DENOMINATOR = 10**12
PANELS = 512


def rounded_values():
    result = []
    for r, parameters in enumerate(rows):
        numerators = [0] * 9
        for j, payment in panel_payments(parameters, 0, PANELS):
            scaled = payment * DENOMINATOR
            numerators[j] += scaled.numerator // scaled.denominator
        total = sigma_payment(parameters, 0) + Fraction(sum(numerators), DENOMINATOR)
        assert Fraction(target[r][0], 1000) + debit[r] <= total
        result.append(numerators)
    return result


def sources(values):
    for r, row in enumerate(values):
        for j, value in enumerate(row):
            name = f"WR2XiRoundedPiece{r}{j}"
            yield name, f"""import WR2XiRationalRounded
namespace Xi2RationalMixed
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rounded_piece_{r}_{j} : roundedPiece {r} 0 {j} = ({value}/{DENOMINATOR} : ℚ) := by
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.rounded_piece_{r}_{j}
"""
        imports = "\n".join(f"import WR2XiRoundedPiece{r}{j}" for j in range(9))
        vector = ", ".join(f"{value}/{DENOMINATOR}" for value in row)
        cases = "".join(f"    · exact rounded_piece_{r}_{j}\n" for j in range(9))
        yield f"WR2XiRationalMixedCell{r}0", f"""import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
{imports}
namespace Xi2RationalMixed
open Xi2RationalTop
open scoped BigOperators
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mixed_{r}_0 : target {r} 0 + (if (0 : Fin 9) = 0 then debit {r} else 0) ≤ entry {r} 0 := by
  apply le_trans (b := roundedEntry {r} 0) _ (roundedEntry_le {r} 0)
  have hpieces : roundedPiece {r} 0 = (![{vector}] : Fin 9 → ℚ) := by
    funext j
    fin_cases j
{cases}  have hsum : (∑ j : Fin 9, roundedPiece {r} 0 j) = ({sum(row)}/{DENOMINATOR} : ℚ) := by
    rw [hpieces]
    norm_num [Fin.sum_univ_succ]
  unfold roundedEntry
  rw [hsum]
  decide +kernel
end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_{r}_0
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--check", type=Path)
    action.add_argument("--write", type=Path)
    args = parser.parse_args()
    values = rounded_values()
    if args.check:
        mismatches = [name for name, source in sources(values)
                      if not (args.check / f"{name}.lean").exists()
                      or (args.check / f"{name}.lean").read_text() != source]
        if mismatches:
            parser.exit(1, "Source mismatch: " + ", ".join(mismatches) + "\n")
        print("All 40 generated sources match; this is not a Lean proof check.")
    elif args.write:
        args.write.mkdir(parents=True, exist_ok=True)
        for name, source in sources(values):
            (args.write / f"{name}.lean").write_text(source)
    else:
        print(json.dumps(values))


if __name__ == "__main__":
    main()
