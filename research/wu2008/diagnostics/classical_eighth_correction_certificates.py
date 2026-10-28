"""Reproduce the eighth correction's finite exact-rational checks.

The existing payment table and analytic integral proof are unchanged. Each
block applies the same rational-to-real soundness theorem to sixteen cells;
Lean's kernel checks every finite inequality.
"""
from pathlib import Path
import argparse


def generate():
    outputs = {}
    for b in range(32):
        outputs[f'WR2ClassicalEighthCorrectionGridBlock{b:03d}.lean'] = f'''import WR2ClassicalEighthCorrectionTableCheck
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem conditions_{b:03d} : ∀ j : Fin 16, TableCheck.condition (16*{b}+j.val) := by
  decide +kernel

theorem grid_block_{b:03d} (j : Fin 16) : step*payment (16*{b}+j.val) ≤ cellPayment (point (16*{b}+j.val)) (point ((16*{b}+j.val)+1)) :=
  TableCheck.condition_sound (conditions_{b:03d} j)

end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.grid_block_{b:03d}
'''
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write', type=Path, metavar='SOURCE_DIR')
    group.add_argument('--check', type=Path, metavar='SOURCE_DIR')
    args = parser.parse_args()
    destination = args.check or args.write
    if args.write:
        destination.mkdir(parents=True, exist_ok=True)
    for name, content in generate().items():
        path = destination / name
        if args.check:
            assert path.read_text() == content, name
        else:
            path.write_text(content)
    print(f'{"CHECK_PASS" if args.check else "GENERATED"} 32 modules')


if __name__ == '__main__':
    main()
