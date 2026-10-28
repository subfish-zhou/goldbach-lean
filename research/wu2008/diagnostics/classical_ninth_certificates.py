"""Reproduce finite certificates for the unchanged ninth-slot payment table.

The original 512 midpoint grid, 12-term logarithm enclosure, whole-cell error,
10^12 scale, and integer payment data in WR2ClassicalNinthPayments are retained.
Only proof assembly is generated here; every condition is checked by Lean's kernel.
"""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1] / 'src'

def generate():
    files = {}
    for b in range(8):
        files[f'WR2ClassicalNinthGridBlock{b:03d}.lean'] = f'''import WR2ClassicalNinthTableCheck
namespace WuPaper.ClassicalNinth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem grid_block_{b:03d} (j : Fin 64) : upperValue ((point (64*{b}+j.val)+point ((64*{b}+j.val)+1))/2) ≤ payment (64*{b}+j.val) := by
  apply ClassicalNinthTableCheck.condition_sound
  exact (by unfold ClassicalNinthTableCheck.condition; decide +kernel :
    ∀ j : Fin 64, ClassicalNinthTableCheck.condition (64*{b}+j.val)) j
end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.grid_block_{b:03d}
'''
    s = ''.join(f'import WR2ClassicalNinthGridBlock{b:03d}\n' for b in range(8))
    s += '''noncomputable section
namespace WuPaper.ClassicalNinth
open Finset
set_option maxHeartbeats 4000000 in
theorem payments_paid (j : Fin 512) : upperValue ((point j.val+point (j.val+1))/2) ≤ payment j.val := by
  have hj : j.val%64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : j.val/64 < 8 := by omega
  have hh (b : Fin 8) : upperValue ((point (64*b.val+j.val%64)+point ((64*b.val+j.val%64)+1))/2) ≤ payment (64*b.val+j.val%64) := by
    fin_cases b
'''
    s += ''.join(f'    · exact grid_block_{b:03d} ⟨j.val%64,hj⟩\n' for b in range(8))
    s += '''  have h := hh ⟨j.val/64,hb⟩
  simpa only [show 64*(j.val/64)+j.val%64 = j.val by omega] using h

theorem ninth_main_upper : Wu08TerminalAlignment.ninthMain ≤ (268621:ℝ)/50000 := by
  have h := uniform_upper payment (fun i hi => payments_paid ⟨i,hi⟩)
  apply h.trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [step,lowerEndpoint,upperEndpoint,Wu2008DoubleSieve.ninthProfileSigma,Wu2008DoubleSieve.ninthProfileK1,Wu2008DoubleSieve.ninthProfileK2]

end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.ninth_main_upper
'''
    files['WR2ClassicalNinthCertificate.lean'] = s
    return files

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--write', action='store_true')
    args = ap.parse_args()
    assert args.check != args.write, 'Choose exactly one of --check / --write'
    for name, text in generate().items():
        path = ROOT / name
        if args.check:
            assert path.read_text() == text, name
        else:
            path.write_text(text)
    print('CHECK_PASS' if args.check else 'GENERATED', len(generate()), 'modules')

if __name__ == '__main__':
    main()
