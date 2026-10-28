"""Reproduce kernel checks of the unchanged 256 seventh-slot payments."""
from pathlib import Path
import argparse

def generate():
    files = {}
    for b in range(4):
        files[f'WR2ClassicalSeventhGridBlock{b:03d}.lean'] = f'''import WR2ClassicalSeventhTableCheck
namespace WuPaper.ClassicalSeventh
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem grid_block_{b:03d} (j : Fin 64) : upperValue ((point (64*{b}+j.val)+point ((64*{b}+j.val)+1))/2) ≤ payment (64*{b}+j.val) := by
  apply ClassicalSeventhTableCheck.condition_sound
  exact (by unfold ClassicalSeventhTableCheck.condition; decide +kernel :
    ∀ j : Fin 64, ClassicalSeventhTableCheck.condition (64*{b}+j.val)) j
end WuPaper.ClassicalSeventh
'''
    text = ''.join(f'import WR2ClassicalSeventhGridBlock{b:03d}\n' for b in range(4))
    text += '''noncomputable section
namespace WuPaper.ClassicalSeventh
open Finset

theorem payments_paid (j : Fin 256) : upperValue ((point j.val+point (j.val+1))/2) ≤ payment j.val := by
  have hj : j.val%64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : j.val/64 < 4 := by omega
  have hh (b : Fin 4) : upperValue ((point (64*b.val+j.val%64)+point ((64*b.val+j.val%64)+1))/2) ≤ payment (64*b.val+j.val%64) := by
    fin_cases b
'''
    text += ''.join(f'    · exact grid_block_{b:03d} ⟨j.val%64,hj⟩\n' for b in range(4))
    text += '''  have h := hh ⟨j.val/64,hb⟩
  have he : 64*(j.val/64)+j.val%64 = j.val := by omega
  simpa only [he] using h

theorem seventh_main_upper : Wu08TerminalAlignment.seventhMain ≤ (29259:ℝ)/50000 := by
  have h := uniform_upper payment (fun i hi => payments_paid ⟨i,hi⟩)
  apply h.trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.sigma,Wu2008DoubleSieve.SeventhEighth.alpha]

end WuPaper.ClassicalSeventh
#print axioms WuPaper.ClassicalSeventh.seventh_main_upper
'''
    files['WR2ClassicalSeventhCertificate.lean'] = text
    return files

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = Path(__file__).resolve().parents[1] / 'src'
    for name, text in generate().items():
        if args.check:
            assert (src / name).read_text() == text, name
        else:
            (src / name).write_text(text)
    print('CHECK_PASS' if args.check else 'GENERATED', 5, 'modules')
