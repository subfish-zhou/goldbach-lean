"""Render unchanged midpoint payment data with shared exact-rational checks.

The 64-point proof blocks are a compilation partition, not a quadrature mesh.
Each finite condition is reduced by Lean's kernel and transported to the
original real-valued formula by the corresponding TableCheck soundness theorem.
"""

def render_family(family, tag, nums, n, start, stop):
    assert len(nums) == n and n % 64 == 0
    key, cap = tag.lower(), tag.capitalize()
    ns = f'WuPaper.Classical{family}Rational'
    prefix = f'WR2Classical{family}'
    scale = 10 ** 12
    data_blocks, proof_blocks = n // 16, n // 64
    total = sum(nums)
    root = {}
    text = f'''import {prefix}Assembly
noncomputable section
namespace {ns}
open Finset
'''
    for b in range(data_blocks):
        text += f'def {key}Block{b:03d} : ℕ → ℕ\n'
        for j in range(16):
            text += f'  | {j} => {nums[16*b+j]}\n'
        text += '  | _ => 0\n'
    text += f'def {key}Numerator (i : ℕ) : ℕ :=\n  match i/16 with\n'
    for b in range(data_blocks):
        text += f'  | {b} => {key}Block{b:03d} (i%16)\n'
    text += f'''  | _ => 0
def {key}Payment (i : ℕ) : ℝ := ({key}Numerator i:ℝ)/{scale}
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem {key}_sum : (∑ i ∈ range {n}, {key}Numerator i) = {total} := by
  decide +kernel

theorem {key}_total : ({total}:ℝ)/{scale} ≤ ∑ i ∈ range {n}, {key}Payment i := by
  simp only [{key}Payment,← Finset.sum_div,← Nat.cast_sum,{key}_sum]
  rfl
end {ns}
#print axioms {ns}.{key}_total
'''
    root[f'{prefix}{cap}Payments.lean'] = text
    opened = ('ClassicalFifthSource ClassicalUniformMidpoint' if family == 'Fifth'
              else 'WuSource.SrcSixthGain ClassicalSixthQuadrature')
    condition = f'Classical{family}TableCheck.{key}Condition'
    for b in range(proof_blocks):
        root[f'{prefix}{cap}GridBlock{b:03d}.lean'] = f'''import {prefix}{cap}Payments
import {prefix}TableCheck
namespace {ns}
open {opened}
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem {key}_grid_block_{b:03d} (j : Fin 64) : {key}Payment (64*{b}+j.val) ≤
    {key}Value ((point {start} {stop} {n} (64*{b}+j.val)+point {start} {stop} {n} (64*{b}+j.val+1))/2) := by
  apply {condition}_sound
  exact (by unfold {condition}; decide +kernel :
    ∀ j : Fin 64, {condition} {key}Numerator (64*{b}+j.val)) j

end {ns}
#print axioms {ns}.{key}_grid_block_{b:03d}
'''
    text = ''.join(f'import {prefix}{cap}GridBlock{b:03d}\n' for b in range(proof_blocks))
    text += f'''noncomputable section
namespace {ns}
open {opened}
set_option maxHeartbeats 4000000 in
theorem all_{key}_paid (i : ℕ) (hindex : i < {n}) : {key}Payment i ≤
    {key}Value ((point {start} {stop} {n} i+point {start} {stop} {n} (i+1))/2) := by
  have hj : i%64 < 64 := Nat.mod_lt _ (by norm_num)
  have hb : i/64 < {proof_blocks} := by omega
  have hh (b : Fin {proof_blocks}) : {key}Payment (64*b.val+i%64) ≤
      {key}Value ((point {start} {stop} {n} (64*b.val+i%64)+point {start} {stop} {n} (64*b.val+i%64+1))/2) := by
    fin_cases b
'''
    for b in range(proof_blocks):
        text += f'    · exact {key}_grid_block_{b:03d} ⟨i%64,hj⟩\n'
    text += f'''  have he : 64*(i/64)+i%64=i := by omega
  simpa only [he] using hh ⟨i/64,hb⟩
end {ns}
#print axioms {ns}.all_{key}_paid
'''
    root[f'{prefix}{cap}Root.lean'] = text
    return root
