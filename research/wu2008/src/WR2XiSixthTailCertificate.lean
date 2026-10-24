import WR2XiSixthProfileTail
import WR2XiSourceLowerCertificate
noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real NodeExtension Finset SourceRational
open scoped Classical

def fullCellNumerator (i : ℕ) : ℕ :=
  if i = 3 then 959758005 else if i = 4 then 857959267 else
    if i = 5 then 735449053 else transferCellNumerator i

def tailNumerator : ℕ → ℕ
  | 2 => 5535423130
  | 3 => 4575665125
  | 4 => 3717705858
  | 5 => 2982256805
  | 6 => 2364295249
  | 7 => 1877671460
  | 8 => 1515413357
  | 9 => 1245841839
  | 10 => 1003818662
  | 11 => 803308555
  | _ => 0

theorem fullCell_paid {i : ℕ} (hi : 3 ≤ i) (hi29 : i ≤ 29) :
    (fullCellNumerator i:ℝ)/1000000000000 ≤
      upperLower i*SourceLogRational.lower (rNode i/rNode (i-1)) := by
  by_cases h6 : 6 ≤ i
  · simpa only [fullCellNumerator,if_neg (by omega : i ≠ 3),
      if_neg (by omega : i ≠ 4),if_neg (by omega : i ≠ 5)] using transferCell_paid h6 hi29
  · interval_cases i <;> norm_num [fullCellNumerator,upperLower,RationalCandidate.lowerH,
      rNode,SourceLogRational.lower]

theorem tailNumerator_sum : ∀ k : Fin 10,
    tailNumerator (2+k.val) = ∑ i ∈ Icc (2+k.val+1) 29, fullCellNumerator i := by
  decide +kernel

theorem tail_paid {k : ℕ} (hk : 2 ≤ k) (hk11 : k ≤ 11) :
    (tailNumerator k:ℝ)/1000000000000 ≤
      ∑ i ∈ Icc (k+1) 29, upperLower i*SourceLogRational.lower (rNode i/rNode (i-1)) := by
  have he := tailNumerator_sum ⟨k-2,by omega⟩
  have hk' : 2+(k-2)=k := by omega
  change tailNumerator (2+(k-2)) = _ at he
  rw [hk'] at he
  rw [he,Nat.cast_sum,Finset.sum_div]
  apply sum_le_sum
  intro i hi
  exact fullCell_paid (by have := (mem_Icc.mp hi).1; omega) (mem_Icc.mp hi).2

theorem compact_point_lower {k : ℕ} {s : ℝ} (hk : 2 ≤ k) (hk11 : k ≤ 11)
    (hs0 : profileLeft k ≤ s-1) (hs1 : s-1 ≤ rNode k) :
    upperLower k*SourceLogRational.lower (rNode k/(s-1))+
      (tailNumerator k:ℝ)/1000000000000 ≤ pointLower s :=
  partial_tail_le_pointLower hk (by omega) hs0 hs1 (tail_paid hk hk11)

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.compact_point_lower
