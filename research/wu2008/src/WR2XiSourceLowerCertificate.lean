import WR2XiSourceUpperRational
import WR2XiSourceTransferRational

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open Real NodeExtension Finset
open scoped Classical

def transferCellNumerator : ℕ → ℕ
  | 6 => 617961556
  | 7 => 486623789
  | 8 => 362258103
  | 9 => 269571518
  | 10 => 242023177
  | 11 => 200510107
  | 12 => 164522938
  | 13 => 134553902
  | 14 => 109571405
  | 15 => 88745491
  | 16 => 71402620
  | 17 => 56991954
  | 18 => 45059889
  | 19 => 35230554
  | 20 => 27190728
  | 21 => 20678043
  | 22 => 15471700
  | 23 => 11374197
  | 24 => 8197625
  | 25 => 5765314
  | 26 => 3920762
  | 27 => 2526953
  | 28 => 1464258
  | 29 => 640222
  | _ => 0

def lowerNumerator : ℕ → ℕ
  | 15 => 2982256805
  | 16 => 2364295249
  | 17 => 1877671460
  | 18 => 1515413357
  | 19 => 1245841839
  | 20 => 1003818662
  | 21 => 803308555
  | 22 => 638785617
  | 23 => 504231715
  | 24 => 394660310
  | 25 => 305914819
  | 26 => 234512199
  | 27 => 177520245
  | _ => 0

def lowerLower (j : ℕ) : ℝ := (lowerNumerator j:ℝ)/1000000000000

theorem lowerLower_nonneg (j : ℕ) : 0 ≤ lowerLower j := by
  unfold lowerLower
  positivity

theorem transferCell_paid {i : ℕ} (hi : 6 ≤ i) (hi29 : i ≤ 29) :
    (transferCellNumerator i:ℝ)/1000000000000 ≤
      upperLower i*SourceLogRational.lower (rNode i/rNode (i-1)) := by
  interval_cases i <;> norm_num [transferCellNumerator, upperLower, upperNumerator,
    rNode, SourceLogRational.lower, RationalCandidate.lowerH]

theorem lowerNumerator_sum : ∀ j : Fin 13,
    lowerNumerator (15+j.val) =
      ∑ i ∈ Icc (max 3 (15+j.val-9)) 29, transferCellNumerator i := by
  decide +kernel

theorem lowerLower_le_transfer {j : ℕ} (hj : 15 ≤ j) (hj27 : j ≤ 27) :
    lowerLower j ≤ transferLower upperLower j := by
  have hratio : rNode (max 2 (j-10))/(rNode j-1) = 1 := by
    have h := start_degenerate (show 12 ≤ j by omega)
    change rNode (max 2 (j-10)) = rNode j-1 at h
    rw [h]
    apply div_self
    have hn : (0:ℝ) ≤ j := Nat.cast_nonneg _
    dsimp [rNode]
    linarith
  have hz : SourceLogRational.lower (rNode (max 2 (j-10))/(rNode j-1)) = 0 := by
    rw [hratio]
    norm_num [SourceLogRational.lower]
  rw [transferLower, hz, mul_zero, zero_add]
  have hsum := sum_le_sum (s := Icc (max 3 (j-9)) 29) (fun i hi =>
    transferCell_paid (by have := (mem_Icc.mp hi).1; omega) (mem_Icc.mp hi).2)
  have he : lowerLower j = ∑ i ∈ Icc (max 3 (j-9)) 29,
      (transferCellNumerator i:ℝ)/1000000000000 := by
    have hn := lowerNumerator_sum ⟨j-15, by omega⟩
    have hjid : 15+(j-15) = j := by omega
    change lowerNumerator (15+(j-15)) = _ at hn
    rw [hjid] at hn
    unfold lowerLower
    rw [hn, Nat.cast_sum, Finset.sum_div]

  rw [he]
  exact hsum

theorem lowerLower_le_original {j : ℕ} (hj : 15 ≤ j) (hj27 : j ≤ 27) :
    lowerLower j ≤ originalTransfer RationalCandidate.lowerH j :=
  (lowerLower_le_transfer hj hj27).trans (transferLower_le_original upperLower_nonneg
    (fun i hi hi29 => upperLower_le_extended hi hi29) (by omega))

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.lowerLower_le_original
