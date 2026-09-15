import SrcSingleLogWeights
import W09PaidRowsV2
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedback

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Real Set Finset
open scoped Classical Interval BigOperators

def psiNode (j : Fin 7) : ℝ := sourceNode (3 + j.val)
def psiTop : Fin 7 → ℝ := ![9 / 2, 223 / 50, 103 / 25, 179 / 50, 347 / 100, 167 / 50, 319 / 100]
def psiLeft (j : Fin 7) : ℝ := 1 / 2 - truncatedSixthLowerAlpha * psiNode j
def psiRight (j : Fin 7) : ℝ :=
  if j.val = 0 then 1 / 3 else 1 / 2 - truncatedSixthLowerAlpha * sourceNode (2 + j.val)
def psiPrimes (j : Fin 7) (N : ℕ) : Finset ℕ :=
  primeWindow N ((N : ℝ) ^ psiLeft j) ((N : ℝ) ^ psiRight j)
def psiCount (j : Fin 7) (N : ℕ) : ℝ :=
  ∑ p ∈ psiPrimes j N, (sieveCount N p N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ)
def psiRatio (N : ℕ) (δ : ℝ) (p : ℕ) : ℝ := (N : ℝ) ^ levelExponent δ / p
def psiLogWeight (j : Fin 7) : ℝ :=
  sourceWeight (if j.val = 0 then 1 / (6 * truncatedSixthLowerAlpha)
    else sourceNode (2 + j.val)) (psiNode j)

theorem seven_parameter_geometry (j : Fin 7) :
    2 < psiNode j ∧ psiNode j ≤ 3 ∧ 3 ≤ psiTop j ∧ psiTop j ≤ 5 ∧
      psiNode j ≤ psiTop j ∧ 2 / psiTop j + 1 / psiNode j ≤ 1 ∧
      2 ≤ psiTop j - psiTop j / psiNode j ∧
      (1 / 4 : ℝ) < psiLeft j ∧ psiLeft j < psiRight j ∧
      psiRight j ≤ 1 / 3 ∧
      (1 / 40 : ℝ) ≤ (1 / 2 - 1 / 100 - psiRight j) / psiTop j := by
  fin_cases j <;> norm_num [psiNode, psiTop, sourceNode, psiLeft, psiRight,
    truncatedSixthLowerAlpha]

theorem seven_source_rows :
    (∀ j : Fin 3, psiNode (j.castAdd 4) = (Wu04RemainingCore.row j).s ∧
      psiTop (j.castAdd 4) = (Wu04RemainingCore.row j).S) ∧
    (∀ j : Fin 4, psiNode (Fin.natAdd 3 j) = ActualNineFeedback.firstNode j.castSucc ∧
      psiTop (Fin.natAdd 3 j) = ActualNineFeedback.firstS j.castSucc) := by
  constructor
  · intro j
    fin_cases j <;> norm_num [psiNode, psiTop, sourceNode, Wu04RemainingCore.row,
      ActualNineFeedback.coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]
    all_goals rfl
  · intro j
    fin_cases j <;> norm_num [psiNode, psiTop, sourceNode,
      ActualNineFeedback.firstNode, ActualNineFeedback.firstS]
    all_goals rfl

theorem seven_ratio_geometry {N p : ℕ} {δ : ℝ} (j : Fin 7)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) :
    1 < psiRatio N δ p ∧
      psiRatio N δ p ≤ (N : ℝ) ^ (truncatedSixthLowerAlpha * psiNode j) ∧
      (N : ℝ) ^ (levelExponent δ - psiRight j) ≤ psiRatio N δ p := by
  have hg := seven_parameter_geometry j
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hm := mem_primeWindow.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hm.1.pos
  have hlo : (N : ℝ) ^ (levelExponent δ - psiRight j) ≤ psiRatio N δ p := by
    apply (le_div_iff₀ hp0).mpr
    calc
      _ ≤ (N : ℝ) ^ (levelExponent δ - psiRight j) * (N : ℝ) ^ psiRight j :=
        mul_le_mul_of_nonneg_left hm.2.2.2.le (by positivity)
      _ = (N : ℝ) ^ levelExponent δ := by rw [← rpow_add hN0]; congr 1; ring
  have hright : psiRight j ≤ (1 / 3 : ℝ) := hg.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, hlo⟩
  · exact (one_lt_rpow hN1 (by dsimp [levelExponent]; linarith)).trans_le hlo
  · apply (div_le_iff₀ hp0).mpr
    calc
      _ ≤ (N : ℝ) ^ (truncatedSixthLowerAlpha * psiNode j + psiLeft j) :=
        rpow_le_rpow_of_exponent_le hN1.le (by dsimp [levelExponent, psiLeft]; linarith)
      _ = (N : ℝ) ^ (truncatedSixthLowerAlpha * psiNode j) * (N : ℝ) ^ psiLeft j :=
        rpow_add hN0 _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hm.2.2.1 (by positivity)

theorem seven_cutoff_geometry {N p : ℕ} {δ : ℝ} (j : Fin 7)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) :
    1 < wuLocalCutoff N δ p (psiTop j) ∧
      wuLocalCutoff N δ p (psiTop j) ≤ wuLocalCutoff N δ p (psiNode j) ∧
      wuLocalCutoff N δ p (psiNode j) ≤ (N : ℝ) ^ truncatedSixthLowerAlpha ∧
      (N : ℝ) ^ truncatedSixthLowerAlpha < p := by
  have hg := seven_parameter_geometry j
  have hr := seven_ratio_geometry j hN hd hh hp
  have hs : 0 < psiNode j := by linarith [hg.1]
  have hS : 0 < psiTop j := by linarith [hg.2.2.1]
  have hsS := hg.2.2.2.2.1
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hleft : truncatedSixthLowerAlpha < psiLeft j :=
    (by norm_num [truncatedSixthLowerAlpha] : truncatedSixthLowerAlpha < 1 / 4).trans
      hg.2.2.2.2.2.2.2.1
  refine ⟨one_lt_rpow hr.1 (one_div_pos.mpr hS),
    rpow_le_rpow_of_exponent_le hr.1.le (one_div_le_one_div_of_le hs hsS), ?_, ?_⟩
  · calc
      wuLocalCutoff N δ p (psiNode j) ≤
          ((N : ℝ) ^ (truncatedSixthLowerAlpha * psiNode j)) ^ (1 / psiNode j) :=
        rpow_le_rpow (by change 0 ≤ psiRatio N δ p; linarith only [hr.1])
          hr.2.1 (one_div_nonneg.mpr hs.le)
      _ = (N : ℝ) ^ truncatedSixthLowerAlpha := by
        rw [← rpow_mul (Nat.cast_nonneg N)]
        congr 1
        field_simp
  · exact (rpow_lt_rpow_of_exponent_lt hN1 hleft).trans_le (mem_primeWindow.mp hp).2.2.1

theorem seven_repeated_zero {N p : ℕ} {δ : ℝ} (j : Fin 7)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) :
    wuOmegaRepeated N p δ (psiNode j) (psiTop j) = 0 := by
  have hg := seven_cutoff_geometry j hN hd hh hp
  apply sum_eq_zero
  intro q hq
  obtain ⟨hq, hdiv⟩ := mem_filter.mp hq
  have hqp : q.Prime := (mem_primeWindow.mp hq).1
  have hlt : q < p := by
    exact_mod_cast (mem_primeWindow.mp hq).2.2.2.trans_le
      (hg.2.2.1.trans hg.2.2.2.le)
  rcases (Nat.dvd_prime (mem_primeWindow.mp hp).1).mp hdiv with h | h
  · exact False.elim (hqp.ne_one h)
  · exact False.elim (Nat.ne_of_lt hlt h)

theorem seven_finite_omega_consumer {N : ℕ} {δ : ℝ} (j : Fin 7)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    2 * psiCount j N ≤
      ∑ p ∈ psiPrimes j N,
        (wuOmega1 N p δ (psiTop j) - wuOmega2 N p δ (psiNode j) (psiTop j) +
          wuOmega3 N p δ (psiNode j) (psiTop j)) := by
  unfold psiCount
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hg := seven_cutoff_geometry j hN hd hh hp
  have hm := wu_omega_weighted_finite N p hg.2.1
  rw [seven_repeated_zero j hN hd hh hp, add_zero] at hm
  have hc : (sourceSieveCount N p (p * N) ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) ≤
      (sourceSieveCount N p (p * N) (wuLocalCutoff N δ p (psiNode j)) : ℝ) := by
    exact_mod_cast sourceSieveCount_antitone N p (p * N) hg.2.2.1
  rw [SingleUpperCounts.source_count (mem_primeWindow.mp hp).1 hg.2.2.2.le] at hc
  exact (mul_le_mul_of_nonneg_left hc (by norm_num)).trans hm

theorem seven_not_direct_source_box {N k : ℕ} {δ Δ : ℝ} {V : Fin 1 → ℝ}
    (j : Fin 7) (hN : 2 ≤ N) (hd : 0 ≤ δ)
    (hV : (N : ℝ) ^ psiLeft j ≤ V 0) :
    ¬ wuSourceBox k δ N 1 Δ V := by
  intro hbox
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpos : 0 ≤ (N : ℝ) ^ psiLeft j := rpow_nonneg hN0 _
  have hsq : ((N : ℝ) ^ psiLeft j) ^ 2 ≤ (V 0) ^ 2 :=
    pow_le_pow_left₀ hpos hV 2
  have hb := hbox.2.2.2.2.2 (0 : Fin 1)
  have hprefix : (V 0) ^ 2 ≤ (N : ℝ) ^ (1 / 2 - δ) := by
    simpa using hb
  have hleft := (seven_parameter_geometry j).2.2.2.2.2.2.2.1
  have hexp : (1 / 2 : ℝ) - δ < psiLeft j * 2 := by linarith
  have hpow := rpow_lt_rpow_of_exponent_lt hN1 hexp
  have hident : ((N : ℝ) ^ psiLeft j) ^ 2 = (N : ℝ) ^ (psiLeft j * 2) := by
    rw [← rpow_natCast, ← rpow_mul hN0]
    norm_num
  rw [hident] at hsq
  exact (not_lt_of_ge (hsq.trans hprefix)) hpow

theorem psi_first_log_weight :
    psiLogWeight 0 = log (4 * truncatedSixthLowerAlpha * sourceNode 3 /
      (1 - 2 * truncatedSixthLowerAlpha * sourceNode 3)) := by
  norm_num [psiLogWeight, psiNode, sourceNode, sourceWeight, truncatedSixthLowerAlpha]

theorem psi_later_log_weight {j : Fin 7} (hj : j.val ≠ 0) :
    psiLogWeight j =
      log (sourceNode (3 + j.val) *
        (1 - 2 * truncatedSixthLowerAlpha * sourceNode (2 + j.val)) /
        (sourceNode (2 + j.val) *
          (1 - 2 * truncatedSixthLowerAlpha * sourceNode (3 + j.val)))) := by
  simp only [psiLogWeight, if_neg hj, psiNode, sourceWeight]

#check @seven_finite_omega_consumer
#check @seven_not_direct_source_box
#print axioms seven_source_rows
#print axioms seven_finite_omega_consumer
#print axioms seven_not_direct_source_box
end WuSource.SrcSingle
