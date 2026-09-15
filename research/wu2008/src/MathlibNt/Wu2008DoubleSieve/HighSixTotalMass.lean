import MathlibNt.Wu2008DoubleSieve.HighSixSignedIntegral
import MathlibNt.Wu2008DoubleSieve.SingleUpperNormalization
import MathlibNt.Wu2008DoubleSieve.SingleUpperPrimePayment

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter Set LiLiuPrereqBuchstab
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The original half-open coprime window embeds into the closed all-prime
window only for an upper mass bound. -/
theorem outer_closed {N p : ℕ} (hp : p ∈ P N) :
    p ∈ primesIcc ((N : ℝ)^left) ((N : ℝ)^right) := by
  obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeWindow.mp hp
  exact (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr ⟨hpp,hlo,hhi.le⟩

theorem outer_log_bound {N p : ℕ} (hN : 2 ≤ N) (hp : p ∈ P N) :
    log (p : ℝ)/log N ≤ right := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  apply (div_le_iff₀ hl).mpr
  rw [← log_rpow hN0]
  exact log_le_log (by exact_mod_cast (mem_primeWindow.mp hp).1.pos)
    (mem_primeWindow.mp hp).2.2.2.le

/-- A full-mass upper bound retains li(N), C(N), and the original p-2 weight.
All three thresholds precede N and its coprime prime carrier. -/
theorem B6_total_mass {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      0 ≤ B6 N δ ∧ B6 N δ ≤ 480*truncatedSixthMassScale N := by
  obtain ⟨T1,hT14,hT1⟩ := SingleUpperPrimePayment.reciprocal_mass_bound
  obtain ⟨T2,_,hT2⟩ := SingleUpperPrimePayment.denominator_payment (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T3,_,hT3⟩ := SingleUpperPrimePayment.trueLi_upper (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N hN _he
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hN3 : T3 ≤ N := by omega
  have hN4 : 4 ≤ N := hT14.trans hN1
  have hNge : 2 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hNge)
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hNge)
  have hden (p : ℕ) (hp : p ∈ P N) :
      2 < p ∧ 1/((p : ℝ)-2) ≤ 2/p := by
    have hd := hT2 N hN2 p (mem_primeWindow.mp hp).1
      ((rpow_le_rpow_of_exponent_le hNr (show (1/15 : ℝ) ≤ left by norm_num [left])).trans
        (mem_primeWindow.mp hp).2.2.1)
    exact ⟨hd.1, by norm_num at hd ⊢; exact hd.2.1⟩
  have hsum : (∑ p ∈ P N, 1/((p : ℝ)-2)) ≤ 10 := by
    calc
      _ ≤ ∑ p ∈ P N, 2/(p : ℝ) := sum_le_sum (fun p hp => (hden p hp).2)
      _ = 2 * ∑ p ∈ P N, 1/(p : ℝ) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ 2 * ∑ p ∈ primesIcc ((N : ℝ)^left) ((N : ℝ)^right), 1/(p : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg (fun p hp => outer_closed hp) (by intros; positivity)
      _ ≤ 10 := by
        have hh := hT1 N hN1 left right (by norm_num [left])
          (by norm_num [left,right]) (by norm_num [right])
        linarith
  have hc (p : ℕ) (hp : p ∈ P N) :
      (1/6 : ℝ) ≤ (1/2-δ)-log (p : ℝ)/log N := by
    have hh := outer_log_bound hNge hp
    norm_num [right] at hh
    linarith
  have hweighted : (∑ p ∈ P N, 1/(((p : ℝ)-2)*((1/2-δ)-log (p : ℝ)/log N))) ≤ 60 := by
    calc
      _ ≤ ∑ p ∈ P N, 6*(1/((p : ℝ)-2)) := by
        apply sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) < p := by exact_mod_cast (hden p hp).1
        have hcp : 0 < (1/2-δ)-log (p : ℝ)/log N := lt_of_lt_of_le (by norm_num) (hc p hp)
        have hi : 1/((1/2-δ)-log (p : ℝ)/log N) ≤ 6 :=
          (div_le_iff₀ hcp).mpr (by linarith [hc p hp])
        calc
          _ = (1/((p : ℝ)-2))*(1/((1/2-δ)-log (p : ℝ)/log N)) := by
            simp only [one_div, mul_inv_rev]; ring
          _ ≤ (1/((p : ℝ)-2))*6 := mul_le_mul_of_nonneg_left hi (by positivity)
          _ = _ := by ring
      _ = 6 * ∑ p ∈ P N, 1/((p : ℝ)-2) := (mul_sum ..).symm
      _ ≤ 60 := by linarith
  have hcoef : 4*logarithmicIntegral N*wuSingularSeries N/log N ≤
      8*truncatedSixthMassScale N := by
    calc
      _ ≤ 4*((1+1)*(N : ℝ)/log N)*wuSingularSeries N/log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT3 N hN3) (by norm_num)) hC)
          hlog.le
      _ = _ := by unfold truncatedSixthMassScale; ring
  refine ⟨?_, ?_⟩
  · rw [B6_sum]; exact sum_nonneg (fun p hp => thetaAtom_nonneg hNge hδ hδhi hp)
  · rw [B6, SingleUpperNormalization.theta_single_exact hNge (P N)
      (fun p hp => ⟨(mem_primeWindow.mp hp).1,(hden p hp).1,(mem_primeWindow.mp hp).2.1⟩)]
    calc
      _ ≤ (4*logarithmicIntegral N*wuSingularSeries N/log N)*60 :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ ≤ (8*truncatedSixthMassScale N)*60 := mul_le_mul_of_nonneg_right hcoef (by norm_num)
      _ = _ := by ring

end Wu2008DoubleSieve.HighSix
