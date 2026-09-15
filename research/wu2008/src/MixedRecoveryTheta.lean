import MixedRecoveryDelta

namespace MixedRecovery
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

theorem singular_prime_upper {N p : ℕ} (hN : 0 < N) (hp : Nat.Prime p) (hp3 : 2 < p) :
    wuSingularSeries (p*N) ≤ 2*wuSingularSeries N := by
  have hC := (wuSingularSeries_pos N hN).le
  by_cases hd : p ∣ N
  · rw [wuSingularSeries_mul_prime_of_dvd hN hp hd]
    linarith
  · rw [wuSingularSeries_mul_prime_of_not_dvd hN hp hp3 hd]
    have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp3
    have hr : ((p:ℝ)-1)/(p-2) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hr hC]

theorem singular_pair_upper {N p q : ℕ} (hN : 0 < N)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hp3 : 2 < p) (hq3 : 2 < q) :
    wuSingularSeries (p*q*N) ≤ 4*wuSingularSeries N := by
  have h1 := singular_prime_upper (Nat.mul_pos hq.pos hN) hp hp3
  have h2 := singular_prime_upper hN hq hq3
  rw [← mul_assoc] at h1
  linarith only [h1,h2]

theorem pair_totient_lower {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (p:ℝ)*q/4 ≤ Nat.totient (p*q) := by
  have ht := Nat.totient_super_multiplicative p q
  rw [Nat.totient_prime hp,Nat.totient_prime hq] at ht
  have hpr : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hqr : (2:ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hreal : ((p:ℝ)-1)*((q:ℝ)-1) ≤ Nat.totient (p*q) := by
    have hc : ((p-1:ℕ):ℝ)*((q-1:ℕ):ℝ) ≤ Nat.totient (p*q) := by exact_mod_cast ht
    simpa only [Nat.cast_sub hp.one_lt.le,Nat.cast_sub hq.one_lt.le,Nat.cast_one] using hc
  nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-2 by linarith) (show 0 ≤ (q:ℝ)-2 by linarith)]

theorem retained_log_lower {N : ℕ} {δ : ℝ} {p : ℕ × ℕ}
    (hN : 1 < N) (hδ : 0 ≤ δ) (hp : p ∈ truncatedSixthLowerPairs N δ) :
    2*truncatedSixthLowerAlpha*log N ≤
      log ((N:ℝ)^truncatedSixthLowerC δ/(p.1*p.2:ℕ)) := by
  have hs := (truncatedSixthLower_prime_s_bounds hN hδ hp).1
  have hNR : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz : 0 < log ((N:ℝ)^truncatedSixthLowerAlpha) := by
    rw [log_rpow hNR]
    exact mul_pos truncatedSixthLower_parameters.1 (log_pos (by exact_mod_cast hN))
  change 2 ≤ _ / log ((N:ℝ)^truncatedSixthLowerAlpha) at hs
  have hh := (le_div_iff₀ hz).mp hs
  rw [log_rpow hNR] at hh
  nlinarith only [hh]

/-- Both box orientations have a genuine upper bound; negative eta can use it. -/
theorem box_theta_upper {N : ℕ} {δ Δ X Y : ℝ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hr : truncatedSixthLowerRegion δ X Y)
    (hpa : (N:ℝ)^truncatedSixthLowerAlpha ≤ (N:ℝ)^X/Δ)
    (hqb : (N:ℝ)^truncatedSixthLowerBeta ≤ (N:ℝ)^Y/Δ)
    (hlarge : (3:ℝ) ≤ (N:ℝ)^truncatedSixthLowerAlpha) :
    boxTheta N ((N:ℝ)^truncatedSixthLowerC δ)
      (convolutionWuWindows N Δ ![(N:ℝ)^X,(N:ℝ)^Y]) ≤
      4*∑ p ∈ truncatedSixthLowerBoxPairs N Δ X Y, truncatedSixthLowerClassicalTheta N δ p := by
  have hN1 : 1 < N := by omega
  have hN0 : 0 < N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hW : convolutionWuWindows N Δ ![(N:ℝ)^X,(N:ℝ)^Y] =
      ![primeWindow N ((N:ℝ)^X/Δ) ((N:ℝ)^X),primeWindow N ((N:ℝ)^Y/Δ) ((N:ℝ)^Y)] := by
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun z => Fin.elim0 z) k) j
  rw [boxTheta,hW]
  simp only [mul_div_assoc]
  rw [truncatedSixthLower_two_window_sum,mul_sum,mul_sum]
  apply sum_le_sum
  intro p hp
  have hpv := mem_primeWindow.mp (mem_product.mp hp).1
  have hqv := mem_primeWindow.mp (mem_product.mp hp).2
  have hpa3 : (3:ℝ) ≤ p.1 := hlarge.trans (hpa.trans hpv.2.2.1)
  have hq3 : (3:ℝ) ≤ p.2 := hlarge.trans
    ((rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le : (1:ℝ) ≤ N)
      truncatedSixthLower_parameters.2.1.le).trans (hqb.trans hqv.2.2.1))
  have hC := singular_pair_upper hN0 hpv.1 hqv.1 (by exact_mod_cast hpa3) (by exact_mod_cast hq3)
  have hsub := HighConsumer.retained_box_subset hN1 hr hpa hqb hp
  have hlog := retained_log_lower hN1 hδ hsub
  have hlpos : 0 < log ((N:ℝ)^truncatedSixthLowerC δ/(p.1*p.2:ℕ)) :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) truncatedSixthLower_parameters.1)
      (log_pos (by exact_mod_cast hN1))) hlog
  have htpos : (0:ℝ) < Nat.totient (p.1*p.2) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hpv.1.pos hqv.1.pos)
  have hli : 0 ≤ logarithmicIntegral N :=
    (show (0:ℝ) ≤ N/(2*log N) by positivity).trans (box_trueLi_lower hN)
  have h := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hC (mul_pos htpos hlpos).le)
    (show (0:ℝ) ≤ 4*logarithmicIntegral N by positivity)
  change 4*logarithmicIntegral N*(wuSingularSeries (p.1*p.2*N)/_) ≤ _
  convert h using 1 <;> first | rfl | (unfold truncatedSixthLowerClassicalTheta; ring)

end
end MixedRecovery
