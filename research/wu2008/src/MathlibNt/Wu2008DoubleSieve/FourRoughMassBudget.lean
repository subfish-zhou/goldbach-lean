import MathlibNt.Wu2008DoubleSieve.FourRoughUniformUpper
import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalQuadrature

namespace Wu2008DoubleSieve.FourRoughClosedMass
open Finset Set Real LiLiuPrereqBuchstab TruncatedFourPhysical
open scoped Classical
noncomputable section

def window (N : ℕ) : Finset ℕ := primesIcc ((N : ℝ)^(1/15 : ℝ)) ((N : ℝ)^(1/3 : ℝ))
def box (N : ℕ) : Finset Quad := window N ×ˢ window N ×ˢ window N ×ˢ window N
def windowMass (N : ℕ) : ℝ := ∑ p ∈ window N, 1/(p : ℝ)

theorem mem_window_of_coord {N p : ℕ} (hN : 1 < N) (hp : p.Prime)
    (ht : coord N p ∈ Icc (1/15 : ℝ) (1/3)) : p ∈ window N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  apply (mem_primesIcc (rpow_nonneg hN0.le _)).mpr
  refine ⟨hp, ?_, ?_⟩
  · apply (log_le_log_iff (rpow_pos_of_pos hN0 _) hp0).mp
    rw [log_rpow hN0]
    exact (le_div_iff₀ hlog).mp ht.1
  · apply (log_le_log_iff hp0 (rpow_pos_of_pos hN0 _)).mp
    rw [log_rpow hN0]
    exact (div_le_iff₀ hlog).mp ht.2

theorem actual_subset_box {N : ℕ} (hN : 1 < N) : labels10 N ∪ labels11 N ⊆ box N := by
  rintro ⟨a,b,c,d⟩ hq
  obtain ⟨ha,hb,hc,hd,_⟩ := actual_primes_lower hq
  obtain ⟨hca,hcb,hcc,hcd⟩ := actual_low_window hN hq
  exact mem_product.mpr ⟨mem_window_of_coord hN ha hca,
    mem_product.mpr ⟨mem_window_of_coord hN hb hcb,
    mem_product.mpr ⟨mem_window_of_coord hN hc hcc, mem_window_of_coord hN hd hcd⟩⟩⟩

theorem box_reciprocal (N : ℕ) : reciprocalMass (box N) = windowMass N ^ 4 := by
  simp only [reciprocalMass, box, sum_product, fourModulusProduct, Nat.cast_mul,
    one_div, mul_inv_rev]
  simp only [← sum_mul, ← mul_sum, windowMass, one_div]
  ring

theorem window_integral_bound : |∫ t in (1/15 : ℝ)..(1/3), (1 : ℝ)/t| ≤ 4 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := (15 : ℝ))
    (a := (1/15 : ℝ)) (b := (1/3 : ℝ)) (f := fun t : ℝ => 1/t) (by
      intro t ht
      rw [uIoc_of_le (by norm_num)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ht0)]
      apply (div_le_iff₀ ht0).mpr
      linarith [ht.1])
  simpa only [Real.norm_eq_abs, show (15 : ℝ)*|1/3-1/15| = 4 by norm_num] using h

theorem windowMass_uniform : ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → windowMass N ≤ 5 := by
  obtain ⟨T,hT,hbound⟩ := SeventhEighth.classical_low_weighted_uniform 1 0 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨T,hT,?_⟩
  intro N hN
  have he := hbound N hN (fun _ => 1) (1/15) (1/3)
    continuousOn_const (by intros; norm_num) (by intros; simp)
    (by norm_num) (by norm_num) (by norm_num)
  change |windowMass N - ∫ t in (1/15 : ℝ)..(1/3), (1 : ℝ)/t| < 1 at he
  have hi := window_integral_bound
  have h1 := le_abs_self (windowMass N - ∫ t in (1/15 : ℝ)..(1/3), (1 : ℝ)/t)
  have h2 := le_abs_self (∫ t in (1/15 : ℝ)..(1/3), (1 : ℝ)/t)
  linarith

/-- Entire fourfold reciprocal masses, including diagonal and closed atoms. -/
theorem actual_reciprocal_uniform :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    reciprocalMass (labels10 N) ≤ 625 ∧ reciprocalMass (labels11 N) ≤ 625 := by
  obtain ⟨T,hT,hbound⟩ := windowMass_uniform
  refine ⟨T,hT,?_⟩
  intro N hN
  have hN1 : 1 < N := by omega
  have hs (S : Finset Quad) (hS : S ⊆ labels10 N ∪ labels11 N) : reciprocalMass S ≤ 625 := by
    calc
      _ ≤ reciprocalMass (box N) := sum_le_sum_of_subset_of_nonneg
        (hS.trans (actual_subset_box hN1)) (by intros; positivity)
      _ = windowMass N ^ 4 := box_reciprocal N
      _ ≤ (5 : ℝ)^4 := pow_le_pow_left₀ (sum_nonneg (by intros; positivity)) (hbound N hN) 4
      _ = 625 := by norm_num
  exact ⟨hs _ subset_union_left, hs _ subset_union_right⟩

/-- Epsilon alone before one common threshold; the still-discrete Buchstab main mass remains. -/
theorem rawMass_main_epsilon {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    rawMass10 N ≤ (mainMass N (labels10 N)+epsilon)*((N : ℝ)/log N) ∧
    rawMass11 N ≤ (mainMass N (labels11 N)+epsilon)*((N : ℝ)/log N) := by
  let tau := epsilon*alpha/625
  have htau : 0 < tau := div_pos (mul_pos he fixed_geometry.2.1) (by norm_num)
  obtain ⟨T1,hT1,hupper⟩ := actual_main_upper htau
  obtain ⟨T2,hT2,hmass⟩ := actual_reciprocal_uniform
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN
  have h1 := hupper N ((le_max_left _ _).trans hN)
  have h2 := hmass N ((le_max_right _ _).trans hN)
  have hN1 : 1 < N := by have := (le_max_left T1 T2).trans hN; omega
  have hscale : 0 ≤ (N : ℝ)/log N := div_nonneg (Nat.cast_nonneg N)
    (log_pos (by exact_mod_cast hN1)).le
  have hpay (m : ℝ) (hm : m ≤ 625) : tau/alpha*m ≤ epsilon := by
    calc
      _ ≤ tau/alpha*625 := mul_le_mul_of_nonneg_left hm (div_nonneg htau.le fixed_geometry.2.1.le)
      _ = epsilon := by dsimp [tau]; field_simp [fixed_geometry.2.1.ne']
  constructor
  · apply h1.1.trans
    nlinarith [mul_nonneg hscale (sub_nonneg.mpr (hpay _ h2.1))]
  · apply h1.2.trans
    nlinarith [mul_nonneg hscale (sub_nonneg.mpr (hpay _ h2.2))]

end
end Wu2008DoubleSieve.FourRoughClosedMass
