import Wu08FourNormalizationOriginal
import U8TwoLogDenominator
import U8OptimalPrefix

noncomputable section
open Finset Real Filter
open scoped Classical
open U8Literal.SmallProduct U8Literal.SmallProduct.TwoDimensional
namespace Wu08FirstPrimeFour.Prefix

/-- The original N is unchanged; only the product interval is shortened. -/
def siftedProducts (N : ℕ) (ξ Z : ℝ) : Finset ℕ :=
  (interval N ξ (1,1)).filter fun m =>
    (twoLinear N (1,1) m).Coprime ((sievePrimes Z).prod id)

theorem unit_rootCount (N : ℕ) {m : ℕ} (hm : Squarefree m) :
    residueRootCount m N 1 = nuN N m := by
  rw [residueRootCount_squarefree hm, nuN]
  apply prod_congr rfl
  intro p hp
  have hpP := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpP⟩
  have ha : ¬p ∣ 1 := hpP.not_dvd_one
  rw [residueRootCount_prime]
  by_cases hN : p ∣ N
  · rw [if_pos hN, localRoots_card_one_of_dvd_N ha hN]
  · rw [if_neg hN, localRoots_card_two ha hN]

theorem unit_quadratic_optimal (N : ℕ) (hN : Even N) (ξ Z R : ℝ)
    (hR : 1 ≤ R) :
    quadratic N ξ (1,1) (carrier Z R) (optimalWeight N hN Z R) =
      ((interval N ξ (1,1)).card : ℝ) / denominator N Z R +
        quadraticRemainder N ξ (1,1) (carrier Z R) (optimalWeight N hN Z R) := by
  rw [quadratic_eq_main_add_remainder]
  have hm : (∑ d ∈ carrier Z R, ∑ f ∈ carrier Z R,
      optimalWeight N hN Z R d * optimalWeight N hN Z R f *
        (residueRootCount (Nat.lcm d f) N (1*1) : ℝ) /
          Nat.lcm d f) = mainMatrix N Z R (optimalWeight N hN Z R) := by
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro f hf
    rw [show (1*1) = 1 by norm_num,
      unit_rootCount N (sieve_lcm_squarefree (carrier_dvd hd) (carrier_dvd hf)),
      nuN_cast_eq_rootCount]
  rw [hm, mainMatrix_optimal N hN Z hR]
  ring

theorem unit_interval_card (N : ℕ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ((interval N ξ (1,1)).card : ℝ) ≤ ξ*N := by
  have hs : interval N ξ (1,1) ⊆ Icc 1 ⌊ξ*N⌋₊ := by
    intro m hm
    obtain ⟨_,hlo,_,hhi⟩ := mem_filter.mp hm
    exact mem_Icc.mpr ⟨hlo,Nat.le_floor (by simpa using hhi)⟩
  have hc : (interval N ξ (1,1)).card ≤ ⌊ξ*N⌋₊ := by
    simpa using card_le_card hs
  exact (show ((interval N ξ (1,1)).card : ℝ) ≤ ⌊ξ*N⌋₊ by exact_mod_cast hc).trans
    (Nat.floor_le (mul_nonneg hξ (Nat.cast_nonneg N)))

/-- Genuine dimension-two upper bound for a rough product and its prime output.
It has no original-pair hypothesis: the linear coefficient is literally one. -/
theorem siftedProducts_upper (N : ℕ) (hN : Even N) {ξ Z R : ℝ}
    (hξ : 0 ≤ ξ) (hR : 1 ≤ R) :
    ((siftedProducts N ξ Z).card : ℝ) ≤
      ξ*N / denominator N Z R + 2*(R+1)^2*R^4 := by
  have hden : 0 < denominator N Z R := by
    rw [← denominator_eq N hN]
    exact TruncatedSelberg.G_pos _ hR
  have hs : ((siftedProducts N ξ Z).card : ℝ) ≤
      quadratic N ξ (1,1) (carrier Z R) (optimalWeight N hN Z R) := by
    rw [← square_eq_quadratic]
    calc
      _ = ∑ _m ∈ siftedProducts N ξ Z, (1 : ℝ) := by simp
      _ = ∑ m ∈ siftedProducts N ξ Z,
          (divisorSum (carrier Z R) (optimalWeight N hN Z R) (twoLinear N (1,1) m))^2 := by
        apply sum_congr rfl
        intro m hm
        rw [divisorSum_eq_one (carrier_one hR) (fun _ hd => carrier_dvd hd)
          (optimalWeight_one N hN Z hR) (mem_filter.mp hm).2,one_pow]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  rw [unit_quadratic_optimal N hN ξ Z R hR] at hs
  exact hs.trans (add_le_add (div_le_div_of_nonneg_right (unit_interval_card N hξ) hden.le)
    ((le_abs_self _).trans (optimal_remainder_bound N hN ξ Z R (1,1) hR)))

#print axioms siftedProducts_upper
end Wu08FirstPrimeFour.Prefix
