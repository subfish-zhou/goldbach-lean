import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundingSieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open scoped BigOperators
noncomputable section

/-- A fixed output determines m after the prime r has been retained. -/
theorem goldbachG12LinkedOutputFiber_injOn (N p : ℕ) (ε : ℝ) :
    Set.InjOn (fun x : GoldbachG12LinkedAtom => x.2)
      ((goldbachG12LinkedAtoms N ε).filter (fun x => goldbachG12LinkedOutput N x = p)) := by
  apply sigma_snd_injOn_sub_mul_fiber
  · intro x hx
    exact (mem_filter.mp (mem_sigma.mp hx).2).2.1.pos
  · intro x hx
    exact goldbachG12LinkedPrimeWindow_product_le (mem_sigma.mp hx).1 (mem_sigma.mp hx).2

theorem goldbachG12LinkedOutputFiber_card_le_twenty {N : ℕ} (hN : 2 ≤ N)
    (ε : ℝ) (p : ℕ) :
    ((goldbachG12LinkedAtoms N ε).filter (fun x => goldbachG12LinkedOutput N x = p)).card ≤ 20 := by
  classical
  let F := (goldbachG12LinkedAtoms N ε).filter (fun x => goldbachG12LinkedOutput N x = p)
  by_cases hF : F.Nonempty
  · obtain ⟨x, hx⟩ := hF
    obtain ⟨hxa, hxp⟩ := mem_filter.mp hx
    obtain ⟨hxm, hxr⟩ := mem_sigma.mp hxa
    have hm0 := (goldbachG12ActiveProductSupport_data hxm).1
    have hrp := (mem_filter.mp hxr).2.1
    have hprod0 : 0 < x.2*x.1 := Nat.mul_pos hrp.pos hm0
    have hprodN := goldbachG12LinkedPrimeWindow_product_le hxm hxr
    have hout0 := goldbachG12LinkedPrimeWindow_output_pos hxm hxr
    have hp0 : 0 < p := by
      change N-x.2*x.1 = p at hxp
      rw [hxp] at hout0
      exact hout0
    have hn0 : 1 ≤ N-p := by dsimp [goldbachG12LinkedOutput] at hxp; omega
    have hnN : N-p < N := by omega
    have hlarge := largePrimeDivisors_card_le_twenty hn0 hnN
      (by norm_num : (1 : ℝ)/21 < 4/53)
    refine (Finset.card_le_card_of_injOn (fun x : GoldbachG12LinkedAtom => x.2) ?_
      (goldbachG12LinkedOutputFiber_injOn N p ε)).trans hlarge
    intro y hy
    obtain ⟨hya, hyp⟩ := mem_filter.mp hy
    obtain ⟨hym, hyr⟩ := mem_sigma.mp hya
    have hyrp := (mem_filter.mp hyr).2.1
    have hymul := goldbachG12LinkedPrimeWindow_product_le hym hyr
    have heq : y.2*y.1 = N-p := by dsimp [goldbachG12LinkedOutput] at hyp; omega
    have hdiv : y.2 ∣ N-p := heq ▸ dvd_mul_right y.2 y.1
    have hz : (N : ℝ)^(4/53 : ℝ) ≤ (y.2 : ℝ) :=
      ((goldbachG12PiLiEndpoints_bounds hN hym).1.trans_lt (mem_filter.mp hyr).2.2.1).le
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hyrp, hdiv, by omega⟩, hz⟩
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 20
    simp only [he, card_empty]
    omega

theorem goldbachG12LinkedOutputWeight_le_twenty {N : ℕ} (hN : 2 ≤ N)
    (ε : ℝ) (p : ℕ) : goldbachG12LinkedOutputWeight N ε p ≤ 20 := by
  calc
    _ ≤ ∑ _x ∈ (goldbachG12LinkedAtoms N ε).filter (fun x => goldbachG12LinkedOutput N x = p),
        (1 : ℝ) := sum_le_sum (fun x _ => (goldbachG12NormalizedCoefficient_bounds N x.1).2)
    _ = (((goldbachG12LinkedAtoms N ε).filter (fun x => goldbachG12LinkedOutput N x = p)).card : ℝ) := by simp
    _ ≤ 20 := by exact_mod_cast goldbachG12LinkedOutputFiber_card_le_twenty hN ε p

def goldbachG12LinkedSmallOutputMass (N : ℕ) (ε Z : ℝ) : ℝ :=
  ∑ p ∈ (goldbachG12LinkedOutputSupport N ε).filter (fun p => p < Nat.ceil Z),
    goldbachG12LinkedOutputWeight N ε p

theorem goldbachG12LinkedSmallOutputMass_le {N : ℕ} (hN : 2 ≤ N) (ε Z : ℝ) :
    goldbachG12LinkedSmallOutputMass N ε Z ≤ 20*(Nat.ceil Z : ℝ) := by
  calc
    _ ≤ ∑ _p ∈ (goldbachG12LinkedOutputSupport N ε).filter (fun p => p < Nat.ceil Z),
        (20 : ℝ) := sum_le_sum (fun p _ => goldbachG12LinkedOutputWeight_le_twenty hN ε p)
    _ ≤ ∑ _p ∈ range (Nat.ceil Z), (20 : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact mem_range.mpr (mem_filter.mp hp).2
      · intro _ _ _; norm_num
    _ = 20*(Nat.ceil Z : ℝ) := by simp [mul_comm]


end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
