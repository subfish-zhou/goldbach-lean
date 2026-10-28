import Goldbach.Theorem

open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem chen_existence_from_public_count : Goldbach.ChenTheorem := by
  obtain ⟨N₀, hcount⟩ := eventually_atTop.mp Goldbach.representation_lower_bound
  refine ⟨max N₀ 9, ?_⟩
  intro N hN hEven
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN9 : 9 ≤ N := le_trans (le_max_right _ _) hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmain : 0 < (0.67 : ℝ) *
      MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log N ^ (2 : ℕ) := by
    exact div_pos
      (mul_pos (mul_pos (by norm_num)
        (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N))
        (by exact_mod_cast (show 0 < N by omega)))
      (pow_pos hlog 2)
  have hcard : 0 < (chenGoodRepresentations N).card := by
    exact_mod_cast hmain.trans_le (hcount N hN₀ hEven)
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨p, N - p, hp.2.1,
    MathlibNt.ChensTheorem.semiprime_iff.mp ⟨hp.2.2.1, hp.2.2.2⟩, by omega⟩

#print axioms chen_existence_from_public_count
