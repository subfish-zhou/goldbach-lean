import MathlibNt.Wu2008DoubleSieve.NinthMainMassPNT

/-!
# The sharp actual ninth main-mass estimate

The literal J9 bounds actual X9 with arbitrarily small additive slack in
its leading constant. No evenness, replacement mass, or assumed analytic
bound is used.
-/

namespace Wu2008DoubleSieve

open Real Filter
open scoped Topology

theorem X9_le_J9_add_epsilon {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      X9 N ≤ (J9 + ε) * N / log N := by
  let η := min 1 (ε / (J9 + 2))
  have hJ : 0 ≤ J9 := J9_nonneg
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by linarith))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηE : η * (J9 + 2) ≤ ε :=
    (le_div_iff₀ (by linarith : 0 < J9 + 2)).mp (min_le_right _ _)
  have hconstant : (1 + η) * (J9 + η) ≤ J9 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le]
  have hevent : ∀ᶠ N : ℕ in atTop, 512 ≤ N ∧
      X9 N ≤ (J9 + ε) * N / log N := by
    filter_upwards [X9_sharp_pair_bound hη, ninthMainPairSum_eventually_le hη,
      eventually_ge_atTop (512 : ℕ)] with N hpnt hquad hN
    have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    refine ⟨hN, ?_⟩
    calc
      X9 N ≤ (1 + η) * ((N : ℝ) / log N) * ninthMainPairSum N := hpnt
      _ ≤ (1 + η) * ((N : ℝ) / log N) * (J9 + η) :=
        mul_le_mul_of_nonneg_left hquad (by positivity)
      _ = ((1 + η) * (J9 + η)) * ((N : ℝ) / log N) := by ring
      _ ≤ (J9 + ε) * ((N : ℝ) / log N) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = _ := by ring
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  exact ⟨max T 512, le_max_right _ _, fun N hN => (hT N ((le_max_left _ _).trans hN)).2⟩

end Wu2008DoubleSieve
