import MathlibNt.Wu2008DoubleSieve.SeventhEighthPairQuadrature

namespace Wu2008DoubleSieve.SeventhEighth
open Real Filter
open scoped Topology

/-- Consumes both the proved PNT prefix and the proved literal pair quadrature.
The slack absorbs each fixed nonnegative Ji without any numerical estimate. -/
theorem seventh_eighth_classicalMass_le_J_add_epsilon {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      classicalMass N (seventhPairs N) ≤ (J7 + ε) * N / log N ∧
      classicalMass N (eighthPairs N) ≤ (J8 + ε) * N / log N := by
  let η := min 1 (ε / (J7 + J8 + 2))
  have hJ7 := J7_nonneg
  have hJ8 := J8_nonneg
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by linarith))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηE : η * (J7 + J8 + 2) ≤ ε :=
    (le_div_iff₀ (by linarith : 0 < J7 + J8 + 2)).mp (min_le_right _ _)
  have hc7 : (1 + η) * (J7 + η) ≤ J7 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le, mul_nonneg hη.le hJ8]
  have hc8 : (1 + η) * (J8 + η) ≤ J8 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le, mul_nonneg hη.le hJ7]
  obtain ⟨Tp, hTp512, hTp⟩ := seventh_eighth_mass_sharp_pair_bound hη
  obtain ⟨Tq, _, hTq⟩ := seventh_eighth_pairSum_le_J_add_epsilon hη
  refine ⟨max Tp Tq, hTp512.trans (le_max_left _ _), ?_⟩
  intro N hN
  have hNp := (le_max_left _ _).trans hN
  have hNq := (le_max_right _ _).trans hN
  have h512 := hTp512.trans hNp
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨hp7, hp8⟩ := hTp N hNp
  obtain ⟨hq7, hq8⟩ := hTq N hNq
  have htransfer (X P J : ℝ)
      (hp : X ≤ (1 + η) * ((N : ℝ) / log N) * P)
      (hq : P ≤ J + η) (hc : (1 + η) * (J + η) ≤ J + ε) :
      X ≤ (J + ε) * N / log N := by
    calc
      X ≤ (1 + η) * ((N : ℝ) / log N) * P := hp
      _ ≤ (1 + η) * ((N : ℝ) / log N) * (J + η) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = ((1 + η) * (J + η)) * ((N : ℝ) / log N) := by ring
      _ ≤ (J + ε) * ((N : ℝ) / log N) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  exact ⟨htransfer _ _ _ hp7 hq7 hc7, htransfer _ _ _ hp8 hq8 hc8⟩

/-- A single threshold simultaneously serves all four original endpoints. -/
theorem seventh_eighth_classical_sharp_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      classicalPairSum N (seventhPairs N) ≤ J7 + ε ∧
      classicalPairSum N (eighthPairs N) ≤ J8 + ε ∧
      classicalMass N (seventhPairs N) ≤ (J7 + ε) * N / log N ∧
      classicalMass N (eighthPairs N) ≤ (J8 + ε) * N / log N := by
  obtain ⟨Tp, hTp512, hTp⟩ := seventh_eighth_pairSum_le_J_add_epsilon hε
  obtain ⟨Tm, _, hTm⟩ := seventh_eighth_classicalMass_le_J_add_epsilon hε
  refine ⟨max Tp Tm, hTp512.trans (le_max_left _ _), ?_⟩
  intro N hN
  obtain ⟨hp7, hp8⟩ := hTp N ((le_max_left _ _).trans hN)
  obtain ⟨hm7, hm8⟩ := hTm N ((le_max_right _ _).trans hN)
  exact ⟨hp7, hp8, hm7, hm8⟩

end Wu2008DoubleSieve.SeventhEighth
