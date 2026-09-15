import MathlibNt.Wu2008DoubleSieve.FourRoughOriginalIdentification

/-! The literal four-labelled nonunit rough masses satisfy the classical
fourfold integral bounds. No quadrature or mass estimate is a premise. -/
namespace Wu2008DoubleSieve.FourRoughClosedMass
open Real
noncomputable section

theorem mainMass_integral_uniform {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |mainMass N (labels10 N) - I10| < epsilon ∧
      |mainMass N (labels11 N) - I11| < epsilon := by
  obtain ⟨T,hT,hq⟩ := Q0_uniform he
  refine ⟨T,hT,?_⟩
  intro N hN
  have hN1 : 1 < N := by omega
  have h10 := hq N hN false
  have h11 := hq N hN true
  rw [← mainMass_eq_Q0 hN1 false, J0_eq_I10] at h10
  rw [← mainMass_eq_Q0 hN1 true, J0_eq_I11] at h11
  simpa only [labelSet_eq, Bool.false_eq_true, ↓reduceIte] using And.intro h10 h11

/-- One threshold for both original closed four-prime-labelled rough masses.
The residual integer is not required to be prime. -/
theorem rawMass_integral_sharp_bounds {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      rawMass10 N ≤ (I10 + epsilon) * ((N : ℝ) / log (N : ℝ)) ∧
      rawMass11 N ≤ (I11 + epsilon) * ((N : ℝ) / log (N : ℝ)) := by
  have hh : 0 < epsilon / 2 := by positivity
  obtain ⟨T1,hT1,hmain⟩ := mainMass_integral_uniform hh
  obtain ⟨T2,hT2,hraw⟩ := rawMass_main_epsilon hh
  refine ⟨max T1 T2, by omega, ?_⟩
  intro N hN
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 ≤ (N : ℝ) / log (N : ℝ) := by positivity
  obtain ⟨hm10,hm11⟩ := hmain N (by omega)
  obtain ⟨hr10,hr11⟩ := hraw N (by omega)
  have hp10 : mainMass N (labels10 N) + epsilon / 2 ≤ I10 + epsilon := by
    have h := (abs_lt.mp hm10).2
    linarith only [h]
  have hp11 : mainMass N (labels11 N) + epsilon / 2 ≤ I11 + epsilon := by
    have h := (abs_lt.mp hm11).2
    linarith only [h]
  exact ⟨hr10.trans (mul_le_mul_of_nonneg_right hp10 hscale),
    hr11.trans (mul_le_mul_of_nonneg_right hp11 hscale)⟩

end
end Wu2008DoubleSieve.FourRoughClosedMass
