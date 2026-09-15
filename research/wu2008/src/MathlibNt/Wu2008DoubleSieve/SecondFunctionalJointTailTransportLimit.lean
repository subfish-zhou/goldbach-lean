import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailTransport

/-! The actual joint limit and the compact-head/tail sandwich. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set MeasureTheory Filter SecondFunctionalCoupled
open scoped BigOperators Topology

/-- No pointwise or integral convergence premise is passed to the final producer. -/
theorem kernel_tendsto (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : Tendsto (kernel p) atTop (𝓝 (buchstabTailLimit * M p)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hM := M_nonneg p hp hs
  have hpos : 0 < M p + 1 := by linarith
  obtain ⟨m, hm, hsmall⟩ := exists_factorial_tail_threshold (div_pos hε hpos)
  refine ⟨((m : ℝ) + 6) / 2, ?_⟩
  intro phi hphi
  rw [Real.dist_eq]
  apply (kernel_tail_error p hp hs m hm hphi).trans_lt
  have hsmall' := (lt_div_iff₀ hpos).1 hsmall
  have hbudget : 0 ≤ 4 / (m.factorial : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hsmall' hbudget ⊢
  nlinarith only [hsmall', hbudget]

/-- The actual limiting value belongs to the closure of the admissible kernel values. -/
theorem limit_le_jointSup (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : buchstabTailLimit * M p ≤ jointSup p := by
  apply le_of_tendsto (kernel_tendsto p hp hs)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with phi hphi
  exact kernel_le_jointSup p hp hs hphi

/-- A full real compact interval and the same-phi tail cover all admissible values. -/
theorem jointSup_le_compact_tail (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m) {P : ℝ}
    (hcut : ((m : ℝ) + 6) / 2 ≤ P) :
    jointSup p ≤ max (compactSup p P)
      (buchstabTailLimit * M p + 4 * M p / (m.factorial : ℝ)) := by
  apply csSup_le (values_nonempty p)
  rintro _ ⟨phi, hphi, rfl⟩
  by_cases hhead : phi ≤ P
  · exact (kernel_le_compactSup p hp hs ⟨hphi, hhead⟩).trans (le_max_left _ _)
  · have htail := (abs_le.mp (kernel_tail_error p hp hs m hm
      (hcut.trans (le_of_not_ge hhead)))).2
    exact (show kernel p phi ≤ buchstabTailLimit * M p +
      4 * M p / (m.factorial : ℝ) by linarith only [htail]).trans (le_max_right _ _)

/-- Both sides refer to the actual unbounded joint supremum; no tail certificate is assumed. -/
theorem compact_tail_sandwich (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m) {P : ℝ}
    (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P) :
    max (compactSup p P) (buchstabTailLimit * M p) ≤ jointSup p ∧
      jointSup p ≤ max (compactSup p P)
        (buchstabTailLimit * M p + 4 * M p / (m.factorial : ℝ)) := by
  obtain ⟨h2, hcut⟩ := max_le_iff.mp hP
  exact ⟨max_le (compactSup_le_jointSup p hp hs h2) (limit_le_jointSup p hp hs),
    jointSup_le_compact_tail p hp hs m hm hcut⟩

end Wu2008DoubleSieve.SecondFunctionalJointTail
