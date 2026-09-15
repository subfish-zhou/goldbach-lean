import MathlibNt.Wu2008DoubleSieve.SecondFunctionalKernelContinuity

/-! Actual compact-interval maxima. No statement identifies the unbounded
joint supremum with a compact supremum without a separate tail certificate. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set SecondFunctionalCoupled

/-- Values on the entire real compact interval, not on a sample set. -/
def compactValues (p : SecondFunctionalParameters) (P : ℝ) : Set ℝ :=
  kernel p '' Icc 2 P

noncomputable def compactSup (p : SecondFunctionalParameters) (P : ℝ) : ℝ :=
  sSup (compactValues p P)

theorem compactValues_nonempty (p : SecondFunctionalParameters) {P : ℝ} (hP : 2 ≤ P) :
    (compactValues p P).Nonempty := ⟨kernel p 2, 2, ⟨le_rfl, hP⟩, rfl⟩

theorem compactValues_subset_values (p : SecondFunctionalParameters) (P : ℝ) :
    compactValues p P ⊆ values p := by
  rintro _ ⟨phi, hphi, rfl⟩
  exact ⟨phi, hphi.1, rfl⟩

theorem compactValues_bddAbove (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (P : ℝ) : BddAbove (compactValues p P) :=
  (values_bddAbove p hp hs).mono (compactValues_subset_values p P)

/-- The value set is genuinely compact by the internally proved continuity. -/
theorem compactValues_isCompact (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (P : ℝ) : IsCompact (compactValues p P) :=
  isCompact_Icc.image (kernel_continuous p hp hs)

theorem kernel_le_compactSup (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {P phi : ℝ} (hphi : phi ∈ Icc 2 P) :
    kernel p phi ≤ compactSup p P :=
  le_csSup (compactValues_bddAbove p hp hs P) ⟨phi, hphi, rfl⟩

/-- Weierstrass supplies a point in the original real interval. -/
theorem compact_exists_argmax (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {P : ℝ} (hP : 2 ≤ P) :
    ∃ phi ∈ Icc 2 P, kernel p phi = compactSup p P := by
  obtain ⟨phi, hphi, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hP)
    (kernel_continuous p hp hs).continuousOn
  refine ⟨phi, hphi, le_antisymm (kernel_le_compactSup p hp hs hphi) ?_⟩
  apply csSup_le (compactValues_nonempty p hP)
  rintro _ ⟨x, hx, rfl⟩
  exact hmax hx

/-- A selected actual maximizer; no uniqueness is claimed. -/
noncomputable def compactArgmax (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (P : ℝ) (hP : 2 ≤ P) : ℝ :=
  (compact_exists_argmax p hp hs hP).choose

theorem compactArgmax_spec (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (P : ℝ) (hP : 2 ≤ P) :
    compactArgmax p hp hs P hP ∈ Icc 2 P ∧
      kernel p (compactArgmax p hp hs P hP) = compactSup p P :=
  (compact_exists_argmax p hp hs hP).choose_spec

theorem compactSup_le_jointSup (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {P : ℝ} (hP : 2 ≤ P) : compactSup p P ≤ jointSup p := by
  apply csSup_le (compactValues_nonempty p hP)
  rintro _ ⟨phi, hphi, rfl⟩
  exact kernel_le_jointSup p hp hs hphi.1

theorem compactSup_mono (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {P Q : ℝ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    compactSup p P ≤ compactSup p Q := by
  apply csSup_le (compactValues_nonempty p hP)
  rintro _ ⟨phi, hphi, rfl⟩
  exact kernel_le_compactSup p hp hs ⟨hphi.1, hphi.2.trans hPQ⟩

theorem compactSup_monotoneOn (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : MonotoneOn (compactSup p) (Ici 2) := by
  intro P hP Q _ hPQ
  exact compactSup_mono p hp hs hP hPQ

theorem compactSup_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {P : ℝ} (hP : 2 ≤ P) :
    0 ≤ compactSup p P ∧ compactSup p P ≤ existenceCap :=
  ⟨(kernel_bounds p hp hs 2).1.trans (kernel_le_compactSup p hp hs ⟨le_rfl, hP⟩),
    (compactSup_le_jointSup p hp hs hP).trans (jointSup_bounds p hp hs).2⟩

/-- Degenerate intervals retain the original endpoint value. -/
theorem compactSup_two (p : SecondFunctionalParameters) : compactSup p 2 = kernel p 2 := by
  simp [compactSup, compactValues]

end Wu2008DoubleSieve.SecondFunctionalJointTail
