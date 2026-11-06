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




end Wu2008DoubleSieve.SecondFunctionalJointTail
