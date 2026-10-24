import WR2GammaHighFourDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitRoughPurification

noncomputable section
namespace WuPaper.R2GammaHigh.Four
open Wu2008DoubleSieve FourPrimeNonunit HighBoxRecovery Finset
open scoped Classical

/-- Only residual roughness is added to the original physical labels. -/
def roughFamily (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 4) :
    LabelledPhysical.Family Gamma16Profile N :=
  (sourceFamily j N δ k).restrictLabels profileRough

/-- Purification preserves the raw-square and bad-prime exception types. -/
theorem prime_mass_split {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 4)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1/100) :
    (sourceFamily j N δ k).primeMass ≤ (roughFamily j N δ k).primeMass +
      (sourceFamily j N δ k).squareRawMass ((N:ℝ)^highEta) +
      (sourceFamily j N δ k).noncoprimePart.primeMass := by
  apply LabelledPhysical.Family.primeMass_le_restrict_add_square_add_bad
  intro x hx hc hn
  have hprof : x ∈ actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k :=
    (mem_filter.mp hx).1
  obtain ⟨_,_,_,_,_,_,hs,_⟩ := profile_data hprof
  exact masked_good_nonrough_square hs hc hn (relative_rough j k hN hd hh hx)

/-- The arbitrary-test dictionary keeps every original weight and last-prime atom. -/
theorem rough_test_dictionary (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 4)
    (test : Gamma16Profile → ℕ → ℝ) :
    (∑ x ∈ (roughFamily j N δ k).labels,
      ∑ q ∈ (roughFamily j N δ k).primes x, test x q) =
    ∑ x ∈ (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) k).filter profileRough,
      ∑ q ∈ actualRawFibre N δ (Wu04RemainingCore.row j) k x, test x q := by
  have h := actualFamily_test_dictionary (N := N) (δ := δ) (Wu04RemainingCore.row j) (windows j N) k
    (fun _ hm => boxConvolutionSupport_pos (fun _ _ hp => (mem_primeWindow.mp hp).1.pos) hm)
    (fun x q => if profileRough x then test x q else 0)
  simpa only [roughFamily, sourceFamily, LabelledPhysical.Family.restrictLabels,
    LabelledPhysical.Family.primes, sum_filter, sum_ite_irrel, sum_const_zero] using h

end WuPaper.R2GammaHigh.Four
#print axioms WuPaper.R2GammaHigh.Four.prime_mass_split
#print axioms WuPaper.R2GammaHigh.Four.rough_test_dictionary
