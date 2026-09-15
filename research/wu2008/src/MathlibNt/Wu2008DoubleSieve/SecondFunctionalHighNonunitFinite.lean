import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitCore
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunit

namespace Wu2008DoubleSieve.HighNonunit
open Finset
open scoped Classical
open HighUnitSource (word20 word21)

/-- The two literal words, with no coordinate compression. -/
def word (high : Bool) : List ℕ := if high then word21 else word20

theorem word_length (high : Bool) : 2 ≤ (word high).length := by
  cases high <;> decide

theorem word_last (high : Bool) :
    (word high).getD ((word high).length-1) 0 = 3 := by
  cases high <;> rfl

/-- Genuine geometry and injectivity for all five prime labels of Gamma20. -/
theorem geometry20 {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) :
    (FourPrimeNonunit.labels N W a b c e f word20).image (encode N) ⊆
      (profiles N W a b c e f word20).sigma (fibre N e f) ∧
    Set.InjOn (encode N) (FourPrimeNonunit.labels N W a b c e f word20) :=
  ⟨inclusion hdpos hN he (by decide) rfl, encode_injOn (by decide)⟩

/-- Genuine geometry and injectivity for all six prime labels of Gamma21. -/
theorem geometry21 {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) :
    (FourPrimeNonunit.labels N W a b c e f word21).image (encode N) ⊆
      (profiles N W a b c e f word21).sigma (fibre N e f) ∧
    Set.InjOn (encode N) (FourPrimeNonunit.labels N W a b c e f word21) :=
  ⟨inclusion hdpos hN he (by decide) rfl, encode_injOn (by decide)⟩

/-- Each original label receives exactly the original sigma coefficient. -/
theorem sigma_labels_le {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) (hcs : 2 ≤ cs.length)
    (hlast : cs.getD (cs.length-1) 0 = 3)
    (σ : ℕ → ℝ) (hσ : ∀ d, 0 ≤ σ d) :
    (∑ x ∈ FourPrimeNonunit.labels N W a b c e f cs, σ x.1) ≤
      ∑ x ∈ profiles N W a b c e f cs, σ x.1 * (fibre N e f x).card := by
  calc
    _ = ∑ y ∈ (FourPrimeNonunit.labels N W a b c e f cs).image (encode N), σ y.1.1 := by
      rw [sum_image (encode_injOn hcs)]
      rfl
    _ ≤ ∑ y ∈ (profiles N W a b c e f cs).sigma (fibre N e f), σ y.1.1 :=
      sum_le_sum_of_subset_of_nonneg (inclusion hdpos hN he hcs hlast)
        (fun y _ _ => hσ y.1.1)
    _ = _ := by
      simp only [sum_sigma, sum_const, nsmul_eq_mul]
      apply sum_congr rfl
      intro x _
      ring

noncomputable def envelope {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : ℝ :=
  ∑ x ∈ profiles N W a b c e f cs,
    (convolutionCoeff W x.1 : ℝ) * (fibre N e f x).card

theorem source_le_envelope {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) (hcs : 2 ≤ cs.length)
    (hlast : cs.getD (cs.length-1) 0 = 3) :
    FourPrimeNonunit.source N W a b c e f cs ≤ envelope N W a b c e f cs := by
  rw [FourPrimeNonunit.source_labels]
  exact sigma_labels_le hdpos hN he hcs hlast _ (fun _ => Nat.cast_nonneg _)

theorem source_le20 {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) :
    FourPrimeNonunit.source N W a b c e f word20 ≤ envelope N W a b c e f word20 :=
  source_le_envelope hdpos hN he (by decide) rfl

theorem source_le21 {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hN : 4 ≤ N) (he : Even N) :
    FourPrimeNonunit.source N W a b c e f word21 ≤ envelope N W a b c e f word21 :=
  source_le_envelope hdpos hN he (by decide) rfl

/-- All five cutoffs are literally the mother cutoffs, and the window still has M=N. -/
noncomputable def actualProfiles {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) : Finset Profile :=
  profiles N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word high)

noncomputable def actualFibre (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters) :
    Profile → Finset ℕ :=
  fibre N (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s)

noncomputable def actualSource {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) : ℝ :=
  FourPrimeNonunit.source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word high)

noncomputable def actualUnit {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) : ℝ :=
  FourPrimeUnit.source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word high)

noncomputable def actualEnvelope {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) : ℝ :=
  ∑ x ∈ actualProfiles N δ p W high,
    (convolutionCoeff W x.1 : ℝ) * (actualFibre N δ p x).card

/-- The new nonunit quantity is exactly the original Gamma summand minus its unit part. -/
theorem actual_partition {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) :
    actualUnit N δ p W high + actualSource N δ p W high =
      secondFunctionalMotherGammaSum p N δ W (if high then 21 else 20) := by
  unfold actualUnit actualSource FourPrimeUnit.source FourPrimeNonunit.source
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← mul_add]
  cases high
  · exact congrArg ((convolutionCoeff W d : ℝ) * ·) (HighUnitSource.partition20 _ _ _ _ _ _ _)
  · exact congrArg ((convolutionCoeff W d : ℝ) * ·) (HighUnitSource.partition21 _ _ _ _ _ _ _)

/-- The literal five-cutoff labels retain the original sigma, with no new screening. -/
theorem actual_source_labels {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) :
    actualSource N δ p W high =
      ∑ x ∈ FourPrimeNonunit.labels N W (fun d => wuLocalCutoff N δ d p.S)
        (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
        (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s)
        (word high), (convolutionCoeff W x.1 : ℝ) :=
  FourPrimeNonunit.source_labels _ _ _ _ _ _ _ _

/-- Finite mother-admissible consumer; source-box positivity is discharged internally.
The inequalities on the mother parameters are not needed by the stronger finite transport. -/
theorem mother_source_le (p : SecondFunctionalParameters) (_hp : p.MotherAdmissible)
    (_hs : 2 ≤ p.s) {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (high : Bool) :
    actualSource N δ p (convolutionWuWindows N Δ V) high ≤
      actualEnvelope N δ p (convolutionWuWindows N Δ V) high :=
  source_le_envelope
    (fun _ hd => (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1)
    hN he (word_length high) (word_last high)

/-- Actual mother Gamma20/21 consumer: only the nonunit part is enlarged.
No analytic switched-kernel estimate or full-Gamma payment is asserted. -/
theorem mother_gamma_le (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (high : Bool) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V)
        (if high then 21 else 20) ≤
      actualUnit N δ p (convolutionWuWindows N Δ V) high +
        actualEnvelope N δ p (convolutionWuWindows N Δ V) high := by
  rw [← actual_partition]
  exact add_le_add le_rfl (mother_source_le p hp hs hN he hδ hδhi hb high)

/-- The same source-box consumer for arbitrary nonnegative sigma, unchanged on each label. -/
theorem mother_sigma_labels_le (p : SecondFunctionalParameters) (_hp : p.MotherAdmissible)
    (_hs : 2 ≤ p.s) {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (high : Bool) (σ : ℕ → ℝ) (hσ : ∀ d, 0 ≤ σ d) :
    (∑ x ∈ FourPrimeNonunit.labels N (convolutionWuWindows N Δ V)
      (fun d => wuLocalCutoff N δ d p.S) (fun d => wuLocalCutoff N δ d p.kappa1)
      (fun d => wuLocalCutoff N δ d p.kappa2) (fun d => wuLocalCutoff N δ d p.kappa3)
      (fun d => wuLocalCutoff N δ d p.s) (word high), σ x.1) ≤
    ∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high,
      σ x.1 * (actualFibre N δ p x).card :=
  sigma_labels_le
    (fun _ hd => (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1)
    hN he (word_length high) (word_last high) σ hσ

end Wu2008DoubleSieve.HighNonunit
