import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitPrimeOutput
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceIntegral

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitPrimeOutput
open Finset HighUnitSource SecondFunctionalUnitPrimeFibre

/-- Complete source-list injection with concrete word geometry supplied internally. -/
theorem injection20 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a2) (hb : b ≤ 1/2) :
    ∃ E : (atoms N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word20) ↪
        ((HighUnit.primePrefix20 R a2 a3 b).sigma
          (fun g => filteredPhysical N d g (Fin.last 3) (R^b))),
      ∀ x, fullList (E x).val = x.val.1 :=
  injection_filtered _ _ (geometry20 hd hR hlow hb)

theorem prefix_le20 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a2) (hb : b ≤ 1/2) :
    FourPrimeUnit.prefixTerm true N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word20 ≤
      ∑ g ∈ HighUnit.primePrefix20 R a2 a3 b,
        ((filteredPhysical N d g (Fin.last 3) (R^b)).card : ℝ) :=
  count_filtered _ _ (geometry20 hd hR hlow hb)

noncomputable def envelope20 {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (R a2 a3 b : ℕ → ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ g ∈ HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d),
      ((filteredPhysical N d g (Fin.last 3) (R d^b d)).card : ℝ)

/-- Original sigma is unchanged; the new test is obtained from actual source membership. -/
theorem source_le20 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a2 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    FourPrimeUnit.source N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word20 ≤
      envelope20 N W R a2 a3 b := by
  unfold FourPrimeUnit.source envelope20
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (prefix_le20 (hdpos d hd) (hR d hd)
    (hlow d hd) (hb d hd)) (Nat.cast_nonneg _)

theorem labels_le20 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a2 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    (∑ x ∈ FourPrimeUnit.labels N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word20,
        (convolutionCoeff W x.1 : ℝ)) ≤ envelope20 N W R a2 a3 b := by
  rw [← FourPrimeUnit.source_labels]
  exact source_le20 hdpos hR hlow hb

/-- Same-weight consistency with the accepted unfiltered physical majorant. -/
theorem envelope20_le_old {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (R a2 a3 b : ℕ → ℝ) :
    envelope20 N W R a2 a3 b ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 3)).val (R d^b d)).card : ℝ) := by
  apply sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (filtered_sum_le_old _ _) (Nat.cast_nonneg _)

/-- Complete source-list injection with concrete word geometry supplied internally. -/
theorem injection21 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a3) (hb : b ≤ 1/2) :
    ∃ E : (atoms N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word21) ↪
        ((HighUnit.primePrefix21 R a3 b).sigma
          (fun g => filteredPhysical N d g (Fin.last 4) (R^b))),
      ∀ x, fullList (E x).val = x.val.1 :=
  injection_filtered _ _ (geometry21 hd hR hlow hb)

theorem prefix_le21 {N d : ℕ} {R a0 a1 a2 a3 b : ℝ}
    (hd : 0 < d) (hR : 1 < R) (hlow : 1/10 ≤ a3) (hb : b ≤ 1/2) :
    FourPrimeUnit.prefixTerm true N d (R^a0) (R^a1) (R^a2) (R^a3) (R^b) word21 ≤
      ∑ g ∈ HighUnit.primePrefix21 R a3 b,
        ((filteredPhysical N d g (Fin.last 4) (R^b)).card : ℝ) :=
  count_filtered _ _ (geometry21 hd hR hlow hb)

noncomputable def envelope21 {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (R a3 b : ℕ → ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ g ∈ HighUnit.primePrefix21 (R d) (a3 d) (b d),
      ((filteredPhysical N d g (Fin.last 4) (R d^b d)).card : ℝ)

/-- Original sigma is unchanged; the new test is obtained from actual source membership. -/
theorem source_le21 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a3 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    FourPrimeUnit.source N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word21 ≤
      envelope21 N W R a3 b := by
  unfold FourPrimeUnit.source envelope21
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (prefix_le21 (hdpos d hd) (hR d hd)
    (hlow d hd) (hb d hd)) (Nat.cast_nonneg _)

theorem labels_le21 {i N : ℕ} {W : Fin i → Finset ℕ}
    {R a0 a1 a2 a3 b : ℕ → ℝ}
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hR : ∀ d ∈ boxConvolutionSupport W, 1 < R d)
    (hlow : ∀ d ∈ boxConvolutionSupport W, 1/10 ≤ a3 d)
    (hb : ∀ d ∈ boxConvolutionSupport W, b d ≤ 1/2) :
    (∑ x ∈ FourPrimeUnit.labels N W (fun d => R d^a0 d) (fun d => R d^a1 d)
      (fun d => R d^a2 d) (fun d => R d^a3 d) (fun d => R d^b d) word21,
        (convolutionCoeff W x.1 : ℝ)) ≤ envelope21 N W R a3 b := by
  rw [← FourPrimeUnit.source_labels]
  exact source_le21 hdpos hR hlow hb

/-- Same-weight consistency with the accepted unfiltered physical majorant. -/
theorem envelope21_le_old {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (R a3 b : ℕ → ℝ) :
    envelope21 N W R a3 b ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ g ∈ HighUnit.primePrefix21 (R d) (a3 d) (b d),
          ((physical (prefixProduct g) ((N : ℝ)/d) (g (Fin.last 4)).val (R d^b d)).card : ℝ) := by
  apply sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (filtered_sum_le_old _ _) (Nat.cast_nonneg _)

/-- Literal five-cutoff finite consumer: source-box geometry and positivity are derived here. -/
theorem mother_unit_pair_filtered {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hbox : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    let W := convolutionWuWindows N Δ V
    let R := fun d : ℕ => (N : ℝ) ^ (1/2-δ) / d
    let a0 := fun d => wuLocalCutoff N δ d p.S
    let a1 := fun d => wuLocalCutoff N δ d p.kappa1
    let a2 := fun d => wuLocalCutoff N δ d p.kappa2
    let a3 := fun d => wuLocalCutoff N δ d p.kappa3
    let b := fun d => wuLocalCutoff N δ d p.s
    FourPrimeUnit.source N W a0 a1 a2 a3 b word20 +
      FourPrimeUnit.source N W a0 a1 a2 a3 b word21 ≤
      envelope20 N W R (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
      envelope21 N W R (fun _ => 1/p.kappa3) (fun _ => 1/p.s) := by
  have hdpos : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), 0 < d :=
    fun _ hd => boxConvolutionSupport_pos
      (fun j q hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
  have hR : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      1 < (N : ℝ) ^ (1/2-δ) / d :=
    fun _ hd => (omega3XPhi_source_bounds hN hδ hδhi hbox hd).2.1
  obtain ⟨h2,h3,hb⟩ := parameter_outer_bounds hp hs
  have h20 := source_le20 (N := N) (a0 := fun _ => 1/p.S) (a1 := fun _ => 1/p.kappa1)
    (a2 := fun _ => 1/p.kappa2) (a3 := fun _ => 1/p.kappa3) (b := fun _ => 1/p.s)
    hdpos hR (fun _ _ => h2) (fun _ _ => hb)
  have h21 := source_le21 (N := N) (a0 := fun _ => 1/p.S) (a1 := fun _ => 1/p.kappa1)
    (a2 := fun _ => 1/p.kappa2) (a3 := fun _ => 1/p.kappa3) (b := fun _ => 1/p.s)
    hdpos hR (fun _ _ => h3) (fun _ _ => hb)
  simpa only [wuLocalCutoff] using add_le_add h20 h21

end Wu2008DoubleSieve.HighUnitPrimeOutput
