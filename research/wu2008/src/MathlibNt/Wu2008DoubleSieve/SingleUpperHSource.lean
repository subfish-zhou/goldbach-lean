import MathlibNt.Wu2008DoubleSieve.SingleUpperLowPacking
import MathlibNt.Wu2008DoubleSieve.ImprovementIntegrals

namespace Wu2008DoubleSieve.SingleUpperHSource
open Finset Set Real Filter SingleUpperCounts SingleUpperSplice SingleUpperLowPacking
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The actual effective coefficient, not a new admissibility predicate. -/
noncomputable def effective (δ s : ℝ) : ℝ :=
  wuUpperCoefficient s - wuImprovementLimit true δ s

noncomputable def argument (δ t : ℝ) : ℝ :=
  ((1/2-δ)-t)/truncatedSixthLowerAlpha

/-- The fixed sample is chosen before the arithmetic threshold. -/
theorem source {δ s η : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hs : 1 ≤ s) (hs10 : s ≤ 10) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox 1 δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (effective δ s + η) * boxTheta N ((N : ℝ)^(1/2-δ))
          (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT⟩ := wuImprovementLimit_sub_mem true 0 hδ hδhi hs hs10 hη
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN he i Δ V hbox
  have h := hT N ((le_max_right _ _).trans hN)
    ((le_max_left _ _).trans hN) he i Δ V hbox
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
    (wuUpperCoefficient s - (wuImprovementLimit true δ s - η)) * _ at h
  convert h using 1
  dsimp [effective]
  ring

/-- Positivity comes from the actual limiting admissible family. -/
theorem effective_nonneg {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hs : 1 ≤ s) (hs10 : s ≤ 10) : 0 ≤ effective δ s :=
  sub_nonneg.mpr (wuImprovementLimit_bounds hδ hδhi hs hs10).2.1

theorem argument_bounds {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : truncatedSixthLowerAlpha/2 ≤ t) (htHi : t ≤ (1/2-δ)/2) :
    1 ≤ argument δ t ∧ argument δ t ≤ 10 := by
  have hα : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  constructor
  · apply (le_div_iff₀ hα).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  · apply (div_le_iff₀ hα).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith

/-- This fixed coarse sample controls every later microcell to its right.
The carrier is the complete source carrier with modulus p*N. -/
theorem fixed_sample_cell {δ η q : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hq : truncatedSixthLowerAlpha/2 ≤ q) (hqHi : q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ a b : ℝ, q ≤ a → a ≤ b → b ≤ (1/2-δ)/2 →
        (N : ℝ)^b/Δ = (N : ℝ)^a →
      (∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^b),
        (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)) ≤
      (effective δ (argument δ q)+η) * boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ (fun _ : Fin 1 => (N : ℝ)^b)) := by
  have hs := argument_bounds hδ hδhi hq hqHi
  obtain ⟨T,hT4,hT⟩ := source hδ (by linarith) hs.1 hs.2 hη
  refine ⟨T,hT4,?_⟩
  intro N hN he Δ hΔlo hΔhi a b hqa hab hb hcell
  have hN4 := hT4.trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hv : ∀ _j : Fin 1, (N : ℝ)^(δ^(1+1)) ≤ (N : ℝ)^b := by
    intro _j
    apply rpow_le_rpow_of_exponent_le hN1
    have hd : δ^2 ≤ (1/100 : ℝ)^2 := pow_le_pow_left₀ hδ.le hδhi 2
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hpref : boxSquaredPrefixes ((N : ℝ)^(1/2-δ)) (fun _ : Fin 1 => (N : ℝ)^b) := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp
    rw [pow_two, ← rpow_add hN0]
    exact rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hbox := hT N hN he 1 Δ (fun _ : Fin 1 => (N : ℝ)^b)
    ⟨le_rfl,hΔlo,hΔhi,(fun _ _ _ => le_rfl),hv,hpref⟩
  have hw : convolutionWuWindows N Δ (fun _ : Fin 1 => (N : ℝ)^b) =
      (fun _ : Fin 1 => primeWindow N ((N : ℝ)^a) ((N : ℝ)^b)) := by
    funext j
    simp only [convolutionWuWindows,hcell]
  apply le_trans _ hbox
  rw [hw,phi_single]
  apply sum_le_sum
  intro p hp
  have hpa := (mem_primeWindow.mp hp).2.2.1
  have hpq := (rpow_le_rpow_of_exponent_le hN1 hqa).trans hpa
  exact (count_le_source N p _).trans (by
    exact_mod_cast sourceSieveCount_antitone N p (p*N)
      (cell_cutoff_le (by omega) (mem_primeWindow.mp hp).1.pos (by linarith) hpq))

/-- A finite coarse set has one threshold; its size is fixed before N. -/
theorem finite_samples {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (Q : Finset ℝ)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ q ∈ Q, ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ a b : ℝ, q ≤ a → a ≤ b → b ≤ (1/2-δ)/2 →
        (N : ℝ)^b/Δ = (N : ℝ)^a →
      (∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^b),
        (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)) ≤
      (effective δ (argument δ q)+η) * boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ (fun _ : Fin 1 => (N : ℝ)^b)) := by
  induction Q using Finset.induction_on with
  | empty => exact ⟨4,le_rfl,by simp⟩
  | @insert q Q hq ih =>
    obtain ⟨T,hT4,hT⟩ := fixed_sample_cell hδ hδhi hη
      (hQ q (mem_insert_self _ _)).1 (hQ q (mem_insert_self _ _)).2
    obtain ⟨S,hS4,hS⟩ := ih (fun x hx => hQ x (mem_insert_of_mem hx))
    refine ⟨max T S,hT4.trans (le_max_left _ _),?_⟩
    intro N hN he x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hT N ((le_max_left _ _).trans hN) he
    · exact hS N ((le_max_right _ _).trans hN) he x hx

end Wu2008DoubleSieve.SingleUpperHSource
