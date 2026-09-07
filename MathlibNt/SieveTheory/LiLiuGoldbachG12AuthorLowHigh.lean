import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorSourceBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedConsumers

open scoped BigOperators
open Classical Finset
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The physical low mother, before ANY output-primality condition. -/
def goldbachG12AuthorLowMotherMass (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ G12FlexibleRectangle.mother N ε,
    goldbachG12NormalizedCoefficient N p.1 * goldbachG12AuthorPrimeWeight N p.2

/-- This source low window is ungated, unlike the physical mother. -/
def goldbachG12AuthorLowSourceMass (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
    ∑ r ∈ (goldbachG11LinkedPrimeWindow N ε m).filter
      (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ)), goldbachG12AuthorPrimeWeight N r

theorem goldbachG12AuthorLowMother_le_source (N : ℕ) (ε : ℝ) :
    goldbachG12AuthorLowMotherMass N ε ≤ goldbachG12AuthorLowSourceMass N ε := by
  let T := (goldbachG12ActiveProductSupport N).sigma (fun m =>
    (goldbachG11LinkedPrimeWindow N ε m).filter
      (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ)))
  let f : (ℕ × ℕ) → (Σ _ : ℕ, ℕ) := fun p => ⟨p.1,p.2⟩
  have hi : Function.Injective f := by
    rintro ⟨m,r⟩ ⟨m',r'⟩ h
    have hm := congrArg Sigma.fst h
    have hr := congrArg (fun p => p.2) h
    dsimp [f] at hm hr
    subst m'; subst r'
    rfl
  have hs : (G12FlexibleRectangle.mother N ε).image f ⊆ T := by
    intro a ha
    obtain ⟨⟨m,r⟩,hp,rfl⟩ := mem_image.mp ha
    obtain ⟨hm,hr,_,_,hcut⟩ := (G12LowRectangle.mother_linked_iff N m r ε).mp hp
    exact mem_sigma.mpr ⟨hm,mem_filter.mpr ⟨hr,hcut⟩⟩
  calc
    _ = ∑ a ∈ (G12FlexibleRectangle.mother N ε).image f,
        goldbachG12NormalizedCoefficient N a.1 * goldbachG12AuthorPrimeWeight N a.2 := by
      rw [sum_image (fun a _ b _ h => hi h)]
      rfl
    _ ≤ ∑ a ∈ T, goldbachG12NormalizedCoefficient N a.1 *
        goldbachG12AuthorPrimeWeight N a.2 :=
      sum_le_sum_of_subset_of_nonneg hs (by
        intro a _ _
        exact mul_nonneg (goldbachG12NormalizedCoefficient_bounds N a.1).1
          (goldbachG11AuthorWeight_nonneg _))
    _ = _ := by
      simp only [T,sum_sigma,goldbachG12AuthorLowSourceMass,mul_sum]

/-- The closed high cutoff maps to the high branch, including equality. -/
theorem goldbachG12AuthorPrimeWeight_eq_high {N r : ℕ} (hN : 4 ≤ N)
    (_hr : r.Prime) (hcut : (N : ℝ)^(1/10 : ℝ) ≤ (r : ℝ)) :
    goldbachG12AuthorPrimeWeight N r = 8 := by
  apply goldbachG11AuthorWeight_eq_high
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hcut
  rw [Real.log_rpow hNp] at hl
  exact (le_div_iff₀ hlog).mpr hl

/-- Exact author source split. High mass is the ORIGINAL UNGATED source window. -/
theorem goldbachG12AuthorSource_split {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) :
    goldbachG12WeightedSource N ε (goldbachG12AuthorPrimeWeight N) =
      goldbachG12AuthorLowSourceMass N ε + 8 * G12ClippedWindow.highMass N ε := by
  unfold goldbachG12WeightedSource goldbachG12AuthorLowSourceMass G12ClippedWindow.highMass
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  have hh : (∑ r ∈ G12LowHighOutput.highWindow N ε m, goldbachG12AuthorPrimeWeight N r) =
      8 * ((G12LowHighOutput.highWindow N ε m).card : ℝ) := by
    calc
      _ = ∑ _r ∈ G12LowHighOutput.highWindow N ε m, (8 : ℝ) := by
        apply sum_congr rfl
        intro r hr
        exact goldbachG12AuthorPrimeWeight_eq_high hN (mem_filter.mp (mem_filter.mp hr).1).2.1
          (mem_filter.mp hr).2
      _ = _ := by simp [mul_comm]
  have hp := sum_filter_add_sum_filter_not (goldbachG11LinkedPrimeWindow N ε m)
    (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ)) (goldbachG12AuthorPrimeWeight N)
  simp only [not_lt] at hp
  change _ + (∑ r ∈ G12LowHighOutput.highWindow N ε m, goldbachG12AuthorPrimeWeight N r) = _ at hp
  rw [hh] at hp
  rw [← hp]
  ring

/-- The physical low plus the original UNGATED high is bounded by the same
weighted source. No product value is treated as a unique body label. -/
theorem goldbachG12AuthorLowHigh_le_source {N : ℕ} (hN : 4 ≤ N) (ε : ℝ) :
    goldbachG12AuthorLowMotherMass N ε + 8 * G12ClippedWindow.highMass N ε ≤
      goldbachG12WeightedSource N ε (goldbachG12AuthorPrimeWeight N) := by
  rw [goldbachG12AuthorSource_split hN]
  exact add_le_add (goldbachG12AuthorLowMother_le_source N ε) le_rfl

/-- Actual low physical weighted mother plus ungated high mass; the cutoff is
uniform in every later epsilon. This is a raw-mother, ONE-logarithm bound. -/
theorem goldbachG12AuthorLowHigh_integral_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ε : ℝ,
      Real.log (N : ℝ)/N * (400 * (goldbachG12AuthorLowMotherMass N ε +
        8 * G12ClippedWindow.highMass N ε)) ≤
          (564383/1000000 : ℝ)*goldbachG12PrimeIntegral goldbachG11AuthorWeight + δ := by
  obtain ⟨K,hK,hb⟩ := goldbachG12AuthorSource_integral_budget δ hδ
  refine ⟨K,hK,?_⟩
  intro N hN ε
  have hn : 0 ≤ Real.log (N : ℝ)/N := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (goldbachG12AuthorLowHigh_le_source (hK.trans hN) ε)
      (by norm_num : (0 : ℝ) ≤ 400)) hn).trans (hb N hN ε)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
