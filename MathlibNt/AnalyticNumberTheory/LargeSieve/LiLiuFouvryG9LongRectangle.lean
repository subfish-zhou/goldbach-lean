import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9LongCoefficient

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- A finite short-coordinate cover with literal real endpoints. No rounding
or analytic interval adapter is built into this definition. -/
def fouvryG9LongShortLabels (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun n => n.Prime ∧ n.Coprime N ∧
    (N : ℝ) ^ (4/53 : ℝ) ≤ n ∧ (n : ℝ) < (N : ℝ) ^ (1/10 : ℝ) ∧
    ρ ^ k.1 ≤ (n : ℝ) ∧ (n : ℝ) < ρ ^ (k.1 + 1)

theorem fouvryG9LongShortLabels_of_cell {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    {k y : ℕ × ℕ × ℕ} (hy : y ∈ fouvryG9GridCell N eps ρ k) :
    y.2.2 ∈ fouvryG9LongShortLabels N ρ k := by
  have hc := (fouvryG9GridCell_mem_iff.mp hy).1
  obtain ⟨hnN, _, _⟩ := fouvryG9Grid_label_bounds hc
  obtain ⟨_, hn, _, _, hcop, hnlo, hnhi, _⟩ := fouvryG9Carrier_geometry hc
  obtain ⟨hlo, hhi, _⟩ := fouvryG9GridCell_rectangle hρ hy
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (by omega), hn, (Nat.coprime_mul_iff_left.mp hcop).1,
    hnlo, hnhi, hlo, ?_⟩
  simpa only [pow_succ, mul_comm] using hhi

/-- The actual cell embeds into the rectangular label product without merging
ordered prime labels. This map is used only for positive enlargement. -/
def fouvryG9LongRectCoordinates (y : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (y.2.2, y.2.1, y.1 / y.2.1)

theorem fouvryG9LongRectCoordinates_injOn (N : ℕ) (eps ρ : ℝ)
    (k : ℕ × ℕ × ℕ) :
    Set.InjOn fouvryG9LongRectCoordinates (fouvryG9GridCell N eps ρ k : Set _) := by
  intro x hx y hy he
  have hxdiv := (fouvryG9Carrier_geometry (fouvryG9GridCell_mem_iff.mp hx).1).2.2.1
  have hydiv := (fouvryG9Carrier_geometry (fouvryG9GridCell_mem_iff.mp hy).1).2.2.1
  have hn := congrArg (fun z : ℕ × ℕ × ℕ => z.1) he
  have hs := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) he
  have ht := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) he
  change x.2.2 = y.2.2 at hn
  change x.2.1 = y.2.1 at hs
  change x.1 / x.2.1 = y.1 / y.2.1 at ht
  refine Prod.ext ?_ (Prod.ext hs hn)
  calc
    x.1 = x.2.1 * (x.1 / x.2.1) := (Nat.mul_div_cancel' hxdiv).symm
    _ = y.2.1 * (y.1 / y.2.1) := by rw [ht, hs]
    _ = y.1 := Nat.mul_div_cancel' hydiv

theorem fouvryG9LongRectCoordinates_subset {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    (k : ℕ × ℕ × ℕ) :
    (fouvryG9GridCell N eps ρ k).image fouvryG9LongRectCoordinates ⊆
      fouvryG9LongShortLabels N ρ k ×ˢ fouvryG9LongLabels N ρ k := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hz
  exact mem_product.mpr ⟨fouvryG9LongShortLabels_of_cell hρ hy,
    fouvryG9LongLabels_of_cell hρ hy⟩

/-- Positive cell enlargement, not a bound for a signed curved-cell error. -/
theorem fouvryG9Long_cell_le_label_rectangle {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    (k : ℕ × ℕ × ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ n m, 0 ≤ F n m) :
    (∑ y ∈ fouvryG9GridCell N eps ρ k, F y.2.2 y.1) ≤
      ∑ n ∈ fouvryG9LongShortLabels N ρ k,
        ∑ z ∈ fouvryG9LongLabels N ρ k, F n (z.1 * z.2) := by
  classical
  calc
    _ = ∑ z ∈ (fouvryG9GridCell N eps ρ k).image fouvryG9LongRectCoordinates,
        F z.1 (z.2.1 * z.2.2) := by
      rw [sum_image (fouvryG9LongRectCoordinates_injOn N eps ρ k)]
      apply sum_congr rfl
      intro y hy
      change F y.2.2 y.1 = F y.2.2 (y.2.1 * (y.1 / y.2.1))
      rw [Nat.mul_div_cancel' (fouvryG9Carrier_geometry
        (fouvryG9GridCell_mem_iff.mp hy).1).2.2.1]
    _ ≤ ∑ z ∈ fouvryG9LongShortLabels N ρ k ×ˢ fouvryG9LongLabels N ρ k,
        F z.1 (z.2.1 * z.2.2) := by
      apply sum_le_sum_of_subset_of_nonneg (fouvryG9LongRectCoordinates_subset hρ k)
      intro z _ _
      exact hF _ _
    _ = _ := sum_product _ _ _

/-- Positive rectangular domination with a genuinely short-independent long
coefficient. The exact regrouping retains the original `s` multiplicity. -/
theorem fouvryG9Long_cell_le_weighted_rectangle {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    (k : ℕ × ℕ × ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ n m, 0 ≤ F n m) :
    (∑ y ∈ fouvryG9GridCell N eps ρ k, F y.2.2 y.1) ≤
      ∑ n ∈ fouvryG9LongShortLabels N ρ k,
        ∑ m ∈ fouvryG9LongProducts N ρ k, fouvryG9LongAlpha N ρ k m * F n m := by
  calc
    _ ≤ ∑ n ∈ fouvryG9LongShortLabels N ρ k,
        ∑ z ∈ fouvryG9LongLabels N ρ k, F n (z.1 * z.2) :=
      fouvryG9Long_cell_le_label_rectangle hρ k F hF
    _ = _ := sum_congr rfl (fun n _ => fouvryG9Long_sum N ρ k F n)

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
