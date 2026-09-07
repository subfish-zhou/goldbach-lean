import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridIndex

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- All three labels of the actual carrier, including the retained second prime. -/
theorem fouvryG9Grid_label_bounds {N : ℕ} {eps : ℝ} {y : ℕ × ℕ × ℕ}
    (hy : y ∈ fouvryG9Carrier N eps) :
    (2 ≤ y.2.2 ∧ y.2.2 ≤ N) ∧ (2 ≤ y.2.1 ∧ y.2.1 ≤ N) ∧
      (2 ≤ y.1 / y.2.1 ∧ y.1 / y.2.1 ≤ N) := by
  obtain ⟨hs, hn, hdiv, hq, _, _, _, _, _, _, hprod⟩ :=
    fouvryG9Carrier_geometry hy
  have hm : 0 < y.1 := by
    by_contra h
    have hz : y.1 = 0 := by omega
    simp only [hz, Nat.zero_div] at hq
    exact Nat.not_prime_zero hq
  have hmN : y.1 ≤ N := (Nat.le_mul_of_pos_left y.1 hn.pos).trans hprod.le
  have hnN : y.2.2 ≤ N := (Nat.le_mul_of_pos_right y.2.2 hm).trans hprod.le
  exact ⟨⟨hn.two_le, hnN⟩, ⟨hs.two_le, (Nat.le_of_dvd hm hdiv).trans hmN⟩,
    ⟨hq.two_le, (Nat.div_le_self _ _).trans hmN⟩⟩

/-- The grid uses the ordered labels `(n,s,m/s)`, never the merged pair `(n,m)`. -/
def fouvryG9GridKey (ρ : ℝ) (y : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (fouvryG9GridIndex ρ y.2.2, fouvryG9GridIndex ρ y.2.1,
    fouvryG9GridIndex ρ ((y.1 / y.2.1 : ℕ) : ℝ))

def fouvryG9GridUsed (N : ℕ) (eps ρ : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (fouvryG9Carrier N eps).image (fouvryG9GridKey ρ)

def fouvryG9GridBox (N : ℕ) (ρ : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  let I := range (fouvryG9GridIndex ρ N + 1)
  I ×ˢ (I ×ˢ I)

theorem fouvryG9GridKey_bounds {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ)
    {y : ℕ × ℕ × ℕ} (hy : y ∈ fouvryG9Carrier N eps) :
    (fouvryG9GridKey ρ y).1 ≤ fouvryG9GridIndex ρ N ∧
    (fouvryG9GridKey ρ y).2.1 ≤ fouvryG9GridIndex ρ N ∧
    (fouvryG9GridKey ρ y).2.2 ≤ fouvryG9GridIndex ρ N := by
  obtain ⟨hn, hs, hq⟩ := fouvryG9Grid_label_bounds hy
  have step : ∀ a : ℕ, 2 ≤ a → a ≤ N →
      fouvryG9GridIndex ρ a ≤ fouvryG9GridIndex ρ N := by
    intro a ha haN
    apply fouvryG9GridIndex_mono hρ
    · exact_mod_cast (show 1 ≤ a by omega)
    · exact_mod_cast haN
  exact ⟨step _ hn.1 hn.2, step _ hs.1 hs.2, step _ hq.1 hq.2⟩

theorem fouvryG9GridUsed_subset {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ) :
    fouvryG9GridUsed N eps ρ ⊆ fouvryG9GridBox N ρ := by
  intro k hk
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hk
  obtain ⟨hi, hj, hk⟩ := fouvryG9GridKey_bounds hρ hy
  simpa only [fouvryG9GridBox, mem_product, mem_range, Nat.lt_succ_iff] using
    And.intro hi (And.intro hj hk)

/-- The number of occupied cells is at most the cube of the logarithmic range. -/
theorem fouvryG9GridUsed_card_le {N : ℕ} {eps ρ : ℝ} (hρ : 1 < ρ) :
    (fouvryG9GridUsed N eps ρ).card ≤ (fouvryG9GridIndex ρ N + 1) ^ 3 := by
  calc
    _ ≤ (fouvryG9GridBox N ρ).card := card_le_card (fouvryG9GridUsed_subset hρ)
    _ = _ := by simp only [fouvryG9GridBox, card_product, card_range]; ring

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
