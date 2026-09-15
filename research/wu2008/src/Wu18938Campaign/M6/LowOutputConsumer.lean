import Wu18938Campaign.M6.LowOutput

noncomputable section
open Finset
open scoped Classical

namespace Wu18938Campaign.M6
open U8Literal

theorem prime_output_lt_cut {N n m : ℕ} {P : Finset ℕ} {z : ℝ}
    (hr : (output N n m).Prime) (hP : ∀ p ∈ P, p.Prime)
    (hcut : ∀ p ∈ P, (p : ℝ) < z)
    (hbad : ¬(output N n m).Coprime (P.prod id)) :
    (output N n m : ℝ) < z := by
  by_contra hout
  apply hbad
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  change (output N n m).Coprime p
  rw [Nat.coprime_comm, (hP p hp).coprime_iff_not_dvd]
  intro hd
  have he := (hr.dvd_iff_eq (hP p hp).ne_one).mp hd
  exact hout (by simpa only [he] using hcut p hp)

theorem labels_le_rectangle_add_small_output {N : ℕ} (hN : 1 ≤ N)
    {ρ : ℝ} (hρ : 1 < ρ) {k : Key} {P : Finset ℕ} {z : ℝ}
    (hP : ∀ p ∈ P, p.Prime) (hcut : ∀ p ∈ P, (p : ℝ) < z)
    (S : Finset Label)
    (hS : ∀ x ∈ S, x.1.1 ∈ shortPrimeSupport N ρ k ∧
      (x.1.2, x.2) ∈ longLabels N ρ k ∧ x.1.1.Prime ∧ x.1.1.Coprime N ∧
      (output N x.1.1 (x.1.2 * x.2)).Prime) :
    (S.card : ℝ) ≤ rectangleSifted N ρ k P + 2 * (⌈z⌉₊ : ℝ) := by
  let good := S.filter fun x => (output N x.1.1 (x.1.2 * x.2)).Coprime (P.prod id)
  let bad := S.filter fun x => ¬(output N x.1.1 (x.1.2 * x.2)).Coprime (P.prod id)
  have hsplit : S.card = good.card + bad.card :=
    (card_filter_add_card_filter_not (s := S)
      (fun x => (output N x.1.1 (x.1.2 * x.2)).Coprime (P.prod id))).symm
  have hgood : (good.card : ℝ) ≤ rectangleSifted N ρ k P := by
    apply labels_le_rectangle
    intro x hx
    obtain ⟨hx, hcop⟩ := mem_filter.mp hx
    obtain ⟨hn, ht, hp, hc, _⟩ := hS x hx
    exact ⟨hn, ht, hp, hc, hcop⟩
  let f : Label → ℕ × ℕ × ℕ := fun x => (x.1.1, x.1.2, x.2)
  have hf : Function.Injective f := by
    rintro ⟨⟨a, b⟩, c⟩ ⟨⟨d, e⟩, g⟩ h
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl
  have hbad : bad.card ≤ (lowTriples N ρ k z).card := by
    apply card_le_card_of_injOn f
    · intro x hx
      obtain ⟨hx, hcop⟩ := mem_filter.mp hx
      obtain ⟨hn, ht, hp, hc, hr⟩ := hS x hx
      exact mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hn, hp, hc⟩, ht⟩,
          prime_output_lt_cut hr hP hcut hcop⟩
    · exact hf.injOn
  have hbadR : (bad.card : ℝ) ≤ 2 * (⌈z⌉₊ : ℝ) := by
    exact_mod_cast hbad.trans (lowTriples_card_le hN hρ k z)
  rw [hsplit, Nat.cast_add]
  exact add_le_add hgood hbadR

theorem labels_le_rectangle_add_sqrt {N : ℕ} (hN : 1 ≤ N)
    {ρ : ℝ} (hρ : 1 < ρ) {k : Key} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hcut : ∀ p ∈ P, (p : ℝ) < Real.sqrt N)
    (S : Finset Label)
    (hS : ∀ x ∈ S, x.1.1 ∈ shortPrimeSupport N ρ k ∧
      (x.1.2, x.2) ∈ longLabels N ρ k ∧ x.1.1.Prime ∧ x.1.1.Coprime N ∧
      (output N x.1.1 (x.1.2 * x.2)).Prime) :
    (S.card : ℝ) ≤ rectangleSifted N ρ k P + 2 * Real.sqrt N + 2 := by
  have h := labels_le_rectangle_add_small_output hN hρ hP hcut S hS
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (N : ℝ))
  linarith

end Wu18938Campaign.M6
