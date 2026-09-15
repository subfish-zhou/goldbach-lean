import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimePrefixAsymptotics
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeSlabUnit

open scoped BigOperators Classical
namespace SecondFunctionalUnitPrimeFibre
open Wu2008DoubleSieve LiLiuPrereqBuchstab Real Finset

noncomputable def fibre (q Z : ℝ) : Finset ℕ :=
  (primesIcc 0 Z).filter (fun p => q < (p : ℝ))

theorem mem_fibre {q Z : ℝ} (hZ : 0 ≤ Z) {p : ℕ} :
    p ∈ fibre q Z ↔ p.Prime ∧ q < (p : ℝ) ∧ (p : ℝ) ≤ Z := by
  simp only [fibre, mem_filter, mem_primesIcc hZ]
  constructor
  · rintro ⟨⟨hp, _, hz⟩, hq⟩; exact ⟨hp, hq, hz⟩
  · rintro ⟨hp, hq, hz⟩; exact ⟨⟨hp, Nat.cast_nonneg _, hz⟩, hq⟩

theorem fibre_empty {q Z : ℝ} (hZ : 0 ≤ Z) (h : Z ≤ q) : fibre q Z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hm := (mem_fibre hZ).mp hp
  exact (not_lt_of_ge (hm.2.2.trans h)) hm.2.1

theorem prefix_subset {A Z : ℝ} (hA : 0 ≤ A) (hAZ : A ≤ Z) :
    primesIcc 0 A ⊆ primesIcc 0 Z := by
  intro p hp
  have hm := (mem_primesIcc hA).mp hp
  exact (mem_primesIcc (hA.trans hAZ)).mpr ⟨hm.1, hm.2.1, hm.2.2.trans hAZ⟩

theorem fibre_eq_sdiff {q Z : ℝ} (hq : 0 ≤ q) (hZ : 0 ≤ Z) :
    fibre q Z = primesIcc 0 Z \ primesIcc 0 (min Z q) := by
  ext p
  simp only [mem_fibre hZ, mem_sdiff, mem_primesIcc hZ,
    mem_primesIcc (le_min hZ hq), le_min_iff]
  constructor
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨hp, Nat.cast_nonneg _, hu⟩, fun h => (not_le_of_gt hl) h.2.2.2⟩
  · rintro ⟨⟨hp, _, hu⟩, hn⟩
    refine ⟨hp, ?_, hu⟩
    by_contra hl
    exact hn ⟨hp, Nat.cast_nonneg _, hu, le_of_not_gt hl⟩

theorem fibre_card {q Z : ℝ} (hq : 0 ≤ q) (hZ : 0 ≤ Z) :
    ((fibre q Z).card : ℝ) = primePi Z - primePi (min Z q) := by
  rw [fibre_eq_sdiff hq hZ, card_sdiff_of_subset (prefix_subset (le_min hZ hq) (min_le_left _ _)),
    Nat.cast_sub (card_le_card (prefix_subset (le_min hZ hq) (min_le_left _ _))),
    secondFunctional_primePrefix_card hZ, secondFunctional_primePrefix_card (le_min hZ hq)]

noncomputable def physical (B X q H : ℝ) : Finset ℕ :=
  (primesIcc 0 H).filter (fun p => q < (p : ℝ) ∧ B * (p : ℝ) ≤ X)

theorem physical_eq {B X q H : ℝ} (hB : 0 < B) (hX : 0 ≤ X) (hH : 0 ≤ H) :
    physical B X q H = fibre q (min (X / B) H) := by
  ext p
  simp only [physical, mem_filter, mem_primesIcc hH,
    mem_fibre (le_min (div_nonneg hX hB.le) hH), le_min_iff]
  constructor
  · rintro ⟨⟨hp, _, hh⟩, hq, hx⟩
    exact ⟨hp, hq, (le_div_iff₀ hB).mpr (by simpa [mul_comm] using hx), hh⟩
  · rintro ⟨hp, hq, hx, hh⟩
    exact ⟨⟨hp, Nat.cast_nonneg _, hh⟩, hq,
      by simpa [mul_comm] using (le_div_iff₀ hB).mp hx⟩

theorem physical_card {B X q H : ℝ} (hB : 0 < B) (hX : 0 ≤ X)
    (hq : 0 ≤ q) (hH : 0 ≤ H) :
    ((physical B X q H).card : ℝ) =
      primePi (min (X / B) H) - primePi (min (min (X / B) H) q) := by
  rw [physical_eq hB hX hH]
  exact fibre_card hq (le_min (div_nonneg hX hB.le) hH)

noncomputable def count (R v ell b : ℝ) : ℝ :=
  ((fibre (R ^ ell) (R ^ (min v b))).card : ℝ)
noncomputable def weight (R v ell b : ℝ) : ℝ := log R * R ^ (-v) * count R v ell b

theorem count_nonneg (R v ell b : ℝ) : 0 ≤ count R v ell b := Nat.cast_nonneg _

theorem count_empty {R v ell b : ℝ} (hR : 1 < R) (hv : v ≤ ell) :
    count R v ell b = 0 := by
  unfold count
  rw [fibre_empty (rpow_nonneg (by linarith : 0 ≤ R) _) (rpow_le_rpow_of_exponent_le hR.le ((min_le_left _ _).trans hv))]
  simp

theorem weight_empty {R v ell b : ℝ} (hR : 1 < R) (hv : v ≤ ell) :
    weight R v ell b = 0 := by rw [weight, count_empty hR hv, mul_zero]

theorem count_feasible {R v ell b : ℝ} (hR : 1 < R) (hv : ell ≤ v) (hb : ell ≤ b) :
    count R v ell b = primePi (R ^ (min v b)) - primePi (R ^ ell) := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR.le
  rw [count, fibre_card (rpow_nonneg hR0 _) (rpow_nonneg hR0 _),
    min_eq_right (rpow_le_rpow_of_exponent_le hR.le (le_min hv hb))]

theorem rpow_min {R v b : ℝ} (hR : 1 < R) :
    R ^ min v b = min (R ^ v) (R ^ b) := by
  rcases le_total v b with h | h
  · rw [min_eq_left h, min_eq_left (rpow_le_rpow_of_exponent_le hR.le h)]
  · rw [min_eq_right h, min_eq_right (rpow_le_rpow_of_exponent_le hR.le h)]
end SecondFunctionalUnitPrimeFibre
