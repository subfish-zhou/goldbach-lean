import MathlibNt.Wu2008DoubleSieve.Omega3XFiniteReorder
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount

/-!
# The actual X fibres are bounded by rough integers and repeated p1

Source: Wu 2004, arXiv TeX lines 2215–2238.  `roughCount` is the literal
positive-integer count imported from the immutable accepted Buchstab seed.
The unit remains present; gcd conditions are dropped only for upper bounds.
-/

namespace Wu2008DoubleSieve

open Finset LiLiuPrereqBuchstab
open scoped Classical

noncomputable def omega3XPositiveMultiples (x : ℝ) (p : ℕ) : Finset ℕ :=
  (range (⌊x⌋₊ + 1)).filter fun n => 0 < n ∧ (n : ℝ) ≤ x ∧ p ∣ n

theorem mem_omega3XPositiveMultiples {x : ℝ} {p n : ℕ} :
    n ∈ omega3XPositiveMultiples x p ↔ 0 < n ∧ (n : ℝ) ≤ x ∧ p ∣ n := by
  classical
  simp only [omega3XPositiveMultiples, mem_filter, mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => h.2, fun h => ⟨Nat.le_floor h.2.1, h⟩⟩

/-- Exact positive-multiple count, not a count that accidentally includes zero. -/
theorem omega3XPositiveMultiples_card {x : ℝ} {p : ℕ}
    (hx : 0 ≤ x) (hp : 0 < p) :
    (omega3XPositiveMultiples x p).card = ⌊x / p⌋₊ := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hxp : 0 ≤ x / p := div_nonneg hx hpR.le
  have hc : (Icc 1 ⌊x / p⌋₊).card = (omega3XPositiveMultiples x p).card := by
    apply card_bij (fun m _ => p * m)
    · intro m hm
      obtain ⟨hm0, hmle⟩ := mem_Icc.mp hm
      have hmR : (m : ℝ) ≤ x / p := (Nat.le_floor_iff hxp).mp hmle
      apply mem_omega3XPositiveMultiples.mpr
      refine ⟨Nat.mul_pos hp hm0, ?_, dvd_mul_right p m⟩
      simpa only [Nat.cast_mul, mul_comm] using (le_div_iff₀ hpR).mp hmR
    · intro m₁ _ m₂ _ he
      exact Nat.eq_of_mul_eq_mul_left hp he
    · intro n hn
      obtain ⟨hn0, hnx, ⟨m, rfl⟩⟩ := mem_omega3XPositiveMultiples.mp hn
      have hm0 : 0 < m := Nat.pos_of_mul_pos_left hn0
      refine ⟨m, mem_Icc.mpr ⟨hm0, Nat.le_floor ?_⟩, rfl⟩
      apply (le_div_iff₀ hpR).mpr
      simpa only [Nat.cast_mul, mul_comm] using hnx
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc.symm

theorem omega3XScale_nonneg (N d p1 p2 p3 : ℕ) :
    0 ≤ omega3XScale N d p1 p2 p3 := by
  unfold omega3XScale
  positivity

/-- Exact real-bound version of the actual fibre, with all original gcd tests. -/
theorem mem_omega3XNCountFibre_iff_real {N d p1 p2 p3 n : ℕ}
    (hd : 0 < d) (h1 : 0 < p1) (h2 : 0 < p2) (h3 : 0 < p3) :
    n ∈ omega3XNCountFibre N d p1 p2 p3 ↔
      0 < n ∧ (n : ℝ) ≤ omega3XScale N d p1 p2 p3 ∧
        Omega3Strengthened N d p1 p2 n := by
  have hprod : 0 < d * p1 * p2 * p3 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd h1) h2) h3
  have hprodR : (0 : ℝ) < (d : ℝ) * p1 * p2 * p3 := by
    exact_mod_cast hprod
  have hsize : (d * p1 * p2 * p3) * n ≤ N ↔
      (n : ℝ) ≤ omega3XScale N d p1 p2 p3 := by
    rw [omega3XScale, le_div_iff₀ hprodR]
    norm_cast
    rw [Nat.mul_comm n]
  rw [mem_omega3XNCountFibre]
  constructor
  · exact fun h => ⟨h.2.1, hsize.mp h.2.2.1, h.2.2.2⟩
  · rintro ⟨hn, hx, hg⟩
    have hs := hsize.mpr hx
    exact ⟨(Nat.le_mul_of_pos_left n hprod).trans hs, hn, hs, hg⟩

theorem omega3Strengthened_rough_of_not_dvd {N d p1 p2 n : ℕ}
    (hg : Omega3Strengthened N d p1 p2 n) (h1 : ¬p1 ∣ n) :
    Rough (p2 : ℝ) n := by
  apply rough_iff_no_small_prime.mpr
  intro q hq hq2 hqn
  by_cases he : q = p1
  · exact h1 (he ▸ hqn)
  · exact hg.2.2 q hq hq2 he hqn

/-- The unit is present precisely when the size and retained prime gcd tests hold. -/
theorem omega3XNCountFibre_one_iff {N d p1 p2 p3 : ℕ}
    (hd : 0 < d) (h1 : 0 < p1) (h2 : 0 < p2) (h3 : 0 < p3) :
    1 ∈ omega3XNCountFibre N d p1 p2 p3 ↔
      1 ≤ omega3XScale N d p1 p2 p3 ∧ (p1 * p2).Coprime (d * N) := by
  rw [mem_omega3XNCountFibre_iff_real hd h1 h2 h3]
  constructor
  · intro h
    exact ⟨by simpa only [Nat.cast_one] using h.2.1, h.2.2.1⟩
  · rintro ⟨hx, hcop⟩
    refine ⟨by decide, by simpa only [Nat.cast_one] using hx, hcop, by simp, ?_⟩
    intro q hq _ _ hq1
    exact hq.ne_one (Nat.dvd_one.mp hq1)

theorem omega3XNCountFibre_split (N d p1 p2 p3 : ℕ) :
    (omega3XNCountFibre N d p1 p2 p3).card =
      ((omega3XNCountFibre N d p1 p2 p3).filter (fun n => ¬p1 ∣ n)).card +
      ((omega3XNCountFibre N d p1 p2 p3).filter (fun n => p1 ∣ n)).card := by
  classical
  rw [add_comm]
  exact (card_filter_add_card_filter_not (s := omega3XNCountFibre N d p1 p2 p3)
    (fun n => p1 ∣ n)).symm

theorem omega3XNCountFibre_nonmultiple_subset_rough {N d p1 p2 p3 : ℕ}
    (hd : 0 < d) (h1 : 0 < p1) (h2 : 0 < p2) (h3 : 0 < p3) :
    (omega3XNCountFibre N d p1 p2 p3).filter (fun n => ¬p1 ∣ n) ⊆
      roughNumbers (omega3XScale N d p1 p2 p3) p2 := by
  intro n hn
  obtain ⟨hn, hnot⟩ := mem_filter.mp hn
  obtain ⟨hn0, hnx, hg⟩ := (mem_omega3XNCountFibre_iff_real hd h1 h2 h3).mp hn
  exact mem_roughNumbers.mpr ⟨hn0, hnx, omega3Strengthened_rough_of_not_dvd hg hnot⟩

theorem omega3XNCountFibre_multiple_subset {N d p1 p2 p3 : ℕ}
    (hd : 0 < d) (h1 : 0 < p1) (h2 : 0 < p2) (h3 : 0 < p3) :
    (omega3XNCountFibre N d p1 p2 p3).filter (fun n => p1 ∣ n) ⊆
      omega3XPositiveMultiples (omega3XScale N d p1 p2 p3) p1 := by
  intro n hn
  obtain ⟨hn, hdiv⟩ := mem_filter.mp hn
  obtain ⟨hn0, hnx, _⟩ := (mem_omega3XNCountFibre_iff_real hd h1 h2 h3).mp hn
  exact mem_omega3XPositiveMultiples.mpr ⟨hn0, hnx, hdiv⟩

/-- The actual finite fibre, with repeated p1 isolated and the unit retained. -/
theorem omega3XNCountFibre_card_le_rough_add_floor {N d p1 p2 p3 : ℕ}
    (hd : 0 < d) (h1 : 0 < p1) (h2 : 0 < p2) (h3 : 0 < p3) :
    (omega3XNCountFibre N d p1 p2 p3).card ≤
      roughCount (omega3XScale N d p1 p2 p3) p2 +
        ⌊omega3XScale N d p1 p2 p3 / p1⌋₊ := by
  rw [omega3XNCountFibre_split]
  apply Nat.add_le_add
  · exact card_le_card (omega3XNCountFibre_nonmultiple_subset_rough hd h1 h2 h3)
  · calc
      _ ≤ (omega3XPositiveMultiples (omega3XScale N d p1 p2 p3) p1).card :=
        card_le_card (omega3XNCountFibre_multiple_subset hd h1 h2 h3)
      _ = _ := omega3XPositiveMultiples_card (omega3XScale_nonneg N d p1 p2 p3) h1

noncomputable def omega3XRoughMajorant {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ omega3XPrimes N δ s t d, (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)

noncomputable def omega3XRepeatedMajorant {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ omega3XPrimes N δ s t d, (⌊omega3XScale N d p.1 p.2.1 p.2.2 / p.1⌋₊ : ℝ)

theorem omega3XRoughMajorant_nonneg {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : 0 ≤ omega3XRoughMajorant N δ s t W :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ => Nat.cast_nonneg _)

theorem omega3XRepeatedMajorant_nonneg {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : 0 ≤ omega3XRepeatedMajorant N δ s t W :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- Physical upper bound for X, before any asymptotic error payment.
The convolution weight occurs once and the closed p3 endpoint is unchanged. -/
theorem omega3SieveX_le_rough_add_repeated {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    omega3SieveX N δ s t W ≤
      omega3XRoughMajorant N δ s t W + omega3XRepeatedMajorant N δ s t W := by
  rw [omega3SieveX_eq_prime_triple_sum]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ omega3XPrimes N δ s t d,
          ((roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) +
            (⌊omega3XScale N d p.1 p.2.1 p.2.2 / p.1⌋₊ : ℝ)) := by
      apply sum_le_sum
      intro d hdmem
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      rintro ⟨p1, p2, p3⟩ hp
      obtain ⟨h2, h1, _, h3, _⟩ := mem_omega3XPrimes.mp hp
      exact_mod_cast omega3XNCountFibre_card_le_rough_add_floor
        (hd d hdmem) (mem_primeWindow.mp h1).1.pos (mem_primeWindow.mp h2).1.pos h3.pos
    _ = _ := by
      simp only [omega3XRoughMajorant, omega3XRepeatedMajorant, sum_add_distrib, mul_add]

end Wu2008DoubleSieve
