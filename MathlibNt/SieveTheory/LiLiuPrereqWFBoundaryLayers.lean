import MathlibNt.SieveTheory.LiLiuPrereqWFSmallDensity

/-!
# High-order support of the actual small-weight density boundaries

For the source parameters `L = D^ε`, `u = D^(ε²)`, a failed cubic test
`L ≤ (∏ s) q³` involving small primes forces `1 < ε (|s| + 3)`.
The finite boundary kernels are therefore sums over these high layers only.
This localizes the explicit errors; it does not estimate their total size.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open Finset
open scoped Classical

private theorem small_cubic_lt (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hs : s ⊆ geometricSmallPrimes P D ε) :
    ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3 <
      D ^ (ε ^ 2 * ((s.card + 3 : ℕ) : ℝ)) := by
  let u := D ^ (ε ^ 2)
  have hu : 0 < u := Real.rpow_pos_of_pos (by linarith) _
  have hqU : (q : ℝ) < u := (Finset.mem_filter.mp hq).2.2
  have hprod : ((s.prod id : ℕ) : ℝ) ≤ u ^ s.card := by
    calc
      ((s.prod id : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := by simp
      _ ≤ ∏ _p ∈ s, u := Finset.prod_le_prod
        (fun p _ => Nat.cast_nonneg p)
        (fun p hp => (Finset.mem_filter.mp (hs hp)).2.2.le)
      _ = u ^ s.card := by simp
  have hq3 : (q : ℝ) ^ 3 < u ^ 3 := by
    calc
      (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q := by ring
      _ ≤ u ^ 2 * q := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg q) hqU.le 2) (Nat.cast_nonneg q)
      _ < u ^ 2 * u := mul_lt_mul_of_pos_left hqU (sq_pos_of_pos hu)
      _ = u ^ 3 := by ring
  calc
    ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3 ≤ u ^ s.card * (q : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hprod (pow_nonneg (Nat.cast_nonneg q) _)
    _ < u ^ s.card * u ^ 3 := mul_lt_mul_of_pos_left hq3 (pow_pos hu _)
    _ = u ^ (s.card + 3) := (pow_add _ _ _).symm
    _ = D ^ (ε ^ 2 * ((s.card + 3 : ℕ) : ℝ)) :=
      (Real.rpow_mul_natCast (by linarith) _ _).symm

theorem small_cubic_failure_card (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hs : s ⊆ geometricSmallPrimes P D ε)
    (hfail : D ^ ε ≤ ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3) :
    1 < ε * (s.card + 3) := by
  have hb := lt_of_le_of_lt hfail (small_cubic_lt P hD hq hs)
  have he : ε < ε ^ 2 * ((s.card + 3 : ℕ) : ℝ) := by
    by_contra! hn
    exact (not_lt_of_ge (Real.rpow_le_rpow_of_exponent_le (by linarith) hn)) hb
  push_cast at he
  nlinarith

/-- Lower boundaries have odd tail length and start beyond `1/ε - 3`. -/
theorem lowerSmallBoundary_highLayer (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hs : s ⊆ geometricSmallPrimes P D ε)
    (hb : LowerBoundary (D ^ ε) q s) :
    ¬Even s.card ∧ 1 < ε * (s.card + 3) :=
  ⟨hb.2.2.1, small_cubic_failure_card P hD hε hq hs hb.2.2.2⟩

/-- Upper boundaries have even tail length and start beyond `1/ε - 3`. -/
theorem upperSmallBoundary_highLayer (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hs : s ⊆ geometricSmallPrimes P D ε)
    (hb : UpperBoundary (D ^ ε) q s) :
    Even s.card ∧ 1 < ε * (s.card + 3) :=
  ⟨hb.2.2.1, small_cubic_failure_card P hD hε hq hs hb.2.2.2⟩

/-- A finite source-aligned restriction of the same lower boundary kernel. -/
theorem lowerBoundaryDensity_eq_highLayers (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (g : ℕ → ℝ) {q : ℕ} {B : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hB : B ⊆ geometricSmallPrimes P D ε) :
    lowerBoundaryDensity (D ^ ε) g q B =
      ∑ s ∈ B.powerset.filter (fun s => ¬Even s.card ∧ 1 < ε * (s.card + 3)),
        if LowerBoundary (D ^ ε) q s then ∏ p ∈ s, g p else 0 := by
  rw [lowerBoundaryDensity, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hb : LowerBoundary (D ^ ε) q s
  · have hh := lowerSmallBoundary_highLayer P hD hε hq
      ((Finset.mem_powerset.mp hs).trans hB) hb
    simp only [if_pos hb, if_pos hh]
  · simp only [if_neg hb, ite_self]

theorem upperBoundaryDensity_eq_highLayers (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (g : ℕ → ℝ) {q : ℕ} {B : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hB : B ⊆ geometricSmallPrimes P D ε) :
    upperBoundaryDensity (D ^ ε) g q B =
      ∑ s ∈ B.powerset.filter (fun s => Even s.card ∧ 1 < ε * (s.card + 3)),
        if UpperBoundary (D ^ ε) q s then ∏ p ∈ s, g p else 0 := by
  rw [upperBoundaryDensity, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hb : UpperBoundary (D ^ ε) q s
  · have hh := upperSmallBoundary_highLayer P hD hε hq
      ((Finset.mem_powerset.mp hs).trans hB) hb
    simp only [if_pos hb, if_pos hh]
  · simp only [if_neg hb, ite_self]

/-- In the Li--Liu parameter range a lower boundary needs at least seven
tail primes (and the new least prime); the upper boundary needs six. -/
theorem lowerSmallBoundary_card_seven (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hs : s ⊆ geometricSmallPrimes P D ε)
    (hb : LowerBoundary (D ^ ε) q s) : 7 ≤ s.card := by
  obtain ⟨hodd, hlayer⟩ := lowerSmallBoundary_highLayer P hD hε hq hs hb
  have hsix : 6 ≤ s.card := by
    by_contra! hn
    have hc : (s.card : ℝ) ≤ 5 := by exact_mod_cast (show s.card ≤ 5 by omega)
    nlinarith
  have hne : s.card ≠ 6 := by
    intro h
    norm_num [h] at hodd
  omega

theorem upperSmallBoundary_card_six (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) {q : ℕ} {s : Finset ℕ}
    (hq : q ∈ geometricSmallPrimes P D ε) (hs : s ⊆ geometricSmallPrimes P D ε)
    (hb : UpperBoundary (D ^ ε) q s) : 6 ≤ s.card := by
  have hlayer := (upperSmallBoundary_highLayer P hD hε hq hs hb).2
  by_contra! hn
  have hc : (s.card : ℝ) ≤ 5 := by exact_mod_cast (show s.card ≤ 5 by omega)
  nlinarith

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
