import MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser

/-!
# Exact density defects for the actual small Rosser weights

The finite starting point for Iwaniec (1980), p.316 (22). The boundary is a
failed cubic test at the newly inserted least prime, with equality on the
failure side. The lower error is subtracted and the upper error is added.
No analytic estimate for these explicit errors is assumed or asserted.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset
open scoped Classical

/-- Prime densities are already `g(p) = ω(p)/p`. -/
noncomputable def lowerSetDensity (L : ℝ) (g : ℕ → ℝ) (B : Finset ℕ) : ℝ :=
  ∑ s ∈ B.powerset, setWeight L s * ∏ p ∈ s, g p

noncomputable def upperSetDensity (L : ℝ) (g : ℕ → ℝ) (B : Finset ℕ) : ℝ :=
  ∑ s ∈ B.powerset, upperSetWeight L s * ∏ p ∈ s, g p

/-- The active odd tail whose next even cubic test fails. -/
def LowerBoundary (L : ℝ) (q : ℕ) (s : Finset ℕ) : Prop :=
  ((s.prod id : ℕ) : ℝ) < L ∧ LowerAdmissibleSet L s ∧
    ¬Even s.card ∧ L ≤ ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3

/-- The active even tail whose next odd cubic test fails. -/
def UpperBoundary (L : ℝ) (q : ℕ) (s : Finset ℕ) : Prop :=
  ((s.prod id : ℕ) : ℝ) < L ∧ UpperAdmissibleSet L s ∧
    Even s.card ∧ L ≤ ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3

noncomputable def lowerBoundaryDensity (L : ℝ) (g : ℕ → ℝ)
    (q : ℕ) (B : Finset ℕ) : ℝ :=
  ∑ s ∈ B.powerset, if LowerBoundary L q s then ∏ p ∈ s, g p else 0

noncomputable def upperBoundaryDensity (L : ℝ) (g : ℕ → ℝ)
    (q : ℕ) (B : Finset ℕ) : ℝ :=
  ∑ s ∈ B.powerset, if UpperBoundary L q s then ∏ p ∈ s, g p else 0

private theorem insert_cut_back {L : ℝ} {q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hq : q.Prime)
    (h : (((insert q s).prod id : ℕ) : ℝ) < L) :
    ((s.prod id : ℕ) : ℝ) < L := by
  apply lt_of_le_of_lt _ h
  exact_mod_cast (show s.prod id ≤ (insert q s).prod id by
    rw [Finset.prod_insert hqs]
    exact Nat.le_mul_of_pos_left (s.prod id) hq.pos)

private theorem insert_cut_of_cube {L : ℝ} {q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hq : q.Prime)
    (h : ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3 < L) :
    (((insert q s).prod id : ℕ) : ℝ) < L := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hcube : (q : ℝ) ≤ (q : ℝ) ^ 3 := by nlinarith [sq_nonneg (q : ℝ)]
  rw [Finset.prod_insert hqs, Nat.cast_mul]
  exact lt_of_le_of_lt (by
    simpa only [mul_comm, id_eq] using
      mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg (s.prod id))) h

private theorem lower_insert_test {L : ℝ} {q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hqmin : ∀ p ∈ s, q ≤ p)
    (hs : LowerAdmissibleSet L s) (hodd : ¬Even s.card) :
    LowerAdmissibleSet L (insert q s) ↔
      ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3 < L := by
  have hmin : (insert q s).filter (fun r => q ≤ r) = insert q s :=
    Finset.filter_eq_self.mpr fun r hr => by
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact le_rfl
      · exact hqmin r hr
  constructor
  · intro h
    have ht := h q (Finset.mem_insert_self q s) (by
      simp only [hmin, Finset.card_insert_of_notMem hqs, Nat.even_add_one]
      exact hodd)
    simpa only [hmin, Finset.prod_insert hqs, Nat.cast_mul, id_eq,
      mul_pow, pow_succ, mul_assoc, mul_comm, mul_left_comm] using ht
  · intro ht p hp hcard
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [hmin, Finset.prod_insert hqs, Nat.cast_mul, id_eq,
        mul_pow, pow_succ, mul_assoc, mul_comm, mul_left_comm] using ht
    · have hpq : ¬p ≤ q :=
        not_le.mpr (lt_of_le_of_ne (hqmin p hp) (Ne.symm fun h => hqs (h ▸ hp)))
      have hf : (insert q s).filter (fun r => p ≤ r) =
          s.filter (fun r => p ≤ r) := by simp [Finset.filter_insert, hpq]
      rw [hf] at hcard ⊢
      exact hs p hp hcard

private theorem upper_insert_test {L : ℝ} {q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hqmin : ∀ p ∈ s, q ≤ p)
    (hs : UpperAdmissibleSet L s) (heven : Even s.card) :
    UpperAdmissibleSet L (insert q s) ↔
      ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3 < L := by
  have hmin : (insert q s).filter (fun r => q ≤ r) = insert q s :=
    Finset.filter_eq_self.mpr fun r hr => by
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact le_rfl
      · exact hqmin r hr
  constructor
  · intro h
    have ht := h q (Finset.mem_insert_self q s) (by
      simp only [hmin, Finset.card_insert_of_notMem hqs, Nat.even_add_one]
      exact not_not_intro heven)
    simpa only [hmin, Finset.prod_insert hqs, Nat.cast_mul, id_eq,
      mul_pow, pow_succ, mul_assoc, mul_comm, mul_left_comm] using ht
  · intro ht p hp hcard
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [hmin, Finset.prod_insert hqs, Nat.cast_mul, id_eq,
        mul_pow, pow_succ, mul_assoc, mul_comm, mul_left_comm] using ht
    · have hpq : ¬p ≤ q :=
        not_le.mpr (lt_of_le_of_ne (hqmin p hp) (Ne.symm fun h => hqs (h ▸ hp)))
      have hf : (insert q s).filter (fun r => p ≤ r) =
          s.filter (fun r => p ≤ r) := by simp [Finset.filter_insert, hpq]
      rw [hf] at hcard ⊢
      exact hs p hp hcard

/-- Exact signed cancellation, including the failed even-prefix boundary. -/
theorem lowerSetWeight_pair_eq_boundary {L : ℝ} {q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hq : q.Prime) (hqL : (q : ℝ) < L)
    (hqmin : ∀ p ∈ s, q ≤ p) :
    setWeight L s + setWeight L (insert q s) =
      -(if LowerBoundary L q s then 1 else 0) := by
  have hcard : Even (insert q s).card ↔ ¬Even s.card := by
    rw [Finset.card_insert_of_notMem hqs, Nat.even_add_one]
  by_cases hbase : ((s.prod id : ℕ) : ℝ) < L ∧ LowerAdmissibleSet L s
  · by_cases heven : Even s.card
    · have hins := And.intro
        (prod_insert_min_lt_of_even hqs hq hqL hqmin hbase.2 heven)
        (admissible_insert_min_of_even hqs hqmin hbase.2 heven)
      have hb : ¬LowerBoundary L q s := fun h => h.2.2.1 heven
      simp only [setWeight, if_pos hbase, if_pos hins, if_neg hb, hcard]
      simp [heven]
    · have htest := lower_insert_test hqs hqmin hbase.2 heven
      by_cases hc : ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3 < L
      · have hins := And.intro (insert_cut_of_cube hqs hq hc) (htest.mpr hc)
        have hb : ¬LowerBoundary L q s := fun h => (not_le.mpr hc) h.2.2.2
        simp only [setWeight, if_pos hbase, if_pos hins, if_neg hb, hcard]
        simp [heven]
      · have hins : ¬LowerAdmissibleSet L (insert q s) := fun h => hc (htest.mp h)
        have hb : LowerBoundary L q s := ⟨hbase.1, hbase.2, heven, le_of_not_gt hc⟩
        simp only [setWeight, if_pos hbase, hins, and_false, if_false, if_neg heven,
          if_pos hb]
        norm_num
  · have hins : ¬((((insert q s).prod id : ℕ) : ℝ) < L ∧
        LowerAdmissibleSet L (insert q s)) :=
      fun h => hbase ⟨insert_cut_back hqs hq h.1,
        admissible_of_insert_min hqs hqmin h.2⟩
    have hb : ¬LowerBoundary L q s := fun h => hbase ⟨h.1, h.2.1⟩
    simp only [setWeight, if_neg hbase, if_neg hins, if_neg hb]
    norm_num

/-- Exact signed cancellation, including the failed odd-prefix boundary. -/
theorem upperSetWeight_pair_eq_boundary {L : ℝ} {q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hq : q.Prime) (hqmin : ∀ p ∈ s, q ≤ p) :
    upperSetWeight L s + upperSetWeight L (insert q s) =
      if UpperBoundary L q s then 1 else 0 := by
  have hcard : Even (insert q s).card ↔ ¬Even s.card := by
    rw [Finset.card_insert_of_notMem hqs, Nat.even_add_one]
  by_cases hbase : ((s.prod id : ℕ) : ℝ) < L ∧ UpperAdmissibleSet L s
  · by_cases heven : Even s.card
    · have htest := upper_insert_test hqs hqmin hbase.2 heven
      by_cases hc : ((s.prod id : ℕ) : ℝ) * (q : ℝ) ^ 3 < L
      · have hins := And.intro (insert_cut_of_cube hqs hq hc) (htest.mpr hc)
        have hb : ¬UpperBoundary L q s := fun h => (not_le.mpr hc) h.2.2.2
        simp only [upperSetWeight, if_pos hbase, if_pos hins, if_neg hb, hcard]
        simp [heven]
      · have hins : ¬UpperAdmissibleSet L (insert q s) := fun h => hc (htest.mp h)
        have hb : UpperBoundary L q s := ⟨hbase.1, hbase.2, heven, le_of_not_gt hc⟩
        simp only [upperSetWeight, if_pos hbase, hins, and_false, if_false,
          if_pos heven, if_pos hb]
        norm_num
    · have hins := And.intro
        (prod_insert_min_lt_of_odd hqs hq hqmin hbase.2 heven)
        (upperAdmissible_insert_min_of_odd hqs hqmin hbase.2 heven)
      have hb : ¬UpperBoundary L q s := fun h => heven h.2.2.1
      simp only [upperSetWeight, if_pos hbase, if_pos hins, if_neg hb, hcard]
      simp [heven]
  · have hins : ¬((((insert q s).prod id : ℕ) : ℝ) < L ∧
        UpperAdmissibleSet L (insert q s)) :=
      fun h => hbase ⟨insert_cut_back hqs hq h.1,
        upperAdmissible_of_insert_min hqs hqmin h.2⟩
    have hb : ¬UpperBoundary L q s := fun h => hbase ⟨h.1, h.2.1⟩
    simp only [upperSetWeight, if_neg hbase, if_neg hins, if_neg hb]
    norm_num

theorem lowerSetDensity_insert_min (g : ℕ → ℝ)
    {L : ℝ} {q : ℕ} {B : Finset ℕ} (hqB : q ∉ B) (hq : q.Prime)
    (hqL : (q : ℝ) < L) (hqmin : ∀ p ∈ B, q ≤ p) :
    lowerSetDensity L g (insert q B) =
      (1 - g q) * lowerSetDensity L g B - g q * lowerBoundaryDensity L g q B := by
  rw [lowerSetDensity, sum_powerset_insert_pairs _ hqB]
  unfold lowerSetDensity lowerBoundaryDensity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  have hqs : q ∉ s := fun h => hqB (hsub h)
  have hp := lowerSetWeight_pair_eq_boundary hqs hq hqL
    (fun p hp => hqmin p (hsub hp))
  rw [Finset.prod_insert hqs]
  by_cases hb : LowerBoundary L q s
  · rw [if_pos hb] at hp ⊢
    linear_combination (g q * ∏ p ∈ s, g p) * hp
  · rw [if_neg hb] at hp ⊢
    linear_combination (g q * ∏ p ∈ s, g p) * hp

theorem upperSetDensity_insert_min (g : ℕ → ℝ)
    {L : ℝ} {q : ℕ} {B : Finset ℕ} (hqB : q ∉ B) (hq : q.Prime)
    (hqmin : ∀ p ∈ B, q ≤ p) :
    upperSetDensity L g (insert q B) =
      (1 - g q) * upperSetDensity L g B + g q * upperBoundaryDensity L g q B := by
  rw [upperSetDensity, sum_powerset_insert_pairs _ hqB]
  unfold upperSetDensity upperBoundaryDensity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  have hqs : q ∉ s := fun h => hqB (hsub h)
  have hp := upperSetWeight_pair_eq_boundary (L := L) hqs hq
    (fun p hp => hqmin p (hsub hp))
  rw [Finset.prod_insert hqs]
  by_cases hb : UpperBoundary L q s
  · rw [if_pos hb] at hp ⊢
    linear_combination (g q * ∏ p ∈ s, g p) * hp
  · rw [if_neg hb] at hp ⊢
    linear_combination (g q * ∏ p ∈ s, g p) * hp

/-- No complete multiplicativity is used: all divisors here are squarefree. -/
theorem lowerWeight_density_eq_setDensity {M : ℕ} (L : ℝ)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) (hM : Squarefree M) :
    ∑ d ∈ M.divisors, lowerWeight M L d * g d =
      lowerSetDensity L g M.primeFactors := by
  rw [sum_divisors_eq_sum_powerset hM]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  rw [lowerWeight_prod_eq_setWeight hM hsub]
  congr 1
  exact hg.map_prod_of_subset_primeFactors M s hsub

theorem upperWeight_density_eq_setDensity {M : ℕ} (L : ℝ)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) (hM : Squarefree M) :
    ∑ d ∈ M.divisors, upperWeight M L d * g d =
      upperSetDensity L g M.primeFactors := by
  rw [sum_divisors_eq_sum_powerset hM]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub := Finset.mem_powerset.mp hs
  rw [upperWeight_prod_eq_setWeight hM hsub]
  congr 1
  exact hg.map_prod_of_subset_primeFactors M s hsub

/-- Explicit boundary accumulation in increasing-prime order. Earlier
primes contribute their Euler factors; no error is defined by subtraction
from the target density. -/
noncomputable def lowerDensityDefect (L : ℝ) (g : ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | q :: ps => (1 - g q) * lowerDensityDefect L g ps +
      g q * lowerBoundaryDensity L g q ps.toFinset

noncomputable def upperDensityDefect (L : ℝ) (g : ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | q :: ps => (1 - g q) * upperDensityDefect L g ps +
      g q * upperBoundaryDensity L g q ps.toFinset

/-- The exact lower density is the Euler product minus its cubic boundaries. -/
theorem lowerSetDensity_eq_euler_sub_defect (g : ℕ → ℝ)
    {L : ℝ} (hL : 1 < L) (ps : List ℕ) (hnd : ps.Nodup)
    (hsorted : ps.Pairwise (· ≤ ·)) (hp : ∀ p ∈ ps, p.Prime)
    (hcut : ∀ p ∈ ps, (p : ℝ) < L) :
    lowerSetDensity L g ps.toFinset =
      (∏ p ∈ ps.toFinset, (1 - g p)) - lowerDensityDefect L g ps := by
  induction ps with
  | nil =>
      simp [lowerSetDensity, setWeight, LowerAdmissibleSet, hL, lowerDensityDefect]
  | cons q ps ih =>
      obtain ⟨hqnot, hnd⟩ := List.nodup_cons.mp hnd
      obtain ⟨hqmin, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hqB : q ∉ ps.toFinset := by simpa using hqnot
      simp only [List.toFinset_cons]
      rw [lowerSetDensity_insert_min g hqB (hp q (by simp)) (hcut q (by simp))
        (fun p h => hqmin p (List.mem_toFinset.mp h)), Finset.prod_insert hqB,
        ih hnd hsorted (fun p h => hp p (by simp [h])) (fun p h => hcut p (by simp [h])),
        lowerDensityDefect]
      ring

/-- The exact upper density is the Euler product plus its cubic boundaries. -/
theorem upperSetDensity_eq_euler_add_defect (g : ℕ → ℝ)
    {L : ℝ} (hL : 1 < L) (ps : List ℕ) (hnd : ps.Nodup)
    (hsorted : ps.Pairwise (· ≤ ·)) (hp : ∀ p ∈ ps, p.Prime) :
    upperSetDensity L g ps.toFinset =
      (∏ p ∈ ps.toFinset, (1 - g p)) + upperDensityDefect L g ps := by
  induction ps with
  | nil =>
      simp [upperSetDensity, upperSetWeight, UpperAdmissibleSet, hL, upperDensityDefect]
  | cons q ps ih =>
      obtain ⟨hqnot, hnd⟩ := List.nodup_cons.mp hnd
      obtain ⟨hqmin, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hqB : q ∉ ps.toFinset := by simpa using hqnot
      simp only [List.toFinset_cons]
      rw [upperSetDensity_insert_min g hqB (hp q (by simp))
        (fun p h => hqmin p (List.mem_toFinset.mp h)), Finset.prod_insert hqB,
        ih hnd hsorted (fun p h => hp p (by simp [h])), upperDensityDefect]
      ring

theorem lowerBoundaryDensity_nonneg {L : ℝ} {g : ℕ → ℝ}
    {q : ℕ} {B : Finset ℕ} (hg : ∀ p ∈ B, 0 ≤ g p) :
    0 ≤ lowerBoundaryDensity L g q B := by
  apply Finset.sum_nonneg
  intro s hs
  split
  · exact Finset.prod_nonneg fun p hp => hg p (Finset.mem_powerset.mp hs hp)
  · exact le_rfl

theorem upperBoundaryDensity_nonneg {L : ℝ} {g : ℕ → ℝ}
    {q : ℕ} {B : Finset ℕ} (hg : ∀ p ∈ B, 0 ≤ g p) :
    0 ≤ upperBoundaryDensity L g q B := by
  apply Finset.sum_nonneg
  intro s hs
  split
  · exact Finset.prod_nonneg fun p hp => hg p (Finset.mem_powerset.mp hs hp)
  · exact le_rfl

theorem lowerDensityDefect_nonneg {L : ℝ} {g : ℕ → ℝ}
    (ps : List ℕ) (hg : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1) :
    0 ≤ lowerDensityDefect L g ps := by
  induction ps with
  | nil => exact le_rfl
  | cons q ps ih =>
      have hq := hg q (by simp)
      have ht : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1 := fun p hp => hg p (by simp [hp])
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hq.2) (ih ht))
        (mul_nonneg hq.1 (lowerBoundaryDensity_nonneg
          (fun p hp => (ht p (List.mem_toFinset.mp hp)).1)))

theorem upperDensityDefect_nonneg {L : ℝ} {g : ℕ → ℝ}
    (ps : List ℕ) (hg : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1) :
    0 ≤ upperDensityDefect L g ps := by
  induction ps with
  | nil => exact le_rfl
  | cons q ps ih =>
      have hq := hg q (by simp)
      have ht : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1 := fun p hp => hg p (by simp [hp])
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hq.2) (ih ht))
        (mul_nonneg hq.1 (upperBoundaryDensity_nonneg
          (fun p hp => (ht p (List.mem_toFinset.mp hp)).1)))

/-- Finite exact density formula for the existing real-level lower weight. -/
theorem lowerWeight_density_eq_euler_sub_defect (B : Finset ℕ)
    {L : ℝ} (hL : 1 < L) (hB : ∀ p ∈ B, p.Prime)
    (hcut : ∀ p ∈ B, (p : ℝ) < L) {g : ArithmeticFunction ℝ}
    (hg : g.IsMultiplicative) :
    ∑ d ∈ (B.prod id).divisors, lowerWeight (B.prod id) L d * g d =
      (∏ p ∈ B, (1 - g p)) - lowerDensityDefect L g (B.sort (· ≤ ·)) := by
  have hpf : (B.prod id).primeFactors = B := by
    simpa only [id_eq] using Nat.primeFactors_prod hB
  rw [lowerWeight_density_eq_setDensity L hg (primeProduct_squarefree B hB), hpf]
  simpa using lowerSetDensity_eq_euler_sub_defect g hL (B.sort (· ≤ ·))
    (B.sort_nodup _) (B.pairwise_sort _)
    (fun p hp => hB p (by simpa using hp))
    (fun p hp => hcut p (by simpa using hp))

theorem upperWeight_density_eq_euler_add_defect (B : Finset ℕ)
    {L : ℝ} (hL : 1 < L) (hB : ∀ p ∈ B, p.Prime)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    ∑ d ∈ (B.prod id).divisors, upperWeight (B.prod id) L d * g d =
      (∏ p ∈ B, (1 - g p)) + upperDensityDefect L g (B.sort (· ≤ ·)) := by
  have hpf : (B.prod id).primeFactors = B := by
    simpa only [id_eq] using Nat.primeFactors_prod hB
  rw [upperWeight_density_eq_setDensity L hg (primeProduct_squarefree B hB), hpf]
  simpa using upperSetDensity_eq_euler_add_defect g hL (B.sort (· ≤ ·))
    (B.sort_nodup _) (B.pairwise_sort _)
    (fun p hp => hB p (by simpa using hp))

/-- The density convention in (22); division is pointwise, not convolution. -/
noncomputable def primeDensity (ω : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => ω n / (n : ℝ), by simp⟩

@[simp]
theorem primeDensity_apply (ω : ArithmeticFunction ℝ) (n : ℕ) :
    primeDensity ω n = ω n / (n : ℝ) := rfl

theorem primeDensity_isMultiplicative {ω : ArithmeticFunction ℝ}
    (hω : ω.IsMultiplicative) : (primeDensity ω).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [hω.map_one]
  · intro m n hmn
    simp only [primeDensity_apply, hω.map_mul_of_coprime hmn, Nat.cast_mul,
      div_mul_div_comm]

theorem lowerSmallWeight_density_eq_euler_sub_defect (P : Finset ℕ)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    ∑ d ∈ ((geometricSmallPrimes P D ε).prod id).divisors,
        lowerSmallWeight P D ε d * g d =
      (∏ p ∈ geometricSmallPrimes P D ε, (1 - g p)) -
        lowerDensityDefect (D ^ ε) g ((geometricSmallPrimes P D ε).sort (· ≤ ·)) :=
  lowerWeight_density_eq_euler_sub_defect _
    (Real.one_lt_rpow (by linarith) hε) (smallPrimes_prime P D ε)
    (fun _ hp => smallPrime_lt_level P (by linarith) hε.le (by linarith) hp) hg

theorem upperSmallWeight_density_eq_euler_add_defect (P : Finset ℕ)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative) :
    ∑ d ∈ ((geometricSmallPrimes P D ε).prod id).divisors,
        upperSmallWeight P D ε d * g d =
      (∏ p ∈ geometricSmallPrimes P D ε, (1 - g p)) +
        upperDensityDefect (D ^ ε) g ((geometricSmallPrimes P D ε).sort (· ≤ ·)) :=
  upperWeight_density_eq_euler_add_defect _
    (Real.one_lt_rpow (by linarith) hε) (smallPrimes_prime P D ε) hg

/-- Both actual weights bracket the Euler product, with explicit nonnegative
defects. This is not a bound for their size. -/
theorem smallWeight_density_bracket (P : Finset ℕ)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative)
    (hg01 : ∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p ≤ 1) :
    (∑ d ∈ ((geometricSmallPrimes P D ε).prod id).divisors,
        lowerSmallWeight P D ε d * g d) ≤
      (∏ p ∈ geometricSmallPrimes P D ε, (1 - g p)) ∧
    (∏ p ∈ geometricSmallPrimes P D ε, (1 - g p)) ≤
      ∑ d ∈ ((geometricSmallPrimes P D ε).prod id).divisors,
        upperSmallWeight P D ε d * g d := by
  rw [lowerSmallWeight_density_eq_euler_sub_defect P hD hε hεsmall hg,
    upperSmallWeight_density_eq_euler_add_defect P hD hε hg]
  have hlo := lowerDensityDefect_nonneg (L := D ^ ε)
    ((geometricSmallPrimes P D ε).sort (· ≤ ·))
    (fun p hp => hg01 p (by simpa using hp))
  have hup := upperDensityDefect_nonneg (L := D ^ ε)
    ((geometricSmallPrimes P D ε).sort (· ≤ ·))
    (fun p hp => hg01 p (by simpa using hp))
  exact ⟨sub_le_self _ hlo, le_add_of_nonneg_right hup⟩

/-- The exact finite identity in the source's `ω(d)/d` convention, with
the original small weights on the left, not surrogate coefficients. -/
theorem smallWeight_source_density_identities (P : Finset ℕ)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    {ω : ArithmeticFunction ℝ} (hω : ω.IsMultiplicative) :
    (∑ d ∈ ((geometricSmallPrimes P D ε).prod id).divisors,
        lowerSmallWeight P D ε d * (ω d / (d : ℝ))) =
      (∏ p ∈ geometricSmallPrimes P D ε, (1 - ω p / (p : ℝ))) -
        lowerDensityDefect (D ^ ε) (primeDensity ω)
          ((geometricSmallPrimes P D ε).sort (· ≤ ·)) ∧
    (∑ d ∈ ((geometricSmallPrimes P D ε).prod id).divisors,
        upperSmallWeight P D ε d * (ω d / (d : ℝ))) =
      (∏ p ∈ geometricSmallPrimes P D ε, (1 - ω p / (p : ℝ))) +
        upperDensityDefect (D ^ ε) (primeDensity ω)
          ((geometricSmallPrimes P D ε).sort (· ≤ ·)) :=
  ⟨lowerSmallWeight_density_eq_euler_sub_defect P hD hε hεsmall
      (primeDensity_isMultiplicative hω),
    upperSmallWeight_density_eq_euler_add_defect P hD hε
      (primeDensity_isMultiplicative hω)⟩

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
