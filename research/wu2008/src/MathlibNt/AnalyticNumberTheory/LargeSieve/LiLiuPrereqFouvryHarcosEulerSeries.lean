import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEuler

/-! # The coefficientwise Euler logarithmic derivative -/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The geometric formal series in `c T^d`; no convergence is involved. -/
def harcosEulerGeometric (d : ℕ) (c : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ if d ∣ n then c ^ (n / d) else 0

theorem harcosEulerGeometric_step (d : ℕ) (hd : 0 < d) (c : ℂ) :
    harcosEulerGeometric d c =
      1 + PowerSeries.C c * PowerSeries.X ^ d * harcosEulerGeometric d c := by
  apply PowerSeries.ext
  intro n
  rw [map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hn : d ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hne : d + m ≠ 0 := by omega
    simp only [harcosEulerGeometric, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      if_neg hne, zero_add, Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
      Nat.dvd_add_self_left, Nat.add_div_left _ hd]
    split_ifs <;> simp [pow_succ, mul_comm]
  · have hlt : n < d := by omega
    simp only [if_neg hn, mul_zero, add_zero, harcosEulerGeometric,
      PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hz : n = 0
    · simp [hz]
    · rw [if_neg hz, if_neg]
      exact fun h ↦ (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h).not_gt hlt

theorem harcosEulerGeometric_mul (d : ℕ) (hd : 0 < d) (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X ^ d) * harcosEulerGeometric d c = 1 := by
  have h := harcosEulerGeometric_step d hd c
  linear_combination h

variable {p : ℕ} [Fact p.Prime]

/-- The formal series of the actual monic coefficient sums. -/
def harcosEulerSeries (η : (ZMod p)[X] →* ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (harcosEulerCoefficient η)

private def eulerMarkedSeries (η : (ZMod p)[X] →* ℂ) (k : (ZMod p)[X]) :
    PowerSeries ℂ :=
  PowerSeries.mk (harcosEulerMarked η k)

private theorem eulerMarkedSeries_step (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) :
    eulerMarkedSeries η k = PowerSeries.C (η k) * PowerSeries.X ^ k.natDegree *
      (harcosEulerSeries η + eulerMarkedSeries η k) := by
  apply PowerSeries.ext
  intro n
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hn : k.natDegree ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
      map_add, eulerMarkedSeries, harcosEulerSeries, PowerSeries.coeff_mk]
    exact harcosEulerMarked_add_degree η k hk hi m
  · simp only [if_neg hn, mul_zero, eulerMarkedSeries, PowerSeries.coeff_mk]
    exact harcosEulerMarked_eq_zero η k n (by omega)

theorem harcosEulerMarked_series (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) :
    PowerSeries.mk (harcosEulerMarked η k) =
      (harcosEulerGeometric k.natDegree (η k) - 1) * harcosEulerSeries η := by
  have hd : 0 < k.natDegree := hi.natDegree_pos
  have hs := eulerMarkedSeries_step η k hk hi
  have hg := harcosEulerGeometric_mul k.natDegree hd (η k)
  change eulerMarkedSeries η k = _
  calc
    eulerMarkedSeries η k =
        ((1 - PowerSeries.C (η k) * PowerSeries.X ^ k.natDegree) *
          harcosEulerGeometric k.natDegree (η k)) * eulerMarkedSeries η k := by rw [hg, one_mul]
    _ = (harcosEulerGeometric k.natDegree (η k) - 1) * harcosEulerSeries η := by
      linear_combination harcosEulerGeometric k.natDegree (η k) * hs -
        harcosEulerSeries η * hg

/-- A finite logarithmic-derivative series, containing all irreducibles up to the cutoff. -/
def harcosEulerLog (η : (ZMod p)[X] →* ℂ) (N : ℕ) : PowerSeries ℂ :=
  ∑ k ∈ harcosEulerPrimes p N, PowerSeries.C (k.natDegree : ℂ) *
    (harcosEulerGeometric k.natDegree (η k) - 1)

theorem harcosEulerLog_mul_coeff (η : (ZMod p)[X] →* ℂ) (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (harcosEulerLog η N * harcosEulerSeries η) =
      (n : ℂ) * harcosEulerCoefficient η n := by
  classical
  rw [harcosEulerLog, sum_mul, map_sum]
  calc
    _ = ∑ k ∈ harcosEulerPrimes p N,
        (k.natDegree : ℂ) * harcosEulerMarked η k n := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hkm, hki, _⟩ := (mem_harcosEulerPrimes N k).mp hk
      rw [mul_assoc, ← harcosEulerMarked_series η k hkm hki,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    _ = _ := by
      rw [harcosEuler_degree_marked η n]
      symm
      apply sum_subset
      · intro k hk
        obtain ⟨hkm, hki, hkd⟩ := (mem_harcosEulerPrimes n k).mp hk
        exact (mem_harcosEulerPrimes N k).mpr ⟨hkm, hki, hkd.trans hn⟩
      · intro k hk hkn
        obtain ⟨hkm, hki, _⟩ := (mem_harcosEulerPrimes N k).mp hk
        have hd : n < k.natDegree := by
          by_contra! h
          exact hkn ((mem_harcosEulerPrimes n k).mpr ⟨hkm, hki, h⟩)
        rw [harcosEulerMarked_eq_zero η k n hd, mul_zero]

/-- The actual irreducible divisor sum appearing in Harcos's equation (10). -/
def harcosEulerLogCoefficient (η : (ZMod p)[X] →* ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ d ∈ n.divisors, (d : ℂ) *
    ∑ k ∈ (harcosMonicPolynomials p d).filter Irreducible, η k ^ (n / d)

theorem harcosEulerLog_coeff (η : (ZMod p)[X] →* ℂ) (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (harcosEulerLog η N) = harcosEulerLogCoefficient η n := by
  classical
  by_cases hz : n = 0
  · subst n
    simp [harcosEulerLog, harcosEulerGeometric, harcosEulerLogCoefficient]
  rw [harcosEulerLog, map_sum]
  simp_rw [PowerSeries.coeff_C_mul, map_sub, harcosEulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg hz, sub_zero]
  rw [harcosEulerPrimes, sum_biUnion]
  · have hfilter : (range (N + 1)).filter (· ∣ n) = n.divisors := by
      ext d
      simp only [mem_filter, mem_range, Nat.mem_divisors]
      constructor
      · exact fun h ↦ ⟨h.2, hz⟩
      · intro h
        exact ⟨by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h.1; omega, h.1⟩
    calc
      _ = ∑ d ∈ range (N + 1), if d ∣ n then (d : ℂ) *
          ∑ k ∈ (harcosMonicPolynomials p d).filter Irreducible,
            η k ^ (n / d) else 0 := by
        apply sum_congr rfl
        intro d _
        by_cases hd : d ∣ n
        · rw [if_pos hd, mul_sum]
          apply sum_congr rfl
          intro k hk
          have hkdeg := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
          rw [hkdeg, if_pos hd]
        · rw [if_neg hd]
          apply sum_eq_zero
          intro k hk
          have hkdeg := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
          rw [hkdeg, if_neg hd, mul_zero]
      _ = _ := by rw [← sum_filter, hfilter]; rfl
  · intro d _ e _ hde
    apply disjoint_left.mpr
    intro k hk hk'
    have hd := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
    have he := ((mem_harcosMonicPolynomials e k).mp (mem_filter.mp hk').1).2
    exact hde (hd.symm.trans he)

/-- The finite Euler logarithmic recurrence, proved from polynomial UFD factorization. -/
theorem harcosEuler_recurrence (η : (ZMod p)[X] →* ℂ) (n : ℕ) :
    (n : ℂ) * harcosEulerCoefficient η n =
      ∑ j ∈ range (n + 1),
        harcosEulerLogCoefficient η j * harcosEulerCoefficient η (n - j) := by
  rw [← harcosEulerLog_mul_coeff η n n le_rfl, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ PowerSeries.coeff i (harcosEulerLog η n) *
        PowerSeries.coeff j (harcosEulerSeries η))]
  apply sum_congr rfl
  intro j hj
  rw [harcosEulerLog_coeff η n j (by simpa using mem_range.mp hj),
    harcosEulerSeries, PowerSeries.coeff_mk]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
