import MathlibNt.SieveTheory.LiLiuGoldbachErrorFoundations
import MathlibNt.SieveTheory.LiLiuGoldbachWeightInitial

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachWeightInitialBudget (P : Prop) : Decidable P :=
  Classical.propDecidable P

private theorem literalH_le_dvdFiberCard_budget
    (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    literalH A M d x ≤ ((A.filter fun n => d ∣ n).card : ℤ) := by
  unfold literalH
  exact_mod_cast Finset.card_le_card
    (Finset.monotone_filter_right A (p := literalHPoint M d x)
      (q := fun n => d ∣ n) (fun _ _ hn => hn.1))

private theorem literalH_eq_zero_of_large_divisor_budget
    (A : Finset ℕ) (M d N : ℕ) (x : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N) (hNd : N < d) :
    literalH A M d x = 0 := by
  unfold literalH
  have hempty : A.filter (literalHPoint M d x) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun n hn hp =>
      (not_le_of_gt (hA n hn).2)
        (hNd.le.trans (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (hA n hn).1) hp.1))
  simp only [hempty, Finset.card_empty, Nat.cast_zero]

private theorem left_dvd_of_pair_dvd_budget
    {a b n : ℕ}
    (h : a * b ∣ n) :
    a ∣ n := by
  exact dvd_trans (dvd_mul_right a b) h

private theorem right_dvd_of_pair_dvd_budget
    {a b n : ℕ}
    (h : a * b ∣ n) :
    b ∣ n := by
  exact dvd_trans (dvd_mul_left b a) h

private noncomputable def goldbachWeightEndpointPrimeCarrier (N : ℕ) (z b : ℝ) : Finset ℕ :=
  (goldbachClosedPrimes N z b).filter (fun p : ℕ => b ≤ (p : ℝ))

private theorem goldbachWeightEndpointPrimeCarrier_cast_eq
    {N p : ℕ} {z b : ℝ}
    (hp : p ∈ goldbachWeightEndpointPrimeCarrier N z b) :
    (p : ℝ) = b := by
  rcases Finset.mem_filter.mp hp with ⟨hpClosed, hbp⟩
  rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨_, _, _, hpb⟩
  exact le_antisymm hpb hbp

private theorem goldbachWeightEndpointPrimeCarrier_subsingleton
    {N u v : ℕ} {z b : ℝ}
    (hu : u ∈ goldbachWeightEndpointPrimeCarrier N z b)
    (hv : v ∈ goldbachWeightEndpointPrimeCarrier N z b) :
    u = v := by
  have huv : (u : ℝ) = (v : ℝ) := by
    calc
      (u : ℝ) = b := goldbachWeightEndpointPrimeCarrier_cast_eq hu
      _ = (v : ℝ) := (goldbachWeightEndpointPrimeCarrier_cast_eq hv).symm
  exact_mod_cast huv

theorem goldbachWeightD6_le_goldbachQA
    (A : Finset ℕ) (N : ℕ) (z b : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N) :
    goldbachWeightD6 A N z b ≤ goldbachQA A N z := by
  unfold goldbachWeightD6 goldbachQA
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachHalfOpenPrimes N z b)
      (fun r : ℕ => r ^ 2 ≤ N)
      (fun r => literalH A N (r ^ 2) z)
  rw [← hsplit]
  have hmain :
      ∑ r ∈ (goldbachHalfOpenPrimes N z b).filter (fun r : ℕ => r ^ 2 ≤ N),
        literalH A N (r ^ 2) z
        ≤
      ∑ q ∈ goldbachSquarePrimes N z, ((A.filter fun n => q ^ 2 ∣ n).card : ℤ) := by
    have hsubset :
        (goldbachHalfOpenPrimes N z b).filter (fun r : ℕ => r ^ 2 ≤ N) ⊆ goldbachSquarePrimes N z := by
      intro r hr
      rcases Finset.mem_filter.mp hr with ⟨hrHalf, hrSq⟩
      rcases mem_goldbachHalfOpenPrimes_iff.mp hrHalf with ⟨hrPrime, _, hrz, _⟩
      exact mem_goldbachSquarePrimes_iff.mpr ⟨hrPrime, hrz, hrSq⟩
    have h1 :
        ∑ r ∈ (goldbachHalfOpenPrimes N z b).filter (fun r : ℕ => r ^ 2 ≤ N),
          literalH A N (r ^ 2) z
          ≤
        ∑ r ∈ (goldbachHalfOpenPrimes N z b).filter (fun r : ℕ => r ^ 2 ≤ N),
          ((A.filter fun n => r ^ 2 ∣ n).card : ℤ) := by
      refine Finset.sum_le_sum ?_
      intro r hr
      exact literalH_le_dvdFiberCard_budget A N (r ^ 2) z
    have h2 :
        ∑ r ∈ (goldbachHalfOpenPrimes N z b).filter (fun r : ℕ => r ^ 2 ≤ N),
          ((A.filter fun n => r ^ 2 ∣ n).card : ℤ)
          ≤
        ∑ q ∈ goldbachSquarePrimes N z, ((A.filter fun n => q ^ 2 ∣ n).card : ℤ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro q hq hqNot
      exact_mod_cast Nat.zero_le ((A.filter fun n => q ^ 2 ∣ n).card)
    exact h1.trans h2
  have hzero :
      ∑ r ∈ (goldbachHalfOpenPrimes N z b).filter (fun r : ℕ => ¬r ^ 2 ≤ N),
        literalH A N (r ^ 2) z = 0 := by
    refine Finset.sum_eq_zero ?_
    intro r hr
    rcases Finset.mem_filter.mp hr with ⟨_, hrSq⟩
    exact literalH_eq_zero_of_large_divisor_budget A N (r ^ 2) N z hA (lt_of_not_ge hrSq)
  rw [hzero, add_zero]
  exact hmain

theorem goldbachWeightD6_real_le_two_mul_div_z
    (A : Finset ℕ) (N : ℕ) (z b : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N) (hz : 2 ≤ z) :
    (goldbachWeightD6 A N z b : ℝ) ≤ 2 * (N : ℝ) / z := by
  have hD6QA : (goldbachWeightD6 A N z b : ℝ) ≤ goldbachQA A N z := by
    exact_mod_cast goldbachWeightD6_le_goldbachQA A N z b hA
  exact hD6QA.trans (goldbachQA_real_le_two_mul_div A N z hA hz)

private theorem goldbachWeightB6pair_slice_le_twenty_mul_card
    (A : Finset ℕ) (N s : ℕ) {κ z : ℝ}
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ) :
    (∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z) ≤
      20 * ((A.filter fun n => s ∣ n).card : ℤ) := by
  let T := goldbachClosedPrimes N z (s : ℝ)
  let D := fun n : ℕ => T.filter (fun p : ℕ => p ∣ n)
  have hpointwise :
      ∀ n ∈ A,
        (∑ r ∈ T, if literalHPoint N (r * s) z n then (1 : ℤ) else 0) ≤
          if s ∣ n then (20 : ℤ) else 0 := by
    intro n hnA
    by_cases hsn : s ∣ n
    · have hDsubset :
          D n ⊆ largePrimeDivisors n z := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpT, hpdvd⟩
        rcases mem_goldbachClosedPrimes_iff.mp hpT with ⟨hpPrime, _, hpz, _⟩
        have hn0 : n ≠ 0 := by
          exact ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hA n hnA).1)
        change p ∈ n.primeFactors.filter (fun q : ℕ => z ≤ (q : ℝ))
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hpPrime, hpdvd, hn0⟩, hpz⟩
      have hDtwenty :
          (D n).card ≤ 20 := by
        have hlarge :
            (largePrimeDivisors n z).card ≤ 20 := by
          rw [hz]
          exact largePrimeDivisors_card_le_twenty (hA n hnA).1 (hA n hnA).2 hk
        exact le_trans (Finset.card_le_card hDsubset) hlarge
      have hcount :
          (∑ r ∈ T, if literalHPoint N (r * s) z n then (1 : ℤ) else 0) ≤ ((D n).card : ℤ) := by
        have hle :
            (∑ r ∈ T, if literalHPoint N (r * s) z n then (1 : ℤ) else 0) ≤
              ∑ r ∈ T, if r ∣ n then (1 : ℤ) else 0 := by
          refine Finset.sum_le_sum ?_
          intro r hr
          by_cases hP : literalHPoint N (r * s) z n
          · have hrd : r ∣ n := left_dvd_of_pair_dvd_budget hP.1
            simp [hP, hrd]
          · by_cases hrd : r ∣ n <;> simp [hP, hrd]
        have hcard :
            (∑ r ∈ T, if r ∣ n then (1 : ℤ) else 0) = ((D n).card : ℤ) := by
          exact Finset.sum_boole (fun r : ℕ => r ∣ n) T
        exact hle.trans (le_of_eq hcard)
      have htwenty : ((D n).card : ℤ) ≤ 20 := by
        exact_mod_cast hDtwenty
      have hbound :
          (∑ r ∈ T, if literalHPoint N (r * s) z n then (1 : ℤ) else 0) ≤ 20 := by
        exact hcount.trans htwenty
      simpa [hsn] using hbound
    · have hzero :
          (∑ r ∈ T, if literalHPoint N (r * s) z n then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        by_cases hP : literalHPoint N (r * s) z n
        · exfalso
          exact hsn (right_dvd_of_pair_dvd_budget hP.1)
        · simp [hP]
      simp [hsn, hzero]
  calc
    (∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z)
        = ∑ r ∈ T, ∑ n ∈ A, if literalHPoint N (r * s) z n then (1 : ℤ) else 0 := by
            simp_rw [literalH_eq_sum_indicator]
            rfl
    _ = ∑ n ∈ A, ∑ r ∈ T, if literalHPoint N (r * s) z n then (1 : ℤ) else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ n ∈ A, if s ∣ n then (20 : ℤ) else 0 := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact hpointwise n hn
    _ = 20 * ((A.filter fun n => s ∣ n).card : ℤ) := by
          calc
            (∑ n ∈ A, if s ∣ n then (20 : ℤ) else 0) =
                ∑ n ∈ A, ((if s ∣ n then (1 : ℤ) else 0) * 20) := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  by_cases hsn : s ∣ n <;> simp [hsn]
            _ = (∑ n ∈ A, if s ∣ n then (1 : ℤ) else 0) * 20 := by
                  rw [Finset.sum_mul]
            _ = 20 * ((A.filter fun n => s ∣ n).card : ℤ) := by
                  rw [Finset.sum_boole (fun n : ℕ => s ∣ n) A]
                  ring

theorem goldbachWeightB6pair_real_le_twenty_mul_div_b
    (A : Finset ℕ) (N : ℕ) {κ z b : ℝ}
    (hN : 1 ≤ N)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ)
    (_hz2 : 2 ≤ z)
    (hzb : z ≤ b) :
    (goldbachWeightB6pair A N z b : ℝ) ≤ 20 * (N : ℝ) / b := by
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hz0 : 0 < z := by
    rw [hz]
    exact Real.rpow_pos_of_pos hN0 _
  have hb0 : 0 < b := lt_of_lt_of_le hz0 hzb
  let U := goldbachWeightEndpointPrimeCarrier N z b
  have huniq :
      ∀ {u v : ℕ}, u ∈ U → v ∈ U → u = v := by
    intro u v hu hv
    exact goldbachWeightEndpointPrimeCarrier_subsingleton hu hv
  by_cases hU : U = ∅
  · have hU' :
        (goldbachClosedPrimes N z b).filter (fun p : ℕ => b ≤ (p : ℝ)) = ∅ := by
      simpa [goldbachWeightEndpointPrimeCarrier, U] using hU
    unfold goldbachWeightB6pair
    rw [hU']
    simp
    positivity
  · obtain ⟨s, hsU⟩ : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
    have hUeq : U = {s} := by
      ext p
      constructor
      · intro hp
        exact Finset.mem_singleton.mpr (huniq hp hsU)
      · intro hp
        rcases Finset.mem_singleton.mp hp with rfl
        exact hsU
    have hsEq : (s : ℝ) = b := goldbachWeightEndpointPrimeCarrier_cast_eq hsU
    rcases Finset.mem_filter.mp hsU with ⟨hsClosed, _⟩
    rcases mem_goldbachClosedPrimes_iff.mp hsClosed with ⟨hsPrime, _, _, _⟩
    have hspos : 0 < s := hsPrime.pos
    have hslice :
        ((∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z : ℤ) : ℝ) ≤
          20 * ((A.filter fun n => s ∣ n).card : ℝ) := by
      exact_mod_cast goldbachWeightB6pair_slice_le_twenty_mul_card A N s hA hk hz
    have hcount :
        ((A.filter fun n => s ∣ n).card : ℝ) ≤ (N : ℝ) / s := by
      exact card_filter_dvd_le_div_real A N s
        (fun n hn => ⟨(hA n hn).1, (hA n hn).2.le⟩)
        hspos
    calc
      (goldbachWeightB6pair A N z b : ℝ) =
          ((∑ r ∈ goldbachClosedPrimes N z (s : ℝ), literalH A N (r * s) z : ℤ) : ℝ) := by
            change ((∑ p ∈ U,
              ∑ r ∈ goldbachClosedPrimes N z (p : ℝ), literalH A N (r * p) z : ℤ) : ℝ) = _
            simp [U, hUeq]
      _ ≤ 20 * ((A.filter fun n => s ∣ n).card : ℝ) := hslice
      _ ≤ 20 * ((N : ℝ) / s) := by
            gcongr
      _ = 20 * (N : ℝ) / b := by
            rw [hsEq]
            ring

private theorem goldbachWeightB7_slice_le_twenty_mul_card
    (A : Finset ℕ) (N r : ℕ) {κ z b c : ℝ}
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ)
    (hzb : z ≤ b) :
    (∑ t ∈ goldbachClosedPrimes N b c, literalH A N (r * t) z) ≤
      20 * ((A.filter fun n => r ∣ n).card : ℤ) := by
  let T := goldbachClosedPrimes N b c
  let D := fun n : ℕ => T.filter (fun p : ℕ => p ∣ n)
  have hpointwise :
      ∀ n ∈ A,
        (∑ t ∈ T, if literalHPoint N (r * t) z n then (1 : ℤ) else 0) ≤
          if r ∣ n then (20 : ℤ) else 0 := by
    intro n hnA
    by_cases hrn : r ∣ n
    · have hDsubset :
          D n ⊆ largePrimeDivisors n z := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpT, hpdvd⟩
        rcases mem_goldbachClosedPrimes_iff.mp hpT with ⟨hpPrime, _, hbp, _⟩
        have hpz : z ≤ (p : ℝ) := hzb.trans hbp
        have hn0 : n ≠ 0 := by
          exact ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hA n hnA).1)
        change p ∈ n.primeFactors.filter (fun q : ℕ => z ≤ (q : ℝ))
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hpPrime, hpdvd, hn0⟩, hpz⟩
      have hDtwenty :
          (D n).card ≤ 20 := by
        have hlarge :
            (largePrimeDivisors n z).card ≤ 20 := by
          rw [hz]
          exact largePrimeDivisors_card_le_twenty (hA n hnA).1 (hA n hnA).2 hk
        exact le_trans (Finset.card_le_card hDsubset) hlarge
      have hcount :
          (∑ t ∈ T, if literalHPoint N (r * t) z n then (1 : ℤ) else 0) ≤ ((D n).card : ℤ) := by
        have hle :
            (∑ t ∈ T, if literalHPoint N (r * t) z n then (1 : ℤ) else 0) ≤
              ∑ t ∈ T, if t ∣ n then (1 : ℤ) else 0 := by
          refine Finset.sum_le_sum ?_
          intro t ht
          by_cases hP : literalHPoint N (r * t) z n
          · have htd : t ∣ n := right_dvd_of_pair_dvd_budget hP.1
            simp [hP, htd]
          · by_cases htd : t ∣ n <;> simp [hP, htd]
        have hcard :
            (∑ t ∈ T, if t ∣ n then (1 : ℤ) else 0) = ((D n).card : ℤ) := by
          exact Finset.sum_boole (fun t : ℕ => t ∣ n) T
        exact hle.trans (le_of_eq hcard)
      have htwenty : ((D n).card : ℤ) ≤ 20 := by
        exact_mod_cast hDtwenty
      have hbound :
          (∑ t ∈ T, if literalHPoint N (r * t) z n then (1 : ℤ) else 0) ≤ 20 := by
        exact hcount.trans htwenty
      simpa [hrn] using hbound
    · have hzero :
          (∑ t ∈ T, if literalHPoint N (r * t) z n then (1 : ℤ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        by_cases hP : literalHPoint N (r * t) z n
        · exfalso
          exact hrn (left_dvd_of_pair_dvd_budget hP.1)
        · simp [hP]
      simp [hrn, hzero]
  calc
    (∑ t ∈ goldbachClosedPrimes N b c, literalH A N (r * t) z)
        = ∑ t ∈ T, ∑ n ∈ A, if literalHPoint N (r * t) z n then (1 : ℤ) else 0 := by
            simp_rw [literalH_eq_sum_indicator]
            rfl
    _ = ∑ n ∈ A, ∑ t ∈ T, if literalHPoint N (r * t) z n then (1 : ℤ) else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ n ∈ A, if r ∣ n then (20 : ℤ) else 0 := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact hpointwise n hn
    _ = 20 * ((A.filter fun n => r ∣ n).card : ℤ) := by
          calc
            (∑ n ∈ A, if r ∣ n then (20 : ℤ) else 0) =
                ∑ n ∈ A, ((if r ∣ n then (1 : ℤ) else 0) * 20) := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  by_cases hrn : r ∣ n <;> simp [hrn]
            _ = (∑ n ∈ A, if r ∣ n then (1 : ℤ) else 0) * 20 := by
                  rw [Finset.sum_mul]
            _ = 20 * ((A.filter fun n => r ∣ n).card : ℤ) := by
                  rw [Finset.sum_boole (fun n : ℕ => r ∣ n) A]
                  ring

theorem goldbachWeightB7_real_le_twenty_mul_div_b
    (A : Finset ℕ) (N : ℕ) {κ z b c : ℝ}
    (hN : 1 ≤ N)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ)
    (_hz2 : 2 ≤ z)
    (hzb : z ≤ b)
    (_hbc : b ≤ c) :
    (goldbachWeightB7 A N z b c : ℝ) ≤ 20 * (N : ℝ) / b := by
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hz0 : 0 < z := by
    rw [hz]
    exact Real.rpow_pos_of_pos hN0 _
  have hb0 : 0 < b := lt_of_lt_of_le hz0 hzb
  let U := goldbachWeightEndpointPrimeCarrier N z b
  have huniq :
      ∀ {u v : ℕ}, u ∈ U → v ∈ U → u = v := by
    intro u v hu hv
    exact goldbachWeightEndpointPrimeCarrier_subsingleton hu hv
  by_cases hU : U = ∅
  · have hU' :
        (goldbachClosedPrimes N z b).filter (fun p : ℕ => b ≤ (p : ℝ)) = ∅ := by
      simpa [goldbachWeightEndpointPrimeCarrier, U] using hU
    unfold goldbachWeightB7
    rw [hU']
    simp
    positivity
  · obtain ⟨r, hrU⟩ : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
    have hUeq : U = {r} := by
      ext p
      constructor
      · intro hp
        exact Finset.mem_singleton.mpr (huniq hp hrU)
      · intro hp
        rcases Finset.mem_singleton.mp hp with rfl
        exact hrU
    have hrEq : (r : ℝ) = b := goldbachWeightEndpointPrimeCarrier_cast_eq hrU
    rcases Finset.mem_filter.mp hrU with ⟨hrClosed, _⟩
    rcases mem_goldbachClosedPrimes_iff.mp hrClosed with ⟨hrPrime, _, _, _⟩
    have hrpos : 0 < r := hrPrime.pos
    have hslice :
        ((∑ t ∈ goldbachClosedPrimes N b c, literalH A N (r * t) z : ℤ) : ℝ) ≤
          20 * ((A.filter fun n => r ∣ n).card : ℝ) := by
      exact_mod_cast goldbachWeightB7_slice_le_twenty_mul_card A N r hA hk hz hzb
    have hcount :
        ((A.filter fun n => r ∣ n).card : ℝ) ≤ (N : ℝ) / r := by
      exact card_filter_dvd_le_div_real A N r
        (fun n hn => ⟨(hA n hn).1, (hA n hn).2.le⟩)
        hrpos
    calc
      (goldbachWeightB7 A N z b c : ℝ) =
          ((∑ t ∈ goldbachClosedPrimes N b c, literalH A N (r * t) z : ℤ) : ℝ) := by
            change ((∑ t ∈ goldbachClosedPrimes N b c,
              ∑ p ∈ U, literalH A N (p * t) z : ℤ) : ℝ) = _
            simp [U, hUeq]
      _ ≤ 20 * ((A.filter fun n => r ∣ n).card : ℝ) := hslice
      _ ≤ 20 * ((N : ℝ) / r) := by
            gcongr
      _ = 20 * (N : ℝ) / b := by
            rw [hrEq]
            ring

theorem goldbachWeight_initial_error_real_le_forty_two_mul_div_z
    (A : Finset ℕ) (N : ℕ) {κ z b c : ℝ}
    (hN : 1 ≤ N)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ)
    (hz2 : 2 ≤ z)
    (hzb : z ≤ b)
    (hbc : b ≤ c) :
    (goldbachWeightD6 A N z b : ℝ) +
        goldbachWeightB6pair A N z b +
        goldbachWeightB7 A N z b c ≤
      42 * (N : ℝ) / z := by
  have hD6 :
      (goldbachWeightD6 A N z b : ℝ) ≤ 2 * (N : ℝ) / z :=
    goldbachWeightD6_real_le_two_mul_div_z A N z b hA hz2
  have hB6 :
      (goldbachWeightB6pair A N z b : ℝ) ≤ 20 * (N : ℝ) / b :=
    goldbachWeightB6pair_real_le_twenty_mul_div_b A N hN hA hk hz hz2 hzb
  have hB7 :
      (goldbachWeightB7 A N z b c : ℝ) ≤ 20 * (N : ℝ) / b :=
    goldbachWeightB7_real_le_twenty_mul_div_b A N hN hA hk hz hz2 hzb hbc
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hz0 : 0 < z := by
    rw [hz]
    exact Real.rpow_pos_of_pos hN0 _
  have hinv : b⁻¹ ≤ z⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hz0 hzb
  have hTwenty : 20 * (N : ℝ) / b ≤ 20 * (N : ℝ) / z := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (20 : ℝ) * (N : ℝ))
  have hForty :
      20 * (N : ℝ) / b + 20 * (N : ℝ) / b ≤
        20 * (N : ℝ) / z + 20 * (N : ℝ) / z := by
    linarith
  calc
    (goldbachWeightD6 A N z b : ℝ) +
        goldbachWeightB6pair A N z b +
        goldbachWeightB7 A N z b c
        ≤ 2 * (N : ℝ) / z + 20 * (N : ℝ) / b + 20 * (N : ℝ) / b := by
            linarith
    _ ≤ 2 * (N : ℝ) / z + (20 * (N : ℝ) / z + 20 * (N : ℝ) / z) := by
          linarith
    _ = 42 * (N : ℝ) / z := by
          ring

theorem goldbachWeight_initial_paid_real
    (A : Finset ℕ) (N : ℕ) {κ z b c : ℝ}
    (hN : 1 ≤ N)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N)
    (hk : (1 : ℝ) / 21 < κ)
    (hz : z = (N : ℝ) ^ κ)
    (hz2 : 2 ≤ z)
    (hzb : z ≤ b)
    (hbc : b ≤ c) :
    (goldbachS1 A N b - goldbachS3Closed A N b c : ℝ) ≥
      (goldbachS1 A N z - goldbachS3Closed A N z c : ℝ) +
        goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c -
        goldbachWeightG14 A N z b - goldbachWeightG15 A N z b c -
        42 * (N : ℝ) / z := by
  have href :
      (goldbachS1 A N b - goldbachS3Closed A N b c : ℝ) ≥
        (goldbachS1 A N z - goldbachS3Closed A N z c : ℝ) +
          goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c -
          goldbachWeightG14 A N z b - goldbachWeightG15 A N z b c -
          goldbachWeightD6 A N z b - goldbachWeightB6pair A N z b -
          goldbachWeightB7 A N z b c := by
    exact_mod_cast goldbachWeight_initial_refinement A N z b c hz2 hzb hbc
  have herror :
      (goldbachWeightD6 A N z b : ℝ) +
          goldbachWeightB6pair A N z b +
          goldbachWeightB7 A N z b c ≤
        42 * (N : ℝ) / z :=
    goldbachWeight_initial_error_real_le_forty_two_mul_div_z A N hN hA hk hz hz2 hzb hbc
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig