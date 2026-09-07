import MathlibNt.SieveTheory.LiLiuGoldbachClosedTriples
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Radical.NatInt

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachErrorFoundations (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The distinct prime divisors of `n` that lie at or above the real cutoff `z`. -/
noncomputable def largePrimeDivisors (n : ℕ) (z : ℝ) : Finset ℕ :=
  n.primeFactors.filter (fun p : ℕ => z ≤ (p : ℝ))

private theorem largePrimeDivisors_prod_dvd (n : ℕ) (z : ℝ) :
    ∏ p ∈ largePrimeDivisors n z, p ∣ n := by
  have hsubset : largePrimeDivisors n z ⊆ n.primeFactors := Finset.filter_subset _ _
  exact (Finset.prod_dvd_prod_of_subset _ _ id hsubset).trans (Nat.prod_primeFactors_dvd n)

private theorem largePrimeDivisors_prod_pos {n : ℕ} {z : ℝ} :
    0 < ∏ p ∈ largePrimeDivisors n z, p := by
  refine Finset.prod_pos ?_
  intro p hp
  exact Nat.pos_of_mem_primeFactors ((Finset.mem_filter.mp hp).1)

private theorem real_pow_card_le_prod_of_mem_ge (s : Finset ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hmem : ∀ p ∈ s, z ≤ (p : ℝ)) :
    z ^ s.card ≤ ∏ p ∈ s, (p : ℝ) := by
  classical
  revert hmem
  refine Finset.induction_on s ?_ ?_
  · intro hmem
    simp
  · intro a s ha hs hmem
    have haz : z ≤ (a : ℝ) := hmem a (by simp [ha])
    have hmem' : ∀ p ∈ s, z ≤ (p : ℝ) := by
      intro p hp
      exact hmem p (by simp [hp])
    have hs' := hs hmem'
    calc
      z ^ (insert a s).card = z ^ s.card * z := by simp [ha, pow_succ, mul_comm]
      _ ≤ (∏ p ∈ s, (p : ℝ)) * a := by
        gcongr
      _ = ∏ p ∈ insert a s, (p : ℝ) := by simp [ha, mul_comm]

/-- The filtered set of distinct prime divisors above `N^κ` has cardinality at most `20`
once `1 ≤ n < N` and `1 / 21 < κ`. -/
theorem largePrimeDivisors_card_le_twenty
    {n N : ℕ} {κ : ℝ}
    (hn1 : 1 ≤ n) (hnN : n < N) (hk : (1 : ℝ) / 21 < κ) :
    (largePrimeDivisors n ((N : ℝ) ^ κ)).card ≤ 20 := by
  let s := largePrimeDivisors n ((N : ℝ) ^ κ)
  have hNtwo : 2 ≤ N := by omega
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hNtwo
  have hk0 : 0 < κ := by nlinarith
  have hz0 : 0 ≤ (N : ℝ) ^ κ := Real.rpow_nonneg hN0 _
  have hs_ge :
      ((N : ℝ) ^ κ) ^ s.card ≤ ∏ p ∈ s, (p : ℝ) := by
    apply real_pow_card_le_prod_of_mem_ge
    · exact hz0
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  have hs_le_n_nat : ∏ p ∈ s, p ≤ n := by
    exact Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hn1) (largePrimeDivisors_prod_dvd n _)
  have hs_le_n : (∏ p ∈ s, (p : ℝ)) ≤ (n : ℝ) := by
    simpa using (show (((∏ p ∈ s, p : ℕ)) : ℝ) ≤ (n : ℝ) by exact_mod_cast hs_le_n_nat)
  by_contra hsCard
  have hs21 : 21 ≤ s.card := Nat.succ_le_of_lt (lt_of_not_ge hsCard)
  have hz1 : 1 < (N : ℝ) ^ κ := by
    simpa using Real.rpow_lt_rpow (show (0 : ℝ) ≤ 1 by positivity) hN1 hk0
  have hs21_ge : ((N : ℝ) ^ κ) ^ 21 ≤ ((N : ℝ) ^ κ) ^ s.card := by
    exact pow_le_pow_right₀ hz1.le hs21
  have hN_lt : (N : ℝ) < ((N : ℝ) ^ κ) ^ 21 := by
    have hk21 : (1 : ℝ) < κ * (21 : ℝ) := by
      nlinarith [hk]
    have hpowEq : ((N : ℝ) ^ κ) ^ 21 = (N : ℝ) ^ (κ * (21 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
      norm_num
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by simp
      _ < (N : ℝ) ^ (κ * (21 : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt hN1 hk21
      _ = ((N : ℝ) ^ κ) ^ 21 := hpowEq.symm
  have hN_lt_n : (N : ℝ) < (n : ℝ) := by
    exact lt_of_lt_of_le hN_lt <| le_trans hs21_ge <| le_trans hs_ge hs_le_n
  have hnN' : (n : ℝ) < N := by exact_mod_cast hnN
  exact (lt_irrefl (n : ℝ) (lt_trans hnN' hN_lt_n)).elim

/-- Generic finite divisibility fibre bound on a bounded positive carrier. -/
theorem card_filter_dvd_le_div
    (A : Finset ℕ) (N d : ℕ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N) (hd : 0 < d) :
    (A.filter fun n => d ∣ n).card ≤ N / d := by
  let s := A.filter fun n => d ∣ n
  have hmaps :
      Set.MapsTo (fun n : ℕ => n / d) s (Finset.Icc 1 (N / d)) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnA, hndvd⟩
    rcases hA n hnA with ⟨hn1, hnN⟩
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · obtain ⟨k, rfl⟩ := hndvd
      have hk0 : k ≠ 0 := by
        intro hk0
        subst hk0
        simp at hn1
      have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
      simpa [Nat.mul_div_cancel_left _ hd] using hk1
    · exact Nat.div_le_div_right hnN
  have hinj : Set.InjOn (fun n : ℕ => n / d) s := by
    intro n hn m hm hnm
    rcases Finset.mem_filter.mp hn with ⟨_, hndvd⟩
    rcases Finset.mem_filter.mp hm with ⟨_, hmdvd⟩
    have hn' : d * (n / d) = n := Nat.mul_div_cancel' hndvd
    have hm' : d * (m / d) = m := Nat.mul_div_cancel' hmdvd
    calc
      n = d * (n / d) := hn'.symm
      _ = d * (m / d) := by simpa using congrArg (fun k : ℕ => d * k) hnm
      _ = m := hm'
  calc
    s.card ≤ (Finset.Icc 1 (N / d)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = N / d := by
      by_cases hNd : N / d = 0
      · simp [hNd]
      · have hpos : 1 ≤ N / d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hNd)
        rw [Nat.card_Icc]
        omega

/-- Real-valued version of the divisibility fibre bound. -/
theorem card_filter_dvd_le_div_real
    (A : Finset ℕ) (N d : ℕ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n ≤ N) (hd : 0 < d) :
    ((A.filter fun n => d ∣ n).card : ℝ) ≤ (N : ℝ) / d := by
  exact (Nat.cast_le.mpr (card_filter_dvd_le_div A N d hA hd)).trans Nat.cast_div_le

/-- Prime carrier for the actual square mass `QA(A,N,z)`. -/
noncomputable def goldbachSquarePrimes (N : ℕ) (z : ℝ) : Finset ℕ :=
  (range (N + 1)).filter fun q : ℕ => q.Prime ∧ z ≤ (q : ℝ) ∧ q ^ 2 ≤ N

theorem mem_goldbachSquarePrimes_iff {N q : ℕ} {z : ℝ} :
    q ∈ goldbachSquarePrimes N z ↔ q.Prime ∧ z ≤ (q : ℝ) ∧ q ^ 2 ≤ N := by
  rw [goldbachSquarePrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hqPrime, hqz, hqSq⟩
    exact ⟨hqPrime, hqz, hqSq⟩
  · rintro ⟨hqPrime, hqz, hqSq⟩
    refine ⟨?_, hqPrime, hqz, hqSq⟩
    apply Nat.lt_succ_of_le
    calc
      q ≤ q ^ 2 := by
        calc
          q = q * 1 := by simp
          _ ≤ q * q := by gcongr; exact hqPrime.one_le
          _ = q ^ 2 := by rw [pow_two]
      _ ≤ N := hqSq

/-- Actual square-divisibility mass `QA(A,N,z)`. -/
noncomputable def goldbachQA (A : Finset ℕ) (N : ℕ) (z : ℝ) : ℤ :=
  ∑ q ∈ goldbachSquarePrimes N z, ((A.filter fun n => q ^ 2 ∣ n).card : ℤ)

theorem goldbachQA_nonneg (A : Finset ℕ) (N : ℕ) (z : ℝ) :
    0 ≤ goldbachQA A N z := by
  unfold goldbachQA
  refine Finset.sum_nonneg ?_
  intro q hq
  exact_mod_cast Nat.zero_le ((A.filter fun n => q ^ 2 ∣ n).card)

private theorem literalH_le_dvdFiberCard
    (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    literalH A M d x ≤ ((A.filter fun n => d ∣ n).card : ℤ) := by
  unfold literalH
  exact_mod_cast Finset.card_le_card
    (Finset.monotone_filter_right A (p := literalHPoint M d x)
      (q := fun n => d ∣ n) (fun _ _ hn => hn.1))

private theorem literalH_eq_zero_of_large_divisor
    (A : Finset ℕ) (M d N : ℕ) (x : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N) (hNd : N < d) :
    literalH A M d x = 0 := by
  unfold literalH
  have hempty : A.filter (literalHPoint M d x) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun n hn hp =>
      (not_le_of_gt (hA n hn).2)
        (hNd.le.trans (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (hA n hn).1) hp.1))
  simp only [hempty, Finset.card_empty, Nat.cast_zero]

private theorem one_div_sq_le_sub_inv (m : ℕ) (hm : 2 ≤ m) :
    (1 : ℝ) / (m : ℝ) ^ 2 ≤ (1 : ℝ) / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (show 1 ≤ m by omega))
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two hm))
  have hden :
      (m : ℝ) * (((m - 1 : ℕ) : ℝ)) ≤ (m : ℝ) ^ 2 := by
    rw [show (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 by
      rw [Nat.cast_sub (show 1 ≤ m by omega)]
      norm_num]
    nlinarith
  have hinv : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((m : ℝ) * (((m - 1 : ℕ) : ℝ))) := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (one_div_le_one_div_of_le (by positivity) hden)
  have heq : 1 / ((m : ℝ) * (((m - 1 : ℕ) : ℝ))) =
      (1 : ℝ) / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
    have hcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ m by omega)]
      norm_num
    rw [hcast]
    have hm1' : (m : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hm0.ne', hm1']
    ring
  exact hinv.trans_eq heq

private theorem sum_Icc_sub_inv_telescope
    (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Icc a b, ((1 : ℝ) / (((m - 1 : ℕ) : ℝ)) - 1 / (m : ℝ))) =
      1 / (((a - 1 : ℕ) : ℝ)) - 1 / (b : ℝ) := by
  have ha1 : 1 ≤ a := by omega
  induction b, hab using Nat.le_induction with
  | base =>
      simp [Nat.cast_sub ha1]
  | succ t _ha ht =>
    rw [Finset.sum_Icc_succ_top (show a ≤ t + 1 by omega), ht]
    simp

private theorem sum_Icc_inv_sq_le_inv_pred
    (a b : ℕ) (ha : 2 ≤ a) :
    (∑ m ∈ Finset.Icc a b, (1 : ℝ) / (m : ℝ) ^ 2) ≤ 1 / (((a - 1 : ℕ) : ℝ)) := by
  by_cases hab : a ≤ b
  · calc
      ∑ m ∈ Finset.Icc a b, (1 : ℝ) / (m : ℝ) ^ 2
          ≤ ∑ m ∈ Finset.Icc a b, ((1 : ℝ) / (((m - 1 : ℕ) : ℝ)) - 1 / (m : ℝ)) := by
              refine Finset.sum_le_sum ?_
              intro m hm
              exact one_div_sq_le_sub_inv m (le_trans ha (Finset.mem_Icc.mp hm).1)
      _ = 1 / (((a - 1 : ℕ) : ℝ)) - 1 / (b : ℝ) := sum_Icc_sub_inv_telescope a b ha hab
      _ ≤ 1 / (((a - 1 : ℕ) : ℝ)) := by
          have hb0 : 0 ≤ (1 : ℝ) / (b : ℝ) := by positivity
          exact sub_le_self (1 / (((a - 1 : ℕ) : ℝ))) hb0
  · rw [Finset.Icc_eq_empty hab, Finset.sum_empty]
    positivity

/-- Actual square mass `QA(A,N,z)` is bounded by `2N / z` on any finite
carrier of positive integers below `N`. -/
theorem goldbachQA_real_le_two_mul_div
    (A : Finset ℕ) (N : ℕ) (z : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N) (hz : 2 ≤ z) :
    (goldbachQA A N z : ℝ) ≤ 2 * (N : ℝ) / z := by
  let m0 : ℕ := ⌈z⌉₊
  have hm0_ge_two : 2 ≤ m0 := by
    exact_mod_cast (le_trans hz (Nat.le_ceil z))
  have hsubset : goldbachSquarePrimes N z ⊆ Finset.Icc m0 N := by
    intro q hq
    rcases mem_goldbachSquarePrimes_iff.mp hq with ⟨hqPrime, hqz, hqSq⟩
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.ceil_le.mpr hqz
    · calc
        q ≤ q ^ 2 := by
          calc
            q = q * 1 := by simp
            _ ≤ q * q := by gcongr; exact hqPrime.one_le
            _ = q ^ 2 := by rw [pow_two]
        _ ≤ N := hqSq
  calc
    (goldbachQA A N z : ℝ)
        = ∑ q ∈ goldbachSquarePrimes N z, ((A.filter fun n => q ^ 2 ∣ n).card : ℝ) := by
            simp [goldbachQA]
    _ ≤ ∑ q ∈ goldbachSquarePrimes N z, (N : ℝ) / (q : ℝ) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro q hq
          rcases mem_goldbachSquarePrimes_iff.mp hq with ⟨hqPrime, _, _⟩
          simpa [Nat.cast_pow] using
            (card_filter_dvd_le_div_real A N (q ^ 2)
              (fun n hn => ⟨(hA n hn).1, (hA n hn).2.le⟩) (pow_pos hqPrime.pos 2))
    _ ≤ ∑ m ∈ Finset.Icc m0 N, (N : ℝ) / (m : ℝ) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro m hmIcc hmNotMem
          positivity
    _ = (N : ℝ) * ∑ m ∈ Finset.Icc m0 N, (1 : ℝ) / (m : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          simp [div_eq_mul_inv]
    _ ≤ (N : ℝ) * (1 / (((m0 - 1 : ℕ) : ℝ))) := by
          have hN0 : 0 ≤ (N : ℝ) := by positivity
          gcongr
          exact sum_Icc_inv_sq_le_inv_pred m0 N hm0_ge_two
    _ ≤ (N : ℝ) * (2 / z) := by
          have hz0 : 0 < z := by linarith
          have hm01_ge : z / 2 ≤ (((m0 - 1 : ℕ) : ℝ)) := by
            have hm0_ge_z : z ≤ (m0 : ℝ) := Nat.le_ceil z
            have hm0sub : (((m0 - 1 : ℕ) : ℝ)) = (m0 : ℝ) - 1 := by
              have hm01 : 1 ≤ m0 := by omega
              have hnat : (m0 - 1 : ℕ) + 1 = m0 := Nat.sub_add_cancel hm01
              have hreal : (((m0 - 1 : ℕ) : ℝ)) + 1 = (m0 : ℝ) := by exact_mod_cast hnat
              linarith
            have hsub : z - 1 ≤ (((m0 - 1 : ℕ) : ℝ)) := by
              calc
                z - 1 ≤ (m0 : ℝ) - 1 := sub_le_sub_right hm0_ge_z 1
                _ = (((m0 - 1 : ℕ) : ℝ)) := hm0sub.symm
            linarith
          have hinv : 1 / (((m0 - 1 : ℕ) : ℝ)) ≤ 2 / z := by
            have htmp : 1 / (((m0 - 1 : ℕ) : ℝ)) ≤ 1 / (z / 2) := by
              simpa using one_div_le_one_div_of_le (by positivity : 0 < z / 2) hm01_ge
            have hz_div : (1 : ℝ) / (z / 2) = 2 / z := by
              field_simp [hz0.ne']
            simpa [hz_div] using htmp
          gcongr
    _ = 2 * (N : ℝ) / z := by ring

/-- The actual diagonal square term `Q` is bounded by the square mass `QA`. -/
theorem goldbachQ_le_goldbachQA
    (A : Finset ℕ) (N : ℕ) (z y : ℝ)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ n < N) :
    goldbachQ A N z y ≤ goldbachQA A N z := by
  unfold goldbachQ goldbachQA
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachHalfOpenPrimes N z y)
      (fun q : ℕ => q ^ 2 ≤ N)
      (fun q => literalH A N (q ^ 2) q)
  rw [← hsplit]
  have hmain :
      ∑ q ∈ (goldbachHalfOpenPrimes N z y).filter (fun q : ℕ => q ^ 2 ≤ N),
        literalH A N (q ^ 2) q
        ≤
      ∑ q ∈ goldbachSquarePrimes N z, ((A.filter fun n => q ^ 2 ∣ n).card : ℤ) := by
    have hsubset :
        (goldbachHalfOpenPrimes N z y).filter (fun q : ℕ => q ^ 2 ≤ N) ⊆ goldbachSquarePrimes N z := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqHalf, hqSq⟩
      rcases mem_goldbachHalfOpenPrimes_iff.mp hqHalf with ⟨hqPrime, _, hqz, _⟩
      exact mem_goldbachSquarePrimes_iff.mpr ⟨hqPrime, hqz, hqSq⟩
    have h1 :
        ∑ q ∈ (goldbachHalfOpenPrimes N z y).filter (fun q : ℕ => q ^ 2 ≤ N),
          literalH A N (q ^ 2) q
          ≤
        ∑ q ∈ (goldbachHalfOpenPrimes N z y).filter (fun q : ℕ => q ^ 2 ≤ N),
          ((A.filter fun n => q ^ 2 ∣ n).card : ℤ) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      exact literalH_le_dvdFiberCard A N (q ^ 2) q
    have h2 :
        ∑ q ∈ (goldbachHalfOpenPrimes N z y).filter (fun q : ℕ => q ^ 2 ≤ N),
          ((A.filter fun n => q ^ 2 ∣ n).card : ℤ)
          ≤
        ∑ q ∈ goldbachSquarePrimes N z, ((A.filter fun n => q ^ 2 ∣ n).card : ℤ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro q hq hq'
      exact_mod_cast Nat.zero_le ((A.filter fun n => q ^ 2 ∣ n).card)
    exact h1.trans h2
  have hzero :
      ∑ q ∈ (goldbachHalfOpenPrimes N z y).filter (fun q : ℕ => ¬q ^ 2 ≤ N),
        literalH A N (q ^ 2) q = 0 := by
    refine Finset.sum_eq_zero ?_
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨_, hqSq⟩
    exact literalH_eq_zero_of_large_divisor A N (q ^ 2) N q hA (lt_of_not_ge hqSq)
  rw [hzero, add_zero]
  exact hmain

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig