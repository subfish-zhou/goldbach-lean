import MathlibNt.SieveTheory.SwitchingPrinciple

open scoped Classical BigOperators
open Filter Real Finset

namespace MathlibNt.SieveTheory.SwitchingPrinciple

/-- The finite supported-prime mass below `z`. -/
noncomputable def suzukiPrimeMassBelow (S : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), S.nu p

/-- Lemma 14.1's total-mass estimate, obtained only from the dimension-one
local Euler-product bound. -/
theorem lemmaFourteenOne_localProduct_mass
    {S : BoundingSieve} {K z : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hz : 2 ≤ z) :
    suzukiPrimeMassBelow S z ≤
      Real.log (Real.log z / Real.log 2) +
        Real.log (1 + K / Real.log 2) := by
  classical
  let A := S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)
  have hprime (p : ℕ) (hp : p ∈ A) : p.Prime := by
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hdiv (p : ℕ) (hp : p ∈ A) : p ∣ S.prodPrimes := by
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
  have hnu_pos (p : ℕ) (hp : p ∈ A) : 0 < S.nu p :=
    S.nu_pos_of_prime p (hprime p hp) (hdiv p hp)
  have hone_sub_pos (p : ℕ) (hp : p ∈ A) : 0 < 1 - S.nu p :=
    sub_pos.mpr (S.nu_lt_one_of_prime p (hprime p hp) (hdiv p hp))
  have hterm (p : ℕ) (hp : p ∈ A) :
      S.nu p ≤ -Real.log (1 - S.nu p) := by
    have hlog := Real.log_le_sub_one_of_pos (hone_sub_pos p hp)
    linarith
  have hmass_log :
      (∑ p ∈ A, S.nu p) ≤
        Real.log (∏ p ∈ A, (1 - S.nu p)⁻¹) := by
    calc
      (∑ p ∈ A, S.nu p) ≤ ∑ p ∈ A, -Real.log (1 - S.nu p) := by
        exact Finset.sum_le_sum fun p hp => hterm p hp
      _ = ∑ p ∈ A, Real.log ((1 - S.nu p)⁻¹) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Real.log_inv]
      _ = Real.log (∏ p ∈ A, (1 - S.nu p)⁻¹) := by
        rw [Real.log_prod]
        intro p hp
        exact inv_ne_zero (ne_of_gt (hone_sub_pos p hp))
  have hA :
      S.prodPrimes.primeFactors.filter
          (fun p : ℕ => (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < z) = A := by
    ext p
    simp only [A, Finset.mem_filter]
    constructor
    · exact fun hp => ⟨hp.1, hp.2.2⟩
    · rintro ⟨hpS, hpz⟩
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
      exact ⟨hpS, (by exact_mod_cast hpprime.two_le), hpz⟩
  have hprod_le :
      (∏ p ∈ A, (1 - S.nu p)⁻¹) ≤
        Real.log z / Real.log 2 * (1 + K / Real.log 2) := by
    have h := hlocal 2 z (by norm_num) hz
    simpa only [hA] using h
  have hprod_pos : 0 < ∏ p ∈ A, (1 - S.nu p)⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    exact inv_pos.mpr (hone_sub_pos p hp)
  have hlog_le := Real.log_le_log hprod_pos hprod_le
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog_z_pos : 0 < Real.log z := Real.log_pos (lt_of_lt_of_le (by norm_num) hz)
  have hfirst_pos : 0 < Real.log z / Real.log 2 := div_pos hlog_z_pos hlog_two_pos
  have hbound_pos :
      0 < Real.log z / Real.log 2 * (1 + K / Real.log 2) :=
    hprod_pos.trans_le hprod_le
  have hsecond_pos : 0 < 1 + K / Real.log 2 :=
    by nlinarith
  unfold suzukiPrimeMassBelow
  change (∑ p ∈ A, S.nu p) ≤ _
  calc
    (∑ p ∈ A, S.nu p) ≤ Real.log (∏ p ∈ A, (1 - S.nu p)⁻¹) := hmass_log
    _ ≤ Real.log (Real.log z / Real.log 2 * (1 + K / Real.log 2)) := hlog_le
    _ = Real.log (Real.log z / Real.log 2) + Real.log (1 + K / Real.log 2) := by
      rw [Real.log_mul (ne_of_gt hfirst_pos) (ne_of_gt hsecond_pos)]

end MathlibNt.SieveTheory.SwitchingPrinciple
