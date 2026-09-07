import MathlibNt.Wu2004MeanValue.APWeightTransferActualAP

/-!
The source-wise `+1` AP envelope would cost `d * |S|`, which is not
payable above the square root. Instead, group the actual pairs by their
product. A positive integer has at most one such pair per prime divisor.
-/

namespace Wu2004MeanValue
open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
noncomputable section

theorem balanced_scaledPrimeCount_sum_bound (x : ℝ) (S : Finset ℕ)
    (r : ℕ → ℝ) (d b : ℕ) (hx : 2 ≤ x) (hdx : (d : ℝ) ≤ x)
    (hS : ∀ m ∈ S, 0 < m)
    (hr : ∀ m ∈ S, 0 ≤ r m ∧ (m : ℝ) * r m ≤ x) :
    (d : ℝ) * (∑ m ∈ S, (scaledPrimeCount ((m : ℝ) * r m) d b m : ℝ)) ≤
      (2 / Real.log 2) * x * Real.log x := by
  let P := S.sigma (fun m => scaledPrimeSet ((m : ℝ) * r m) d b m)
  let g : (Σ _ : ℕ, ℕ) → ℕ := fun z => z.1 * z.2
  let T := P.image g
  have hP (z : Σ _ : ℕ, ℕ) (hz : z ∈ P) :
      0 < z.1 ∧ z.2.Prime ∧ (g z : ℝ) ≤ x ∧ g z ≡ b [MOD d] := by
    obtain ⟨hm, hp⟩ := mem_sigma.mp hz
    have h := (mem_scaledPrimeSet (mul_nonneg (Nat.cast_nonneg _) (hr _ hm).1)
      (hS _ hm)).mp hp
    exact ⟨hS _ hm, h.1, by exact_mod_cast h.2.1.trans (hr _ hm).2, h.2.2⟩
  have hT (n : ℕ) (hn : n ∈ T) :
      0 < n ∧ (n : ℝ) ≤ x ∧ n ≡ b [MOD d] := by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hn
    have h := hP z hz
    exact ⟨Nat.mul_pos h.1 h.2.1.pos, h.2.2⟩
  have hfiber (n : ℕ) (hn : n ∈ T) :
      (P.filter (fun z => g z = n)).card ≤ n.primeFactors.card := by
    let R := P.filter (fun z => g z = n)
    have hinj : Set.InjOn (fun z : Σ _ : ℕ, ℕ => z.2) R := by
      intro z hz w hw heq
      change z.2 = w.2 at heq
      have hzP := (mem_filter.mp hz).1
      have hwP := (mem_filter.mp hw).1
      have hprod : z.1 * z.2 = w.1 * w.2 :=
        (mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm
      have hfirst : z.1 = w.1 := by
        rw [heq] at hprod
        exact Nat.eq_of_mul_eq_mul_right (hP w hwP).2.1.pos hprod
      exact Sigma.ext hfirst (by simpa using heq)
    have himage : R.image (fun z => z.2) ⊆ n.primeFactors := by
      intro p hp
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
      obtain ⟨hzP, hzn⟩ := mem_filter.mp hz
      apply Nat.mem_primeFactors.mpr
      exact ⟨(hP z hzP).2.1,
        by rw [← hzn]; exact dvd_mul_left _ _, (hT n hn).1.ne'⟩
    exact (card_image_of_injOn hinj).symm.trans_le (card_le_card himage)
  have hsum : (P.card : ℝ) ≤ T.card * ((Real.log 2)⁻¹ * Real.log x) := by
    have heq := card_eq_sum_card_image g P
    rw [heq, Nat.cast_sum]
    calc
      _ ≤ ∑ n ∈ T, (n.primeFactors.card : ℝ) := by
        apply sum_le_sum
        intro n hn
        exact_mod_cast hfiber n hn
      _ ≤ ∑ _n ∈ T, ((Real.log 2)⁻¹ * Real.log x) :=
        sum_le_sum fun n hn =>
          PanLow.primeFactors_card_le_log_of_le (hT n hn).1 (hT n hn).2.1
      _ = _ := by simp
  have hquotinj : Set.InjOn (fun n : ℕ => n / d) T := by
    intro a ha c hc heq
    change a / d = c / d at heq
    have hmod : a % d = c % d := (hT a ha).2.2.trans (hT c hc).2.2.symm
    calc
      a = a % d + d * (a / d) := (Nat.mod_add_div a d).symm
      _ = c % d + d * (c / d) := by rw [hmod, heq]
      _ = c := Nat.mod_add_div c d
  have hquotimage : T.image (fun n => n / d) ⊆ range (⌊x⌋₊ / d + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_floor (hT n hn).2.1)))
  have hcard : T.card ≤ ⌊x⌋₊ / d + 1 :=
    (card_image_of_injOn hquotinj).symm.trans_le
      ((card_le_card hquotimage).trans_eq (card_range _))
  have hmass : (d : ℝ) * T.card ≤ 2 * x := by
    have h := (Nat.mul_le_mul_left d hcard).trans
      (show d * (⌊x⌋₊ / d + 1) ≤ ⌊x⌋₊ + d by
        simpa only [Nat.mul_add, Nat.mul_one] using
          Nat.add_le_add_right (Nat.mul_div_le ⌊x⌋₊ d) d)
    have h' : (d : ℝ) * T.card ≤ ⌊x⌋₊ + d := by exact_mod_cast h
    have := Nat.floor_le (by linarith : 0 ≤ x)
    linarith
  have hcount : (∑ m ∈ S, (scaledPrimeCount ((m : ℝ) * r m) d b m : ℝ)) =
      (P.card : ℝ) := by
    simp only [P, card_sigma, Nat.cast_sum, scaledPrimeCount]
  rw [hcount]
  calc
    _ ≤ (d : ℝ) * (T.card * ((Real.log 2)⁻¹ * Real.log x)) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
    _ ≤ (2 * x) * ((Real.log 2)⁻¹ * Real.log x) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hmass
        (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
    _ = _ := by ring

end
end Wu2004MeanValue