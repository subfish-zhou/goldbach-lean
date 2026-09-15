import MathlibNt.Wu2008DoubleSieve.NinthSwitchingCountExceptions

/-! Relative sifting is purified before any assertion of ordinary roughness.
The unit and the inclusive endpoint are retained explicitly. -/
namespace Wu2008DoubleSieve.SeventhEighth

/-- Removing the two actual arithmetic exceptions restores ordinary roughness. -/
theorem relative_purification {N a b p : ℕ}
    (ha : Nat.Prime a) (hpN : p ≤ N) (hp : Nat.Prime p)
    (hd : a * b ∣ N - p) (hs : Sifted (N * a) ((N - p) / (a * b)) b)
    (hpbad : ¬ p ∣ N) (hasq : ¬ a ^ 2 ∣ N - p) :
    ∀ q : ℕ, Nat.Prime q → q ∣ (N - p) / (a * b) → b ≤ q := by
  intro q hq hqd
  have hqn : q ∣ N - p := by
    rw [← Nat.mul_div_cancel' hd]
    exact hqd.trans (dvd_mul_left _ _)
  have hqN : ¬ q ∣ N := by
    intro h
    have hqp : q ∣ p := by
      simpa only [Nat.sub_sub_self hpN] using Nat.dvd_sub h hqn
    rcases (Nat.dvd_prime hp).mp hqp with h1 | heq
    · exact hq.ne_one h1
    · exact hpbad (heq ▸ h)
  have hqa : ¬ q ∣ a := by
    intro h
    rcases (Nat.dvd_prime ha).mp h with h1 | heq
    · exact hq.ne_one h1
    · subst q
      obtain ⟨k, hk⟩ := hqd
      apply hasq
      refine ⟨b * k, ?_⟩
      rw [← Nat.mul_div_cancel' hd, hk]
      ring
  by_contra hlt
  exact hs q hq ((hq.coprime_iff_not_dvd.mpr hqN).mul_right
    (hq.coprime_iff_not_dvd.mpr hqa)) (by exact_mod_cast (Nat.lt_of_not_ge hlt)) hqd

/-- The domain inequality rules out every positive composite residual. -/
theorem cofactor_one_or_prime {N a b p : ℕ}
    (hN : 4 ≤ N) (he : Even N) (ha : Nat.Prime a) (hb : Nat.Prime b)
    (hgeom : N ≤ a * b ^ 3)
    (hp : p ∈ sieveCarrier N (a * b) (N * a) b)
    (hpbad : ¬ p ∣ N) (hasq : ¬ a ^ 2 ∣ N - p) :
    (N - p) / (a * b) = 1 ∨
      (Nat.Prime ((N - p) / (a * b)) ∧ b ≤ (N - p) / (a * b)) := by
  classical
  obtain ⟨hpr, hpp, hd, hs⟩ := Finset.mem_filter.mp hp
  have hpN : p ≤ N := by have := Finset.mem_range.mp hpr; omega
  have hn := complement_pos_of_even hN he hpN hpp
  have hm : 0 < (N - p) / (a * b) :=
    Nat.div_pos (Nat.le_of_dvd hn hd) (Nat.mul_pos ha.pos hb.pos)
  have hrough := relative_purification ha hpN hpp hd hs hpbad hasq
  by_cases h1 : (N - p) / (a * b) = 1
  · exact Or.inl h1
  right
  have hprime : Nat.Prime ((N - p) / (a * b)) := by
    by_contra hnp
    have hmin := hrough _ (Nat.minFac_prime h1) (Nat.minFac_dvd _)
    have hsq := Nat.minFac_sq_le_self hm hnp
    have hb2 : b ^ 2 ≤ (N - p) / (a * b) :=
      (Nat.pow_le_pow_left hmin 2).trans hsq
    have hprod := Nat.mul_le_mul_left (a * b) hb2
    rw [Nat.mul_div_cancel' hd] at hprod
    have hid : a * b * b ^ 2 = a * b ^ 3 := by ring
    rw [hid] at hprod
    have := hpp.pos
    omega
  exact ⟨hprime, hrough _ hprime (dvd_refl _)⟩

end Wu2008DoubleSieve.SeventhEighth
