import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprime

/-! Reciprocal saving only at primes shared with the sieve modulus. -/
namespace Wu2008DoubleSieve
open Finset Real
open scoped Classical

theorem omega3_shared_prime_non_coprime_reciprocal_le (N q : ℕ) (E : Finset ℕ)
    {Y : ℝ} (hY : 0 < Y) (hq : 0 < q) (hqN : q ≤ N)
    (hE : ∀ e ∈ E, 0 < e ∧ e ≤ N)
    (hrough : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → p ∣ q → Y ≤ p) :
    (∑ e ∈ E.filter (fun e => ¬ e.Coprime q), 1 / (e : ℝ)) ≤
      (1 + log N) * log N / (Y * log 2) := by
  let P := q.primeFactors.filter (fun p : ℕ => Y ≤ (p : ℝ))
  have hlog : 0 ≤ log (N : ℝ) := log_natCast_nonneg N
  have hsum :
      (∑ e ∈ E.filter (fun e => ¬ e.Coprime q), 1 / (e : ℝ)) ≤
        ∑ p ∈ P, ∑ e ∈ (Icc 1 N).filter (fun e => p ∣ e), 1 / (e : ℝ) := by
    calc
      _ ≤ ∑ e ∈ E.filter (fun e => ¬ e.Coprime q),
          ∑ p ∈ P, if p ∣ e then 1 / (e : ℝ) else 0 := by
        apply sum_le_sum
        intro e he
        obtain ⟨he, hbad⟩ := mem_filter.mp he
        obtain ⟨p, hp, hpe, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
        have hpP : p ∈ P := mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, Nat.ne_of_gt hq⟩, hrough e he p hp hpe hpq⟩
        simpa only [if_pos hpe] using
          (single_le_sum (f := fun r : ℕ => if r ∣ e then 1 / (e : ℝ) else 0)
            (fun r _ => by positivity) hpP :
            (if p ∣ e then 1 / (e : ℝ) else 0) ≤
              ∑ r ∈ P, if r ∣ e then 1 / (e : ℝ) else 0)
      _ = ∑ p ∈ P, ∑ e ∈ E.filter (fun e => ¬ e.Coprime q),
          if p ∣ e then 1 / (e : ℝ) else 0 := sum_comm
      _ ≤ _ := by
        apply sum_le_sum
        intro p _
        rw [← sum_filter]
        apply sum_le_sum_of_subset_of_nonneg
        · intro e he
          obtain ⟨he, hp⟩ := mem_filter.mp he
          have heE := (mem_filter.mp he).1
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hE e heE).1, (hE e heE).2⟩, hp⟩
        · intro e _ _
          positivity
  have hcard : (P.card : ℝ) ≤ log N / log 2 := by
    have hω := primeFactors_card_mul_log_two_le q hq
    have hl : log (q : ℝ) ≤ log N :=
      log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqN)
    apply (le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    have hc : (P.card : ℝ) ≤ q.primeFactors.card := by
      exact_mod_cast card_le_card (filter_subset _ _)
    nlinarith [log_pos (by norm_num : (1 : ℝ) < 2)]
  calc
    _ ≤ ∑ p ∈ P, ∑ e ∈ (Icc 1 N).filter (fun e => p ∣ e), 1 / (e : ℝ) := hsum
    _ ≤ ∑ _p ∈ P, (1 + log N) / Y := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hp, hYp⟩ := mem_filter.mp hp
      exact (omega3_reciprocal_multiples_le N p
        (Nat.prime_of_mem_primeFactors hp).pos).trans
          (div_le_div_of_nonneg_left (by positivity) hY hYp)
    _ = (P.card : ℝ) * ((1 + log N) / Y) := by simp
    _ ≤ (log N / log 2) * ((1 + log N) / Y) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- A common prime inherits coprimality from the actual sieve modulus. -/
theorem omega3_relative_rough_non_coprime_reciprocal_le (N q : ℕ) (E : Finset ℕ)
    {Y : ℝ} (hY : 0 < Y) (hq : 0 < q) (hqN : q ≤ N) (hcop : q.Coprime N)
    (hE : ∀ e ∈ E, 0 < e ∧ e ≤ N)
    (hrough : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → p.Coprime N → Y ≤ p) :
    (∑ e ∈ E.filter (fun e => ¬ e.Coprime q), 1 / (e : ℝ)) ≤
      (1 + log N) * log N / (Y * log 2) := by
  apply omega3_shared_prime_non_coprime_reciprocal_le N q E hY hq hqN hE
  intro e he p hp hpe hpq
  exact hrough e he p hp hpe (hcop.of_dvd_left hpq)

namespace RelativeRoughness

/-- The mask excludes primes strictly below z; equality with Y is retained. -/
theorem of_sifted {M N n : ℕ} {Y z : ℝ} (hs : Sifted M n z) (hYz : Y ≤ z)
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → p.Coprime N → Y ≤ (p : ℝ)) :
    ∀ p : ℕ, p.Prime → p ∣ n → p.Coprime N → Y ≤ (p : ℝ) := by
  intro p hp hpn hcop
  by_cases hpm : p ∣ M
  · exact hM p hp hpm hcop
  · by_contra hy
    exact hs p hp (hp.coprime_iff_not_dvd.mpr hpm) ((lt_of_not_ge hy).trans_le hYz) hpn

/-- Multiplication preserves relative roughness, without deleting any factor. -/
theorem mul {N a b : ℕ} {Y : ℝ}
    (ha : ∀ p : ℕ, p.Prime → p ∣ a → p.Coprime N → Y ≤ (p : ℝ))
    (hb : ∀ p : ℕ, p.Prime → p ∣ b → p.Coprime N → Y ≤ (p : ℝ)) :
    ∀ p : ℕ, p.Prime → p ∣ a * b → p.Coprime N → Y ≤ (p : ℝ) := by
  intro p hp hd hc
  exact (hp.dvd_mul.mp hd).elim (fun h => ha p hp h hc) (fun h => hb p hp h hc)

/-- Every prime of a literal ordered prefix product is paid by a prefix entry. -/
theorem prefix_prod (pre : List ℕ) {Y : ℝ}
    (hpre : ∀ r ∈ pre, r.Prime ∧ Y ≤ (r : ℝ)) :
    ∀ p : ℕ, p.Prime → p ∣ pre.prod → Y ≤ (p : ℝ) := by
  induction pre with
  | nil =>
    intro p hp hd
    exact (hp.ne_one (Nat.dvd_one.mp hd)).elim
  | cons r pre ih =>
    intro p hp hd
    have hr := hpre r (by simp)
    have htail := ih (fun s hs => hpre s (by simp [hs]))
    rcases hp.dvd_mul.mp (show p ∣ r * pre.prod from hd) with h | h
    · have he : p = r := (Nat.dvd_prime hr.1).mp h |>.resolve_left hp.ne_one
      simpa only [he] using hr.2
    · exact htail p hp h

/-- The genuine nonunit mask permits small primes of N, but none shared with q. -/
theorem masked_prefix {N d n : ℕ} (pre : List ℕ) {Y z : ℝ}
    (hs : Sifted (d * pre.prod * N) n z) (hYz : Y ≤ z)
    (hd : ∀ p : ℕ, p.Prime → p ∣ d → Y ≤ (p : ℝ))
    (hpre : ∀ r ∈ pre, r.Prime ∧ Y ≤ (r : ℝ)) :
    ∀ p : ℕ, p.Prime → p ∣ d * pre.prod * n → p.Coprime N → Y ≤ (p : ℝ) := by
  have hdp : ∀ p : ℕ, p.Prime → p ∣ d * pre.prod → p.Coprime N → Y ≤ (p : ℝ) :=
    mul (fun p hp h _ => hd p hp h) (fun p hp h _ => prefix_prod pre hpre p hp h)
  have hn := of_sifted hs hYz (N := N) (fun p hp h hc => by
    rcases hp.dvd_mul.mp h with h | h
    · exact hdp p hp h hc
    · exact (hp.coprime_iff_not_dvd.mp hc h).elim)
  exact mul hdp hn

end RelativeRoughness
end Wu2008DoubleSieve
