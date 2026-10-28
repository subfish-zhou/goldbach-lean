import MathlibNt.SieveTheory.LiLiuGoldbachG11GateBudget

open scoped BigOperators
open Classical Finset LiLiuPrereqBuchstab

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


/-- Remove one prime divisor before applying the existing strict `n < N` bound. -/
theorem goldbachG11_largePrimeDivisors_card_le_twenty_one {N : ℕ} (hN : 4 ≤ N) :
    (largePrimeDivisors N ((N : ℝ) ^ (4 / 53 : ℝ))).card ≤ 21 := by
  let L := largePrimeDivisors N ((N : ℝ) ^ (4 / 53 : ℝ))
  change L.card ≤ 21
  by_cases hL : L.Nonempty
  · obtain ⟨p, hp⟩ := hL
    obtain ⟨hpp, hpN, _⟩ := Nat.mem_primeFactors.mp (mem_filter.mp hp).1
    have hN0 : 0 < N := by omega
    have hd0 : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN0 hpN) hpp.pos
    have hdN : N / p < N := Nat.div_lt_self hN0 hpp.one_lt
    have hsub : L.erase p ⊆
        largePrimeDivisors (N / p) ((N : ℝ) ^ (4 / 53 : ℝ)) := by
      intro q hq
      obtain ⟨hqp, hqL⟩ := mem_erase.mp hq
      obtain ⟨hqf, hzq⟩ := mem_filter.mp hqL
      obtain ⟨hqq, hqN, _⟩ := Nat.mem_primeFactors.mp hqf
      have hqd : q ∣ N / p := by
        have hmul : q ∣ p * (N / p) := by rwa [Nat.mul_div_cancel' hpN]
        exact (hqq.dvd_mul.mp hmul).resolve_left
          (fun hqp' => hqp ((Nat.dvd_prime hpp).mp hqp' |>.resolve_left hqq.ne_one))
      exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hqq, hqd, hd0.ne'⟩, hzq⟩
    have hc := (card_le_card hsub).trans
      (largePrimeDivisors_card_le_twenty hd0 hdN
        (by norm_num : (1 : ℝ) / 21 < 4 / 53))
    have he := card_erase_add_one hp
    omega
  · have he : L = ∅ := not_nonempty_iff_eq_empty.mp hL
    simp [he]


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig