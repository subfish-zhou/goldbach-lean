import R2SixthCountGeometry
import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly

noncomputable section
namespace WuPaper.R2SixthCount
open Real Finset Wu2008DoubleSieve
open scoped Classical

def window (N : ℕ) (l u : ℝ) : Finset ℕ :=
  primeWindow N ((N : ℝ) ^ l) ((N : ℝ) ^ u)

theorem mem_window {N p : ℕ} {l u : ℝ} :
    p ∈ window N l u ↔ p.Prime ∧ p.Coprime N ∧
      (N : ℝ) ^ l ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ u :=
  mem_primeWindow

theorem prime_ne_rational_cutoff {N p m n : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hc : p.Coprime N) :
    (p : ℝ) ≠ (N : ℝ) ^ ((m : ℝ) / n) := by
  intro he
  have hpow : (p : ℝ) ^ n = (N : ℝ) ^ m := by
    rw [he, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg N)]
    rw [div_mul_cancel₀ _ (by exact_mod_cast hn : (n : ℝ) ≠ 0), rpow_natCast]
  have hnat : p ^ n = N ^ m := by exact_mod_cast hpow
  have hd : p ∣ p ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    refine ⟨p ^ k, ?_⟩
    rw [pow_succ, Nat.mul_comm]
  have hpN : p ∣ N := hp.dvd_of_dvd_pow (hnat ▸ hd)
  exact hp.not_dvd_one (by
    simpa only [hc.gcd_eq_one] using Nat.dvd_gcd (dvd_refl p) hpN)

theorem prime_ne_alpha_cutoff {N p : ℕ} (hp : p.Prime) (hc : p.Coprime N) :
    (p : ℝ) ≠ (N : ℝ) ^ alpha := by
  exact prime_ne_rational_cutoff (m := 100) (n := 1327) (by norm_num) hp hc

theorem alpha_sifted_closed_iff (N n : ℕ) :
    SiftedLE N n ((N : ℝ) ^ alpha) ↔ Sifted N n ((N : ℝ) ^ alpha) := by
  constructor
  · intro h q hp hc hq
    exact h q hp hc hq.le
  · intro h q hp hc hq
    exact h q hp hc ((lt_iff_le_and_ne).mpr ⟨hq, prime_ne_alpha_cutoff hp hc⟩)

theorem alpha_source_carrier_closed_eq (N d : ℕ) :
    sourceSieveCarrierLE N d N ((N : ℝ) ^ alpha) =
      sourceSieveCarrier N d N ((N : ℝ) ^ alpha) := by
  ext p
  simp only [sourceSieveCarrierLE, sourceSieveCarrier, mem_filter, alpha_sifted_closed_iff]

theorem alpha_source_count_closed_eq (N d : ℕ) :
    sourceSieveCountLE N d N ((N : ℝ) ^ alpha) =
      sourceSieveCount N d N ((N : ℝ) ^ alpha) := by
  simp only [sourceSieveCountLE, sourceSieveCount, alpha_source_carrier_closed_eq]

theorem selected_pair_sifted {N p q : ℕ} {z : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hzp : z ≤ (p : ℝ)) (hzq : z ≤ (q : ℝ)) :
    Sifted N (p * q) z :=
  (sifted_mul_iff _ _ _ _).mpr ⟨sifted_prime_of_le hp hzp, sifted_prime_of_le hq hzq⟩

theorem selected_pair_source_eq_quotient {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hzp : (N : ℝ) ^ alpha ≤ (p : ℝ)) (hzq : (N : ℝ) ^ alpha ≤ (q : ℝ)) :
    sourceSieveCountLE N (p * q) N ((N : ℝ) ^ alpha) =
      sieveCount N (p * q) N ((N : ℝ) ^ alpha) := by
  rw [alpha_source_count_closed_eq]
  simp only [sourceSieveCount, sieveCount, sourceSieveCarrier_eq_ite,
    if_pos (selected_pair_sifted hp hq hzp hzq)]

theorem sifted_remove_sifted_modulus {N d n : ℕ} {z : ℝ} (hd : Sifted N d z) :
    Sifted N n z ↔ Sifted (d * N) n z := by
  constructor
  · intro h r hp hc hz
    exact h r hp (Nat.coprime_mul_iff_right.mp hc).2 hz
  · intro h r hp hc hz
    have hrd : r.Coprime d := hp.coprime_iff_not_dvd.mpr (hd r hp hc hz)
    exact h r hp (Nat.coprime_mul_iff_right.mpr ⟨hrd, hc⟩) hz

theorem selected_pair_source_eq_double_modulus {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hzp : (N : ℝ) ^ alpha ≤ (p : ℝ)) (hzq : (N : ℝ) ^ alpha ≤ (q : ℝ)) :
    sourceSieveCountLE N (p * q) N ((N : ℝ) ^ alpha) =
      sourceSieveCount N (p * q) ((p * q) * N) ((N : ℝ) ^ alpha) := by
  rw [alpha_source_count_closed_eq]
  unfold sourceSieveCount
  apply congrArg (fun S : Finset ℕ => (S.card : ℤ))
  ext r
  simp only [sourceSieveCarrier, mem_filter,
    sifted_remove_sifted_modulus (selected_pair_sifted hp hq hzp hzq)]

def rectangleCount (N : ℕ) (l u v w : ℝ) : ℤ :=
  ∑ q ∈ window N v w, ∑ p ∈ window N l u,
    sourceSieveCountLE N (p * q) N ((N : ℝ) ^ alpha)

def upsilon6 (N : ℕ) : ℤ := rectangleCount N alpha beta beta sigma
def countA (N : ℕ) : ℤ := rectangleCount N alpha beta beta aCeiling
def countB (N : ℕ) : ℤ := rectangleCount N alpha bCut aCeiling sigma
def countC (N : ℕ) : ℤ := rectangleCount N bCut beta aCeiling sigma

theorem mem_original_pair {N p q : ℕ} :
    p ∈ window N alpha beta ∧ q ∈ window N beta sigma ↔
      p.Prime ∧ q.Prime ∧ (p * q).Coprime N ∧
        (N : ℝ) ^ alpha ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ beta ∧
        (N : ℝ) ^ beta ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ sigma := by
  simp only [mem_window, Nat.coprime_mul_iff_left]
  tauto

theorem original_pair_order {N p q : ℕ}
    (hp : p ∈ window N alpha beta) (hq : q ∈ window N beta sigma) :
    p < q := by
  exact_mod_cast (mem_window.mp hp).2.2.2.trans_le (mem_window.mp hq).2.2.1

theorem window_sum_split {N : ℕ} (hN : 1 ≤ N) {l m u : ℝ}
    (hlm : l ≤ m) (hmu : m ≤ u) (f : ℕ → ℤ) :
    (∑ p ∈ window N l u, f p) =
      (∑ p ∈ window N l m, f p) + ∑ p ∈ window N m u, f p := by
  exact sum_primeWindow_split N
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hlm)
    (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hmu) f

theorem upsilon6_exact_three_blocks {N : ℕ} (hN : 1 ≤ N) :
    upsilon6 N = countA N + countB N + countC N := by
  have hb : beta ≤ aCeiling :=
    (parameter_order.2.2.2.1.trans parameter_order.2.2.2.2.1).le
  unfold upsilon6 countA countB countC rectangleCount
  rw [window_sum_split hN hb parameter_order.2.2.2.2.2.1.le]
  simp_rw [window_sum_split hN parameter_order.2.1.le parameter_order.2.2.1.le]
  simp only [sum_add_distrib]
  ring

theorem rectangle_count_nonneg (N : ℕ) (l u v w : ℝ) :
    0 ≤ rectangleCount N l u v w := by
  apply sum_nonneg
  intro q _
  apply sum_nonneg
  intro p _
  exact Int.natCast_nonneg _

theorem original_ab_le_upsilon6 {N : ℕ} (hN : 1 ≤ N) :
    countA N + countB N ≤ upsilon6 N := by
  rw [upsilon6_exact_three_blocks hN]
  exact le_add_of_nonneg_right (rectangle_count_nonneg N bCut beta aCeiling sigma)

theorem upsilon6_eq_full_quotient {N : ℕ} (hN : 1 ≤ N) :
    upsilon6 N =
      ∑ q ∈ window N beta sigma, ∑ p ∈ window N alpha beta,
        sieveCount N (p * q) N ((N : ℝ) ^ alpha) := by
  unfold upsilon6 rectangleCount
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro p hp
  have hp' := mem_window.mp hp
  have hq' := mem_window.mp hq
  apply selected_pair_source_eq_quotient hp'.1 hq'.1 hp'.2.2.1
  exact (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    (parameter_order.2.1.trans parameter_order.2.2.1).le).trans hq'.2.2.1

#check @WuPaper.R2SixthCount.window
#check @WuPaper.R2SixthCount.mem_window
#check @WuPaper.R2SixthCount.prime_ne_rational_cutoff
#check @WuPaper.R2SixthCount.prime_ne_alpha_cutoff
#check @WuPaper.R2SixthCount.alpha_sifted_closed_iff
#check @WuPaper.R2SixthCount.alpha_source_carrier_closed_eq
#check @WuPaper.R2SixthCount.alpha_source_count_closed_eq
#check @WuPaper.R2SixthCount.selected_pair_sifted
#check @WuPaper.R2SixthCount.selected_pair_source_eq_quotient
#check @WuPaper.R2SixthCount.sifted_remove_sifted_modulus
#check @WuPaper.R2SixthCount.selected_pair_source_eq_double_modulus
#check @WuPaper.R2SixthCount.rectangleCount
#check @WuPaper.R2SixthCount.upsilon6
#check @WuPaper.R2SixthCount.countA
#check @WuPaper.R2SixthCount.countB
#check @WuPaper.R2SixthCount.countC
#check @WuPaper.R2SixthCount.mem_original_pair
#check @WuPaper.R2SixthCount.original_pair_order
#check @WuPaper.R2SixthCount.window_sum_split
#check @WuPaper.R2SixthCount.upsilon6_exact_three_blocks
#check @WuPaper.R2SixthCount.rectangle_count_nonneg
#check @WuPaper.R2SixthCount.original_ab_le_upsilon6
#check @WuPaper.R2SixthCount.upsilon6_eq_full_quotient
#print axioms WuPaper.R2SixthCount.window
#print axioms WuPaper.R2SixthCount.mem_window
#print axioms WuPaper.R2SixthCount.prime_ne_rational_cutoff
#print axioms WuPaper.R2SixthCount.prime_ne_alpha_cutoff
#print axioms WuPaper.R2SixthCount.alpha_sifted_closed_iff
#print axioms WuPaper.R2SixthCount.alpha_source_carrier_closed_eq
#print axioms WuPaper.R2SixthCount.alpha_source_count_closed_eq
#print axioms WuPaper.R2SixthCount.selected_pair_sifted
#print axioms WuPaper.R2SixthCount.selected_pair_source_eq_quotient
#print axioms WuPaper.R2SixthCount.sifted_remove_sifted_modulus
#print axioms WuPaper.R2SixthCount.selected_pair_source_eq_double_modulus
#print axioms WuPaper.R2SixthCount.rectangleCount
#print axioms WuPaper.R2SixthCount.upsilon6
#print axioms WuPaper.R2SixthCount.countA
#print axioms WuPaper.R2SixthCount.countB
#print axioms WuPaper.R2SixthCount.countC
#print axioms WuPaper.R2SixthCount.mem_original_pair
#print axioms WuPaper.R2SixthCount.original_pair_order
#print axioms WuPaper.R2SixthCount.window_sum_split
#print axioms WuPaper.R2SixthCount.upsilon6_exact_three_blocks
#print axioms WuPaper.R2SixthCount.rectangle_count_nonneg
#print axioms WuPaper.R2SixthCount.original_ab_le_upsilon6
#print axioms WuPaper.R2SixthCount.upsilon6_eq_full_quotient
end WuPaper.R2SixthCount
