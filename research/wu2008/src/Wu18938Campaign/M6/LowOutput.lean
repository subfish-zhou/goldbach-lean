import Wu18938Campaign.M6.RectangleEndpoint

noncomputable section
open Finset
open scoped Classical

namespace Wu18938Campaign.M6
open U8Literal

private theorem least_prime_le {a b c d : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (hbc : b ≤ c) (hcd : c ≤ d) (h : a ∣ b * c * d) : b ≤ a := by
  rcases ha.dvd_mul.mp h with h | h
  · rcases ha.dvd_mul.mp h with h | h
    · exact ((Nat.prime_dvd_prime_iff_eq ha hb).mp h).symm.le
    · exact hbc.trans (((Nat.prime_dvd_prime_iff_eq ha hc).mp h).symm.le)
  · exact (hbc.trans hcd).trans (((Nat.prime_dvd_prime_iff_eq ha hd).mp h).symm.le)

theorem ordered_prime_triple_unique {a b c d e f : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hd : d.Prime) (he : e.Prime) (hf : f.Prime)
    (hab : a ≤ b) (hbc : b ≤ c) (hde : d ≤ e) (hef : e ≤ f)
    (h : a * b * c = d * e * f) :
    a = d ∧ b = e ∧ c = f := by
  have had : a ∣ d * e * f := by rw [← h]; exact dvd_mul_of_dvd_left (dvd_mul_right a b) c
  have hda : d ∣ a * b * c := by rw [h]; exact dvd_mul_of_dvd_left (dvd_mul_right d e) f
  have hadEq : a = d := le_antisymm
    (least_prime_le hd ha hb hc hab hbc hda)
    (least_prime_le ha hd he hf hde hef had)
  subst d
  have hpair : b * c = e * f := by
    apply Nat.eq_of_mul_eq_mul_left ha.pos
    simpa only [Nat.mul_assoc] using h
  have hbe : b ∣ e * f := hpair ▸ dvd_mul_right b c
  have heb : e ∣ b * c := hpair.symm ▸ dvd_mul_right e f
  have hble : b ≤ e := by
    rcases he.dvd_mul.mp heb with hh | hh
    · exact ((Nat.prime_dvd_prime_iff_eq he hb).mp hh).symm.le
    · have hec := (Nat.prime_dvd_prime_iff_eq he hc).mp hh
      exact hbc.trans hec.symm.le
  have helb : e ≤ b := by
    rcases hb.dvd_mul.mp hbe with hh | hh
    · exact ((Nat.prime_dvd_prime_iff_eq hb he).mp hh).symm.le
    · have hbf := (Nat.prime_dvd_prime_iff_eq hb hf).mp hh
      exact hef.trans hbf.symm.le
  have hbeEq : b = e := le_antisymm hble helb
  subst e
  exact ⟨rfl, rfl, Nat.eq_of_mul_eq_mul_left hb.pos hpair⟩

def rectangleTriples (N : ℕ) (ρ : ℝ) (k : Key) : Finset (ℕ × ℕ × ℕ) :=
  ((shortPrimeSupport N ρ k).filter fun n => n.Prime ∧ n.Coprime N) ×ˢ longLabels N ρ k

def tripleProduct (t : ℕ × ℕ × ℕ) : ℕ := t.1 * t.2.1 * t.2.2

theorem rectangleTriples_ordered {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) {k : Key} {t : ℕ × ℕ × ℕ} (ht : t ∈ rectangleTriples N ρ k) :
    t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 < t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  obtain ⟨hs, hl⟩ := mem_product.mp ht
  obtain ⟨hs, ha, _⟩ := mem_filter.mp hs
  obtain ⟨_, hb, hc, _, hbc, hlo, _⟩ := mem_filter.mp hl
  have hcut := ((mem_shortPrimeSupport hN hρ k t.1).mp hs).2.2.2
  have hpow : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hab : (t.1 : ℝ) < t.2.1 := hcut.trans_le (hpow.trans hlo)
  exact ⟨ha, hb, hc, by exact_mod_cast hab, hbc⟩

theorem rectangleTriples_product_inj {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) :
    Set.InjOn tripleProduct (rectangleTriples N ρ k) := by
  intro x hx y hy h
  obtain ⟨ha, hb, hc, hab, hbc⟩ := rectangleTriples_ordered hN hρ hx
  obtain ⟨hd, he, hf, hde, hef⟩ := rectangleTriples_ordered hN hρ hy
  obtain ⟨h1, h2, h3⟩ := ordered_prime_triple_unique ha hb hc hd he hf
    hab.le hbc hde.le hef h
  exact Prod.ext h1 (Prod.ext h2 h3)

private theorem absolute_difference_side_inj {N x y : ℕ}
    (h : ((N : ℤ) - x).natAbs = ((N : ℤ) - y).natAbs)
    (hs : decide (N ≤ x) = decide (N ≤ y)) : x = y := by
  have hx := Int.natAbs_eq_iff.mp (rfl : ((N : ℤ) - x).natAbs = ((N : ℤ) - x).natAbs)
  have hy := Int.natAbs_eq_iff.mp h.symm
  by_cases hNx : N ≤ x <;> by_cases hNy : N ≤ y
  · rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega
  · simp [hNx, hNy] at hs
  · simp [hNx, hNy] at hs
  · rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega

def lowTriples (N : ℕ) (ρ : ℝ) (k : Key) (z : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (rectangleTriples N ρ k).filter fun t =>
    (output N t.1 (t.2.1 * t.2.2) : ℝ) < z

theorem lowTriples_card_le {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) (z : ℝ) :
    (lowTriples N ρ k z).card ≤ 2 * ⌈z⌉₊ := by
  let f : (ℕ × ℕ × ℕ) → ℕ × Bool :=
    fun t => (output N t.1 (t.2.1 * t.2.2), decide (N ≤ tripleProduct t))
  have hcard : (lowTriples N ρ k z).card ≤ (range ⌈z⌉₊ ×ˢ (univ : Finset Bool)).card := by
    apply card_le_card_of_injOn f
    · intro t ht
      exact mem_product.mpr
        ⟨mem_range.mpr (Nat.lt_ceil.mpr (mem_filter.mp ht).2), mem_univ _⟩
    · intro x hx y hy heq
      apply rectangleTriples_product_inj hN hρ k (mem_filter.mp hx).1 (mem_filter.mp hy).1
      apply absolute_difference_side_inj (N := N)
      · have he := congrArg Prod.fst heq
        change output N x.1 (x.2.1 * x.2.2) = output N y.1 (y.2.1 * y.2.2) at he
        simpa only [output, tripleProduct, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using he
      · exact congrArg Prod.snd heq
  simpa only [card_product, card_range, Fintype.card_bool, card_univ, Nat.mul_comm] using hcard

def lowRectangle (N : ℕ) (ρ : ℝ) (k : Key) (z : ℝ) : ℝ :=
  ∑ m ∈ longProducts N ρ k, ∑ n ∈ shortPrimeSupport N ρ k,
    longAlpha N ρ k m * rectangleBeta N n *
      (if (output N n m : ℝ) < z then 1 else 0)

theorem lowRectangle_eq_card (N : ℕ) (ρ : ℝ) (k : Key) (z : ℝ) :
    lowRectangle N ρ k z = ((lowTriples N ρ k z).card : ℝ) := by
  have hlabels : lowRectangle N ρ k z =
      ∑ n ∈ shortPrimeSupport N ρ k, ∑ t ∈ longLabels N ρ k,
        rectangleBeta N n * (if (output N n (t.1 * t.2) : ℝ) < z then 1 else 0) := by
    unfold lowRectangle
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    rw [long_sum N ρ k (fun m => rectangleBeta N n *
      (if (output N n m : ℝ) < z then 1 else 0))]
    apply sum_congr rfl
    intro m _
    exact mul_assoc _ _ _
  rw [hlabels]
  have hcard : ((lowTriples N ρ k z).card : ℝ) =
      ∑ t ∈ rectangleTriples N ρ k,
        if (output N t.1 (t.2.1 * t.2.2) : ℝ) < z then (1 : ℝ) else 0 := by
    simp only [lowTriples, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, rectangleTriples, sum_product, sum_filter]
  apply sum_congr rfl
  intro n _
  rw [← mul_sum]
  unfold rectangleBeta
  split_ifs <;> simp_all

theorem lowRectangle_le {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) (z : ℝ) :
    lowRectangle N ρ k z ≤ 2 * (⌈z⌉₊ : ℝ) := by
  rw [lowRectangle_eq_card]
  exact_mod_cast lowTriples_card_le hN hρ k z

theorem lowRectangle_sqrt_upper {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ}
    (hρ : 1 < ρ) (k : Key) {z : ℝ} (hz : z ≤ Real.sqrt N) :
    lowRectangle N ρ k z ≤ 2 * Real.sqrt N + 2 := by
  have hceil : (⌈z⌉₊ : ℝ) ≤ Real.sqrt N + 1 :=
    (Nat.cast_le.mpr (Nat.ceil_mono hz)).trans
      (Nat.ceil_lt_add_one (Real.sqrt_nonneg (N : ℝ))).le
  exact (lowRectangle_le hN hρ k z).trans (by linarith)

end Wu18938Campaign.M6
