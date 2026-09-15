import WR2SixthCountCarriers

noncomputable section
namespace WuPaper.R2SixthCount
open Real Finset Filter Wu2008DoubleSieve
open scoped Classical Topology

def pairWindows (N : ℕ) (l u v w : ℝ) : Fin 2 → Finset ℕ :=
  ![window N v w, window N l u]

theorem pair_window_fibres (N : ℕ) (l u v w : ℝ) (f : ℕ → ℝ) :
    (∑ d ∈ boxConvolutionSupport (pairWindows N l u v w),
      (convolutionCoeff (pairWindows N l u v w) d : ℝ) * f d) =
      ∑ q ∈ window N v w, ∑ p ∈ window N l u, f (p * q) := by
  rw [boxConvolution_sum_fibres,
    ← sum_product (f := fun t : ℕ × ℕ => f (t.2 * t.1))]
  apply sum_bij (fun t _ => (t 0, t 1))
  · intro t ht
    exact mem_product.mpr ⟨Fintype.mem_piFinset.mp ht 0, Fintype.mem_piFinset.mp ht 1⟩
  · intro t _ t' _ he
    funext j
    fin_cases j
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · rintro ⟨q, p⟩ ht
    refine ⟨![q, p], Fintype.mem_piFinset.mpr ?_, rfl⟩
    intro j
    fin_cases j
    · exact (mem_product.mp ht).1
    · exact (mem_product.mp ht).2
  · intro t _
    simp only [Fin.prod_univ_two, mul_comm]

theorem pair_window_coefficient_pos {N p q : ℕ} {l u v w : ℝ}
    (hp : p ∈ window N l u) (hq : q ∈ window N v w) :
    0 < convolutionCoeff (pairWindows N l u v w) (p * q) := by
  apply convolutionCoeff_pos_iff.mpr
  refine ⟨![q, p], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hq
    · exact hp
  · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.mul_comm]

theorem separated_window_order {N p q : ℕ} {l u v w : ℝ}
    (hN : 1 ≤ N) (huv : u ≤ v)
    (hp : p ∈ window N l u) (hq : q ∈ window N v w) : p < q := by
  have huv' : (N : ℝ) ^ u ≤ (N : ℝ) ^ v :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) huv
  exact_mod_cast ((mem_window.mp hp).2.2.2.trans_le huv').trans_le (mem_window.mp hq).2.2.1

theorem separated_coefficient_one {N p q : ℕ} {l u v w : ℝ}
    (hN : 1 ≤ N) (huv : u ≤ v)
    (hp : p ∈ window N l u) (hq : q ∈ window N v w) :
    convolutionCoeff (pairWindows N l u v w) (p * q) = 1 := by
  unfold convolutionCoeff
  apply card_eq_one.mpr
  refine ⟨![q, p], ?_⟩
  ext t
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨ht, he⟩
    have ht0 : t 0 ∈ window N v w := Fintype.mem_piFinset.mp ht 0
    have ht1 : t 1 ∈ window N l u := Fintype.mem_piFinset.mp ht 1
    have hqprime := (mem_window.mp hq).1
    have he' : t 0 * t 1 = p * q := by simpa only [Fin.prod_univ_two] using he
    have hqd : q ∣ t 0 * t 1 := he'.symm ▸ dvd_mul_left q p
    have h0 : t 0 = q := by
      rcases hqprime.dvd_mul.mp hqd with h0 | h1
      · exact (((Nat.dvd_prime (mem_window.mp ht0).1).mp h0).resolve_left hqprime.ne_one).symm
      · have heq := ((Nat.dvd_prime (mem_window.mp ht1).1).mp h1).resolve_left hqprime.ne_one
        have hlt := separated_window_order hN huv ht1 hq
        omega
    have h1 : t 1 = p := by
      apply Nat.eq_of_mul_eq_mul_left hqprime.pos
      simpa only [h0, Nat.mul_comm p q] using he'
    funext j
    fin_cases j
    · exact h0
    · exact h1
  · intro he
    subst t
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      fin_cases j
      · exact hq
      · exact hp
    · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.mul_comm]

theorem rectangle_count_eq_convolution (N : ℕ) (l u v w : ℝ) :
    (rectangleCount N l u v w : ℝ) =
      ∑ d ∈ boxConvolutionSupport (pairWindows N l u v w),
        (convolutionCoeff (pairWindows N l u v w) d : ℝ) *
          (sourceSieveCountLE N d N ((N : ℝ) ^ alpha) : ℝ) := by
  rw [pair_window_fibres]
  simp only [rectangleCount, Int.cast_sum]

theorem eventually_window_nonempty {l u : ℝ} (hl : 0 < l) (hlu : l < u) (hu : u ≤ 1) :
    ∀ᶠ N : ℕ in atTop, (window N l u).Nonempty := by
  obtain ⟨T, hm⟩ := wu_primeWindow_reciprocal_mass_lower hl
  have hg : ∀ᶠ N : ℕ in atTop, (3 : ℝ) ≤ (N : ℝ) ^ (u - l) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hlu)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 3)
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ log (N : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hg, hlog, eventually_ge_atTop T, eventually_ge_atTop (2 : ℕ)]
    with N hg hlog hT hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog0 : 0 < log (N : ℝ) := by linarith
  let D := 1 + log (N : ℝ) ^ (-4 : ℝ)
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hDhi : D < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) := by
    have ht := rpow_pos_of_pos hlog0 (-4 : ℝ)
    dsimp [D]
    linarith
  have hD3 : D ≤ 3 := by
    have ht := rpow_le_one_of_one_le_of_nonpos hlog (by norm_num : (-4 : ℝ) ≤ 0)
    dsimp [D]
    linarith
  have hcut : (N : ℝ) ^ l ≤ (N : ℝ) ^ u / D := by
    apply (le_div_iff₀ hD0).mpr
    calc
      (N : ℝ) ^ l * D ≤ (N : ℝ) ^ l * (N : ℝ) ^ (u - l) :=
        mul_le_mul_of_nonneg_left (hD3.trans hg) (rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ u := by rw [← rpow_add hN0]; congr 1; ring
  have hmass := hm N hT D ((N : ℝ) ^ u) le_rfl hDhi
    (rpow_le_rpow_of_exponent_le hN1 hlu.le)
    (by simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1 hu)
  have hne : (primeWindow N ((N : ℝ) ^ u / D) ((N : ℝ) ^ u)).Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he, sum_empty] at hmass
    have hp : (0 : ℝ) < 1 / (12 * log (N : ℝ) ^ 5) := by positivity
    linarith
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hp, hc, hlo, hhi⟩ := mem_primeWindow.mp hp
  exact ⟨p, mem_window.mpr ⟨hp, hc, hcut.trans hlo, hhi⟩⟩

theorem eventually_original_high_pairs :
    ∀ᶠ N : ℕ in atTop,
      (∃ p q : ℕ, p ∈ window N alpha beta ∧ q ∈ window N beta aCeiling ∧
        (N : ℝ) ^ (1 / 4 : ℝ) < q) ∧
      (∃ p q : ℕ, p ∈ window N alpha bCut ∧ q ∈ window N aCeiling sigma ∧
        (N : ℝ) ^ (1 / 4 : ℝ) < q) := by
  have hpA := eventually_window_nonempty parameter_order.1
    (parameter_order.2.1.trans parameter_order.2.2.1)
    (parameter_order.2.2.2.1.trans_le (by norm_num : (1 / 4 : ℝ) ≤ 1)).le
  have hpB := eventually_window_nonempty parameter_order.1 parameter_order.2.1
    (parameter_order.2.2.1.trans (parameter_order.2.2.2.1.trans_le
      (by norm_num : (1 / 4 : ℝ) ≤ 1))).le
  have hmid : (1 / 4 : ℝ) < ((1 / 4 : ℝ) + aCeiling) / 2 ∧
      ((1 / 4 : ℝ) + aCeiling) / 2 < aCeiling := by
    have h := parameter_order.2.2.2.2.1
    constructor <;> linarith
  have hqa := eventually_window_nonempty
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hmid.1) hmid.2
    (parameter_order.2.2.2.2.2.1.trans parameter_order.2.2.2.2.2.2).le
  have hqb := eventually_window_nonempty
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 4) parameter_order.2.2.2.2.1)
    parameter_order.2.2.2.2.2.1 parameter_order.2.2.2.2.2.2.le
  filter_upwards [hpA, hpB, hqa, hqb, eventually_ge_atTop (2 : ℕ)] with N hpA hpB hqa hqb hN
  obtain ⟨pA, hpA⟩ := hpA
  obtain ⟨pB, hpB⟩ := hpB
  obtain ⟨qA, hqA⟩ := hqa
  obtain ⟨qB, hqB⟩ := hqb
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hqa' := mem_window.mp hqA
  have hqb' := mem_window.mp hqB
  have haHigh : (N : ℝ) ^ (1 / 4 : ℝ) < qA :=
    (rpow_lt_rpow_of_exponent_lt hN1 hmid.1).trans_le hqa'.2.2.1
  have hbHigh : (N : ℝ) ^ (1 / 4 : ℝ) < qB :=
    (rpow_lt_rpow_of_exponent_lt hN1 parameter_order.2.2.2.2.1).trans_le hqb'.2.2.1
  refine ⟨⟨pA, qA, hpA, ?_, haHigh⟩, ⟨pB, qB, hpB, hqB, hbHigh⟩⟩
  exact mem_window.mpr ⟨hqa'.1, hqa'.2.1,
    (rpow_le_rpow_of_exponent_le hN1.le (parameter_order.2.2.2.1.trans hmid.1).le).trans
      hqa'.2.2.1, hqa'.2.2.2⟩

#check @WuPaper.R2SixthCount.pairWindows
#check @WuPaper.R2SixthCount.pair_window_fibres
#check @WuPaper.R2SixthCount.pair_window_coefficient_pos
#check @WuPaper.R2SixthCount.separated_window_order
#check @WuPaper.R2SixthCount.separated_coefficient_one
#check @WuPaper.R2SixthCount.rectangle_count_eq_convolution
#check @WuPaper.R2SixthCount.eventually_window_nonempty
#check @WuPaper.R2SixthCount.eventually_original_high_pairs
#print axioms WuPaper.R2SixthCount.pairWindows
#print axioms WuPaper.R2SixthCount.pair_window_fibres
#print axioms WuPaper.R2SixthCount.pair_window_coefficient_pos
#print axioms WuPaper.R2SixthCount.separated_window_order
#print axioms WuPaper.R2SixthCount.separated_coefficient_one
#print axioms WuPaper.R2SixthCount.rectangle_count_eq_convolution
#print axioms WuPaper.R2SixthCount.eventually_window_nonempty
#print axioms WuPaper.R2SixthCount.eventually_original_high_pairs
end WuPaper.R2SixthCount
