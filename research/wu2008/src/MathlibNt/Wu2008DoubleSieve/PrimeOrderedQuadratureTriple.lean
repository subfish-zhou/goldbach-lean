import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureIntegral

/-! # Uniform quadrature for strictly ordered triples of actual primes -/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

/-- Regularity only, with no prime sum or quadrature hypothesis. -/
structure PrimeOrderedWeight (M K : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : Prop where
  bound : ∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ b ∈ Icc (1 / 10 : ℝ) (1 / 2),
    ∀ c ∈ Icc (1 / 10 : ℝ) (1 / 2), |f a b c| ≤ M
  first : ∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ a' ∈ Icc (1 / 10 : ℝ) (1 / 2),
    ∀ b ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ c ∈ Icc (1 / 10 : ℝ) (1 / 2),
    |f a b c - f a' b c| ≤ K * |a - a'|
  second : ∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ b ∈ Icc (1 / 10 : ℝ) (1 / 2),
    ∀ b' ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ c ∈ Icc (1 / 10 : ℝ) (1 / 2),
    |f a b c - f a b' c| ≤ K * |b - b'|
  third : ∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ b ∈ Icc (1 / 10 : ℝ) (1 / 2),
    ∀ c ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ c' ∈ Icc (1 / 10 : ℝ) (1 / 2),
    |f a b c - f a b c'| ≤ K * |c - c'|

noncomputable def primeOrderedInnerIntegral (B : ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (a b : ℝ) : ℝ := ∫ c in b..B, f a b c / c

noncomputable def primeOrderedMiddleIntegral (B : ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (a : ℝ) : ℝ := ∫ b in a..B, primeOrderedInnerIntegral B f a b / b

noncomputable def primeOrderedTripleIntegral (A B : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ a in A..B, primeOrderedMiddleIntegral B f a / a

theorem primeOrdered_inner_regular {f : ℝ → ℝ → ℝ → ℝ} {B M K : ℝ}
    (hw : PrimeOrderedWeight M K f) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hB : B ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    (∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ b ∈ Icc (1 / 10 : ℝ) (1 / 2), |primeOrderedInnerIntegral B f a b| ≤ 4 * M) ∧
    (∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ a' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ b ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |primeOrderedInnerIntegral B f a b - primeOrderedInnerIntegral B f a' b| ≤
        4 * K * |a - a'|) ∧
    (∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ b ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ b' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |primeOrderedInnerIntegral B f a b - primeOrderedInnerIntegral B f a b'| ≤
        (4 * K + 10 * M) * |b - b'|) := by
  have hc (a : ℝ) (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
      (b : ℝ) (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
      ContinuousOn (f a b) (Icc (1 / 10 : ℝ) (1 / 2)) :=
    primeOrdered_continuous_of_lipschitz (hw.third a ha b hb)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    exact primeOrdered_integral_norm_le_four hb hB hM (hw.bound a ha b hb)
  · intro a ha a' ha' b hb
    have h := primeOrdered_integral_sub_bound (hc a ha b hb) (hc a' ha' b hb)
      hb hB (mul_nonneg hK (abs_nonneg _)) (hw.first a ha a' ha' b hb)
    dsimp [primeOrderedInnerIntegral]
    linarith only [h]
  · intro a ha
    exact (primeOrdered_moving_integral_lipschitz hB hM hK
      (hc a ha) (hw.bound a ha) (hw.second a ha)).2

theorem primeOrdered_middle_regular {f : ℝ → ℝ → ℝ → ℝ} {B M K : ℝ}
    (hw : PrimeOrderedWeight M K f) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hB : B ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    (∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |primeOrderedMiddleIntegral B f a| ≤ 16 * M) ∧
    (∀ a ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ a' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |primeOrderedMiddleIntegral B f a - primeOrderedMiddleIntegral B f a'| ≤
        (16 * K + 40 * M) * |a - a'|) := by
  obtain ⟨hb, hl₁, hl₂⟩ := primeOrdered_inner_regular hw hM hK hB
  have h := primeOrdered_moving_integral_lipschitz hB
    (show 0 ≤ 4 * M by positivity) (show 0 ≤ 4 * K by positivity)
    (fun a ha => primeOrdered_continuous_of_lipschitz (hl₂ a ha)) hb hl₁
  simpa only [primeOrderedMiddleIntegral, show 4 * (4 * M) = 16 * M by ring,
    show 4 * (4 * K) + 10 * (4 * M) = 16 * K + 40 * M by ring] using h

private theorem closed_coordinate_mem {R A B : ℝ} (hR : 1 < R)
    {p : ℕ} (hp : p ∈ primesIcc (R ^ A) (R ^ B)) :
    log p / log R ∈ Icc A B := by
  have hR0 : 0 < R := by linarith
  have h := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hp
  have hl := log_le_log (rpow_pos_of_pos hR0 _) h.2.1
  have hu := log_le_log (by exact_mod_cast h.1.pos : (0 : ℝ) < p) h.2.2
  rw [log_rpow hR0] at hl hu
  exact ⟨(le_div_iff₀ (log_pos hR)).2 hl, (div_le_iff₀ (log_pos hR)).2 hu⟩

private theorem sum_difference {s : Finset ℕ} {u v : ℕ → ℝ} {η : ℝ}
    (h : ∀ p ∈ s, |u p - v p| ≤ η) :
    |(∑ p ∈ s, u p / p) - ∑ p ∈ s, v p / p| ≤
      η * ∑ p ∈ s, 1 / (p : ℝ) := by
  rw [← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (h p hp) (Nat.cast_nonneg p)

private theorem prime_mass_le_five {R A B : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hD : primeOrderedDiscrepancy R ≤ 1)
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2) :
    (∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ)) ≤ 5 ∧
    (∑ p ∈ primesIoc (R ^ A) (R ^ B), 1 / (p : ℝ)) ≤ 5 := by
  have h := (le_abs_self _).trans (primeOrdered_reciprocal_Icc_uniform_bound hR hs hA hAB hB)
  have hi := (primeOrdered_exponent_density_bounds hA hAB hB).2
  have hclosed : (∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ)) ≤ 5 := by linarith
  refine ⟨hclosed, (sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)).trans hclosed⟩
  intro p hp
  have hR0 : 0 ≤ R := by linarith
  rw [mem_primesIcc (rpow_nonneg hR0 _)]
  have hp' := (mem_primesIoc (rpow_nonneg hR0 _)).mp hp
  exact ⟨hp'.1, hp'.2.1.le, hp'.2.2⟩

private theorem one_dimensional_both (M K ε : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ (f : ℝ → ℝ) (A B : ℝ),
      ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)) →
      (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M) →
      (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
        |f x - f y| ≤ K * |x - y|) →
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |primeOrderedClosedSum R A B f - ∫ t in A..B, f t / t| ≤ ε ∧
      |primeOrderedSum R A B f - ∫ t in A..B, f t / t| ≤ ε := by
  have hlim : Tendsto (fun R : ℝ => M / R ^ (1 / 10 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
  filter_upwards [primeOrdered_weighted_uniform M K (ε / 2) hM hK (half_pos hε),
    eventually_gt_atTop 1, hlim.eventually (gt_mem_nhds (half_pos hε))] with R h hR ha
  intro f A B hf hb hl hA hAB hB
  have hc := h f A B hf hb hl hA hAB hB
  have hatom := primeOrdered_closed_atom_bound hR hA hAB hB hM hb
  have hh := abs_sub_le (primeOrderedSum R A B f) (primeOrderedClosedSum R A B f)
    (∫ t in A..B, f t / t)
  rw [abs_sub_comm (primeOrderedSum R A B f) (primeOrderedClosedSum R A B f)] at hh
  constructor <;> linarith

noncomputable def primeOrderedNestedSum (R A B : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  primeOrderedClosedSum R A B (fun a =>
    primeOrderedSum R a B (fun b => primeOrderedSum R b B (f a b)))

/-- The actual prime sums occur in the conclusion. Uniformity is over the
entire bounded separately Lipschitz cube class and over moving endpoints. -/
theorem primeOrdered_nested_uniform (M K ε : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ (f : ℝ → ℝ → ℝ → ℝ),
      PrimeOrderedWeight M K f → ∀ A B : ℝ,
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |primeOrderedNestedSum R A B f - primeOrderedTripleIntegral A B f| < ε := by
  let η := ε / 32
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    one_dimensional_both M K η hM hK hη,
    one_dimensional_both (4 * M) (4 * K + 10 * M) η (by positivity) (by positivity) hη,
    one_dimensional_both (16 * M) (16 * K + 40 * M) η (by positivity) (by positivity) hη]
    with R hR hs hD h₁ h₂ h₃
  intro f hw A B hA hAB hB
  have hBm : B ∈ Icc (1 / 10 : ℝ) (1 / 2) := ⟨hA.trans hAB, hB⟩
  obtain ⟨hib, hil₁, hil₂⟩ := primeOrdered_inner_regular hw hM hK hBm
  obtain ⟨hmb, hml⟩ := primeOrdered_middle_regular hw hM hK hBm
  have hc₃ (a : ℝ) (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
      (b : ℝ) (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2)) :=
    primeOrdered_continuous_of_lipschitz (hw.third a ha b hb)
  have hinner (a : ℝ) (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
      (b : ℝ) (hb : b ∈ Icc (1 / 10 : ℝ) B) :
      |primeOrderedSum R b B (f a b) - primeOrderedInnerIntegral B f a b| ≤ η :=
    (h₁ (f a b) b B (hc₃ a ha b ⟨hb.1, hb.2.trans hB⟩)
      (hw.bound a ha b ⟨hb.1, hb.2.trans hB⟩)
      (hw.third a ha b ⟨hb.1, hb.2.trans hB⟩) hb.1 hb.2 hB).2
  have hmiddle (a : ℝ) (ha : a ∈ Icc (1 / 10 : ℝ) B) :
      |primeOrderedSum R a B (fun b => primeOrderedSum R b B (f a b)) -
        primeOrderedMiddleIntegral B f a| ≤ 6 * η := by
    have ham : a ∈ Icc (1 / 10 : ℝ) (1 / 2) := ⟨ha.1, ha.2.trans hB⟩
    have hreplace :
        |primeOrderedSum R a B (fun b => primeOrderedSum R b B (f a b)) -
          primeOrderedSum R a B (primeOrderedInnerIntegral B f a)| ≤ 5 * η := by
      refine (sum_difference (η := η) ?_).trans ?_
      · intro p hp
        have hpc := primeOrdered_coordinate_mem hR hp
        exact hinner a ham _ ⟨ha.1.trans hpc.1.le, hpc.2⟩
      · have hm := (prime_mass_le_five hR hs hD.le ha.1 ha.2 hB).2
        nlinarith [mul_le_mul_of_nonneg_left hm hη.le]
    have hquad := (h₂ (primeOrderedInnerIntegral B f a) a B
      (primeOrdered_continuous_of_lipschitz (hil₂ a ham)) (hib a ham) (hil₂ a ham)
      ha.1 ha.2 hB).2
    change |primeOrderedSum R a B (primeOrderedInnerIntegral B f a) -
      primeOrderedMiddleIntegral B f a| ≤ η at hquad
    have hh := abs_sub_le
      (primeOrderedSum R a B (fun b => primeOrderedSum R b B (f a b)))
      (primeOrderedSum R a B (primeOrderedInnerIntegral B f a))
      (primeOrderedMiddleIntegral B f a)
    linarith only [hreplace, hquad, hh]
  have houter :
      |primeOrderedNestedSum R A B f -
        primeOrderedClosedSum R A B (primeOrderedMiddleIntegral B f)| ≤ 30 * η := by
    dsimp only [primeOrderedNestedSum, primeOrderedClosedSum]
    refine (sum_difference (η := 6 * η) ?_).trans ?_
    · intro p hp
      have hpc := closed_coordinate_mem hR hp
      exact hmiddle _ ⟨hA.trans hpc.1, hpc.2⟩
    · have hm := (prime_mass_le_five hR hs hD.le hA hAB hB).1
      nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 6 * η by positivity)]
  have hquad := (h₃ (primeOrderedMiddleIntegral B f) A B
    (primeOrdered_continuous_of_lipschitz hml) hmb hml hA hAB hB).1
  have hh := abs_sub_le (primeOrderedNestedSum R A B f)
    (primeOrderedClosedSum R A B (primeOrderedMiddleIntegral B f))
    (primeOrderedTripleIntegral A B f)
  change |primeOrderedClosedSum R A B (primeOrderedMiddleIntegral B f) -
    primeOrderedTripleIntegral A B f| ≤ η at hquad
  dsimp [η] at houter hquad
  linarith

/-- A literal finite sum with closed outer lower endpoint, strict prime
inequalities, and closed upper endpoints. No diagonal is inserted or discarded. -/
noncomputable def primeOrderedTripleSum (R A B : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∑ p₁ ∈ primesIcc (R ^ A) (R ^ B),
    ∑ p₂ ∈ primesIoc (p₁ : ℝ) (R ^ B),
      ∑ p₃ ∈ primesIoc (p₂ : ℝ) (R ^ B),
        f (log p₁ / log R) (log p₂ / log R) (log p₃ / log R) /
          ((p₁ : ℝ) * p₂ * p₃)

theorem primeOrdered_coordinate_rpow {R : ℝ} (hR : 1 < R)
    {p : ℕ} (hp : p.Prime) : R ^ (log p / log R) = (p : ℝ) := by
  rw [rpow_def_of_pos (by linarith : 0 < R)]
  have hlR : log R ≠ 0 := (log_pos hR).ne'
  rw [mul_div_cancel₀ _ hlR]
  exact exp_log (by exact_mod_cast hp.pos)

theorem primeOrderedTripleSum_eq_nested {R A B : ℝ} (hR : 1 < R)
    (f : ℝ → ℝ → ℝ → ℝ) :
    primeOrderedTripleSum R A B f = primeOrderedNestedSum R A B f := by
  unfold primeOrderedTripleSum primeOrderedNestedSum primeOrderedClosedSum
  apply sum_congr rfl
  intro p₁ hp₁
  dsimp only
  have hp₁' := ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp hp₁).1
  rw [primeOrderedSum, primeOrdered_coordinate_rpow hR hp₁', Finset.sum_div]
  apply sum_congr rfl
  intro p₂ hp₂
  have hp₂' := ((mem_primesIoc (rpow_nonneg (by linarith : 0 ≤ R) _)).mp hp₂).1
  rw [primeOrderedSum, primeOrdered_coordinate_rpow hR hp₂', Finset.sum_div, Finset.sum_div]
  apply sum_congr rfl
  intro p₃ _
  ring

/-- The density is exactly `1/(a*b*c)` over the ordered simplex. -/
theorem primeOrderedTripleIntegral_eq (A B : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    primeOrderedTripleIntegral A B f =
      ∫ a in A..B, ∫ b in a..B, ∫ c in b..B, f a b c / (a * b * c) := by
  unfold primeOrderedTripleIntegral primeOrderedMiddleIntegral primeOrderedInnerIntegral
  apply intervalIntegral.integral_congr
  intro a _
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro b _
  dsimp only
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro c _
  ring

theorem primeOrderedTripleSum_self {R A : ℝ} (hR : 1 < R)
    (f : ℝ → ℝ → ℝ → ℝ) :
    primeOrderedTripleSum R A A f = 0 := by
  unfold primeOrderedTripleSum
  apply sum_eq_zero
  intro p₁ hp₁
  have hR0 : 0 ≤ R := by linarith
  have hp₁' := (mem_primesIcc (rpow_nonneg hR0 _)).mp hp₁
  apply sum_eq_zero
  intro p₂ hp₂
  have hp₂' := (mem_primesIoc (rpow_nonneg hR0 _)).mp hp₂
  exact False.elim (not_lt_of_ge (hp₂'.2.2.trans hp₁'.2.1) hp₂'.2.1)

theorem primeOrderedTripleIntegral_self (A : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    primeOrderedTripleIntegral A A f = 0 := by
  simp only [primeOrderedTripleIntegral, intervalIntegral.integral_same]

/-- Uniform ordered three-prime quadrature, with an actual strict finite prime
carrier and the actual iterated integral. The only hypotheses on the entire
weight family are a common bound and a common coordinatewise Lipschitz bound. -/
theorem primeOrdered_triple_uniform (M K ε : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ (f : ℝ → ℝ → ℝ → ℝ),
      PrimeOrderedWeight M K f → ∀ A B : ℝ,
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |primeOrderedTripleSum R A B f -
        ∫ a in A..B, ∫ b in a..B, ∫ c in b..B, f a b c / (a * b * c)| < ε := by
  filter_upwards [eventually_gt_atTop 1, primeOrdered_nested_uniform M K ε hM hK hε]
    with R hR h
  intro f hf A B hA hAB hB
  rw [primeOrderedTripleSum_eq_nested hR, ← primeOrderedTripleIntegral_eq]
  exact h f hf A B hA hAB hB

end Wu2008DoubleSieve
