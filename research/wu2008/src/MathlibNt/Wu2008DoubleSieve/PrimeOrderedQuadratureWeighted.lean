import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadrature

/-!
# Uniform weighted reciprocal-prime quadrature

Finite exponent partitions transfer the Mertens interval discrepancy to bounded
Lipschitz families. Differentiability is not assumed, in particular not across
the Buchstab fold.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def primeOrderedSum (R A B : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ p ∈ primesIoc (R ^ A) (R ^ B), f (log p / log R) / p

theorem primeOrdered_coordinate_mem {R A B : ℝ} (hR : 1 < R)
    {p : ℕ} (hp : p ∈ primesIoc (R ^ A) (R ^ B)) :
    log p / log R ∈ Ioc A B := by
  have hR0 : 0 < R := by linarith
  have h := (mem_primesIoc (rpow_nonneg hR0.le _) ).mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast h.1.pos
  have hl := log_lt_log (rpow_pos_of_pos hR0 _) h.2.1
  have hu := log_le_log hp0 h.2.2
  rw [log_rpow hR0] at hl hu
  exact ⟨(lt_div_iff₀ (log_pos hR)).2 hl,
    (div_le_iff₀ (log_pos hR)).2 hu⟩

theorem primeOrderedSum_add {R A B C : ℝ} (hR : 1 < R)
    (hAB : A ≤ B) (hBC : B ≤ C) (f : ℝ → ℝ) :
    primeOrderedSum R A C f =
      primeOrderedSum R A B f + primeOrderedSum R B C f := by
  have hR0 : 0 < R := by linarith
  have hpowAB := rpow_le_rpow_of_exponent_le hR.le hAB
  have hpowBC := rpow_le_rpow_of_exponent_le hR.le hBC
  have hs : primesIoc (R ^ A) (R ^ C) =
      primesIoc (R ^ A) (R ^ B) ∪ primesIoc (R ^ B) (R ^ C) := by
    ext p
    simp only [Finset.mem_union, mem_primesIoc (rpow_nonneg hR0.le _)]
    constructor
    · intro hp
      by_cases h : (p : ℝ) ≤ R ^ B
      · exact Or.inl ⟨hp.1, hp.2.1, h⟩
      · exact Or.inr ⟨hp.1, lt_of_not_ge h, hp.2.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1, hp.2.1, hp.2.2.trans hpowBC⟩
      · exact ⟨hp.1, hpowAB.trans_lt hp.2.1, hp.2.2⟩
  have hd : Disjoint (primesIoc (R ^ A) (R ^ B)) (primesIoc (R ^ B) (R ^ C)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_primesIoc (rpow_nonneg hR0.le _)).mp hp
    have hq' := (mem_primesIoc (rpow_nonneg hR0.le _)).mp hq
    exact (not_lt_of_ge hp'.2.2) hq'.2.1
  simp only [primeOrderedSum, hs, Finset.sum_union hd]

theorem primeOrderedSum_self {R : ℝ} (hR : 1 < R) (A : ℝ) (f : ℝ → ℝ) :
    primeOrderedSum R A A f = 0 := by
  unfold primeOrderedSum
  apply sum_eq_zero
  intro p hp
  have hp' := (mem_primesIoc (rpow_nonneg (by linarith : 0 ≤ R) A)).mp hp
  exact False.elim (lt_irrefl _ (hp'.2.1.trans_le hp'.2.2))

private theorem weighted_integrable {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)))
    {A B : ℝ} (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2) :
    IntervalIntegrable (fun t => f t / t) volume A B := by
  have hs : uIcc A B ⊆ Icc (1 / 10 : ℝ) (1 / 2) := by
    rw [uIcc_of_le hAB]
    exact Icc_subset_Icc hA hB
  exact ((hf.mono hs).div continuousOn_id
    (fun t ht => ne_of_gt (by change 0 < t; have := (hs ht).1; linarith))).intervalIntegrable

theorem primeOrdered_weighted_cell {R A B M K : ℝ} {f : ℝ → ℝ}
    (hR : 1 < R) (hstart : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2)
    (hf : ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)))
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M)
    (hlip : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2), |f x - f y| ≤ K * |x - y|) :
    |primeOrderedSum R A B f - ∫ t in A..B, f t / t| ≤
      K * (B - A) *
        ((∑ p ∈ primesIoc (R ^ A) (R ^ B), 1 / (p : ℝ)) +
          ∫ t in A..B, 1 / t) + M * primeOrderedDiscrepancy R := by
  have hAmem : A ∈ Icc (1 / 10 : ℝ) (1 / 2) := ⟨hA, hAB.trans hB⟩
  have hsub : Icc A B ⊆ Icc (1 / 10 : ℝ) (1 / 2) := Icc_subset_Icc hA hB
  have hv (t : ℝ) (ht : t ∈ Icc A B) : |f t - f A| ≤ K * (B - A) := by
    have h := hlip t (hsub ht) A hAmem
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK)
  let P := ∑ p ∈ primesIoc (R ^ A) (R ^ B), 1 / (p : ℝ)
  let I := ∫ t in A..B, 1 / t
  have hP0 : 0 ≤ P := sum_nonneg (fun p _ => by positivity)
  have hI0 : 0 ≤ I := (primeOrdered_exponent_density_bounds hA hAB hB).1
  have hp : |primeOrderedSum R A B f - f A * P| ≤ K * (B - A) * P := by
    dsimp [primeOrderedSum, P]
    rw [mul_sum, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro p hp
    have ht := primeOrdered_coordinate_mem hR hp
    have he : f (log p / log R) / p - f A * (1 / (p : ℝ)) =
        (f (log p / log R) - f A) / p := by ring
    rw [he, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    simpa only [div_eq_mul_inv, one_mul] using
      div_le_div_of_nonneg_right (hv _ ⟨ht.1.le, ht.2⟩) (Nat.cast_nonneg p)
  have hi : |(∫ t in A..B, f t / t) - f A * I| ≤ K * (B - A) * I := by
    have hj : IntervalIntegrable (fun t : ℝ => 1 / t) volume A B :=
      weighted_integrable continuousOn_const hA hAB hB
    dsimp [I]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (weighted_integrable hf hA hAB hB) (hj.const_mul (f A)),
      ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hAB
    · apply Eventually.of_forall
      intro t ht
      rw [Real.norm_eq_abs, show f t / t - f A * (1 / t) = (f t - f A) / t by ring,
        abs_div, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]
      simpa only [div_eq_mul_inv, one_mul] using
        div_le_div_of_nonneg_right (hv t ⟨ht.1.le, ht.2⟩)
          (by linarith [ht.1] : 0 ≤ t)
    · exact hj.const_mul _
  have he : |f A * P - f A * I| ≤ M * primeOrderedDiscrepancy R := by
    rw [← mul_sub, abs_mul]
    apply mul_le_mul (hbound A hAmem) _ (abs_nonneg _) hM
    have h := primeOrdered_reciprocal_Ioc_uniform_bound hR hstart hA hAB hB
    exact h.trans (by
      unfold primeOrderedDiscrepancy
      have : 0 ≤ 1 / R ^ (1 / 10 : ℝ) := by positivity
      linarith)
  have hh := abs_sub_le (primeOrderedSum R A B f) (f A * P) (∫ t in A..B, f t / t)
  have hh' := abs_sub_le (f A * P) (f A * I) (∫ t in A..B, f t / t)
  rw [abs_sub_comm (f A * I)] at hh'
  dsimp [P, I] at hp hi he hh hh' ⊢
  nlinarith only [hp, hi, he, hh, hh']

private theorem additive_partition_sum (J : ℝ → ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ)
    (hzero : J (x 0) (x 0) = 0)
    (hadd : ∀ i < n, J (x 0) (x (i + 1)) = J (x 0) (x i) + J (x i) (x (i + 1))) :
    ∑ i ∈ range n, J (x i) (x (i + 1)) = J (x 0) (x n) := by
  induction n with
  | zero => simpa using hzero.symm
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => hadd i (by omega)), hadd n (by omega)]

/-- A finite-partition bound. The number of cells is chosen before the scale,
the moving endpoints, and the weight. -/
theorem primeOrdered_weighted_partition_bound {R A B M K : ℝ} {f : ℝ → ℝ}
    (n : ℕ) (hn : 0 < n)
    (hR : 1 < R) (hstart : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hD : primeOrderedDiscrepancy R ≤ 1)
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2)
    (hf : ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)))
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M)
    (hlip : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2), |f x - f y| ≤ K * |x - y|) :
    |primeOrderedSum R A B f - ∫ t in A..B, f t / t| ≤
      9 * K / n + n * M * primeOrderedDiscrepancy R := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let x : ℕ → ℝ := fun i => A + (B - A) * i / n
  have hx0 : x 0 = A := by simp [x]
  have hxn : x n = B := by dsimp [x]; field_simp; ring
  have hmono : Monotone x := by
    intro i j hij
    dsimp [x]
    gcongr
  have hxmin (i : ℕ) : A ≤ x i := hx0 ▸ hmono (Nat.zero_le i)
  have hxmax (i : ℕ) (hi : i ≤ n) : x i ≤ B := hxn ▸ hmono hi
  have hxstep (i : ℕ) : x (i + 1) - x i = (B - A) / n := by
    dsimp [x]
    push_cast
    ring
  have hsumP (g : ℝ → ℝ) :
      ∑ i ∈ range n, primeOrderedSum R (x i) (x (i + 1)) g =
        primeOrderedSum R A B g := by
    have h := additive_partition_sum (fun a b => primeOrderedSum R a b g) x n
      (primeOrderedSum_self hR _ _)
      (fun i _ => primeOrderedSum_add hR (hmono (Nat.zero_le i)) (hmono (by omega)) g)
    simpa only [hx0, hxn] using h
  have hsumI (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (1 / 10 : ℝ) (1 / 2))) :
      ∑ i ∈ range n, (∫ t in x i..x (i + 1), g t / t) =
        ∫ t in A..B, g t / t := by
    have h := additive_partition_sum (fun a b => ∫ t in a..b, g t / t) x n
      (intervalIntegral.integral_same)
      (fun i hi => (intervalIntegral.integral_add_adjacent_intervals
        (weighted_integrable hg (hx0 ▸ hA) (hmono (Nat.zero_le i))
          ((hxmax i (by omega)).trans hB))
        (weighted_integrable hg (hA.trans (hxmin i)) (hmono (by omega))
          ((hxmax (i + 1) (by omega)).trans hB))).symm)
    simpa only [hx0, hxn] using h
  have hcell (i : ℕ) (hi : i ∈ range n) :=
    primeOrdered_weighted_cell hR hstart (hA.trans (hxmin i)) (hmono (by omega))
      ((hxmax (i + 1) (by have := mem_range.mp hi; omega)).trans hB)
      hf hM hK hbound hlip
  have hsum :
      |primeOrderedSum R A B f - ∫ t in A..B, f t / t| ≤
      K * ((B - A) / n) *
        (primeOrderedSum R A B (fun _ => 1) + ∫ t in A..B, 1 / t) +
        n * M * primeOrderedDiscrepancy R := by
    rw [← hsumP f, ← hsumI f hf, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ range n, (K * ((B - A) / n) *
          (primeOrderedSum R (x i) (x (i + 1)) (fun _ => 1) +
            ∫ t in x i..x (i + 1), 1 / t) + M * primeOrderedDiscrepancy R) := by
        apply sum_le_sum
        intro i hi
        simpa only [hxstep, primeOrderedSum] using hcell i hi
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, sum_add_distrib,
          hsumP (fun _ => 1), hsumI (fun _ => 1) continuousOn_const]
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
  have hI := primeOrdered_exponent_density_bounds hA hAB hB
  have hP := primeOrdered_reciprocal_Ioc_uniform_bound hR hstart hA hAB hB
  have hP' : primeOrderedSum R A B (fun _ => 1) ≤ 5 := by
    have hh := (le_abs_self _).trans hP
    have htail : 0 ≤ 1 / R ^ (1 / 10 : ℝ) := by positivity
    unfold primeOrderedDiscrepancy at hD
    dsimp [primeOrderedSum]
    linarith
  have hprod := mul_le_mul_of_nonneg_left
    (show primeOrderedSum R A B (fun _ => 1) + (∫ t in A..B, 1 / t) ≤ 9 by linarith)
    (show 0 ≤ K * ((B - A) / n) by positivity)
  have hwidth : (B - A) / (n : ℝ) ≤ 1 / n :=
    div_le_div_of_nonneg_right (by linarith) hnR.le
  have hprod' := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 9 * K by positivity)
  have hprod'' : K * ((B - A) / n) * 9 ≤ 9 * K / n := by
    convert! hprod' using 1 <;> ring
  linarith only [hsum, hprod, hprod'']

noncomputable def primeOrderedClosedSum (R A B : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ p ∈ primesIcc (R ^ A) (R ^ B), f (log p / log R) / p

theorem primeOrdered_closed_atom_bound {R A B M : ℝ} {f : ℝ → ℝ}
    (hR : 1 < R) (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2)
    (hM : 0 ≤ M) (hbound : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M) :
    |primeOrderedClosedSum R A B f - primeOrderedSum R A B f| ≤
      M / R ^ (1 / 10 : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hlR : log R ≠ 0 := (log_pos hR).ne'
  unfold primeOrderedClosedSum primeOrderedSum
  rw [sum_primesIcc_eq_sum_primesIoc_add (rpow_nonneg hR0.le _)
    (fun t : ℝ => f (log t / log R) / t), add_sub_cancel_left]
  split_ifs
  · rw [log_rpow hR0, mul_div_cancel_right₀ _ hlR, abs_div,
      abs_of_pos (rpow_pos_of_pos hR0 A)]
    exact (div_le_div_of_nonneg_right (hbound A ⟨hA, hAB.trans hB⟩)
      (rpow_nonneg hR0.le A)).trans
      (div_le_div_of_nonneg_left hM (rpow_pos_of_pos hR0 _)
        (rpow_le_rpow_of_exponent_le hR.le hA))
  · simp only [abs_zero]
    positivity

theorem primeOrdered_weighted_closed_partition_bound {R A B M K : ℝ} {f : ℝ → ℝ}
    (n : ℕ) (hn : 0 < n)
    (hR : 1 < R) (hstart : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (hD : primeOrderedDiscrepancy R ≤ 1)
    (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2)
    (hf : ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)))
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M)
    (hlip : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2), |f x - f y| ≤ K * |x - y|) :
    |primeOrderedClosedSum R A B f - ∫ t in A..B, f t / t| ≤
      9 * K / n + (n + 1) * M * primeOrderedDiscrepancy R := by
  have hp := primeOrdered_weighted_partition_bound n hn hR hstart hD hA hAB hB
    hf hM hK hbound hlip
  have ha := primeOrdered_closed_atom_bound hR hA hAB hB hM hbound
  have hb : M / R ^ (1 / 10 : ℝ) ≤ M * primeOrderedDiscrepancy R := by
    have hl : 0 ≤ 20 * primeOrderedMertensConstant / log R := by
      have := log_pos hR
      have := primeOrderedMertensConstant_pos
      positivity
    have hh : 1 / R ^ (1 / 10 : ℝ) ≤ primeOrderedDiscrepancy R := by
      unfold primeOrderedDiscrepancy
      linarith
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh hM
  have hh := abs_sub_le (primeOrderedClosedSum R A B f) (primeOrderedSum R A B f)
    (∫ t in A..B, f t / t)
  nlinarith only [hp, ha, hb, hh]

/-- Genuine uniform quadrature for an entire bounded Lipschitz family.
The threshold precedes the function and both real endpoints. -/
theorem primeOrdered_weighted_uniform (M K ε : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ (f : ℝ → ℝ) (A B : ℝ),
      ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)) →
      (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ M) →
      (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
        ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2), |f x - f y| ≤ K * |x - y|) →
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |primeOrderedClosedSum R A B f - ∫ t in A..B, f t / t| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (18 * K / ε))
  have hn0 : 0 < n := by
    have : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
    exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnerr : 9 * K / n < ε / 2 := by
    have hn' := (le_max_right _ _).trans_lt hn
    have hh := (div_lt_iff₀ hε).mp hn'
    apply (div_lt_iff₀ hnR).2
    nlinarith
  have hlim : Tendsto (fun R : ℝ => 9 * K / n +
      ((n : ℝ) + 1) * M * primeOrderedDiscrepancy R) atTop (𝓝 (9 * K / n)) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (primeOrderedDiscrepancy_tendsto.const_mul (((n : ℝ) + 1) * M))
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlim.eventually (gt_mem_nhds (hnerr.trans (half_lt_self hε)))] with R hR hs hD herr
  intro f A B hf hb hl hA hAB hB
  exact (primeOrdered_weighted_closed_partition_bound n hn0 hR hs hD.le hA hAB hB
    hf hM hK hb hl).trans_lt herr

end Wu2008DoubleSieve
