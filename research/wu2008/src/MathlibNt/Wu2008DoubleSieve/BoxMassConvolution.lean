import MathlibNt.Wu2008DoubleSieve.BoxMassUniform

/-!
# Wu (2004), (3.5), (3.6), and the exact identity (3.8)

All sums retain ordered-tuple multiplicities, including repeated primes and
overlapping windows. The empty tuple gives the Dirichlet unit at `1`.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology

noncomputable def boxConvolutionSupport {i : ℕ} (W : Fin i → Finset ℕ) : Finset ℕ :=
  (Fintype.piFinset W).image (fun t => ∏ j, t j)

noncomputable def boxConvolutionReciprocalMass {i : ℕ} (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) / d

theorem mem_boxConvolutionSupport {i d : ℕ} {W : Fin i → Finset ℕ} :
    d ∈ boxConvolutionSupport W ↔ 0 < convolutionCoeff W d := by
  simp only [boxConvolutionSupport, mem_image, convolutionCoeff_pos_iff,
    Fintype.mem_piFinset]

/-- Exact fibre regrouping for any real-valued function of the product. -/
theorem boxConvolution_sum_fibres {i : ℕ} (W : Fin i → Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * f d) =
      ∑ t ∈ Fintype.piFinset W, f (∏ j, t j) := by
  have h := sum_fiberwise_of_maps_to' (s := Fintype.piFinset W)
    (fun t ht => mem_image_of_mem (fun u : Fin i → ℕ => ∏ j, u j) ht) f
  simpa only [sum_const, nsmul_eq_mul, convolutionCoeff, boxConvolutionSupport] using h

/-- Wu (3.8), literally on the full finite convolution support. -/
theorem boxConvolutionReciprocalMass_eq_product {i : ℕ} (W : Fin i → Finset ℕ) :
    boxConvolutionReciprocalMass W =
      ∏ j, ∑ p ∈ W j, (1 : ℝ) / p := by
  unfold boxConvolutionReciprocalMass
  simp_rw [div_eq_mul_inv]
  rw [boxConvolution_sum_fibres, prod_univ_sum]
  apply sum_congr rfl
  intro t _
  simp only [Nat.cast_prod, prod_inv_distrib, one_mul]

theorem boxConvolutionReciprocalMass_zero_depth (W : Fin 0 → Finset ℕ) :
    boxConvolutionReciprocalMass W = 1 := by
  rw [boxConvolutionReciprocalMass_eq_product]
  simp

theorem boxConvolutionSupport_pos {i : ℕ} {W : Fin i → Finset ℕ}
    (hW : ∀ j p, p ∈ W j → 0 < p) {d : ℕ} (hd : d ∈ boxConvolutionSupport W) :
    0 < d := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
  exact prod_pos fun j _ => hW j (t j) (Fintype.mem_piFinset.mp ht j)

theorem boxConvolutionSupport_le_product {i : ℕ} {W : Fin i → Finset ℕ}
    {V : Fin i → ℝ} (hW : ∀ j p, p ∈ W j → (p : ℝ) ≤ V j)
    {d : ℕ} (hd : d ∈ boxConvolutionSupport W) :
    (d : ℝ) ≤ ∏ j, V j := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
  rw [Nat.cast_prod]
  exact prod_le_prod (fun j _ => Nat.cast_nonneg (t j))
    (fun j _ => hW j (t j) (Fintype.mem_piFinset.mp ht j))

/-- The elementary companion upper bound uses all integers, not a PNT. -/
theorem box_primeWindow_mass_upper {N : ℕ} {Δ V : ℝ}
    (hV : 1 ≤ V) (hΔ : 0 < Δ) (hΔ3 : Δ ≤ 3) :
    (∑ p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / p) ≤ 6 := by
  have hY : 0 < V / Δ := div_pos (by linarith) hΔ
  have hcard : ((primeWindow N (V / Δ) V).card : ℝ) ≤ (⌈V⌉₊ : ℝ) := by
    exact_mod_cast (card_le_card (filter_subset
      (fun p : ℕ => p.Prime ∧ p.Coprime N ∧ V / Δ ≤ (p : ℝ)) (range ⌈V⌉₊))).trans
        (by simp : (range ⌈V⌉₊).card ≤ ⌈V⌉₊)
  have hceil : (⌈V⌉₊ : ℝ) ≤ 2 * V := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ V)
    linarith
  calc
    _ ≤ ∑ _p ∈ primeWindow N (V / Δ) V, (1 : ℝ) / (V / Δ) := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hY (mem_primeWindow.mp hp).2.2.1
    _ = ((primeWindow N (V / Δ) V).card : ℝ) / (V / Δ) := by simp [div_eq_mul_inv]
    _ ≤ (2 * V) / (V / Δ) := div_le_div_of_nonneg_right (hcard.trans hceil) hY.le
    _ = 2 * Δ := by field_simp
    _ ≤ 6 := by linarith

/-- Uniform two-sided mass in (3.5). Fixed `k,α` precede the threshold,
all depths `i ≤ k`, and all endpoints. The source exponent is
`α = δ^(k+1)`. Ordering and squared-prefix constraints are not needed here. -/
theorem wu_boxConvolution_mass_bounds (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
      1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
      ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ α ≤ V j) → (∀ j, V j ≤ N) →
        (1 / 12 : ℝ) ^ k / Real.log (N : ℝ) ^ (5 * k) ≤
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ∧
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤ 6 ^ k := by
  obtain ⟨N₁, hmass⟩ := wu_primeWindow_reciprocal_mass_lower hα
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  obtain ⟨N₂, hlog⟩ := eventually_atTop.mp hlog
  refine ⟨max 1 (max N₁ N₂), ?_⟩
  intro N hN i hik Δ hΔlo hΔhi V hVlo hVhi
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hL := hlog N hN₂
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hbase : 1 / (12 * Real.log (N : ℝ) ^ 5) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    have := one_le_pow₀ hL (n := 5)
    linarith
  have hΔ0 : 0 < Δ := by
    have := Real.rpow_nonneg hL0.le (-4)
    linarith
  have hΔ3 : Δ ≤ 3 := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hL (show (-4 : ℝ) ≤ 0 by norm_num)
    linarith
  rw [boxConvolutionReciprocalMass_eq_product]
  constructor
  · calc
      _ = (1 / (12 * Real.log (N : ℝ) ^ 5)) ^ k := by
        simp only [div_pow, mul_pow, ← pow_mul]
        ring
      _ ≤ (1 / (12 * Real.log (N : ℝ) ^ 5)) ^ i :=
        pow_le_pow_of_le_one (by positivity) hbase hik
      _ = ∏ _j : Fin i, (1 / (12 * Real.log (N : ℝ) ^ 5)) := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => by positivity)
        (fun j _ => hmass N hN₁ Δ (V j) hΔlo hΔhi (hVlo j) (hVhi j))
  · calc
      _ ≤ ∏ _j : Fin i, (6 : ℝ) := by
        apply prod_le_prod (fun j _ => sum_nonneg (fun p _ => by positivity))
        intro j _
        apply box_primeWindow_mass_upper _ hΔ0 hΔ3
        exact (Real.one_le_rpow (by exact_mod_cast hN1) hα.le).trans (hVlo j)
      _ = 6 ^ i := by simp
      _ ≤ 6 ^ k := pow_le_pow_right₀ (by norm_num) hik

/-- Finite (3.6) transport: support at most `∏ V_j` converts reciprocal
mass to ordinary mass, with the Dirichlet unit included. -/
theorem boxConvolution_total_mass_le {i : ℕ} {W : Fin i → Finset ℕ}
    {V : Fin i → ℝ} (hWpos : ∀ j p, p ∈ W j → 0 < p)
    (hWle : ∀ j p, p ∈ W j → (p : ℝ) ≤ V j) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ)) ≤
      (∏ j, V j) * boxConvolutionReciprocalMass W := by
  unfold boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast boxConvolutionSupport_pos hWpos hd
  have hdle := boxConvolutionSupport_le_product hWle hd
  calc
    _ = (d : ℝ) * ((convolutionCoeff W d : ℝ) / d) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hdle (by positivity)

/-- The actual ordinary convolution mass bound (3.6), uniformly in depth
and the permitted real endpoints. -/
theorem wu_boxConvolution_total_mass_upper (k : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
      1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
      ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ α ≤ V j) → (∀ j, V j ≤ N) →
        (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ)) ≤
            (∏ j, V j) * 6 ^ k := by
  obtain ⟨N₀, hbound⟩ := wu_boxConvolution_mass_bounds k hα
  refine ⟨N₀, ?_⟩
  intro N hN i hik Δ hΔlo hΔhi V hVlo hVhi
  have hmass := (hbound N hN i hik Δ hΔlo hΔhi V hVlo hVhi).2
  exact (boxConvolution_total_mass_le
    (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos)
    (fun j p hp => (mem_convolutionWuWindows.mp hp).2.2.2.le)).trans
      (mul_le_mul_of_nonneg_left hmass
        (prod_nonneg (fun j _ => (Real.rpow_nonneg (Nat.cast_nonneg N) α).trans (hVlo j))))

end Wu2008DoubleSieve
