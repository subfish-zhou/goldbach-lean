import MathlibNt.Wu2008DoubleSieve.MotherPairMassFinite
namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval
theorem row_discrepancy {a U : ℝ} (ha : 1/10 ≤ a) (hU : U < 1/2) {N p : ℕ} {R C D α e : ℝ}
    (hN : 1 < N) (hα : 0 < α) (hR : 1 < R) (hp : p.Prime)
    (hC : a ≤ C) (hCD : C ≤ D) (hD : D ≤ U)
    (hZ : (N : ℝ) ^ α ≤ R ^ a)
    (hquad : ∀ (f : ℝ → ℝ) (A B : ℝ),
      ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)) →
      (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ (1/(1-2*U))) →
      (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
        |f x - f y| ≤ (1/(1-2*U)^2) * |x - y|) →
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |primeOrderedClosedSum R A B f - ∫ t in A..B, f t / t| < e) :
    |(∑ q ∈ rowPrimes N R C D p,
        clipH U (gamma5MassCoordinate R p) (gamma5MassCoordinate R q) / q) -
      kernelSection U C D (gamma5MassCoordinate R p)| ≤
        e + 3*(1/(1-2*U)) / (N : ℝ) ^ α + (1/(1-2*U)) / (α * (N : ℝ) ^ α) := by
  have hg : 0 < 1-2*U := by linarith
  let t := gamma5MassCoordinate R p
  let P := gamma5MassPrimes R (gamma5MassSectionStart C D t) D
  let P' := P.filter (fun q => p < q ∧ (q : ℝ) < R ^ D)
  let g := fun q : ℕ => clipH U t (gamma5MassCoordinate R q) / q
  have hpow : 0 < (N : ℝ) ^ α := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hg (q : ℕ) : |g q| ≤ (1/(1-2*U)) / q := by
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
      abs_of_pos (clipH_bounds hU _ _).1]
    exact div_le_div_of_nonneg_right (clipH_bounds hU _ _).2 (Nat.cast_nonneg _)
  have hCpow := hZ.trans (rpow_le_rpow_of_exponent_le hR.le hC)
  have hb := row_boundary hR hp hCD hpow hCpow
    (by positivity : (0 : ℝ) ≤ (1/(1-2*U))) g (fun q _ => hg q)
  have hdel := gamma5Mass_divisor_deletion hN hα (by positivity : (0 : ℝ) ≤ (1/(1-2*U)))
    P' (fun q hq => prime_lower hR
      (hC.trans (gamma5Mass_start_bounds hCD t).1) hZ q (mem_filter.mp hq).1)
    g (fun q _ => hg q)
  have he : P'.filter (fun q => q.Coprime N) = rowPrimes N R C D p := by
    ext q
    simp only [P', P, rowPrimes, mem_filter, t, and_assoc]
  rw [he] at hdel
  have hs := gamma5Mass_start_bounds hCD t
  have hq := hquad (clipH U t) (gamma5MassSectionStart C D t) D
    (clipH_continuous hU t)
    (fun u _ => by rw [abs_of_pos (clipH_bounds hU t u).1]; exact (clipH_bounds hU t u).2)
    (fun u _ v _ => clipH_second_lipschitz hU t u v)
    ((ha.trans hC).trans hs.1) hs.2
    (hD.trans hU.le)
  change |(∑ q ∈ P, g q) - kernelSection U C D t| < e at hq
  change |(∑ q ∈ P, g q) - ∑ q ∈ P', g q| ≤ 3 * (1/(1-2*U)) / (N : ℝ) ^ α at hb
  have h1 := abs_sub_le (∑ q ∈ rowPrimes N R C D p, g q)
    (∑ q ∈ P', g q) (kernelSection U C D t)
  have h2 := abs_sub_le (∑ q ∈ P', g q) (∑ q ∈ P, g q) (kernelSection U C D t)
  rw [abs_sub_comm] at hb hdel
  change |(∑ q ∈ rowPrimes N R C D p, g q) - kernelSection U C D t| ≤ _
  linarith

theorem pair_quadrature_finite {a U : ℝ} (ha : 1/10 ≤ a) (hU : U < 1/2) {e : ℝ} (he : 0 < e) :
    ∀ᶠ R : ℝ in atTop, ∀ N : ℕ, 1 < N → ∀ α : ℝ, 0 < α →
      (N : ℝ) ^ α ≤ R ^ a →
      ∀ A B C D : ℝ,
      a ≤ A → A ≤ B → B ≤ U →
      a ≤ C → C ≤ D → D ≤ U →
      |reciprocalPairs U N R A B C D - rectIntegral A B C D| ≤
        6 * e + (19*(1/(1-2*U)) + 9*(1/(1-2*U)) / α) / (N : ℝ) ^ α := by
  have hg : 0 < 1-2*U := by linarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    primeOrdered_weighted_uniform (1/(1-2*U)) (1/(1-2*U)^2) e (by positivity) (by positivity) he,
    primeOrdered_weighted_uniform (4*(1/(1-2*U))) (4*(1/(1-2*U)^2)+10*(1/(1-2*U))) e (by positivity) (by positivity) he,
    primeOrdered_reciprocal_uniform 1 (by norm_num)] with R hR hinner houter hmass
  intro N hN α hα hZ A B C D hA hAB hB hC hCD hD
  have hAa := ha.trans hA
  have hBb := hB.trans hU.le
  have hCc := ha.trans hC
  have hDd := hD.trans hU.le
  have hr := kernelSection_regular hU hCc hCD hDd
  let P := gamma5MassPrimes R A B
  let P0 := P.filter (fun p => p.Coprime N)
  let P' := P.filter (fun p : ℕ => p.Coprime N ∧ (p:ℝ)<R^B)
  let I := ∫ t in A..B, kernelSection U C D t / t
  let E := e + 3*(1/(1-2*U)) / (N : ℝ) ^ α + (1/(1-2*U)) / (α * (N : ℝ) ^ α)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hmassP : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 := by
    have h := (le_abs_self _).trans (hmass A B hAa hAB hBb).le
    have hi := (primeOrdered_exponent_density_bounds hAa hAB hBb).2
    dsimp [P, gamma5MassPrimes]
    linarith
  have hmassP' : (∑ p ∈ P', 1 / (p : ℝ)) ≤ 5 :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by positivity)).trans hmassP
  have hrow :
      |reciprocalPairs U N R A B C D -
        ∑ p ∈ P', kernelSection U C D (gamma5MassCoordinate R p) / p| ≤ 5 * E := by
    rw [pairs_eq_rows U hR hCD]
    change |(∑ p ∈ P', _) - ∑ p ∈ P', _| ≤ _
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ P', E / p := by
        apply sum_le_sum
        intro p hp
        rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact row_discrepancy ha hU hN hα hR
          ((gamma5Mass_coordinate_mem_iff hR p).mp (mem_filter.mp hp).1).1
          hC hCD hD hZ hinner
      _ = E * ∑ p ∈ P', 1 / (p : ℝ) := by rw [mul_sum]; simp only [mul_one_div]
      _ ≤ 5 * E := by nlinarith [mul_le_mul_of_nonneg_left hmassP' hE]
  have hdel := gamma5Mass_divisor_deletion hN hα (by positivity : (0 : ℝ) ≤ 4*(1/(1-2*U)))
    P (prime_lower hR hA hZ)
    (fun p => kernelSection U C D (gamma5MassCoordinate R p) / p)
    (fun p _ => by
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
      exact div_le_div_of_nonneg_right (hr.1 _) (Nat.cast_nonneg _))
  have hupper := upper_deletion (rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) α)
    (show 0 ≤ 4*(1/(1-2*U)) by positivity) P0
    (fun p hp => ⟨(prime_lower hR hA hZ p (mem_filter.mp hp).1).2,
      ((mem_primesIcc (rpow_nonneg (by linarith : 0≤R) B)).mp (mem_filter.mp hp).1).2.2⟩)
    (fun p => kernelSection U C D (gamma5MassCoordinate R p)/p)
    (fun p _ => by
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0:ℝ)≤p)]
      exact div_le_div_of_nonneg_right (hr.1 _) (Nat.cast_nonneg _))
  have heP : P0.filter (fun p : ℕ => (p:ℝ)<R^B) = P' := by
    ext p
    simp only [P0, P', mem_filter, and_assoc]
  rw [heP] at hupper
  have hdel' := abs_sub_le (∑ p ∈ P, kernelSection U C D (gamma5MassCoordinate R p)/p)
    (∑ p ∈ P0, kernelSection U C D (gamma5MassCoordinate R p)/p)
    (∑ p ∈ P', kernelSection U C D (gamma5MassCoordinate R p)/p)
  have hdelboth : |(∑ p ∈ P, kernelSection U C D (gamma5MassCoordinate R p)/p)-
      ∑ p ∈ P', kernelSection U C D (gamma5MassCoordinate R p)/p| ≤
      4*(1/(1-2*U))/(α*(N:ℝ)^α)+4*(1/(1-2*U))/(N:ℝ)^α := by
    linarith
  have hquad := houter (kernelSection U C D) A B
    (primeOrdered_continuous_of_lipschitz (fun x _ y _ => hr.2 x y))
    (fun t _ => hr.1 t) (fun x _ y _ => hr.2 x y) hAa hAB hBb
  change |(∑ p ∈ P, kernelSection U C D (gamma5MassCoordinate R p) / p) - I| < e at hquad
  have h1 := abs_sub_le (reciprocalPairs U N R A B C D)
    (∑ p ∈ P', kernelSection U C D (gamma5MassCoordinate R p) / p) I
  have h2 := abs_sub_le (∑ p ∈ P', kernelSection U C D (gamma5MassCoordinate R p) / p)
    (∑ p ∈ P, kernelSection U C D (gamma5MassCoordinate R p) / p) I
  rw [abs_sub_comm] at hdelboth
  rw [rectIntegral_eq hAB hB hCD hD]
  change |reciprocalPairs U N R A B C D - I| ≤ _
  have heq : 5 * E + 4*(1/(1-2*U)) / (α * (N : ℝ) ^ α) + 4*(1/(1-2*U))/(N:ℝ)^α + e =
      6 * e + (19*(1/(1-2*U)) + 9*(1/(1-2*U)) / α) / (N : ℝ) ^ α := by dsimp [E]; ring
  linarith

/-- One threshold precedes the moving scale and all four rectangle endpoints. -/
theorem pair_quadrature_uniform {a U : ℝ} (ha : 1/10 ≤ a) (hU : U < 1/2) {α β ε : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≤ β * a) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, (N : ℝ) ^ β ≤ R →
      ∀ A B C D : ℝ,
      a ≤ A → A ≤ B → B ≤ U →
      a ≤ C → C ≤ D → D ≤ U →
      |reciprocalPairs U N R A B C D - rectIntegral A B C D| < ε := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (pair_quadrature_finite ha hU (show 0 < ε / 12 by positivity))
  have hlarge := ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop R0)
  have hdecay : Tendsto (fun N : ℕ => (19*(1/(1-2*U))+9*(1/(1-2*U))/α) / (N : ℝ) ^ α) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlarge, hdecay.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity)),
    eventually_ge_atTop (2 : ℕ)] with N hlargeN herr hN
  intro R hR A B C D hA hAB hB hC hCD hD
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hZ : (N : ℝ) ^ α ≤ R ^ a := by
    calc
      _ ≤ (N : ℝ) ^ (β * a) := rpow_le_rpow_of_exponent_le hN1 hαβ
      _ = ((N : ℝ) ^ β) ^ a := rpow_mul (Nat.cast_nonneg _) _ _
      _ ≤ _ := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hR
        (by linarith)
  have h := hR0 R (hlargeN.trans hR) N (by omega) α hα hZ A B C D hA hAB hB hC hCD hD
  linarith


noncomputable def arithmeticPairs (U : ℝ) (N d : ℕ) (R A B C D : ℝ) : ℝ :=
  ∑ x ∈ primePairs N R A B C D,
    gamma5MassAtom d x.1 * gamma5MassAtom (d * x.1) x.2 *
      clipH U (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2)

/-- Bilateral comparison on every finite pair mask, including shared factors. -/
theorem mask_bilateral {U : ℝ} (hU : U < 1/2) (d : ℕ) (R Z : ℝ) (X : Finset (ℕ × ℕ))
    (hZ : 4 ≤ Z) (hX : ∀ x ∈ X, Z ≤ (x.1 : ℝ) ∧ Z ≤ (x.2 : ℝ)) :
    (∑ x ∈ X, clipH U (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) /
        ((x.1 : ℝ) * x.2)) ≤
      ∑ x ∈ X, gamma5MassAtom d x.1 * gamma5MassAtom (d * x.1) x.2 *
        clipH U (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) ∧
    (∑ x ∈ X, gamma5MassAtom d x.1 * gamma5MassAtom (d * x.1) x.2 *
        clipH U (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2)) ≤
      (1 + 4 / Z) ^ 2 *
        ∑ x ∈ X, clipH U (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) /
          ((x.1 : ℝ) * x.2) := by
  constructor
  · apply sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_right
      (gamma5Mass_atoms_bilateral (d := d) hZ (hX x hx).1 (hX x hx).2).1
      (clipH_bounds hU (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2)).1.le
    convert h using 1
    ring
  · rw [mul_sum]
    apply sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_right
      (gamma5Mass_atoms_bilateral (d := d) hZ (hX x hx).1 (hX x hx).2).2
      (clipH_bounds hU (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2)).1.le
    exact h.trans_eq (by ring)

theorem pairs_bilateral {a U : ℝ} (hU : U < 1/2) {N : ℕ} (d : ℕ) {R A B C D α : ℝ}
    (hR : 1 < R) (hA : a ≤ A) (hC : a ≤ C)
    (hZ : (N : ℝ) ^ α ≤ R ^ a) (hfour : 4 ≤ (N : ℝ) ^ α) :
    reciprocalPairs U N R A B C D ≤ arithmeticPairs U N d R A B C D ∧
      arithmeticPairs U N d R A B C D ≤
        (1 + 4 / (N : ℝ) ^ α) ^ 2 * reciprocalPairs U N R A B C D := by
  apply mask_bilateral hU d R ((N : ℝ) ^ α) _ hfour
  intro x hx
  obtain ⟨hp, hq⟩ := mem_product.mp (mem_filter.mp hx).1
  exact ⟨(prime_lower hR hA hZ x.1 hp).2,
    (prime_lower hR hC hZ x.2 hq).2⟩

theorem arithmetic_pair_uniform {a U : ℝ} (ha : 1/10 ≤ a) (hU : U < 1/2) {α β ε : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≤ β * a) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, (N : ℝ) ^ β ≤ R → ∀ d : ℕ,
      ∀ A B C D : ℝ,
      a ≤ A → A ≤ B → B ≤ U →
      a ≤ C → C ≤ D → D ≤ U →
      |arithmeticPairs U N d R A B C D - rectIntegral A B C D| < ε := by
  have hg : 0 < 1-2*U := by linarith
  let τ := min 1 (ε / 4)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 4 := min_le_right _ _
  have hdecay : Tendsto (fun N : ℕ => (1 + 4 / (N : ℝ) ^ α) ^ (2 : ℕ) - 1)
      atTop (𝓝 0) := by
    have h := tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop) (a := (4 : ℝ))
    simpa only [Function.comp_apply, add_zero, one_pow, sub_self] using
      ((h.const_add 1).pow 2).sub_const 1
  filter_upwards [pair_quadrature_uniform ha hU hα hβ hαβ hτ,
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)),
    hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2*(16*(1/(1-2*U))+1)) by positivity)),
    eventually_ge_atTop (2 : ℕ)] with N hquad hfour hsmall hN
  intro R hNR d A B C D hA hAB hB hC hCD hD
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hR : 1 < R := (one_lt_rpow hN1 hβ).trans_le hNR
  have hZ : (N : ℝ) ^ α ≤ R ^ a := by
    calc
      _ ≤ (N : ℝ) ^ (β * a) := rpow_le_rpow_of_exponent_le hN1.le hαβ
      _ = ((N : ℝ) ^ β) ^ a := rpow_mul (Nat.cast_nonneg _) _ _
      _ ≤ _ := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hNR
        (by linarith)
  have hb := pairs_bilateral (B := B) (D := D) hU d hR hA hC hZ hfour
  have hq := hquad R hNR A B C D hA hAB hB hC hCD hD
  have hi := rectIntegral_bounds hU (ha.trans hA) hAB hB (ha.trans hC) hCD hD
  have hq' := abs_lt.mp hq
  have hU : reciprocalPairs U N R A B C D ≤ 16*(1/(1-2*U))+1 := by linarith
  have hF : 0 ≤ (1 + 4 / (N : ℝ) ^ α) ^ (2 : ℕ) - 1 := by
    have h : 0 ≤ 4 / (N : ℝ) ^ α := by positivity
    nlinarith
  have hcost := mul_le_mul_of_nonneg_left hU hF
  have hsmall' : ((1+4/(N:ℝ)^α)^2-1)*(2*(16*(1/(1-2*U))+1)) < ε :=
    (lt_div_iff₀ (by positivity)).mp hsmall
  rw [abs_lt]
  constructor <;> nlinarith


end Wu2008DoubleSieve.MotherPair
