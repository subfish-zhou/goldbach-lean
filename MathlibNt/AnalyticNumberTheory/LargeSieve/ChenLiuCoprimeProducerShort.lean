import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerCutoff
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19UniformMoments
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The short-polynomial primitive mean in Pan (2.25)--(2.27)

The sharp primitive large sieve is applied to the complete source polynomial
and the complete prime polynomial. Cauchy--Schwarz is applied across characters,
not across the source coefficients. The fixed large-sieve constant is already
proved and precedes all coefficients, spectral parameters, and real cutoffs.
-/

noncomputable section
open Classical Complex Finset Filter
open scoped BigOperators

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

theorem weighted_product_mean_le (S : Finset ℕ)
    (F G : (q : ℕ) → PrimitiveCharacter q → ℂ) :
    (∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ, ‖F q χ * G q χ‖) ≤
      Real.sqrt (∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ, ‖F q χ‖ ^ 2) *
      Real.sqrt (∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ, ‖G q χ‖ ^ 2) := by
  have hw (q : ℕ) : Real.sqrt ((q.totient : ℝ)⁻¹) ^ 2 = (q.totient : ℝ)⁻¹ :=
    Real.sq_sqrt (by positivity)
  have hp (q : ℕ) (χ : PrimitiveCharacter q) :
      Real.sqrt ((q.totient : ℝ)⁻¹) * ‖F q χ‖ *
        (Real.sqrt ((q.totient : ℝ)⁻¹) * ‖G q χ‖) =
      (q.totient : ℝ)⁻¹ * (‖F q χ‖ * ‖G q χ‖) := by
    calc
      _ = Real.sqrt ((q.totient : ℝ)⁻¹) ^ 2 * (‖F q χ‖ * ‖G q χ‖) := by ring
      _ = _ := by rw [hw]
  have h := Real.sum_mul_le_sqrt_mul_sqrt
    (S.sigma (fun q => (univ : Finset (PrimitiveCharacter q))))
    (fun z => Real.sqrt ((z.1.totient : ℝ)⁻¹) * ‖F z.1 z.2‖)
    (fun z => Real.sqrt ((z.1.totient : ℝ)⁻¹) * ‖G z.1 z.2‖)
  simpa only [Finset.sum_sigma, mul_pow, hw, hp, ← Finset.mul_sum, norm_mul] using h

/-- Sharp Theorem A on the exact real cell `R < q ≤ 2R`. -/
theorem primitive_square_moment_real_cell (c : ℤ → ℂ) (M : ℤ) (N : ℕ)
    {R : ℝ} (hR : 1 ≤ R) :
    (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
      ∑ χ : PrimitiveCharacter q,
        ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) * (R + (N : ℝ) / R) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hD : 0 < ⌊R⌋₊ :=
    (Nat.le_floor_iff hR0.le).mpr (by simpa using hR)
  have hDR : (0 : ℝ) < ⌊R⌋₊ := by exact_mod_cast hD
  have hQ : (⌊2 * R⌋₊ : ℝ) ≤ 2 * R := Nat.floor_le (by positivity)
  have hdiv : (N : ℝ) / ⌊R⌋₊ ≤ 2 * ((N : ℝ) / R) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hDR hR0]
    nlinarith [mul_le_mul_of_nonneg_left (radius_le_two_mul_floor hR) (Nat.cast_nonneg N)]
  have h := chen1973Lemma2_equationThree_complex_fixed c M N ⌊R⌋₊ ⌊2 * R⌋₊ hD
  simp only [one_div] at h
  refine h.trans ?_
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  have hE : 0 ≤ ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by positivity
  calc
    _ ≤ chen1973Lemma6Eq19SharpConstant * (2 * (R + (N : ℝ) / R)) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by gcongr; linarith
    _ = _ := by ring

private theorem sum_int_toNat_Icc {α : Type*} [AddCommMonoid α]
    (M N : ℕ) (F : ℕ → α) :
    (∑ z ∈ Icc (M : ℤ) (N : ℤ), F z.toNat) = ∑ n ∈ Icc M N, F n := by
  refine sum_bij (fun z _ => z.toNat) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [mem_Icc] at hz ⊢
    omega
  · intro a ha b hb hab
    simp only [mem_Icc] at ha hb
    omega
  · intro n hn
    refine ⟨(n : ℤ), ?_, by simp⟩
    simpa using hn
  · intro z hz
    rfl

/-- A finite Dirichlet polynomial with its complete coefficient sum intact. -/
def polynomial (S : Finset ℕ) (c : ℕ → ℂ) {q : ℕ}
    (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  ∑ n ∈ S, c n * χ.1 (n : ZMod q) / (n : ℂ) ^ s

/-- The sharp large sieve with the exact finite polynomial energy. -/
theorem polynomial_second_moment_energy (S : Finset ℕ) (c : ℕ → ℂ) (N : ℕ)
    (hS : S ⊆ Icc 1 N) {R : ℝ} (hR : 1 ≤ R) (s : ℂ) :
    (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
      ∑ χ : PrimitiveCharacter q, ‖polynomial S c χ s‖ ^ 2) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) * (R + (N : ℝ) / R) *
        ∑ n ∈ S, ‖c n / (n : ℂ) ^ s‖ ^ 2 := by
  let b : ℕ → ℂ := fun n => if n ∈ S then c n / (n : ℂ) ^ s else 0
  have hamp (q : ℕ) (χ : PrimitiveCharacter q) :
      (∑ z ∈ Icc (1 : ℤ) N, b z.toNat * χ.1 (z : ZMod q)) =
        polynomial S c χ s := by
    calc
      _ = ∑ z ∈ Icc (1 : ℤ) N, b z.toNat * χ.1 (z.toNat : ZMod q) := by
        apply sum_congr rfl
        intro z hz
        have hz0 : 0 ≤ z := by have := (mem_Icc.mp hz).1; omega
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hz0]
      _ = ∑ n ∈ Icc 1 N, b n * χ.1 (n : ZMod q) := by
        simpa only [Nat.cast_one] using
          sum_int_toNat_Icc 1 N (fun n => b n * χ.1 (n : ZMod q))
      _ = ∑ n ∈ S, b n * χ.1 (n : ZMod q) := by
        exact (sum_subset hS (by intro n hn hnS; simp [b, hnS])).symm
      _ = _ := by
        apply sum_congr rfl
        intro n hn
        simp only [b, if_pos hn]
        ring
  have henergy : (∑ z ∈ Icc (1 : ℤ) N, ‖b z.toNat‖ ^ 2) =
      ∑ n ∈ S, ‖c n / (n : ℂ) ^ s‖ ^ 2 := by
    have heq := sum_int_toNat_Icc 1 N (fun n => ‖b n‖ ^ 2)
    simp only [Nat.cast_one] at heq
    rw [heq]
    calc
      _ = ∑ n ∈ S, ‖b n‖ ^ 2 :=
        (sum_subset hS (by intro n hn hnS; simp [b, hnS])).symm
      _ = _ := by apply sum_congr rfl; intro n hn; simp only [b, if_pos hn]
  have h := primitive_square_moment_real_cell (fun z => b z.toNat) 0 N hR
  simpa only [zero_add, hamp, henergy] using h

/-- Large sieve with the true harmonic coefficient energy on `Re s ≥ 1/2`. -/
theorem polynomial_second_moment (S : Finset ℕ) (c : ℕ → ℂ) (N : ℕ)
    (hS : S ⊆ Icc 1 N) (hc : ∀ n ∈ S, ‖c n‖ ≤ 1)
    {R : ℝ} (hR : 1 ≤ R) (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
      ∑ χ : PrimitiveCharacter q, ‖polynomial S c χ s‖ ^ 2) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) * (R + (N : ℝ) / R) *
        ∑ n ∈ S, (n : ℝ)⁻¹ := by
  refine (polynomial_second_moment_energy S c N hS hR s).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum ?_)
      (by have := chen1973Lemma6_eq19SharpConstant_pos; positivity))
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (hS hn)).1
  have hn0 : (0 : ℝ) < n := by linarith
  have hden : Real.sqrt n ≤ (n : ℝ) ^ s.re := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hs
  have hnorm : ‖c n / (n : ℂ) ^ s‖ ≤ (Real.sqrt n)⁻¹ := by
    rw [norm_div, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    calc
      _ ≤ 1 / (n : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right (hc n hn) (Real.rpow_nonneg hn0.le _)
      _ ≤ 1 / Real.sqrt n :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn0) hden
      _ = _ := one_div _
  calc
    ‖c n / (n : ℂ) ^ s‖ ^ 2 ≤ ((Real.sqrt n)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (n : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hn0.le]

theorem harmonic_energy_le_log (S : Finset ℕ) (x : ℕ) (hS : S ⊆ Icc 1 x) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ 1 + Real.log x := by
  calc
    _ ≤ ∑ n ∈ Icc 1 x, (n : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg hS
      intro n _ _
      positivity
    _ ≤ _ := by simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log x

/-- The literal `(2.22)` short-polynomial mean, on the real conductor cell. -/
def shortMean (f : ℕ → ℂ) (m A₁ A₂ k : ℕ) (R : ℝ) (s : ℂ) : ℝ :=
  ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
    ∑ χ : PrimitiveCharacter q,
      ‖panDyadicG f m A₁ A₂ k χ s * panShortF₁ m (shortCutoff R) χ s‖

theorem shortMean_nonneg (f : ℕ → ℂ) (m A₁ A₂ k : ℕ) (R : ℝ) (s : ℂ) :
    0 ≤ shortMean f m A₁ A₂ k R s := by unfold shortMean; positivity

/-- Equation (2.25), without a triangle inequality inside either polynomial. -/
theorem shortMean_le_sqrt_moments (f : ℕ → ℂ) (m A₁ A₂ k : ℕ)
    (R : ℝ) (s : ℂ) :
    shortMean f m A₁ A₂ k R s ≤
      Real.sqrt (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q, ‖panDyadicG f m A₁ A₂ k χ s‖ ^ 2) *
      Real.sqrt (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q, ‖panShortF₁ m (shortCutoff R) χ s‖ ^ 2) :=
  weighted_product_mean_le (conductorCell R) _ _

private theorem sqrt_moments_le {U V C R N H L : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hC : 0 ≤ C) (hR : 0 < R)
    (hN : 0 ≤ N) (hH : H ≤ R ^ 2) (hL : 0 ≤ L)
    (hUb : U ≤ 2 * C * (R + N / R) * L)
    (hVb : V ≤ 2 * C * (R + H / R) * L) :
    Real.sqrt U * Real.sqrt V ≤ 4 * C * Real.sqrt (R ^ 2 + N) * L := by
  have hHR : H / R ≤ R := (div_le_iff₀ hR).mpr (by nlinarith)
  have hVb' : V ≤ 4 * C * R * L := by
    calc
      V ≤ 2 * C * (R + H / R) * L := hVb
      _ ≤ 2 * C * (R + R) * L := by gcongr
      _ = _ := by ring
  have hprod : U * V ≤ 8 * C ^ 2 * (R ^ 2 + N) * L ^ 2 := by
    calc
      U * V ≤ (2 * C * (R + N / R) * L) * (4 * C * R * L) :=
        mul_le_mul hUb hVb' hV (by positivity)
      _ = _ := by field_simp; ring
  have hUs := Real.sq_sqrt hU
  have hVs := Real.sq_sqrt hV
  have hRs := Real.sq_sqrt (by positivity : 0 ≤ R ^ 2 + N)
  have hlhs : (Real.sqrt U * Real.sqrt V) ^ 2 = U * V := by
    rw [mul_pow, hUs, hVs]
  have hrhs : (4 * C * Real.sqrt (R ^ 2 + N) * L) ^ 2 =
      16 * C ^ 2 * (R ^ 2 + N) * L ^ 2 := by
    calc
      _ = 16 * C ^ 2 * (Real.sqrt (R ^ 2 + N)) ^ 2 * L ^ 2 := by ring
      _ = _ := by rw [hRs]
  have hnonneg : 0 ≤ 4 * C * Real.sqrt (R ^ 2 + N) * L := by positivity
  have hscale : 0 ≤ C ^ 2 * (R ^ 2 + N) * L ^ 2 := by positivity
  nlinarith

/-- A general bounded-coefficient version of the short-polynomial estimate.
The square-root saving comes from the conductor mean, not pointwise bounds. -/
theorem polynomial_product_mean_le (S T : Finset ℕ) (c d : ℕ → ℂ)
    (N H x : ℕ) (hS : S ⊆ Icc 1 N) (hT : T ⊆ Icc 1 H)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ 1) (hd : ∀ n ∈ T, ‖d n‖ ≤ 1)
    (hNx : N ≤ x) (hHx : H ≤ x) (hx : 1 ≤ x)
    {R : ℝ} (hR : 1 ≤ R) (hH : (H : ℝ) ≤ R ^ 2)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
      ∑ χ : PrimitiveCharacter q, ‖polynomial S c χ s * polynomial T d χ s‖) ≤
      (4 * chen1973Lemma6Eq19SharpConstant) *
        Real.sqrt (R ^ 2 + N) * (1 + Real.log x) := by
  have hlog : 0 ≤ 1 + Real.log x := by
    have : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx)
    linarith
  have hSx : S ⊆ Icc 1 x := fun n hn =>
    mem_Icc.mpr ⟨(mem_Icc.mp (hS hn)).1, (mem_Icc.mp (hS hn)).2.trans hNx⟩
  have hTx : T ⊆ Icc 1 x := fun n hn =>
    mem_Icc.mpr ⟨(mem_Icc.mp (hT hn)).1, (mem_Icc.mp (hT hn)).2.trans hHx⟩
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  have hU := (polynomial_second_moment S c N hS hc hR s hs).trans
    (mul_le_mul_of_nonneg_left (harmonic_energy_le_log S x hSx)
      (by positivity))
  have hV := (polynomial_second_moment T d H hT hd hR s hs).trans
    (mul_le_mul_of_nonneg_left (harmonic_energy_le_log T x hTx)
      (by positivity))
  exact (weighted_product_mean_le (conductorCell R) _ _).trans
    (sqrt_moments_le (by positivity) (by positivity) hC (by linarith)
      (Nat.cast_nonneg N) hH hlog hU hV)

/-- Equation (2.27) at the exact cutoff (2.26), uniformly in the whole vertical
line and in the bounded source. The clipped source-cell endpoint is retained. -/
theorem shortMean_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (m A₁ A₂ k x : ℕ) (hAx : A₂ ≤ x) (hx : 1 ≤ x)
    {R : ℝ} (hR : 1 ≤ R) (hHx : shortCutoff R ≤ x)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    shortMean f m A₁ A₂ k R s ≤ (4 * chen1973Lemma6Eq19SharpConstant) *
      Real.sqrt (R ^ 2 + min (2 ^ (k + 1) * A₁) A₂) * (1 + Real.log x) := by
  let N := min (2 ^ (k + 1) * A₁) A₂
  have hS : Ioc (2 ^ k * A₁) N ⊆ Icc 1 N := by
    intro n hn
    simp only [mem_Ioc, mem_Icc] at hn ⊢
    omega
  exact polynomial_product_mean_le
    (Ioc (2 ^ k * A₁) N) (Icc 1 (shortCutoff R))
    (panSourceG f m) (panSourceD m) N (shortCutoff R) x hS (fun _ h => h)
    (fun n _ => panSourceG_norm_le f hf m n) (fun n _ => panSourceD_norm_le m n)
    ((min_le_right _ _).trans hAx) hHx hx hR (shortCutoff_le_square R) s hs

theorem shortMean_le_log_scale (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (m A₁ A₂ k x : ℕ) {B R : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ Real.log x)
    (hR : 1 ≤ R) (hRD : R ≤ upperConductor x B)
    (hA : (A₂ : ℝ) ≤ upperConductor x B ^ 2)
    (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    shortMean f m A₁ A₂ k R s ≤
      (16 * chen1973Lemma6Eq19SharpConstant) *
        Real.sqrt x * Real.log x ^ (1 - B) := by
  have hxpos : (0 : ℝ) < x := by
    by_contra h
    have hz : x = 0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg x)
    norm_num [hz] at hx
  have hxnat : 1 ≤ x := by exact_mod_cast hxpos
  have hD : 0 ≤ upperConductor x B := by
    unfold upperConductor lowConductor
    positivity
  have hDs := upperConductor_le_sqrt hx hB
  have hAx : A₂ ≤ x := by
    have h : (A₂ : ℝ) ≤ x := by nlinarith [Real.sq_sqrt hxpos.le]
    exact_mod_cast h
  have hH := shortCutoff_le_x hx hB (by linarith) hRD
  have hN : ((min (2 ^ (k + 1) * A₁) A₂ : ℕ) : ℝ) ≤
      upperConductor x B ^ 2 := by
    have hle : ((min (2 ^ (k + 1) * A₁) A₂ : ℕ) : ℝ) ≤ A₂ := by
      exact_mod_cast min_le_right (2 ^ (k + 1) * A₁) A₂
    exact hle.trans hA
  have hsqrt : Real.sqrt (R ^ 2 + (min (2 ^ (k + 1) * A₁) A₂ : ℕ)) ≤
      2 * upperConductor x B := by
    have he := Real.sq_sqrt
      (by positivity : 0 ≤ R ^ 2 + (min (2 ^ (k + 1) * A₁) A₂ : ℕ))
    nlinarith [sq_nonneg (upperConductor x B - R)]
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  have hlog : 0 < Real.log x := by linarith
  have hscale : upperConductor x B * Real.log x =
      Real.sqrt x * Real.log x ^ (1 - B) := by
    rw [Real.rpow_sub hlog, Real.rpow_one]
    unfold upperConductor lowConductor
    ring
  calc
    _ ≤ (4 * chen1973Lemma6Eq19SharpConstant) *
        Real.sqrt (R ^ 2 + (min (2 ^ (k + 1) * A₁) A₂ : ℕ)) *
        (1 + Real.log x) := shortMean_le f hf m A₁ A₂ k x hAx hxnat hR hH s hs
    _ ≤ (4 * chen1973Lemma6Eq19SharpConstant) *
        (2 * upperConductor x B) * (2 * Real.log x) := by gcongr; linarith
    _ = (16 * chen1973Lemma6Eq19SharpConstant) *
        (upperConductor x B * Real.log x) := by ring
    _ = _ := by rw [hscale]; ring

/-- The source power cutoff is eventually inside the square of the chosen
conductor ceiling. This is proved from logarithmic growth, not assumed. -/
theorem eventually_power_le_upperConductor_square (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (1 - ε) ≤ upperConductor x B ^ 2 := by
  have he := (isLittleO_log_rpow_rpow_atTop (2 * B) hε).bound
    (by norm_num : (0 : ℝ) < 1)
  have hen := tendsto_natCast_atTop_atTop.eventually he
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hen, hlog, eventually_ge_atTop (1 : ℕ)] with x hx hl hx1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  have hl0 : 0 < Real.log x := by linarith
  have hpow : Real.log x ^ (2 * B) ≤ (x : ℝ) ^ ε := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl0.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hx
  have hlow : lowConductor x B ^ 2 = Real.log x ^ (2 * B) := by
    rw [lowConductor, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
    congr 1
    ring
  rw [upperConductor_square, le_div_iff₀ (by
    unfold lowConductor
    positivity : 0 < lowConductor x B ^ 2), hlow]
  calc
    _ ≤ (x : ℝ) ^ (1 - ε) * (x : ℝ) ^ ε := by gcongr
    _ = (x : ℝ) := by rw [← Real.rpow_add hx0]; norm_num

/-- The source (2.27) saving, with an absolute constant chosen before `B`,
`ε`, `x`, every dyadic cell, the source coefficients, and the spectral height. -/
theorem chosen_short_mean_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ) (s : ℂ),
      conductorRadius x B j ≤ upperConductor x B →
      (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      (∀ n, ‖f n‖ ≤ 1) → 1 / 2 ≤ s.re →
      shortMean f m A₁ A₂ k (conductorRadius x B j) s ≤
        C * Real.sqrt x * Real.log x ^ (1 - B) := by
  refine ⟨16 * chen1973Lemma6Eq19SharpConstant,
    mul_pos (by norm_num) chen1973Lemma6_eq19SharpConstant_pos, ?_⟩
  intro B ε hB hε
  have hlog : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  obtain ⟨X₀, hX⟩ := eventually_atTop.mp
    (hlog.and (eventually_power_le_upperConductor_square B ε hε))
  refine ⟨X₀, ?_⟩
  intro x hx j m A₁ A₂ k f s hRD hA hf hs
  exact shortMean_le_log_scale f hf m A₁ A₂ k x hB (hX x hx).1
    (conductorRadius_ge_one j (hX x hx).1 hB) hRD (hA.trans (hX x hx).2) s hs

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
