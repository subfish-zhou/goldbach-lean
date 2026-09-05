import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerShort
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingTheoremADyadicCoverage
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Pan's long-polynomial primitive mean

On `Re s ≥ 1`, bounded coefficients have inverse-square energy. Apply the
sharp primitive large sieve to complete dyadic polynomials, then sum the
long-polynomial blocks. The source polynomial is never split into absolute
values of individual source coefficients.
-/

noncomputable section
open Classical Complex Finset Filter
open scoped BigOperators

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

theorem polynomial_dyadic_second_moment (S : Finset ℕ) (c : ℕ → ℂ)
    (L : ℕ) (hL : 0 < L) (hS : S ⊆ Ioc L (2 * L))
    (hc : ∀ n ∈ S, ‖c n‖ ≤ 1) {R : ℝ} (hR : 1 ≤ R)
    (s : ℂ) (hs : 1 ≤ s.re) :
    (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
      ∑ χ : PrimitiveCharacter q, ‖polynomial S c χ s‖ ^ 2) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) * (R / L + 2 / R) := by
  have hS' : S ⊆ Icc 1 (2 * L) := by
    intro n hn
    have := mem_Ioc.mp (hS hn)
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  have hE : (∑ n ∈ S, ‖c n / (n : ℂ) ^ s‖ ^ 2) ≤ (L : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ n ∈ S, ((n : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (hS' hn)).1
        have hn0 : (0 : ℝ) < n := by linarith
        have hden : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hn1 hs
        have hnorm : ‖c n / (n : ℂ) ^ s‖ ≤ (n : ℝ)⁻¹ := by
          rw [norm_div, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
            Complex.norm_cpow_eq_rpow_re_of_pos hn0]
          exact (div_le_div_of_nonneg_right (hc n hn)
            (Real.rpow_nonneg hn0.le _)).trans
              (by simpa only [one_div] using one_div_le_one_div_of_le hn0 hden)
        simpa only [inv_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ ∑ n ∈ Ioc L (2 * L), ((n : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg hS
        intro n _ _
        positivity
      _ ≤ (L : ℝ)⁻¹ - ((2 * L : ℕ) : ℝ)⁻¹ :=
        sum_Ioc_inv_sq_le_sub hL.ne' (by omega)
      _ ≤ _ := sub_le_self _ (by positivity)
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  refine (polynomial_second_moment_energy S c (2 * L) hS' hR s).trans ?_
  calc
    _ ≤ (2 * chen1973Lemma6Eq19SharpConstant) *
        (R + ((2 * L : ℕ) : ℝ) / R) * (L : ℝ)⁻¹ := by gcongr
    _ = _ := by
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      have hR0 : R ≠ 0 := by linarith
      push_cast
      field_simp

private theorem sqrt_long_moments_le {U V C R A H : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hC : 0 ≤ C) (hR : 0 < R)
    (hA : 0 < A) (hH : 0 < H) (hHR : H ≤ R ^ 2) (hRH : R ^ 2 ≤ 2 * H)
    (hUb : U ≤ 2 * C * (R / A + 2 / R))
    (hVb : V ≤ 2 * C * (R / H + 2 / R)) :
    Real.sqrt U * Real.sqrt V ≤ 8 * C * Real.sqrt (1 / A + 1 / H) := by
  have hRH' : R / H ≤ 2 / R := (div_le_div_iff₀ hH hR).mpr (by nlinarith)
  have hVb' : V ≤ 8 * C / R := by
    calc
      V ≤ 2 * C * (R / H + 2 / R) := hVb
      _ ≤ 2 * C * (2 / R + 2 / R) := by gcongr
      _ = _ := by ring
  have hinv : 1 / R ^ 2 ≤ 1 / H :=
    one_div_le_one_div_of_le hH hHR
  have hprod : U * V ≤ 32 * C ^ 2 * (1 / A + 1 / H) := by
    calc
      U * V ≤ (2 * C * (R / A + 2 / R)) * (8 * C / R) :=
        mul_le_mul hUb hVb' hV (by positivity)
      _ = 16 * C ^ 2 * (1 / A + 2 * (1 / R ^ 2)) := by field_simp; ring
      _ ≤ 16 * C ^ 2 * (1 / A + 2 * (1 / H)) := by gcongr
      _ ≤ 32 * C ^ 2 * (1 / A + 1 / H) := by
        have : 0 ≤ C ^ 2 * (1 / A) := by positivity
        nlinarith
  have hlhs : (Real.sqrt U * Real.sqrt V) ^ 2 = U * V := by
    rw [mul_pow, Real.sq_sqrt hU, Real.sq_sqrt hV]
  have hrhs : (8 * C * Real.sqrt (1 / A + 1 / H)) ^ 2 =
      64 * C ^ 2 * (1 / A + 1 / H) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hpos : 0 ≤ 8 * C * Real.sqrt (1 / A + 1 / H) := by positivity
  have hnonneg : 0 ≤ C ^ 2 * (1 / A + 1 / H) := by positivity
  nlinarith

/-- Each complete long dyadic block has the paper's square-root reciprocal
scale, including the factor needed to account for `H = floor(R²)`. -/
theorem long_block_mean_le (S T : Finset ℕ) (c d : ℕ → ℂ)
    (A L V : ℕ) (hA : 0 < A) (hAL : A ≤ L)
    (hS : S ⊆ Ioc L (2 * L)) (hT : T ⊆ Ioc V (2 * V))
    (hc : ∀ n ∈ S, ‖c n‖ ≤ 1) (hd : ∀ n ∈ T, ‖d n‖ ≤ 1)
    {R : ℝ} (hR : 1 ≤ R) (hHV : shortCutoff R ≤ V)
    (s : ℂ) (hs : 1 ≤ s.re) :
    (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
      ∑ χ : PrimitiveCharacter q, ‖polynomial S c χ s * polynomial T d χ s‖) ≤
      (8 * chen1973Lemma6Eq19SharpConstant) *
        Real.sqrt (1 / (A : ℝ) + 1 / (shortCutoff R : ℝ)) := by
  have hH := shortCutoff_pos hR
  have hL : 0 < L := hA.trans_le hAL
  have hV : 0 < V := hH.trans hHV
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hHR : (0 : ℝ) < shortCutoff R := by exact_mod_cast hH
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  have hU := (polynomial_dyadic_second_moment S c L hL hS hc hR s hs).trans
    (show (2 * chen1973Lemma6Eq19SharpConstant) * (R / L + 2 / R) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) * (R / A + 2 / R) by gcongr)
  have hW := (polynomial_dyadic_second_moment T d V hV hT hd hR s hs).trans
    (show (2 * chen1973Lemma6Eq19SharpConstant) * (R / V + 2 / R) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) *
        (R / (shortCutoff R : ℝ) + 2 / R) by gcongr)
  exact (weighted_product_mean_le (conductorCell R) _ _).trans
    (sqrt_long_moments_le (by positivity) (by positivity) hC (by linarith)
      hAR hHR (shortCutoff_le_square R) (square_le_two_mul_shortCutoff hR) hU hW)

def longF₂ {q : ℕ} (m H : ℕ) (T : ℝ) (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  polynomial (Ioc H ⌊T⌋₊) (panSourceD m) χ s

def longMean (f : ℕ → ℂ) (m A₁ A₂ k : ℕ) (R T : ℝ) (s : ℂ) : ℝ :=
  ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
    ∑ χ : PrimitiveCharacter q,
      ‖panDyadicG f m A₁ A₂ k χ s * longF₂ m (shortCutoff R) T χ s‖

theorem mem_long_interval_iff (R : ℝ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    n ∈ Ioc (shortCutoff R) ⌊T⌋₊ ↔ R ^ 2 < n ∧ (n : ℝ) ≤ T := by
  simp only [mem_Ioc, shortCutoff, Nat.floor_lt (sq_nonneg R), Nat.le_floor_iff hT]

theorem polynomial_eq_sum_dyadic (c : ℕ → ℂ) (H K : ℕ) (hH : 0 < H)
    {q : ℕ} (χ : PrimitiveCharacter q) (s : ℂ) :
    polynomial (Ioc H K) c χ s =
      ∑ r ∈ range (panDyadicDepth H K), polynomial (panDyadicCell H K r) c χ s := by
  unfold polynomial
  rw [← panDyadicCells_cover H K hH, sum_biUnion (panDyadicCells_pairwise H K hH)]

theorem longMean_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (m A₁ A₂ k : ℕ) (hA : 0 < A₁) {R : ℝ} (hR : 1 ≤ R)
    (T : ℝ) (s : ℂ) (hs : 1 ≤ s.re) :
    longMean f m A₁ A₂ k R T s ≤
      (panDyadicDepth (shortCutoff R) ⌊T⌋₊ : ℝ) *
        ((8 * chen1973Lemma6Eq19SharpConstant) *
          Real.sqrt (1 / (A₁ : ℝ) + 1 / (shortCutoff R : ℝ))) := by
  let H := shortCutoff R
  let L := 2 ^ k * A₁
  let S := Ioc L (min (2 ^ (k + 1) * A₁) A₂)
  let J := range (panDyadicDepth H ⌊T⌋₊)
  have hH : 0 < H := shortCutoff_pos hR
  have hAL : A₁ ≤ L := by
    dsimp [L]
    nlinarith [show 1 ≤ (2 : ℕ) ^ k from Nat.one_le_pow k 2 (by omega)]
  have hS : S ⊆ Ioc L (2 * L) := by
    intro n hn
    rcases mem_Ioc.mp hn with ⟨hnL, hnU⟩
    apply mem_Ioc.mpr ⟨hnL, ?_⟩
    have : n ≤ 2 ^ (k + 1) * A₁ := hnU.trans (min_le_left _ _)
    dsimp [L]
    rw [pow_succ] at this
    nlinarith
  have hblock (r : ℕ) :
      (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q,
          ‖panDyadicG f m A₁ A₂ k χ s *
            polynomial (panDyadicCell H ⌊T⌋₊ r) (panSourceD m) χ s‖) ≤
      (8 * chen1973Lemma6Eq19SharpConstant) *
        Real.sqrt (1 / (A₁ : ℝ) + 1 / (H : ℝ)) := by
    have hV : H ≤ H * 2 ^ r :=
      Nat.le_mul_of_pos_right H (pow_pos (by norm_num) r)
    have hT : panDyadicCell H ⌊T⌋₊ r ⊆ Ioc (H * 2 ^ r) (2 * (H * 2 ^ r)) := by
      intro n hn
      rcases mem_Ioc.mp hn with ⟨hl, hu⟩
      exact mem_Ioc.mpr ⟨hl, hu.trans (min_le_left _ _)⟩
    exact long_block_mean_le S (panDyadicCell H ⌊T⌋₊ r)
      (panSourceG f m) (panSourceD m) A₁ L (H * 2 ^ r) hA hAL hS hT
      (fun n _ => panSourceG_norm_le f hf m n) (fun n _ => panSourceD_norm_le m n)
      hR hV s hs
  calc
    _ ≤ ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q, ∑ r ∈ J,
          ‖panDyadicG f m A₁ A₂ k χ s *
            polynomial (panDyadicCell H ⌊T⌋₊ r) (panSourceD m) χ s‖ := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro χ hχ
      change ‖panDyadicG f m A₁ A₂ k χ s *
        polynomial (Ioc H ⌊T⌋₊) (panSourceD m) χ s‖ ≤ _
      rw [polynomial_eq_sum_dyadic _ _ _ hH, mul_sum]
      exact norm_sum_le _ _
    _ = ∑ r ∈ J, ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q,
          ‖panDyadicG f m A₁ A₂ k χ s *
            polynomial (panDyadicCell H ⌊T⌋₊ r) (panSourceD m) χ s‖ := by
      simp_rw [sum_comm (s := univ) (t := J), mul_sum]
      rw [sum_comm]
    _ ≤ ∑ _r ∈ J, (8 * chen1973Lemma6Eq19SharpConstant) *
        Real.sqrt (1 / (A₁ : ℝ) + 1 / (H : ℝ)) := sum_le_sum fun r _ => hblock r
    _ = _ := by simp [J, H, mul_comm]

theorem depth_at_source_height_le (H x : ℕ) (hx : 1 ≤ Real.log x) :
    (panDyadicDepth H ⌊panSourceHeight x⌋₊ : ℝ) ≤
      (1 + 2 / Real.log 2) * (Real.log x) ^ 2 := by
  have hT : 1 ≤ panSourceHeight x := by
    unfold panSourceHeight
    exact Real.one_le_exp (by positivity)
  have hK : 0 < ⌊panSourceHeight x⌋₊ := Nat.floor_pos.mpr hT
  have hKR : (0 : ℝ) < ⌊panSourceHeight x⌋₊ := by exact_mod_cast hK
  have hlog : Real.log (⌊panSourceHeight x⌋₊ : ℝ) ≤ 2 * (Real.log x) ^ 2 := by
    have h := Real.log_le_log hKR (Nat.floor_le (by linarith : 0 ≤ panSourceHeight x))
    simpa only [panSourceHeight, Real.log_exp] using h
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : (Nat.log 2 (⌊panSourceHeight x⌋₊ / H) : ℝ) ≤
      Real.log (⌊panSourceHeight x⌋₊ : ℝ) / Real.log 2 := by
    calc
      _ ≤ (Nat.log 2 ⌊panSourceHeight x⌋₊ : ℝ) := by
        exact_mod_cast Nat.log_mono_right (Nat.div_le_self ⌊panSourceHeight x⌋₊ H)
      _ ≤ _ := by simpa [Real.logb] using Real.natLog_le_logb ⌊panSourceHeight x⌋₊ 2
  have hn' := hn.trans (div_le_div_of_nonneg_right hlog hln2.le)
  unfold panDyadicDepth
  push_cast
  have hsq : 1 ≤ (Real.log x) ^ 2 := by nlinarith
  calc
    _ ≤ 2 * (Real.log x) ^ 2 / Real.log 2 + (Real.log x) ^ 2 :=
      add_le_add hn' hsq
    _ = _ := by ring

/-- The dyadic block count through the literal height `exp(2 log² x)` costs
only `O(log² x)`, with no source- or conductor-dependent constant. -/
theorem longMean_at_source_height_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (m A₁ A₂ k x : ℕ) (hA : 0 < A₁) (hx : 1 ≤ Real.log x)
    {R : ℝ} (hR : 1 ≤ R) (s : ℂ) (hs : 1 ≤ s.re) :
    longMean f m A₁ A₂ k R (panSourceHeight x) s ≤
      (8 * chen1973Lemma6Eq19SharpConstant * (1 + 2 / Real.log 2)) *
        (Real.log x) ^ 2 *
          Real.sqrt (1 / (A₁ : ℝ) + 1 / (shortCutoff R : ℝ)) := by
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  calc
    _ ≤ (panDyadicDepth (shortCutoff R) ⌊panSourceHeight x⌋₊ : ℝ) *
        ((8 * chen1973Lemma6Eq19SharpConstant) *
          Real.sqrt (1 / (A₁ : ℝ) + 1 / (shortCutoff R : ℝ))) :=
      longMean_le f hf m A₁ A₂ k hA hR _ s hs
    _ ≤ ((1 + 2 / Real.log 2) * (Real.log x) ^ 2) *
        ((8 * chen1973Lemma6Eq19SharpConstant) *
          Real.sqrt (1 / (A₁ : ℝ) + 1 / (shortCutoff R : ℝ))) := by
      gcongr
      exact depth_at_source_height_le _ x hx
    _ = _ := by ring

theorem source_reciprocal_scale_le (x y A₁ j : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hy : 1 ≤ Real.log y) (hyx : y ≤ x)
    (hA : Real.log y ^ (2 * B) ≤ A₁) :
    Real.sqrt (1 / (A₁ : ℝ) +
      1 / (shortCutoff (conductorRadius x B j) : ℝ)) ≤
        2 / Real.log y ^ B := by
  have hypos : (0 : ℝ) < y := by
    by_contra h
    have hz : y = 0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg y)
    norm_num [hz] at hy
  have hlogs : Real.log (y : ℝ) ≤ Real.log x :=
    Real.log_le_log hypos (by exact_mod_cast hyx)
  have hx : 1 ≤ Real.log x := hy.trans hlogs
  have hly : 0 < Real.log y := by linarith
  have hpow : (Real.log y ^ B) ^ 2 = Real.log y ^ (2 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hly.le]
    congr 1
    ring
  let R := conductorRadius x B j
  let H := shortCutoff R
  let D := Real.log y ^ B
  have hD : 0 < D := Real.rpow_pos_of_pos hly B
  have hR : 1 ≤ R := conductorRadius_ge_one j hx hB
  have hDR : D ≤ R := by
    have hmono : Real.log y ^ B ≤ Real.log x ^ B :=
      Real.rpow_le_rpow hly.le hlogs hB
    have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hp0 : 0 ≤ Real.log x ^ B := Real.rpow_nonneg (by linarith) _
    dsimp [D, R, conductorRadius, lowConductor]
    nlinarith
  have hH : (0 : ℝ) < H := by exact_mod_cast shortCutoff_pos hR
  have hDH : D ^ 2 ≤ 2 * (H : ℝ) := by
    have h := square_le_two_mul_shortCutoff hR
    dsimp [H]
    nlinarith
  have hDA : D ^ 2 ≤ (A₁ : ℝ) := by simpa only [D, hpow] using hA
  have hApos : (0 : ℝ) < A₁ := lt_of_lt_of_le (sq_pos_of_pos hD) hDA
  have hAi : 1 / (A₁ : ℝ) ≤ 1 / D ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hD) hDA
  have hHi : 1 / (H : ℝ) ≤ 2 / D ^ 2 := by
    rw [div_le_div_iff₀ hH (sq_pos_of_pos hD)]
    simpa only [one_mul] using hDH
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1 / (A₁ : ℝ) + 1 / (H : ℝ))
  have hrhs : (2 / D) ^ 2 = 4 / D ^ 2 := by ring
  have hnonneg : 0 ≤ 2 / D := by positivity
  change Real.sqrt (1 / (A₁ : ℝ) + 1 / (H : ℝ)) ≤ 2 / D
  simp only [div_eq_mul_inv] at hAi hHi hsq hrhs hnonneg ⊢
  nlinarith [inv_pos.mpr (sq_pos_of_pos hD)]

/-- The long-polynomial estimate (2.28), retaining the original `log y` lower
source cutoff and the `log² x` cost of the literal height. -/
theorem chosen_long_mean_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (x y j m A₁ A₂ k : ℕ)
      (f : ℕ → ℂ) (s : ℂ),
      0 ≤ B → 1 ≤ Real.log y → y ≤ x →
      Real.log y ^ (2 * B) ≤ A₁ →
      (∀ n, ‖f n‖ ≤ 1) → 1 ≤ s.re →
      longMean f m A₁ A₂ k (conductorRadius x B j) (panSourceHeight x) s ≤
        C * (Real.log x) ^ 2 / Real.log y ^ B := by
  have hK := chen1973Lemma6_eq19SharpConstant_pos
  have hln2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨16 * chen1973Lemma6Eq19SharpConstant * (1 + 2 / Real.log 2),
    by positivity, ?_⟩
  intro B x y j m A₁ A₂ k f s hB hy hyx hA hf hs
  have hypos : (0 : ℝ) < y := by
    by_contra h
    have hz : y = 0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg y)
    norm_num [hz] at hy
  have hx : 1 ≤ Real.log x := hy.trans
    (Real.log_le_log hypos (by exact_mod_cast hyx))
  have hApos : 0 < A₁ := by
    have : (0 : ℝ) < A₁ := lt_of_lt_of_le
      (Real.rpow_pos_of_pos (by linarith) _) hA
    exact_mod_cast this
  calc
    _ ≤ (8 * chen1973Lemma6Eq19SharpConstant * (1 + 2 / Real.log 2)) *
        (Real.log x) ^ 2 *
          Real.sqrt (1 / (A₁ : ℝ) +
            1 / (shortCutoff (conductorRadius x B j) : ℝ)) :=
      longMean_at_source_height_le f hf m A₁ A₂ k x hApos hx
        (conductorRadius_ge_one j hx hB) s hs
    _ ≤ (8 * chen1973Lemma6Eq19SharpConstant * (1 + 2 / Real.log 2)) *
        (Real.log x) ^ 2 * (2 / Real.log y ^ B) := by
      gcongr
      exact source_reciprocal_scale_le x y A₁ j hB hy hyx hA
    _ = _ := by ring

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
