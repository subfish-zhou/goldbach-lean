import MathlibNt.SieveTheory.Switching.ScreenedDarboux

/-!
# Stieltjes and integral comparisons for alternating pairs

Uniform screened Stieltjes estimates, thickened indicators, and log-ratio
integrals transfer weighted prime sums to normalized alternating-pair kernels.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- Uniform Stieltjes comparison on an arbitrary fixed positive logarithmic
screen. -/
theorem exists_weighted_sum_nu_div_one_sub_le_integral_add_screened
    (K ρ B L c : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hc : 0 < c) (hc1 : c < 1) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc c 1) →
        (∀ x ∈ Set.Icc c 1, 0 ≤ f x) →
        (∀ x ∈ Set.Icc c 1, f x ≤ B) →
        (∀ x ∈ Set.Icc c 1, ∀ y ∈ Set.Icc c 1,
          |f x - f y| ≤ L * |x - y|) →
        MeasureTheory.IntegrableOn (fun x => x⁻¹ * f x) (Set.Ioo c 1) →
        (∀ p ∈ T, 0 ≤ w p ∧ w p ≤ f (Real.log p / Real.log z)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo c 1, x⁻¹ * f x) + ρ := by
  let D : ℝ := 2 * L / c + B / c ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let δ : ℝ := ρ / (3 * (D + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 - c) / δ < m := exists_nat_gt _
  let h : ℝ := upperRosserFixedDepthMeshWidth c m
  have hh : 0 < h := upperRosserFixedDepthMeshWidth_pos hc1 m
  have hhδ : h < δ := by
    have hmReal : (1 - c) / δ < (m : ℝ) := hm
    have hcross : 1 - c < δ * (m : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hδ).1 hmReal
    dsimp [h, upperRosserFixedDepthMeshWidth]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  have hhOne : h ≤ 1 := by
    dsimp [h, upperRosserFixedDepthMeshWidth]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  have hmesh :
      2 * L * h / c + B * h / c ^ 2 ≤ ρ / 3 := by
    have hδD : δ * D ≤ ρ / 3 := by
      have hδeq : 3 * δ * (D + 1) = ρ := by
        dsimp [δ]
        field_simp
      have hδ0 : 0 ≤ δ := hδ.le
      nlinarith
    have hhD : h * D ≤ δ * D :=
      mul_le_mul_of_nonneg_right hhδ.le hD
    calc
      2 * L * h / c + B * h / c ^ 2 = h * D := by
        dsimp [D]
        ring
      _ ≤ δ * D := hhD
      _ ≤ ρ / 3 := hδD
  obtain ⟨zPart, hzPart, hPart⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add
      (Fin (m + 1)) K (ρ / 3) B c hK (by positivity) hB hc
  obtain ⟨zCorr, hzCorr, hCorr⟩ :=
    exists_upperRosserFixedDepthMesh_correctedDarboux_le_add
      m (K := K) (ρ := ρ / 3) (B := B + L) (c := c)
        (by linarith) (by positivity) (add_nonneg hB hL) hc hc1
  let z₀ := max zPart zCorr
  refine ⟨z₀, hzPart.trans (le_max_left _ _), ?_⟩
  intro S z T w f hz hlocal hT hcoord hf hfB hfLip hint hw
  have hzPartZ : zPart ≤ z := (le_max_left _ _).trans hz
  have hzCorrZ : zCorr ≤ z := (le_max_right _ _).trans hz
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) (hzPart.trans hzPartZ)
  have hzpos : 0 < z := by linarith
  let cell : ℕ → Fin (m + 1) :=
    fun p => upperRosserFixedDepthMeshCell c m (Real.log p / Real.log z)
  let M : Fin (m + 1) → ℝ :=
    fun i => f (upperRosserFixedDepthMeshLeft c m i) + L * h
  have hleftMem : ∀ i : Fin (m + 1),
      upperRosserFixedDepthMeshLeft c m i ∈ Set.Icc c 1 := by
    intro i
    exact ⟨(upperRosserFixedDepthMeshLeft_mem hc1 m i).1,
      (upperRosserFixedDepthMeshLeft_le_right hc1 m i).trans
        (upperRosserFixedDepthMeshRight_le_one hc1 m i)⟩
  have hcell : ∀ p ∈ T,
      Real.log p / Real.log z ∈ Set.Icc
        (upperRosserFixedDepthMeshLeft c m (cell p))
        (upperRosserFixedDepthMeshRight c m (cell p)) := by
    intro p hp
    exact upperRosserFixedDepthMeshCell_bounds hc1 m (hcoord p hp)
  have hpow : ∀ p ∈ T,
      z ^ upperRosserFixedDepthMeshLeft c m (cell p) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ z ^ upperRosserFixedDepthMeshRight c m (cell p) := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (hT hp)
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have heq : z ^ (Real.log p / Real.log z) = (p : ℝ) := by
      simpa [Real.logb] using
        (Real.rpow_logb (x := (p : ℝ)) hzpos (ne_of_gt hz1) hpPos)
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hz1.le (hcell p hp).1).trans_eq heq,
      heq.symm.trans_le
        (Real.rpow_le_rpow_of_exponent_le hz1.le (hcell p hp).2)⟩
  have hM : ∀ i, 0 ≤ M i ∧ M i ≤ B + L := by
    intro i
    constructor
    · exact add_nonneg (hf _ (hleftMem i)) (mul_nonneg hL hh.le)
    · dsimp [M]
      have hLh : L * h ≤ L := mul_le_of_le_one_right hL hhOne
      linarith [hfB _ (hleftMem i)]
  have hwM : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M (cell p) := by
    intro p hp
    refine ⟨(hw p hp).1, ?_⟩
    let x := Real.log p / Real.log z
    let i := cell p
    have hbounds := hcell p hp
    have hdist : |x - upperRosserFixedDepthMeshLeft c m i| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hbounds.1)]
      calc
        x - upperRosserFixedDepthMeshLeft c m i ≤
            upperRosserFixedDepthMeshRight c m i -
              upperRosserFixedDepthMeshLeft c m i := by linarith [hbounds.2]
        _ = h := by
          dsimp [h, upperRosserFixedDepthMeshRight]
          ring
    have hdiff :=
      (hfLip x (hcoord p hp) (upperRosserFixedDepthMeshLeft c m i)
        (hleftMem i)).trans (mul_le_mul_of_nonneg_left hdist hL)
    have hupper :
        f x ≤ f (upperRosserFixedDepthMeshLeft c m i) + L * h := by
      linarith [le_abs_self (f x - f (upperRosserFixedDepthMeshLeft c m i))]
    exact (hw p hp).2.trans (by simpa [M, i, x] using hupper)
  have hpart :=
    hPart S z T w cell
      (upperRosserFixedDepthMeshLeft c m)
      (upperRosserFixedDepthMeshRight c m) M hzPartZ hlocal
      (fun i => (upperRosserFixedDepthMeshLeft_mem hc1 m i).1)
      (fun i => upperRosserFixedDepthMeshLeft_le_right hc1 m i)
      hT hpow (fun i => (hM i).1) hwM
      (fun p hp => (hw p hp).2.trans (hfB _ (hcoord p hp)))
  have hcorr := hCorr z hzCorrZ M hM
  have hmajorant : ∀ i : Fin (m + 1), ∀ x ∈
      Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
        (upperRosserFixedDepthMeshRight c m i),
      M i ≤ f x + 2 * L * h := by
    intro i x hx
    have hxMem : x ∈ Set.Icc c 1 :=
      ⟨(hleftMem i).1.trans hx.1.le,
        hx.2.le.trans (upperRosserFixedDepthMeshRight_le_one hc1 m i)⟩
    have hdist :
        |upperRosserFixedDepthMeshLeft c m i - x| ≤ h := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
      have := hx.2
      dsimp [h, upperRosserFixedDepthMeshRight] at this
      linarith
    have hdiff :=
      (hfLip _ (hleftMem i) x hxMem).trans
        (mul_le_mul_of_nonneg_left hdist hL)
    have hupper :
        f (upperRosserFixedDepthMeshLeft c m i) ≤ f x + L * h := by
      linarith [le_abs_self
        (f (upperRosserFixedDepthMeshLeft c m i) - f x)]
    dsimp [M]
    linarith
  have hdarboux :=
    upperRosserFixedDepthMesh_darbouxSum_le_integral_add
      m (c := c) (ε := 2 * L * h) (B := B) (f := f) (M := M)
        hc hc1 (mul_nonneg (mul_nonneg (by norm_num) hL) hh.le) hB
        hfB hmajorant hint
  calc
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
        (∑ i : Fin (m + 1), M i *
          (upperRosserFixedDepthMeshRight c m i /
              upperRosserFixedDepthMeshLeft c m i *
            (1 + K / (upperRosserFixedDepthMeshLeft c m i * Real.log z)) - 1)) +
          ρ / 3 := hpart
    _ ≤ ((∑ i : Fin (m + 1), M i *
          (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i - 1)) + ρ / 3) + ρ / 3 := by
      linarith
    _ ≤ ((∫ x in Set.Ioo c 1, x⁻¹ * f x) +
          (2 * L * h) / c + B * h / c ^ 2) + ρ / 3 + ρ / 3 := by
      linarith
    _ ≤ (∫ x in Set.Ioo c 1, x⁻¹ * f x) + ρ := by
      linarith

/-- A common uniform modulus on a positive logarithmic screen is enough for a
uniform weighted Stieltjes comparison.  Unlike the Lipschitz specialization,
this form applies uniformly to compact continuous families. -/
theorem
    exists_weighted_sum_nu_div_one_sub_le_integral_add_screened_of_uniform_modulus
    (K ρ B c δ : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hc : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc c 1) →
        (∀ x ∈ Set.Icc c 1, 0 ≤ f x) →
        (∀ x ∈ Set.Icc c 1, f x ≤ B) →
        (∀ x ∈ Set.Icc c 1, ∀ y ∈ Set.Icc c 1,
          |x - y| < δ → |f x - f y| < ρ * c / 12) →
        MeasureTheory.IntegrableOn (fun x => x⁻¹ * f x) (Set.Ioo c 1) →
        (∀ p ∈ T, 0 ≤ w p ∧ w p ≤ f (Real.log p / Real.log z)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo c 1, x⁻¹ * f x) + ρ := by
  let ε : ℝ := ρ * c / 12
  let τ : ℝ := min δ (ρ * c ^ 2 / (6 * (B + 1)))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hB1 : 0 < B + 1 := by linarith
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min hδ (by positivity)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 - c) / τ < m := exists_nat_gt _
  let h : ℝ := upperRosserFixedDepthMeshWidth c m
  have hh : 0 < h := upperRosserFixedDepthMeshWidth_pos hc1 m
  have hhτ : h < τ := by
    have hmReal : (1 - c) / τ < (m : ℝ) := hm
    have hcross : 1 - c < τ * (m : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hτ).1 hmReal
    dsimp [h, upperRosserFixedDepthMeshWidth]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  have hhδ : h < δ := hhτ.trans_le (min_le_left _ _)
  have hhSmall : h ≤ ρ * c ^ 2 / (6 * (B + 1)) :=
    hhτ.le.trans (min_le_right _ _)
  have hmeshError : B * h / c ^ 2 ≤ ρ / 6 := by
    have hfrac : B / (B + 1) ≤ 1 := by
      apply (div_le_iff₀ hB1).2
      linarith
    calc
      B * h / c ^ 2 ≤
          B * (ρ * c ^ 2 / (6 * (B + 1))) / c ^ 2 := by
        gcongr
      _ = (ρ / 6) * (B / (B + 1)) := by
        field_simp [hc.ne', hB1.ne']
      _ ≤ ρ / 6 := by
        nlinarith [mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ ρ / 6)]
  have hBε : 0 ≤ B + ε := add_nonneg hB hε.le
  obtain ⟨zPart, hzPart, hPart⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add
      (Fin (m + 1)) K (ρ / 3) (B + ε) c hK (by positivity) hBε hc
  obtain ⟨zCorr, hzCorr, hCorr⟩ :=
    exists_upperRosserFixedDepthMesh_correctedDarboux_le_add
      m (K := K) (ρ := ρ / 3) (B := B + ε) (c := c)
        (zero_le_one.trans hK) (by positivity) hBε hc hc1
  let z₀ : ℝ := max zPart zCorr
  refine ⟨z₀, hzPart.trans (le_max_left _ _), ?_⟩
  intro S z T w f hz hlocal hT hcoord hf hfB hfmod hint hw
  have hzPartZ : zPart ≤ z := (le_max_left _ _).trans hz
  have hzCorrZ : zCorr ≤ z := (le_max_right _ _).trans hz
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) (hzPart.trans hzPartZ)
  have hzpos : 0 < z := by linarith
  let cell : ℕ → Fin (m + 1) :=
    fun p => upperRosserFixedDepthMeshCell c m (Real.log p / Real.log z)
  let M : Fin (m + 1) → ℝ :=
    fun i => f (upperRosserFixedDepthMeshLeft c m i) + ε
  have hleftMem : ∀ i : Fin (m + 1),
      upperRosserFixedDepthMeshLeft c m i ∈ Set.Icc c 1 := by
    intro i
    exact ⟨(upperRosserFixedDepthMeshLeft_mem hc1 m i).1,
      (upperRosserFixedDepthMeshLeft_le_right hc1 m i).trans
        (upperRosserFixedDepthMeshRight_le_one hc1 m i)⟩
  have hcell : ∀ p ∈ T,
      Real.log p / Real.log z ∈ Set.Icc
        (upperRosserFixedDepthMeshLeft c m (cell p))
        (upperRosserFixedDepthMeshRight c m (cell p)) := by
    intro p hp
    exact upperRosserFixedDepthMeshCell_bounds hc1 m (hcoord p hp)
  have hpow : ∀ p ∈ T,
      z ^ upperRosserFixedDepthMeshLeft c m (cell p) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ z ^ upperRosserFixedDepthMeshRight c m (cell p) := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (hT hp)
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have heq : z ^ (Real.log p / Real.log z) = (p : ℝ) := by
      simpa [Real.logb] using
        (Real.rpow_logb (x := (p : ℝ)) hzpos (ne_of_gt hz1) hpPos)
    exact
      ⟨(Real.rpow_le_rpow_of_exponent_le hz1.le (hcell p hp).1).trans_eq heq,
        heq.symm.trans_le
          (Real.rpow_le_rpow_of_exponent_le hz1.le (hcell p hp).2)⟩
  have hM : ∀ i, 0 ≤ M i ∧ M i ≤ B + ε := by
    intro i
    refine ⟨add_nonneg (hf _ (hleftMem i)) hε.le, ?_⟩
    simpa [M] using add_le_add_right (hfB _ (hleftMem i)) ε
  have hwM : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ M (cell p) := by
    intro p hp
    refine ⟨(hw p hp).1, ?_⟩
    let x := Real.log p / Real.log z
    let i := cell p
    have hbounds := hcell p hp
    have hdist :
        |x - upperRosserFixedDepthMeshLeft c m i| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hbounds.1)]
      calc
        x - upperRosserFixedDepthMeshLeft c m i ≤
            upperRosserFixedDepthMeshRight c m i -
              upperRosserFixedDepthMeshLeft c m i := by linarith [hbounds.2]
        _ = h := by
          dsimp [h, upperRosserFixedDepthMeshRight]
          ring
    have hdiff :
        |f x - f (upperRosserFixedDepthMeshLeft c m i)| < ε := by
      simpa [ε] using
        hfmod x (hcoord p hp) _ (hleftMem i) (hdist.trans_lt hhδ)
    have hupper :
        f x ≤ f (upperRosserFixedDepthMeshLeft c m i) + ε := by
      linarith [le_abs_self
        (f x - f (upperRosserFixedDepthMeshLeft c m i))]
    exact (hw p hp).2.trans (by simpa [M, i, x] using hupper)
  have hwBound : ∀ p ∈ T, w p ≤ B + ε := by
    intro p hp
    exact (hw p hp).2.trans
      ((hfB _ (hcoord p hp)).trans (le_add_of_nonneg_right hε.le))
  have hpart :=
    hPart S z T w cell
      (upperRosserFixedDepthMeshLeft c m)
      (upperRosserFixedDepthMeshRight c m) M hzPartZ hlocal
      (fun i => (upperRosserFixedDepthMeshLeft_mem hc1 m i).1)
      (fun i => upperRosserFixedDepthMeshLeft_le_right hc1 m i)
      hT hpow (fun i => (hM i).1) hwM hwBound
  have hcorr := hCorr z hzCorrZ M hM
  have hmajorant : ∀ i : Fin (m + 1), ∀ x ∈
      Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
        (upperRosserFixedDepthMeshRight c m i),
      M i ≤ f x + 2 * ε := by
    intro i x hx
    have hxMem : x ∈ Set.Icc c 1 :=
      ⟨(hleftMem i).1.trans hx.1.le,
        hx.2.le.trans (upperRosserFixedDepthMeshRight_le_one hc1 m i)⟩
    have hdist :
        |upperRosserFixedDepthMeshLeft c m i - x| ≤ h := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
      have hx' := hx.2
      dsimp [h, upperRosserFixedDepthMeshRight] at hx'
      linarith
    have hdiff :
        |f (upperRosserFixedDepthMeshLeft c m i) - f x| < ε := by
      simpa [ε] using
        hfmod _ (hleftMem i) x hxMem (hdist.trans_lt hhδ)
    dsimp [M]
    linarith [le_abs_self
      (f (upperRosserFixedDepthMeshLeft c m i) - f x)]
  have hdarboux :=
    upperRosserFixedDepthMesh_darbouxSum_le_integral_add
      m (c := c) (ε := 2 * ε) (B := B) (f := f) (M := M)
        hc hc1 (by positivity) hB hfB hmajorant hint
  have hεc : (2 * ε) / c = ρ / 6 := by
    dsimp [ε]
    field_simp [hc.ne']
    norm_num
  have hdarbouxError : (2 * ε) / c + B * h / c ^ 2 ≤ ρ / 3 := by
    rw [hεc]
    linarith
  calc
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
        (∑ i : Fin (m + 1), M i *
          (upperRosserFixedDepthMeshRight c m i /
              upperRosserFixedDepthMeshLeft c m i *
            (1 + K /
              (upperRosserFixedDepthMeshLeft c m i * Real.log z)) - 1)) +
          ρ / 3 := hpart
    _ ≤ ((∑ i : Fin (m + 1), M i *
          (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i - 1)) + ρ / 3) + ρ / 3 := by
      linarith
    _ ≤ ((∫ x in Set.Ioo c 1, x⁻¹ * f x) +
          (2 * ε) / c + B * h / c ^ 2) + ρ / 3 + ρ / 3 := by
      linarith
    _ ≤ (∫ x in Set.Ioo c 1, x⁻¹ * f x) + ρ := by
      linarith

/-- Thickening an interval by `δ` changes the integral of a nonnegative
uniformly bounded function by at most the two boundary strips. -/
theorem integral_thickenedIndicator_mul_le_integral_Ioo_add_screened
    {c δ u v C : ℝ} (hδ : 0 < δ) (hu : c ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1) (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn g (Set.Ioo (c : ℝ) 1))
    (hg : ∀ x ∈ Set.Ioo (c : ℝ) 1, 0 ≤ g x ∧ g x ≤ C) :
    (∫ x in Set.Ioo (c : ℝ) 1,
      (thickenedIndicator hδ (Set.Icc u v) x : ℝ) * g x) ≤
      (∫ x in Set.Ioo u v, g x) + 2 * C * δ := by
  let χ : ℝ → ℝ :=
    fun x => (thickenedIndicator hδ (Set.Icc u v) x : ℝ)
  let l : ℝ := max (c) (u - δ)
  let r : ℝ := min 1 (v + δ)
  have hlu : l ≤ u := by
    dsimp [l]
    exact max_le hu (by linarith)
  have hvr : v ≤ r := by
    dsimp [r]
    exact le_min hv (by linarith)
  have hlr : l ≤ r := hlu.trans (huv.trans hvr)
  have hJA : Set.Ioo l r ⊆ Set.Ioo (c : ℝ) 1 := by
    intro x hx
    exact ⟨(le_max_left _ _).trans_lt hx.1,
      hx.2.trans_le (min_le_left _ _)⟩
  have hthick :
      Metric.thickening δ (Set.Icc u v) = Set.Ioo (u - δ) (v + δ) := by
    rw [Real.Icc_eq_closedBall, thickening_closedBall hδ (by positivity),
      Real.ball_eq_Ioo]
    congr 1 <;> ring
  have hsupport :
      (∫ x in Set.Ioo (c : ℝ) 1, χ x * g x) =
        ∫ x in Set.Ioo l r, χ x * g x := by
    apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioo hJA
    intro x hx
    have hxnot : x ∉ Metric.thickening δ (Set.Icc u v) := by
      rw [hthick]
      intro hxt
      exact hx.2 ⟨max_lt hx.1.1 hxt.1, lt_min hx.1.2 hxt.2⟩
    dsimp [χ]
    rw [thickenedIndicator_zero hδ (Set.Icc u v) hxnot]
    norm_num
  have hintJ : MeasureTheory.IntegrableOn g (Set.Ioo l r) :=
    hint.mono_set hJA
  have hχcont : Continuous χ := by
    dsimp [χ]
    fun_prop
  have hχint :
      MeasureTheory.IntegrableOn (fun x => χ x * g x) (Set.Ioo l r) := by
    change MeasureTheory.Integrable (fun x => χ x * g x)
      (MeasureTheory.volume.restrict (Set.Ioo l r))
    have hmul := hintJ.mul_bdd hχcont.aestronglyMeasurable
      (show ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioo l r), ‖χ x‖ ≤ 1 by
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [χ]; positivity)]
        exact_mod_cast thickenedIndicator_le_one hδ (Set.Icc u v) x)
    simpa [mul_comm] using hmul
  have hmono :
      (∫ x in Set.Ioo l r, χ x * g x) ≤ ∫ x in Set.Ioo l r, g x := by
    apply MeasureTheory.setIntegral_mono_on hχint hintJ measurableSet_Ioo
    intro x hx
    apply mul_le_of_le_one_left (hg x (hJA hx)).1
    exact_mod_cast thickenedIndicator_le_one hδ (Set.Icc u v) x
  have hLUA : Set.Ioo l u ⊆ Set.Ioo (c : ℝ) 1 := by
    intro x hx
    exact ⟨(le_max_left _ _).trans_lt hx.1,
      hx.2.trans_le (huv.trans hv)⟩
  have hUVA : Set.Ioo u v ⊆ Set.Ioo (c : ℝ) 1 := by
    intro x hx
    exact ⟨hu.trans_lt hx.1, hx.2.trans_le hv⟩
  have hVRA : Set.Ioo v r ⊆ Set.Ioo (c : ℝ) 1 := by
    intro x hx
    exact ⟨hu.trans_lt (huv.trans_lt hx.1),
      hx.2.trans_le (min_le_left _ _)⟩
  have hintLU := hint.mono_set hLUA
  have hintUV := hint.mono_set hUVA
  have hintVR := hint.mono_set hVRA
  have hintUR : IntervalIntegrable g MeasureTheory.volume u r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (huv.trans hvr)).2
      (hint.mono_set (fun x hx => hJA ⟨hlu.trans_lt hx.1, hx.2⟩))
  have hdecomp :
      (∫ x in Set.Ioo l r, g x) =
        (∫ x in Set.Ioo l u, g x) + (∫ x in Set.Ioo u v, g x) +
          ∫ x in Set.Ioo v r, g x := by
    calc
      (∫ x in Set.Ioo l r, g x) = ∫ x in l..r, g x := by
        rw [intervalIntegral.integral_of_le hlr,
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = (∫ x in l..u, g x) + ∫ x in u..r, g x :=
        (intervalIntegral.integral_add_adjacent_intervals
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlu).2 hintLU)
          hintUR).symm
      _ = (∫ x in l..u, g x) +
          ((∫ x in u..v, g x) + ∫ x in v..r, g x) := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le huv).2 hintUV)
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le hvr).2 hintVR)]
      _ = (∫ x in Set.Ioo l u, g x) + (∫ x in Set.Ioo u v, g x) +
          ∫ x in Set.Ioo v r, g x := by
        rw [intervalIntegral.integral_of_le hlu,
          intervalIntegral.integral_of_le huv,
          intervalIntegral.integral_of_le hvr]
        simp_rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
        ring
  have hleft : (∫ x in Set.Ioo l u, g x) ≤ C * δ := by
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ => C) (Set.Ioo l u) :=
      MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    calc
      (∫ x in Set.Ioo l u, g x) ≤ ∫ _x in Set.Ioo l u, C := by
        apply MeasureTheory.setIntegral_mono_on hintLU hconst measurableSet_Ioo
        intro x hx
        exact (hg x (hLUA hx)).2
      _ = (u - l) * C := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hlu)]
        rfl
      _ ≤ C * δ := by
        have hwidth : u - l ≤ δ := by
          dsimp [l]
          linarith [le_max_right (c : ℝ) (u - δ)]
        nlinarith
  have hright : (∫ x in Set.Ioo v r, g x) ≤ C * δ := by
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ => C) (Set.Ioo v r) :=
      MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top)
    calc
      (∫ x in Set.Ioo v r, g x) ≤ ∫ _x in Set.Ioo v r, C := by
        apply MeasureTheory.setIntegral_mono_on hintVR hconst measurableSet_Ioo
        intro x hx
        exact (hg x (hVRA hx)).2
      _ = (r - v) * C := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hvr)]
        rfl
      _ ≤ C * δ := by
        have hwidth : r - v ≤ δ := by
          dsimp [r]
          linarith [min_le_right (1 : ℝ) (v + δ)]
        nlinarith
  rw [show (fun x => (thickenedIndicator hδ (Set.Icc u v) x : ℝ) * g x) =
      fun x => χ x * g x by rfl, hsupport]
  calc
    (∫ x in Set.Ioo l r, χ x * g x) ≤ ∫ x in Set.Ioo l r, g x := hmono
    _ = (∫ x in Set.Ioo l u, g x) + (∫ x in Set.Ioo u v, g x) +
        ∫ x in Set.Ioo v r, g x := hdecomp
    _ ≤ (∫ x in Set.Ioo u v, g x) + 2 * C * δ := by linarith

/-- Compatibility specialization of the thickened-interval estimate to the
traditional one-sixth screen. -/
theorem integral_thickenedIndicator_mul_le_integral_Ioo_add
    {δ u v C : ℝ} (hδ : 0 < δ) (hu : 1 / 6 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1) (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn g (Set.Ioo (1 / 6 : ℝ) 1))
    (hg : ∀ x ∈ Set.Ioo (1 / 6 : ℝ) 1, 0 ≤ g x ∧ g x ≤ C) :
    (∫ x in Set.Ioo (1 / 6 : ℝ) 1,
      (thickenedIndicator hδ (Set.Icc u v) x : ℝ) * g x) ≤
      (∫ x in Set.Ioo u v, g x) + 2 * C * δ :=
  integral_thickenedIndicator_mul_le_integral_Ioo_add_screened
    (c := (1 / 6 : ℝ)) hδ hu huv hv hC hint hg

/-- Uniform weighted Stieltjes comparison on any moving subinterval of the
screened box.  A thickened indicator absorbs both endpoint atoms without
requiring the weight to vanish at the moving endpoints. -/
theorem exists_weighted_sum_nu_div_one_sub_le_integral_Ioo_add
    (K ρ B L : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ) (u v : ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        1 / 6 ≤ u → u ≤ v → v ≤ 1 →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc u v) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, 0 ≤ f x) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, f x ≤ B) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
          ∀ y ∈ Set.Icc (1 / 6 : ℝ) 1,
            |f x - f y| ≤ L * |x - y|) →
        MeasureTheory.IntegrableOn
          (fun x => x⁻¹ * f x) (Set.Ioo (1 / 6) 1) →
        (∀ p ∈ T, 0 ≤ w p ∧ w p ≤ f (Real.log p / Real.log z)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo u v, x⁻¹ * f x) + ρ := by
  let δ : ℝ := ρ / (24 * (B + 1))
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let L' : ℝ := L + B / δ
  have hL' : 0 ≤ L' := by
    dsimp [L']
    positivity
  obtain ⟨z₀, hz₀, hglobal⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_add
      K (ρ / 2) B L' hK (half_pos hρ) hB hL'
  refine ⟨z₀, hz₀, ?_⟩
  intro S z T w f u v hz hlocal hT hu huv hv hcoord hf hfB hfLip hint hw
  let χ : ℝ → ℝ :=
    fun x => (thickenedIndicator hδ (Set.Icc u v) x : ℝ)
  let F : ℝ → ℝ := fun x => χ x * f x
  have hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    exact ⟨by dsimp [χ]; positivity,
      by
        dsimp [χ]
        exact_mod_cast thickenedIndicator_le_one hδ (Set.Icc u v) x⟩
  have hχone : ∀ x ∈ Set.Icc u v, χ x = 1 := by
    intro x hx
    dsimp [χ]
    norm_num [thickenedIndicator_one hδ (Set.Icc u v) hx]
  have hχLip : ∀ x y, |χ x - χ y| ≤ δ⁻¹ * |x - y| := by
    intro x y
    have h :=
      (lipschitzWith_thickenedIndicator hδ (Set.Icc u v)).dist_le_mul x y
    rw [NNReal.dist_eq, Real.dist_eq] at h
    norm_num at h ⊢
    simpa [χ, max_eq_left hδ.le] using h
  have hF : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, 0 ≤ F x := by
    intro x hx
    exact mul_nonneg (hχ x).1 (hf x hx)
  have hFB : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, F x ≤ B := by
    intro x hx
    exact (mul_le_of_le_one_left (hf x hx) (hχ x).2).trans (hfB x hx)
  have hFLip : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 6 : ℝ) 1,
        |F x - F y| ≤ L' * |x - y| := by
    intro x hx y hy
    have hχabs : |χ x| ≤ 1 := by
      rw [abs_of_nonneg (hχ x).1]
      exact (hχ x).2
    have hfyabs : |f y| ≤ B := by
      rw [abs_of_nonneg (hf y hy)]
      exact hfB y hy
    calc
      |F x - F y| =
          |χ x * (f x - f y) + (χ x - χ y) * f y| := by
        dsimp [F]
        congr 1
        ring
      _ ≤ |χ x| * |f x - f y| + |χ x - χ y| * |f y| := by
        simpa only [abs_mul] using
          abs_add_le (χ x * (f x - f y)) ((χ x - χ y) * f y)
      _ ≤ 1 * (L * |x - y|) + (δ⁻¹ * |x - y|) * B := by
        apply add_le_add
        · exact mul_le_mul hχabs (hfLip x hx y hy)
            (abs_nonneg _) (by norm_num)
        · exact mul_le_mul (hχLip x y) hfyabs
            (abs_nonneg _) (by positivity)
      _ = L' * |x - y| := by
        dsimp [L']
        ring
  have hχcont : Continuous χ := by
    dsimp [χ]
    fun_prop
  have hFint : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * F x) (Set.Ioo (1 / 6) 1) := by
    change MeasureTheory.Integrable (fun x => x⁻¹ * F x)
      (MeasureTheory.volume.restrict (Set.Ioo (1 / 6) 1))
    have hmul := hint.mul_bdd hχcont.aestronglyMeasurable
      (show ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioo (1 / 6 : ℝ) 1),
          ‖χ x‖ ≤ 1 by
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
        exact (hχ x).2)
    simpa [F, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hcoordGlobal : ∀ p ∈ T,
      Real.log p / Real.log z ∈ Set.Icc (1 / 6 : ℝ) 1 := by
    intro p hp
    exact ⟨hu.trans (hcoord p hp).1, (hcoord p hp).2.trans hv⟩
  have hwF : ∀ p ∈ T,
      0 ≤ w p ∧ w p ≤ F (Real.log p / Real.log z) := by
    intro p hp
    simpa [F, hχone _ (hcoord p hp)] using hw p hp
  have hcomparison :=
    hglobal S z T w F hz hlocal hT hcoordGlobal hF hFB hFLip hFint hwF
  have hg : ∀ x ∈ Set.Ioo (1 / 6 : ℝ) 1,
      0 ≤ x⁻¹ * f x ∧ x⁻¹ * f x ≤ 6 * B := by
    intro x hx
    have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 6).trans hx.1
    have hxmem : x ∈ Set.Icc (1 / 6 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hxinv : x⁻¹ ≤ (6 : ℝ) := by
      calc
        x⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
          (inv_le_inv₀ hxpos (by norm_num)).2 hxmem.1
        _ = 6 := by norm_num
    exact ⟨mul_nonneg (inv_nonneg.mpr hxpos.le) (hf x hxmem),
      mul_le_mul hxinv (hfB x hxmem) (hf x hxmem) (by norm_num)⟩
  have hcutoff :=
    integral_thickenedIndicator_mul_le_integral_Ioo_add
      hδ hu huv hv (mul_nonneg (by norm_num) hB) hint hg
  have hintegral :
      (∫ x in Set.Ioo (1 / 6 : ℝ) 1, x⁻¹ * F x) ≤
        (∫ x in Set.Ioo u v, x⁻¹ * f x) + 12 * B * δ := by
    calc
      (∫ x in Set.Ioo (1 / 6 : ℝ) 1, x⁻¹ * F x) =
          ∫ x in Set.Ioo (1 / 6 : ℝ) 1,
            (thickenedIndicator hδ (Set.Icc u v) x : ℝ) *
              (x⁻¹ * f x) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
            intro x hx
            dsimp [F, χ]
            ring
      _ ≤ (∫ x in Set.Ioo u v, x⁻¹ * f x) + 2 * (6 * B) * δ :=
        hcutoff
      _ = (∫ x in Set.Ioo u v, x⁻¹ * f x) + 12 * B * δ := by ring
  have hδbudget : 12 * B * δ ≤ ρ / 2 := by
    have hratio : B / (B + 1) ≤ 1 :=
      (div_le_iff₀ hB1).2 (by linarith)
    calc
      12 * B * δ = (ρ / 2) * (B / (B + 1)) := by
        dsimp [δ]
        field_simp
        ring
      _ ≤ (ρ / 2) * 1 :=
        mul_le_mul_of_nonneg_left hratio (half_pos hρ).le
      _ = ρ / 2 := by ring
  calc
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
        (∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * F x) + ρ / 2 := hcomparison
    _ ≤ ((∫ x in Set.Ioo u v, x⁻¹ * f x) + 12 * B * δ) +
        ρ / 2 := by linarith
    _ ≤ (∫ x in Set.Ioo u v, x⁻¹ * f x) + ρ := by linarith

/-- Uniform Stieltjes comparison on a moving subinterval of an arbitrary
positive logarithmic screen. -/
theorem exists_weighted_sum_nu_div_one_sub_le_integral_Ioo_add_screened
    (K ρ B L c : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hc : 0 < c) (hc1 : c < 1) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ) (u v : ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        c ≤ u → u ≤ v → v ≤ 1 →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc u v) →
        (∀ x ∈ Set.Icc c 1, 0 ≤ f x) →
        (∀ x ∈ Set.Icc c 1, f x ≤ B) →
        (∀ x ∈ Set.Icc c 1, ∀ y ∈ Set.Icc c 1,
          |f x - f y| ≤ L * |x - y|) →
        MeasureTheory.IntegrableOn (fun x => x⁻¹ * f x) (Set.Ioo c 1) →
        (∀ p ∈ T, 0 ≤ w p ∧ w p ≤ f (Real.log p / Real.log z)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo u v, x⁻¹ * f x) + ρ := by
  let C : ℝ := c⁻¹ * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ : ℝ := ρ / (4 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let L' : ℝ := L + B / δ
  have hL' : 0 ≤ L' := by dsimp [L']; positivity
  obtain ⟨z₀, hz₀, hglobal⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_add_screened
      K (ρ / 2) B L' c hK (half_pos hρ) hB hL' hc hc1
  refine ⟨z₀, hz₀, ?_⟩
  intro S z T w f u v hz hlocal hT hu huv hv hcoord hf hfB hfLip hint hw
  let χ : ℝ → ℝ :=
    fun x => (thickenedIndicator hδ (Set.Icc u v) x : ℝ)
  let F : ℝ → ℝ := fun x => χ x * f x
  have hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    exact ⟨by dsimp [χ]; positivity,
      by
        dsimp [χ]
        exact_mod_cast thickenedIndicator_le_one hδ (Set.Icc u v) x⟩
  have hχone : ∀ x ∈ Set.Icc u v, χ x = 1 := by
    intro x hx
    dsimp [χ]
    norm_num [thickenedIndicator_one hδ (Set.Icc u v) hx]
  have hχLip : ∀ x y, |χ x - χ y| ≤ δ⁻¹ * |x - y| := by
    intro x y
    have h :=
      (lipschitzWith_thickenedIndicator hδ (Set.Icc u v)).dist_le_mul x y
    rw [NNReal.dist_eq, Real.dist_eq] at h
    norm_num at h ⊢
    simpa [χ, max_eq_left hδ.le] using h
  have hF : ∀ x ∈ Set.Icc c 1, 0 ≤ F x := by
    intro x hx
    exact mul_nonneg (hχ x).1 (hf x hx)
  have hFB : ∀ x ∈ Set.Icc c 1, F x ≤ B := by
    intro x hx
    exact (mul_le_of_le_one_left (hf x hx) (hχ x).2).trans (hfB x hx)
  have hFLip : ∀ x ∈ Set.Icc c 1, ∀ y ∈ Set.Icc c 1,
      |F x - F y| ≤ L' * |x - y| := by
    intro x hx y hy
    have hχabs : |χ x| ≤ 1 := by
      rw [abs_of_nonneg (hχ x).1]
      exact (hχ x).2
    have hfyabs : |f y| ≤ B := by
      rw [abs_of_nonneg (hf y hy)]
      exact hfB y hy
    calc
      |F x - F y| =
          |χ x * (f x - f y) + (χ x - χ y) * f y| := by
        dsimp [F]
        congr 1
        ring
      _ ≤ |χ x| * |f x - f y| + |χ x - χ y| * |f y| := by
        simpa only [abs_mul] using
          abs_add_le (χ x * (f x - f y)) ((χ x - χ y) * f y)
      _ ≤ 1 * (L * |x - y|) + (δ⁻¹ * |x - y|) * B := by
        apply add_le_add
        · exact mul_le_mul hχabs (hfLip x hx y hy)
            (abs_nonneg _) (by norm_num)
        · exact mul_le_mul (hχLip x y) hfyabs
            (abs_nonneg _) (by positivity)
      _ = L' * |x - y| := by
        dsimp [L']
        ring
  have hχcont : Continuous χ := by
    dsimp [χ]
    fun_prop
  have hFint : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * F x) (Set.Ioo c 1) := by
    change MeasureTheory.Integrable (fun x => x⁻¹ * F x)
      (MeasureTheory.volume.restrict (Set.Ioo c 1))
    have hmul := hint.mul_bdd hχcont.aestronglyMeasurable
      (show ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioo c 1),
          ‖χ x‖ ≤ 1 by
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ x).1]
        exact (hχ x).2)
    simpa [F, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hcoordGlobal : ∀ p ∈ T,
      Real.log p / Real.log z ∈ Set.Icc c 1 := by
    intro p hp
    exact ⟨hu.trans (hcoord p hp).1, (hcoord p hp).2.trans hv⟩
  have hwF : ∀ p ∈ T,
      0 ≤ w p ∧ w p ≤ F (Real.log p / Real.log z) := by
    intro p hp
    simpa [F, hχone _ (hcoord p hp)] using hw p hp
  have hcomparison :=
    hglobal S z T w F hz hlocal hT hcoordGlobal hF hFB hFLip hFint hwF
  have hg : ∀ x ∈ Set.Ioo c 1,
      0 ≤ x⁻¹ * f x ∧ x⁻¹ * f x ≤ C := by
    intro x hx
    have hxpos : 0 < x := hc.trans hx.1
    have hxmem : x ∈ Set.Icc c 1 := ⟨hx.1.le, hx.2.le⟩
    have hxinv : x⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hxpos hc).2 hxmem.1
    exact ⟨mul_nonneg (inv_nonneg.mpr hxpos.le) (hf x hxmem),
      by
        dsimp [C]
        exact mul_le_mul hxinv (hfB x hxmem) (hf x hxmem)
          (inv_nonneg.mpr hc.le)⟩
  have hcutoff :=
    integral_thickenedIndicator_mul_le_integral_Ioo_add_screened
      hδ hu huv hv hC hint hg
  have hintegral :
      (∫ x in Set.Ioo c 1, x⁻¹ * F x) ≤
        (∫ x in Set.Ioo u v, x⁻¹ * f x) + 2 * C * δ := by
    calc
      (∫ x in Set.Ioo c 1, x⁻¹ * F x) =
          ∫ x in Set.Ioo c 1,
            (thickenedIndicator hδ (Set.Icc u v) x : ℝ) *
              (x⁻¹ * f x) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
            intro x hx
            dsimp [F, χ]
            ring
      _ ≤ (∫ x in Set.Ioo u v, x⁻¹ * f x) + 2 * C * δ := hcutoff
  have hδbudget : 2 * C * δ ≤ ρ / 2 := by
    have hratio : C / (C + 1) ≤ 1 :=
      (div_le_iff₀ hC1).2 (by linarith)
    calc
      2 * C * δ = (ρ / 2) * (C / (C + 1)) := by
        dsimp [δ]
        field_simp
        ring
      _ ≤ (ρ / 2) * 1 :=
        mul_le_mul_of_nonneg_left hratio (half_pos hρ).le
      _ = ρ / 2 := by ring
  calc
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
        (∫ x in Set.Ioo c 1, x⁻¹ * F x) + ρ / 2 := hcomparison
    _ ≤ ((∫ x in Set.Ioo u v, x⁻¹ * f x) + 2 * C * δ) +
        ρ / 2 := by linarith
    _ ≤ (∫ x in Set.Ioo u v, x⁻¹ * f x) + ρ := by linarith

/-- Uniform Stieltjes comparison in logarithmic ratios relative to a prime.
Rescaling the screened comparison by `R` turns the base from `q` into `q ^ R`;
the resulting estimate is uniform in the terminal prime `q`. -/
theorem exists_weighted_sum_nu_div_one_sub_le_logRatio_integral_add
    (K ρ B L R : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hR : 1 < R) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log q ∈ Set.Icc (1 : ℝ) R) →
        (∀ x ∈ Set.Icc (1 : ℝ) R, 0 ≤ f x) →
        (∀ x ∈ Set.Icc (1 : ℝ) R, f x ≤ B) →
        (∀ x ∈ Set.Icc (1 : ℝ) R, ∀ y ∈ Set.Icc (1 : ℝ) R,
          |f x - f y| ≤ L * |x - y|) →
        MeasureTheory.IntegrableOn
          (fun x => x⁻¹ * f x) (Set.Ioo 1 R) →
        (∀ p ∈ T, 0 ≤ w p ∧
          w p ≤ f (Real.log p / Real.log q)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo 1 R, x⁻¹ * f x) + ρ := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hc : 0 < 1 / R := div_pos zero_lt_one hRpos
  have hc1 : 1 / R < 1 := (div_lt_one hRpos).2 hR
  obtain ⟨z₀, hz₀, htransfer⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_add_screened
      K ρ B (L * R) (1 / R) hK hρ hB
        (mul_nonneg hL hRpos.le) hc hc1
  refine ⟨z₀, hz₀, ?_⟩
  intro S q T w f hqLarge hq hlocal hT hcoord hf hfB hfLip hint hw
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hqR).ne'
  let F : ℝ → ℝ := fun t => f (R * t)
  have hbase : z₀ ≤ (q : ℝ) ^ R := by
    calc
      z₀ ≤ (q : ℝ) := by exact_mod_cast hqLarge
      _ = (q : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (q : ℝ) ^ R :=
        Real.rpow_le_rpow_of_exponent_le hqR.le hR.le
  have hscaledCoord : ∀ p ∈ T,
      Real.log p / Real.log ((q : ℝ) ^ R) ∈
        Set.Icc (1 / R : ℝ) 1 := by
    intro p hp
    have hx := hcoord p hp
    rw [Real.log_rpow hqpos]
    have heq : Real.log (p : ℝ) / (R * Real.log q) =
        (Real.log (p : ℝ) / Real.log q) / R := by field_simp
    rw [heq]
    exact ⟨(div_le_div_iff_of_pos_right hRpos).2 hx.1,
      (div_le_one hRpos).2 hx.2⟩
  have hF : ∀ t ∈ Set.Icc (1 / R : ℝ) 1, 0 ≤ F t := by
    intro t ht
    apply hf
    change 1 ≤ R * t ∧ R * t ≤ R
    constructor
    · have := mul_le_mul_of_nonneg_left ht.1 hRpos.le
      field_simp [hRpos.ne'] at this
      exact this
    · simpa using mul_le_mul_of_nonneg_left ht.2 hRpos.le
  have hFB : ∀ t ∈ Set.Icc (1 / R : ℝ) 1, F t ≤ B := by
    intro t ht
    apply hfB
    constructor
    · have := mul_le_mul_of_nonneg_left ht.1 hRpos.le
      field_simp [hRpos.ne'] at this
      exact this
    · simpa using mul_le_mul_of_nonneg_left ht.2 hRpos.le
  have hFLip : ∀ x ∈ Set.Icc (1 / R : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / R : ℝ) 1,
        |F x - F y| ≤ (L * R) * |x - y| := by
    intro x hx y hy
    have hxy := hfLip (R * x) (by
        constructor
        · have := mul_le_mul_of_nonneg_left hx.1 hRpos.le
          field_simp [hRpos.ne'] at this
          exact this
        · simpa using mul_le_mul_of_nonneg_left hx.2 hRpos.le)
      (R * y) (by
        constructor
        · have := mul_le_mul_of_nonneg_left hy.1 hRpos.le
          field_simp [hRpos.ne'] at this
          exact this
        · simpa using mul_le_mul_of_nonneg_left hy.2 hRpos.le)
    calc
      |F x - F y| = |f (R * x) - f (R * y)| := rfl
      _ ≤ L * |R * x - R * y| := hxy
      _ = (L * R) * |x - y| := by
        rw [← mul_sub, abs_mul, abs_of_pos hRpos]
        ring
  have hscaledInt : MeasureTheory.IntegrableOn
      (fun t => t⁻¹ * F t) (Set.Ioo (1 / R) 1) := by
    have hi : IntervalIntegrable (fun x => x⁻¹ * f x)
        MeasureTheory.volume 1 R :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).2 hint
    have hcomp := hi.comp_mul_left (c := R)
    have hraw : IntervalIntegrable
        (fun t => (R * t)⁻¹ * f (R * t))
        MeasureTheory.volume (1 / R) 1 := by
      simpa [div_self hRpos.ne'] using hcomp
    have hscaled : IntervalIntegrable
        (fun t => R * ((R * t)⁻¹ * f (R * t)))
        MeasureTheory.volume (1 / R) 1 :=
      hraw.const_mul R
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hc1.le).1
    apply hscaled.congr
    intro t ht
    rw [Set.uIoc_of_le hc1.le] at ht
    have htpos : 0 < t := lt_trans hc ht.1
    dsimp [F]
    field_simp [hRpos.ne', htpos.ne']
  have hwF : ∀ p ∈ T, 0 ≤ w p ∧
      w p ≤ F (Real.log p / Real.log ((q : ℝ) ^ R)) := by
    intro p hp
    refine ⟨(hw p hp).1, ?_⟩
    have heq : R * (Real.log p / Real.log ((q : ℝ) ^ R)) =
        Real.log p / Real.log q := by
      rw [Real.log_rpow hqpos]
      field_simp [hRpos.ne', hlogq]
    simpa [F, heq] using (hw p hp).2
  have hbound :=
    htransfer S ((q : ℝ) ^ R) T w F hbase hlocal hT hscaledCoord
      hF hFB hFLip hscaledInt hwF
  have hintegral :
      (∫ t in Set.Ioo (1 / R) 1, t⁻¹ * F t) =
        ∫ x in Set.Ioo 1 R, x⁻¹ * f x := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hc1.le,
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hR.le]
    have hscale := intervalIntegral.mul_integral_comp_mul_left
      (f := fun x => x⁻¹ * f x) (a := 1 / R) (b := 1) R
    rw [show R * (1 / R) = 1 by field_simp, mul_one] at hscale
    calc
      (∫ t : ℝ in 1 / R..1, t⁻¹ * F t) =
          ∫ t : ℝ in 1 / R..1,
            R * ((R * t)⁻¹ * f (R * t)) := by
              apply intervalIntegral.integral_congr
              intro t ht
              rw [Set.uIcc_of_le hc1.le] at ht
              have htpos : 0 < t := hc.trans_le ht.1
              dsimp [F]
              field_simp [hRpos.ne', htpos.ne']
      _ = R * ∫ t : ℝ in 1 / R..1,
          (R * t)⁻¹ * f (R * t) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ x : ℝ in 1..R, x⁻¹ * f x := hscale
  rw [hintegral] at hbound
  exact hbound

/-- Uniform logarithmic-ratio Stieltjes comparison on moving subintervals.
The prime cutoff is independent of the terminal prime and of the endpoints. -/
theorem exists_weighted_sum_nu_div_one_sub_le_logRatio_integral_Ioo_add
    (K ρ B L R : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hR : 1 < R) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ) (u v : ℝ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        1 ≤ u → u ≤ v → v ≤ R →
        (∀ p ∈ T, Real.log p / Real.log q ∈ Set.Icc u v) →
        (∀ x ∈ Set.Icc (1 : ℝ) R, 0 ≤ f x) →
        (∀ x ∈ Set.Icc (1 : ℝ) R, f x ≤ B) →
        (∀ x ∈ Set.Icc (1 : ℝ) R, ∀ y ∈ Set.Icc (1 : ℝ) R,
          |f x - f y| ≤ L * |x - y|) →
        MeasureTheory.IntegrableOn
          (fun x => x⁻¹ * f x) (Set.Ioo 1 R) →
        (∀ p ∈ T, 0 ≤ w p ∧
          w p ≤ f (Real.log p / Real.log q)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo u v, x⁻¹ * f x) + ρ := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hc : 0 < 1 / R := div_pos zero_lt_one hRpos
  have hc1 : 1 / R < 1 := (div_lt_one hRpos).2 hR
  obtain ⟨z₀, hz₀, htransfer⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_Ioo_add_screened
      K ρ B (L * R) (1 / R) hK hρ hB
        (mul_nonneg hL hRpos.le) hc hc1
  refine ⟨z₀, hz₀, ?_⟩
  intro S q T w f u v hqLarge hq hlocal hT hu huv hv hcoord
    hf hfB hfLip hint hw
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  let F : ℝ → ℝ := fun t => f (R * t)
  have hbase : z₀ ≤ (q : ℝ) ^ R := by
    calc
      z₀ ≤ (q : ℝ) := by exact_mod_cast hqLarge
      _ = (q : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (q : ℝ) ^ R :=
        Real.rpow_le_rpow_of_exponent_le hqR.le hR.le
  have hscaleEq : ∀ p : ℕ,
      Real.log p / Real.log ((q : ℝ) ^ R) =
        (Real.log p / Real.log q) / R := by
    intro p
    rw [Real.log_rpow hqpos]
    field_simp
  have hscaledCoord : ∀ p ∈ T,
      Real.log p / Real.log ((q : ℝ) ^ R) ∈
        Set.Icc (u / R) (v / R) := by
    intro p hp
    rw [hscaleEq]
    exact ⟨(div_le_div_iff_of_pos_right hRpos).2 (hcoord p hp).1,
      (div_le_div_iff_of_pos_right hRpos).2 (hcoord p hp).2⟩
  have hF : ∀ t ∈ Set.Icc (1 / R : ℝ) 1, 0 ≤ F t := by
    intro t ht
    apply hf
    change 1 ≤ R * t ∧ R * t ≤ R
    constructor
    · have := mul_le_mul_of_nonneg_left ht.1 hRpos.le
      field_simp [hRpos.ne'] at this
      exact this
    · simpa using mul_le_mul_of_nonneg_left ht.2 hRpos.le
  have hFB : ∀ t ∈ Set.Icc (1 / R : ℝ) 1, F t ≤ B := by
    intro t ht
    apply hfB
    constructor
    · have := mul_le_mul_of_nonneg_left ht.1 hRpos.le
      field_simp [hRpos.ne'] at this
      exact this
    · simpa using mul_le_mul_of_nonneg_left ht.2 hRpos.le
  have hFLip : ∀ x ∈ Set.Icc (1 / R : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / R : ℝ) 1,
        |F x - F y| ≤ (L * R) * |x - y| := by
    intro x hx y hy
    have hxy := hfLip (R * x) (by
        constructor
        · have := mul_le_mul_of_nonneg_left hx.1 hRpos.le
          field_simp [hRpos.ne'] at this
          exact this
        · simpa using mul_le_mul_of_nonneg_left hx.2 hRpos.le)
      (R * y) (by
        constructor
        · have := mul_le_mul_of_nonneg_left hy.1 hRpos.le
          field_simp [hRpos.ne'] at this
          exact this
        · simpa using mul_le_mul_of_nonneg_left hy.2 hRpos.le)
    calc
      |F x - F y| = |f (R * x) - f (R * y)| := rfl
      _ ≤ L * |R * x - R * y| := hxy
      _ = (L * R) * |x - y| := by
        rw [← mul_sub, abs_mul, abs_of_pos hRpos]
        ring
  have hscaledInt : MeasureTheory.IntegrableOn
      (fun t => t⁻¹ * F t) (Set.Ioo (1 / R) 1) := by
    have hi : IntervalIntegrable (fun x => x⁻¹ * f x)
        MeasureTheory.volume 1 R :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).2 hint
    have hcomp := hi.comp_mul_left (c := R)
    have hraw : IntervalIntegrable
        (fun t => (R * t)⁻¹ * f (R * t))
        MeasureTheory.volume (1 / R) 1 := by
      simpa [div_self hRpos.ne'] using hcomp
    have hscaled : IntervalIntegrable
        (fun t => R * ((R * t)⁻¹ * f (R * t)))
        MeasureTheory.volume (1 / R) 1 :=
      hraw.const_mul R
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hc1.le).1
    apply hscaled.congr
    intro t ht
    rw [Set.uIoc_of_le hc1.le] at ht
    have htpos : 0 < t := lt_trans hc ht.1
    dsimp [F]
    field_simp [hRpos.ne', htpos.ne']
  have hwF : ∀ p ∈ T, 0 ≤ w p ∧
      w p ≤ F (Real.log p / Real.log ((q : ℝ) ^ R)) := by
    intro p hp
    refine ⟨(hw p hp).1, ?_⟩
    rw [hscaleEq]
    have heq : R * (Real.log p / Real.log q / R) =
        Real.log p / Real.log q := by field_simp [hRpos.ne']
    simpa [F, heq] using (hw p hp).2
  have hbound :=
    htransfer S ((q : ℝ) ^ R) T w F (u / R) (v / R)
      hbase hlocal hT
      ((div_le_div_iff_of_pos_right hRpos).2 hu)
      ((div_le_div_iff_of_pos_right hRpos).2 huv)
      ((div_le_one hRpos).2 hv)
      hscaledCoord hF hFB hFLip hscaledInt hwF
  have hintegral :
      (∫ t in Set.Ioo (u / R) (v / R), t⁻¹ * F t) =
        ∫ x in Set.Ioo u v, x⁻¹ * f x := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le
          ((div_le_div_iff_of_pos_right hRpos).2 huv),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le huv]
    have hscale := intervalIntegral.mul_integral_comp_mul_left
      (f := fun x => x⁻¹ * f x) (a := u / R) (b := v / R) R
    rw [show R * (u / R) = u by field_simp,
      show R * (v / R) = v by field_simp] at hscale
    calc
      (∫ t : ℝ in u / R..v / R, t⁻¹ * F t) =
          ∫ t : ℝ in u / R..v / R,
            R * ((R * t)⁻¹ * f (R * t)) := by
              apply intervalIntegral.integral_congr
              intro t ht
              rw [Set.uIcc_of_le
                ((div_le_div_iff_of_pos_right hRpos).2 huv)] at ht
              have htpos : 0 < t :=
                (div_pos (lt_of_lt_of_le zero_lt_one hu) hRpos).trans_le ht.1
              dsimp [F]
              field_simp [hRpos.ne', htpos.ne']
      _ = R * ∫ t : ℝ in u / R..v / R,
          (R * t)⁻¹ * f (R * t) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ x : ℝ in u..v, x⁻¹ * f x := hscale
  rw [hintegral] at hbound
  exact hbound

/-- One discrete inner reverse-pair sum is uniformly approximated by its
continuous logarithmic integral on every fixed ratio window. -/
theorem exists_upperRosserAlternatingPairDiscrete_inner_le_integral_add
    (K ρ R : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hR : 3 ≤ R) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (r y v : ℝ) (T : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → y ∈ Set.Icc (1 : ℝ) R → y ≤ v → v ≤ R →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log q ∈ Set.Icc y v) →
        ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
            LinearSieve.upperRosserAlternatingPairNormalizedKernel r y
              (Real.log p / Real.log q) ≤
          (∫ x in Set.Ioo y v, x⁻¹ *
            LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x) + ρ := by
  obtain ⟨Q, hQ, htransfer⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_logRatio_integral_Ioo_add
      K ρ (R ^ 2) (3 * R ^ 2) R hK hρ (sq_nonneg R)
        (mul_nonneg (by norm_num) (sq_nonneg R))
        (lt_of_lt_of_le (by norm_num) hR)
  refine ⟨Q, hQ, ?_⟩
  intro S q r y v T hq hqPrime hlocal hr hy hyv hv hT hcoord
  let f : ℝ → ℝ := fun x =>
    LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x
  have hf : ∀ x ∈ Set.Icc (1 : ℝ) R, 0 ≤ f x := by
    intro x hx
    exact LinearSieve.upperRosserAlternatingPairNormalizedKernel_nonneg _ _ _
  have hfB : ∀ x ∈ Set.Icc (1 : ℝ) R, f x ≤ R ^ 2 := by
    intro x hx
    exact LinearSieve.upperRosserAlternatingPairNormalizedKernel_le_sq
      hr hR hx hy
  have hfLip : ∀ x ∈ Set.Icc (1 : ℝ) R,
      ∀ x' ∈ Set.Icc (1 : ℝ) R,
        |f x - f x'| ≤ 3 * R ^ 2 * |x - x'| := by
    intro x hx x' hx'
    exact
      LinearSieve.abs_upperRosserAlternatingPairNormalizedKernel_sub_le
        hr hR hx hx' hy
  have hfInt : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * f x) (Set.Ioo 1 R) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (le_trans (by norm_num) hR)).1
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_trans (by norm_num) hR)]
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hr0 : r ≠ 0 := by linarith
    apply ContinuousAt.continuousWithinAt
    dsimp [f, LinearSieve.upperRosserAlternatingPairNormalizedKernel]
    fun_prop
  have hbound :=
    htransfer S q T
      (fun p => f (Real.log p / Real.log q)) f y v
      hq hqPrime hlocal hT hy.1 hyv hv
      hcoord hf hfB hfLip hfInt
        (fun p hp => ⟨hf _ ⟨hy.1.trans (hcoord p hp).1,
          (hcoord p hp).2.trans hv⟩, le_rfl⟩)
  simpa [f, mul_comm] using hbound

/-- The explicit normalized mass left after continuously integrating the larger
member of one reverse Rosser pair. -/
noncomputable def upperRosserAlternatingPairNormalizedInnerRaw
    (r y : ℝ) : ℝ :=
  (r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
    Real.log ((y + r) / (2 * y))) / r ^ 2

/-- The nonnegative extension of the normalized inner reverse-pair mass.  The
raw formula vanishes at `y = r` and is nonpositive beyond that point. -/
noncomputable def upperRosserAlternatingPairNormalizedInner
    (r y : ℝ) : ℝ :=
  max 0 (upperRosserAlternatingPairNormalizedInnerRaw r y)

theorem integral_upperRosserAlternatingPairNormalizedKernel_inner
    {r y : ℝ} (_hr : 0 < r) (hy : 0 < y) (hyr : y ≤ r) :
    (∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
      LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x) =
      upperRosserAlternatingPairNormalizedInnerRaw r y := by
  rw [show (fun x : ℝ => x⁻¹ *
      LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x) =
      fun x => (x⁻¹ * ((r + y + x) / x) ^ 2) / r ^ 2 by
    funext x
    unfold LinearSieve.upperRosserAlternatingPairNormalizedKernel
    ring,
    MeasureTheory.integral_div,
    LinearSieve.integral_upperRosserAlternatingPair_quadratic_inner hy hyr]
  rfl

theorem upperRosserAlternatingPairNormalizedInner_eq_integral
    {r y : ℝ} (hr : 0 < r) (hy : 0 < y) (hyr : y ≤ r) :
    upperRosserAlternatingPairNormalizedInner r y =
      ∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
        LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x := by
  have hnonneg :
      0 ≤ ∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
        LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (inv_nonneg.mpr (hy.trans hx.1).le)
      (LinearSieve.upperRosserAlternatingPairNormalizedKernel_nonneg r y x)
  rw [upperRosserAlternatingPairNormalizedInner,
    ← integral_upperRosserAlternatingPairNormalizedKernel_inner hr hy hyr,
    max_eq_right hnonneg]

theorem hasDerivAt_upperRosserAlternatingPairNormalizedInnerRaw
    {r y : ℝ} (hr : 0 < r) (hy : 0 < y) :
    HasDerivAt (upperRosserAlternatingPairNormalizedInnerRaw r)
      ((-r ^ 2 / y ^ 3 - 3 * r / y ^ 2 +
        (1 / (y + r) - 1 / y)) / r ^ 2) y := by
  unfold upperRosserAlternatingPairNormalizedInnerRaw
  have hy2 : 2 * y ^ 2 ≠ 0 := by positivity
  have hratio : (y + r) / (2 * y) ≠ 0 := by positivity
  have hterm1 :=
    (hasDerivAt_const y (r ^ 2)).div
      ((hasDerivAt_const y (2 : ℝ)).mul ((hasDerivAt_id y).pow 2)) hy2
  change HasDerivAt (fun y : ℝ => r ^ 2 / (2 * y ^ 2)) _ y at hterm1
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply] at hterm1
  have hterm1' :
      HasDerivAt (fun y : ℝ => r ^ 2 / (2 * y ^ 2))
        (-r ^ 2 / y ^ 3) y := by
    convert hterm1 using 1
    field_simp [hy.ne']
    ring
  have hterm2 :=
    (hasDerivAt_const y (3 * r)).div (hasDerivAt_id y) hy.ne'
  change HasDerivAt (fun y : ℝ => 3 * r / y) _ y at hterm2
  simp only [id_eq] at hterm2
  have hterm2' :
      HasDerivAt (fun y : ℝ => 3 * r / y) (-3 * r / y ^ 2) y := by
    convert hterm2 using 1
    field_simp [hy.ne']
    ring
  have hlog :=
    ((hasDerivAt_id y).add_const r).div
      (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id y)) (by positivity)
  change HasDerivAt (fun y : ℝ => (y + r) / (2 * y)) _ y at hlog
  simp only [id_eq] at hlog
  have hlog' :
      HasDerivAt (fun y : ℝ => Real.log ((y + r) / (2 * y)))
        (1 / (y + r) - 1 / y) y := by
    convert hlog.log hratio using 1
    field_simp [hy.ne', (by linarith : y + r ≠ 0)]
  convert
    (((hterm1'.add hterm2').sub (hasDerivAt_const y (7 / 2 : ℝ))).add
      hlog').div_const (r ^ 2) using 1
  all_goals first | rfl | ring

theorem abs_upperRosserAlternatingPairNormalizedInnerRaw_deriv_le
    {r y : ℝ} (hr : 3 ≤ r) (hy : 1 ≤ y) :
    |(-r ^ 2 / y ^ 3 - 3 * r / y ^ 2 +
        (1 / (y + r) - 1 / y)) / r ^ 2| ≤ 3 := by
  have hrpos : 0 < r := by linarith
  have hypos : 0 < y := by linarith
  have hy3 : 1 ≤ y ^ 3 := one_le_pow₀ hy
  have hy2 : 1 ≤ y ^ 2 := one_le_pow₀ hy
  have hA : r ^ 2 / y ^ 3 ≤ r ^ 2 := by
    rw [div_le_iff₀ (pow_pos hypos 3)]
    nlinarith [sq_nonneg r]
  have hB : 3 * r / y ^ 2 ≤ r ^ 2 := by
    rw [div_le_iff₀ (pow_pos hypos 2)]
    nlinarith
  have hInv : 1 / (y + r) ≤ 1 / y := by
    exact one_div_le_one_div_of_le hypos (by linarith)
  have hCnonneg : 0 ≤ 1 / y - 1 / (y + r) := by linarith
  have hC : 1 / y - 1 / (y + r) ≤ r ^ 2 := by
    have hyinv : 1 / y ≤ 1 := (div_le_one hypos).2 hy
    have hyrinv : 0 ≤ 1 / (y + r) := by positivity
    have hrsq : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
    nlinarith
  have hnum :
      0 ≤ r ^ 2 / y ^ 3 + 3 * r / y ^ 2 +
        (1 / y - 1 / (y + r)) := by positivity
  have heq :
      (-r ^ 2 / y ^ 3 - 3 * r / y ^ 2 +
          (1 / (y + r) - 1 / y)) / r ^ 2 =
        -(r ^ 2 / y ^ 3 + 3 * r / y ^ 2 +
          (1 / y - 1 / (y + r))) / r ^ 2 := by ring
  rw [heq, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hnum) (sq_nonneg r))]
  simp only [neg_div, neg_neg]
  apply (div_le_iff₀ (sq_pos_of_pos hrpos)).2
  nlinarith

/-- The explicit normalized inner mass is uniformly Lipschitz on every positive
ratio interval, independently of the reverse-chain state. -/
theorem abs_upperRosserAlternatingPairNormalizedInner_sub_le
    {r u v R : ℝ} (hr : 3 ≤ r)
    (hu : u ∈ Set.Icc (1 : ℝ) R) (hv : v ∈ Set.Icc (1 : ℝ) R) :
    |upperRosserAlternatingPairNormalizedInner r u -
        upperRosserAlternatingPairNormalizedInner r v| ≤
      3 * |u - v| := by
  have hraw :
      |upperRosserAlternatingPairNormalizedInnerRaw r u -
          upperRosserAlternatingPairNormalizedInnerRaw r v| ≤
        3 * |u - v| := by
    have hderiv : ∀ x ∈ Set.Icc (1 : ℝ) R,
        HasDerivWithinAt
          (upperRosserAlternatingPairNormalizedInnerRaw r)
          ((-r ^ 2 / x ^ 3 - 3 * r / x ^ 2 +
            (1 / (x + r) - 1 / x)) / r ^ 2)
          (Set.Icc (1 : ℝ) R) x := by
      intro x hx
      exact (hasDerivAt_upperRosserAlternatingPairNormalizedInnerRaw
        (by linarith) (by linarith [hx.1])).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Icc (1 : ℝ) R,
        ‖((-r ^ 2 / x ^ 3 - 3 * r / x ^ 2 +
          (1 / (x + r) - 1 / x)) / r ^ 2)‖ ≤ 3 := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact abs_upperRosserAlternatingPairNormalizedInnerRaw_deriv_le hr hx.1
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Icc (1 : ℝ) R) hv hu
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  unfold upperRosserAlternatingPairNormalizedInner
  simpa [max_comm] using (abs_max_sub_max_le_abs
    (upperRosserAlternatingPairNormalizedInnerRaw r u)
    (upperRosserAlternatingPairNormalizedInnerRaw r v) 0).trans hraw

theorem upperRosserAlternatingPairNormalizedInner_nonneg
    (r y : ℝ) :
    0 ≤ upperRosserAlternatingPairNormalizedInner r y := by
  unfold upperRosserAlternatingPairNormalizedInner
  exact le_max_left _ _

theorem upperRosserAlternatingPairNormalizedInnerRaw_le_two
    {r y : ℝ} (hr : 3 ≤ r) (hy : 1 ≤ y) :
    upperRosserAlternatingPairNormalizedInnerRaw r y ≤ 2 := by
  have hrpos : 0 < r := by linarith
  have hypos : 0 < y := by linarith
  let t : ℝ := r / y
  have ht0 : 0 ≤ t := div_nonneg hrpos.le hypos.le
  have htr : t ≤ r := by
    dsimp [t]
    rw [div_le_iff₀ hypos]
    nlinarith
  have hratioPos : 0 < (y + r) / (2 * y) := by positivity
  have hratioEq : (y + r) / (2 * y) = (1 + t) / 2 := by
    dsimp [t]
    field_simp [hypos.ne']
  have hlog : Real.log ((y + r) / (2 * y)) ≤ t := by
    have h := Real.log_le_sub_one_of_pos hratioPos
    rw [hratioEq] at h
    rw [hratioEq]
    linarith
  have htSq : t ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ht0 htr 2
  have hfour : 4 * t ≤ (3 / 2 : ℝ) * r ^ 2 := by
    have hrr : 4 * r ≤ (3 / 2 : ℝ) * r ^ 2 := by
      nlinarith [sq_nonneg r]
    linarith
  have hnumEq :
      r ^ 2 / (2 * y ^ 2) + 3 * r / y - (7 / 2 : ℝ) +
          Real.log ((y + r) / (2 * y)) =
        t ^ 2 / 2 + 3 * t - (7 / 2 : ℝ) +
          Real.log ((y + r) / (2 * y)) := by
    dsimp [t]
    field_simp [hypos.ne']
  unfold upperRosserAlternatingPairNormalizedInnerRaw
  rw [hnumEq]
  apply (div_le_iff₀ (sq_pos_of_pos hrpos)).2
  nlinarith

theorem upperRosserAlternatingPairNormalizedInner_le_two
    {r y : ℝ} (hr : 3 ≤ r) (hy : 1 ≤ y) :
    upperRosserAlternatingPairNormalizedInner r y ≤ 2 := by
  unfold upperRosserAlternatingPairNormalizedInner
  exact max_le (by norm_num)
    (upperRosserAlternatingPairNormalizedInnerRaw_le_two hr hy)

theorem integrableOn_inv_mul_upperRosserAlternatingPairNormalizedInner
    {r R : ℝ} (hr : 3 ≤ r) (hR : 1 ≤ R) :
    MeasureTheory.IntegrableOn
      (fun y => y⁻¹ * upperRosserAlternatingPairNormalizedInner r y)
      (Set.Ioo 1 R) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hR).1
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hR]
  intro y hy
  have hy0 : y ≠ 0 := by linarith [hy.1]
  have hr0 : r ≠ 0 := by linarith
  have hyr0 : y + r ≠ 0 := by linarith [hy.1]
  have hy20 : 2 * y ^ 2 ≠ 0 := by positivity
  have h2y0 : 2 * y ≠ 0 := by positivity
  have hrsq0 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0
  have hratio0 : (y + r) / (2 * y) ≠ 0 := div_ne_zero hyr0 h2y0
  apply ContinuousAt.continuousWithinAt
  dsimp [upperRosserAlternatingPairNormalizedInner,
    upperRosserAlternatingPairNormalizedInnerRaw]
  fun_prop

theorem integral_inv_mul_upperRosserAlternatingPairNormalizedInner_le
    {r v : ℝ} (hr : 3 ≤ r) (_hv : 1 ≤ v) (hvr : v ≤ r) :
    (∫ y in Set.Ioo 1 v,
      y⁻¹ * upperRosserAlternatingPairNormalizedInner r y) ≤
      (4 / 5 : ℝ) := by
  have hr1 : 1 ≤ r := by linarith
  have hint :=
    integrableOn_inv_mul_upperRosserAlternatingPairNormalizedInner hr hr1
  have hmono :
      (∫ y in Set.Ioo 1 v,
        y⁻¹ * upperRosserAlternatingPairNormalizedInner r y) ≤
        ∫ y in Set.Ioo 1 r,
          y⁻¹ * upperRosserAlternatingPairNormalizedInner r y := by
    apply MeasureTheory.setIntegral_mono_set hint
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with y hy
      exact mul_nonneg (inv_nonneg.mpr (by linarith [hy.1]))
        (upperRosserAlternatingPairNormalizedInner_nonneg r y)
    · filter_upwards with y hy
      exact ⟨hy.1, hy.2.trans_le hvr⟩
  calc
    (∫ y in Set.Ioo 1 v,
      y⁻¹ * upperRosserAlternatingPairNormalizedInner r y) ≤
        ∫ y in Set.Ioo 1 r,
          y⁻¹ * upperRosserAlternatingPairNormalizedInner r y := hmono
    _ = ∫ y in Set.Ioo 1 r, y⁻¹ *
        ∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
          LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro y hy
      change y⁻¹ * upperRosserAlternatingPairNormalizedInner r y =
        y⁻¹ * ∫ x in Set.Ioo y ((y + r) / 2), x⁻¹ *
          LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x
      rw [upperRosserAlternatingPairNormalizedInner_eq_integral
        (by linarith) (by linarith [hy.1]) hy.2.le]
    _ ≤ (4 / 5 : ℝ) :=
      LinearSieve.integral_upperRosserAlternatingPairNormalizedKernel_le hr

theorem integral_upperRosserAlternatingPairNormalizedKernel_Ioo_le_inner
    {r y v : ℝ} (hr : 3 ≤ r) (hy : 1 ≤ y) (hyv : y ≤ v)
    (hv : v ≤ (y + r) / 2) :
    (∫ x in Set.Ioo y v, x⁻¹ *
      LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x) ≤
      upperRosserAlternatingPairNormalizedInner r y := by
  have hrpos : 0 < r := by linarith
  have hypos : 0 < y := by linarith
  have hyu : y ≤ (y + r) / 2 := hyv.trans hv
  let g : ℝ → ℝ := fun x => x⁻¹ *
    LinearSieve.upperRosserAlternatingPairNormalizedKernel r y x
  have hint : MeasureTheory.IntegrableOn g
      (Set.Ioo y ((y + r) / 2)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hyu).1
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hyu]
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hr0 : r ≠ 0 := by linarith
    apply ContinuousAt.continuousWithinAt
    dsimp [g, LinearSieve.upperRosserAlternatingPairNormalizedKernel]
    fun_prop
  have hmono :
      (∫ x in Set.Ioo y v, g x) ≤
        ∫ x in Set.Ioo y ((y + r) / 2), g x := by
    apply MeasureTheory.setIntegral_mono_set hint
    · filter_upwards
        [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (inv_nonneg.mpr (by linarith [hx.1]))
        (LinearSieve.upperRosserAlternatingPairNormalizedKernel_nonneg r y x)
    · filter_upwards with x hx
      exact ⟨hx.1, hx.2.trans_le hv⟩
  change (∫ x in Set.Ioo y v, g x) ≤ _
  rw [upperRosserAlternatingPairNormalizedInner_eq_integral
    hrpos hypos (by linarith)]
  exact hmono

/-- The outer member of a compact reverse Rosser pair admits a second uniform
Stieltjes transfer after the inner prime has been integrated out. -/
theorem exists_upperRosserAlternatingPairDiscrete_outer_le_integral_add
    (K ρ R : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hR : 3 ≤ R) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (r u v : ℝ) (T : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → 1 ≤ u → u ≤ v → v ≤ R →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log q ∈ Set.Icc u v) →
        ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
            upperRosserAlternatingPairNormalizedInner r
              (Real.log p / Real.log q) ≤
          (∫ y in Set.Ioo u v,
            y⁻¹ * upperRosserAlternatingPairNormalizedInner r y) + ρ := by
  obtain ⟨Q, hQ, htransfer⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_logRatio_integral_Ioo_add
      K ρ 2 3 R hK hρ (by norm_num) (by norm_num)
        (lt_of_lt_of_le (by norm_num) hR)
  refine ⟨Q, hQ, ?_⟩
  intro S q r u v T hq hqPrime hlocal hr hu huv hv hT hcoord
  let f : ℝ → ℝ :=
    upperRosserAlternatingPairNormalizedInner r
  have hf : ∀ y ∈ Set.Icc (1 : ℝ) R, 0 ≤ f y := by
    intro y hy
    exact upperRosserAlternatingPairNormalizedInner_nonneg r y
  have hfB : ∀ y ∈ Set.Icc (1 : ℝ) R, f y ≤ 2 := by
    intro y hy
    exact upperRosserAlternatingPairNormalizedInner_le_two hr hy.1
  have hfLip : ∀ y ∈ Set.Icc (1 : ℝ) R,
      ∀ y' ∈ Set.Icc (1 : ℝ) R,
        |f y - f y'| ≤ 3 * |y - y'| := by
    intro y hy y' hy'
    exact abs_upperRosserAlternatingPairNormalizedInner_sub_le hr hy hy'
  simpa [f, mul_comm] using
    htransfer S q T
      (fun p => f (Real.log p / Real.log q)) f u v
      hq hqPrime hlocal hT hu huv hv hcoord hf hfB hfLip
      (integrableOn_inv_mul_upperRosserAlternatingPairNormalizedInner hr
        (le_trans (by norm_num) hR))
      (fun p hp => ⟨hf _ ⟨hu.trans (hcoord p hp).1,
        (hcoord p hp).2.trans hv⟩, le_rfl⟩)

end MathlibNt.SieveTheory.SwitchingPrinciple
