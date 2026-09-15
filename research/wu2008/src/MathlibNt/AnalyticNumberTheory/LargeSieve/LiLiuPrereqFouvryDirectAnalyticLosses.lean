import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticPartialSummation
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFrequencyCount

/-! Actual five-coordinate counting and slow-variation costs. -/
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem direct_variation_le {Z : ℝ} (hZ : 1 ≤ Z) :
    wAnalyticVariationConstant Z ≤
      (2048 * (6 + 2 * Real.pi)^5 * 113^5) * Z^5 := by
  unfold wAnalyticVariationConstant
  calc
    _ ≤ 2048 * (6 + 2 * Real.pi)^5 * (113*Z)^5 := by gcongr; linarith
    _ = _ := by ring

theorem direct_coordinate_bound {x L M η : ℝ}
    (hx : 2 ≤ x) (hL0 : 0 ≤ L) (hL : L ≤ x) (hM : 1 ≤ M)
    (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (N : Finset ℕ) (hN : ∀ n ∈ N, (n : ℝ) ≤ x)
    (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    wAnalyticCoordinateBound (wFloorCutoff M (x^η)) N (Ioc 0 ⌊L⌋₊) a P R S ξ ≤
      ⌈x^(4 : ℝ)⌉₊ := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  have hZ : 0 ≤ x^η := Real.rpow_nonneg hx0.le η
  have hZx : x^η ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hη1
  have hxx : x ≤ x^(4 : ℝ) := by
    calc
      x = x^(1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hb : L^2/M*x^η ≤ x^(4 : ℝ) := by
    calc
      _ ≤ L^2*x^η := mul_le_mul_of_nonneg_right
        ((div_le_iff₀ hM0).mpr (le_mul_of_one_le_right (sq_nonneg L) hM)) hZ
      _ ≤ x^2*x := by gcongr
      _ = x^(3 : ℝ) := by rw [Real.rpow_ofNat]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hf := wExtractedMaxFrequency_le_of_cutoff_le hM0 hZ hL0
    (wFloorCutoff M (x^η)) (fun q _ r _ => wFloorCutoff_le_uniformCutoff M (x^η) q r)
    N a P R S ξ
  unfold wAnalyticCoordinateBound
  apply max_le (hf.trans (Nat.ceil_mono hb))
  apply max_le
  · apply Finset.sup_le
    intro q hq
    exact_mod_cast (((Nat.cast_le.mpr (mem_Ioc.mp hq).2).trans (Nat.floor_le hL0)).trans
      (hL.trans hxx)).trans (Nat.le_ceil (x^(4 : ℝ)))
  · apply Finset.sup_le
    intro n hn
    exact_mod_cast ((hN n hn).trans hxx).trans (Nat.le_ceil (x^(4 : ℝ)))

theorem direct_dyadic_card_le {x L M η : ℝ}
    (hx : 2 ≤ x) (hL0 : 0 ≤ L) (hL : L ≤ x) (hM : 1 ≤ M)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) (hNX : ∀ n ∈ N, (n : ℝ) ≤ x)
    (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) :
    (((wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊L⌋₊) a P R S ξ b K).image
      wAnalyticDyadicKey).card : ℝ) ≤ (2 + 4*Real.log x/Real.log 2)^5 := by
  have hQ : ∀ q ∈ Ioc 0 ⌊L⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hc := wExtractedKeyFiber_dyadic_card_le (H := wFloorCutoff M (x^η)) hN hQ a P R S ξ b K
  have hb := direct_coordinate_bound hx hL0 hL hM hη hη1 N hNX a P R S ξ
  have hn := Nat.add_le_add_right (Nat.log_mono_right (b := 2) hb) 1
  have hpow := Nat.pow_le_pow_left hn 5
  have hr : (((wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊L⌋₊)
      a P R S ξ b K).image wAnalyticDyadicKey).card : ℝ) ≤
      ((Nat.log 2 ⌈x^(4 : ℝ)⌉₊ + 1 : ℕ) : ℝ)^5 := by exact_mod_cast hc.trans hpow
  exact hr.trans (pow_le_pow_left₀ (by positivity)
    (log_two_ceil_rpow_bound (by linarith) (by norm_num : (0 : ℝ) ≤ 4)) 5)

theorem direct_log_cost_subpower (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      (2 + 4*Real.log x/Real.log 2)^p ≤ C*x^δ := by
  obtain ⟨B, hB, hb⟩ := betaClean_log_pow_le_const_rpow p hδ
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(6/Real.log 2)^p*B, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  have hlog2 : Real.log x ≤ Real.log (2*x) :=
    Real.log_le_log hx0 (by linarith)
  have hbase : 2 + 4*Real.log x/Real.log 2 ≤ (6/Real.log 2)*Real.log (2*x) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ht).2
    have he : (4*Real.log x/Real.log 2)*Real.log 2 = 4*Real.log x :=
      div_mul_cancel₀ _ ht.ne'
    nlinarith
  calc
    _ ≤ ((6/Real.log 2)*Real.log (2*x))^p :=
      pow_le_pow_left₀ (by positivity [Real.log_nonneg hx1]) hbase p
    _ = (6/Real.log 2)^p * Real.log (2*x)^p := mul_pow _ _ _
    _ ≤ (6/Real.log 2)^p * (B*x^δ) := mul_le_mul_of_nonneg_left (hb x hx1) (by positivity)
    _ = _ := by ring

/-- The actual shell count, five dyadic coordinates, key loss and variation
are paid together, uniformly before the finite carrier and all scales. -/
theorem direct_analytic_prefactor_subpower {η δ : ℝ}
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x L M : ℝ), 2 ≤ x → 0 ≤ L → L ≤ x → 1 ≤ M →
      ∀ (N : Finset ℕ), (∀ n ∈ N, 0 < n) → (∀ n ∈ N, (n : ℝ) ≤ x) →
      ∀ (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey),
      (Nat.log 2 ⌈L^2/M*x^η⌉₊ + 1 : ℕ) * (x^η)^7 * wAnalyticVariationConstant (x^η) *
        (((wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊L⌋₊)
          a P R S ξ b K).image wAnalyticDyadicKey).card : ℝ) ≤ C*x^(12*η+δ) := by
  obtain ⟨B, hB, hb⟩ := direct_log_cost_subpower 6 hδ
  let V : ℝ := 2048 * (6 + 2 * Real.pi)^5 * 113^5
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨V*B, mul_pos hV hB, ?_⟩
  intro x L M hx hL0 hL hM N hN hNX a P R S ξ b K
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hZ : 1 ≤ x^η := Real.one_le_rpow hx1 hη
  have hv := direct_variation_le hZ
  have hv0 := wAnalyticVariationConstant_nonneg (show 0 ≤ x^η by positivity)
  have hc := direct_dyadic_card_le hx hL0 hL hM hη hη1 N hN hNX a P R S ξ b K
  have hj : ((Nat.log 2 ⌈L^2/M*x^η⌉₊ + 1 : ℕ) : ℝ) ≤
      2+4*Real.log x/Real.log 2 := by
    apply (fullLevel_frequency_count_bound hx1 hL0 hL hM hη).trans
    gcongr
    linarith
  have hp : (x^η)^12 = x^(12*η) := by
    rw [← Real.rpow_mul_natCast hx0.le]
    congr 1
    ring
  calc
    _ ≤ (2+4*Real.log x/Real.log 2)*(x^η)^7 * (V*(x^η)^5) *
        (2+4*Real.log x/Real.log 2)^5 := by gcongr
    _ = V*(x^η)^12*(2+4*Real.log x/Real.log 2)^6 := by ring
    _ ≤ V*(x^η)^12*(B*x^δ) := mul_le_mul_of_nonneg_left (hb x hx) (by positivity)
    _ = (V*B)*x^(12*η+δ) := by rw [hp, Real.rpow_add hx0]; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
