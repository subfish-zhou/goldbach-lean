import Wu18938Campaign.M1.Confirmed.ReverseIntegral
import Wu18938Campaign.M1.Confirmed.BuchstabTransfer

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Real MeasureTheory
open scoped Classical Interval

def profileIntegral (f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ v in (s - 1)..(t - 1), f v / v

theorem profileIntegral_shift {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 1 10))
    {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (ρ : ℝ) :
    profileIntegral (fun v => f v + ρ) s t =
      profileIntegral f s t + ρ * ∫ v in (s - 1)..(t - 1), 1 / v := by
  have hab : s - 1 ≤ t - 1 := by linarith
  have hsub : Set.uIcc (s - 1) (t - 1) ⊆ Set.Icc (1 : ℝ) 10 := by
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  have hcont : ContinuousOn (fun v : ℝ => v⁻¹) (Set.uIcc (s - 1) (t - 1)) :=
    continuousOn_id.inv₀ (fun _ hv => ne_of_gt (lt_of_lt_of_le (by norm_num) (hsub hv).1))
  have hi : IntervalIntegrable (fun v => f v / v) volume (s - 1) (t - 1) := by
    simpa only [div_eq_mul_inv] using (hf.mono hsub).intervalIntegrable.mul_continuousOn hcont
  have hk : IntervalIntegrable (fun v : ℝ => 1 / v) volume (s - 1) (t - 1) := by
    simpa only [one_div] using hcont.intervalIntegrable
  unfold profileIntegral
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add hi (hk.const_mul ρ)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  ring

theorem reciprocal_interval_bound {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    0 ≤ (∫ v : ℝ in (s - 1)..(t - 1), 1 / v) ∧
      (∫ v : ℝ in (s - 1)..(t - 1), 1 / v) ≤ 10 := by
  have hab : s - 1 ≤ t - 1 := by linarith
  have hk : IntervalIntegrable (fun v : ℝ => 1 / v) volume (s - 1) (t - 1) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro v hv
    rw [Set.uIcc_of_le hab] at hv
    change v ≠ 0
    linarith [hv.1]
  refine ⟨intervalIntegral.integral_nonneg hab (fun v hv => by
    apply one_div_nonneg.mpr
    linarith [hv.1]),?_⟩
  have hh := intervalIntegral.integral_mono_on hab hk
    (intervalIntegrable_const (c := (1 : ℝ))) (fun v hv => by
      apply (div_le_one (by linarith [hv.1] : 0 < v)).mpr
      linarith [hv.1])
  rw [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hh
  linarith

theorem upper_buchstab_actual (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc 1 10))
    (hfb : ∀ v ∈ Set.Icc (1 : ℝ) 10, 0 ≤ f v ∧ f v ≤ 10)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε)
    (hn : ∀ ρ : ℝ, 0 < ρ → ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox (m + 1) (η / 20) δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
      (f v - ρ) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) v) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) t -
          (profileIntegral f s t - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let ρ := min 1 (ε / 20)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : 10 * ρ ≤ ε / 2 := by have hh := min_le_right 1 (ε / 20); change ρ ≤ ε / 20 at hh; linarith
  obtain ⟨T0,hT04,h0⟩ := lower_node_integral m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := hn ρ hρ
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht ht5
  have hf' : MonotoneOn (fun v => f v - ρ) (Set.Icc 1 10) :=
    fun _ ha _ hb hab => sub_le_sub_right (hf ha hb hab) ρ
  have hfb' (v : ℝ) (hv : v ∈ Set.Icc (1 : ℝ) 10) : |f v - ρ| ≤ 11 := by
    rw [abs_le]
    have hh := hfb v hv
    constructor <;> linarith
  have hc := h0 N (by omega) heven i Δ V hb (fun v => f v - ρ) hf' hfb'
    (fun k U hu v hv hv10 => h1 N (by omega) heven k Δ U hu v hv hv10) s t hs hst ht ht5
  have hI : profileIntegral (fun v => f v - ρ) s t =
      profileIntegral f s t - ρ * ∫ v in (s - 1)..(t - 1), 1 / v := by
    simpa only [sub_eq_add_neg,neg_mul] using profileIntegral_shift hf hs hst (by linarith) (-ρ)
  change (profileIntegral (fun v => f v - ρ) s t - ε / 2) * _ ≤ _ at hc
  rw [hI] at hc
  have herr := mul_le_mul_of_nonneg_left (reciprocal_interval_bound hs hst (by linarith)).2 hρ.le
  have hpay := mul_le_mul_of_nonneg_right
    (show profileIntegral f s t - ε ≤
      profileIntegral f s t - ρ * (∫ v in (s - 1)..(t - 1), 1 / v) - ε / 2 by linarith)
    (theta_nonneg hb (by omega) hη hδ)
  have hid := wuBoxPhi_buchstab (convolutionWuWindows N Δ V)
    (fun d hd => (hb.support_geometry (by omega) hη hδ hd).2.2.1.le)
    (by linarith : 0 < s) hst
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) t =
    wuBoxPhi N δ (convolutionWuWindows N Δ V) s +
      reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) at hid
  linarith only [hc,hpay,hid]

theorem lower_buchstab_actual (u : ℝ → ℝ) (vmax : ℝ)
    (hu : MonotoneOn u (Set.Icc 1 10))
    (hub : ∀ v ∈ Set.Icc (1 : ℝ) 10, 0 ≤ u v ∧ u v ≤ 10)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε)
    (hn : ∀ ρ : ℝ, 0 < ρ → ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox (m + 1) (η / 20) δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ vmax →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) v ≤
        (u v + ρ) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → t - 1 ≤ vmax →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) t -
        (profileIntegral u s t + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  let ρ := min 1 (ε / 20)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : 10 * ρ ≤ ε / 2 := by have hh := min_le_right 1 (ε / 20); change ρ ≤ ε / 20 at hh; linarith
  obtain ⟨T0,hT04,h0⟩ := lower_node_update m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := hn ρ hρ
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht htv
  have hu' : MonotoneOn (fun v => u v + ρ) (Set.Icc 1 10) :=
    fun _ ha _ hb hab => by dsimp only; linarith [hu ha hb hab]
  have hub' (v : ℝ) (hv : v ∈ Set.Icc (1 : ℝ) 10) :
      0 ≤ u v + ρ ∧ u v + ρ ≤ 11 := by
    have hh := hub v hv
    constructor <;> linarith
  have hc := h0 N (by omega) heven i Δ V hb (fun v => u v + ρ) vmax hu' hub'
    (fun k U hu v hv hvmax => h1 N (by omega) heven k Δ U hu v hv hvmax)
    s t hs hst ht htv
  change _ - (profileIntegral (fun v => u v + ρ) s t + ε / 2) * _ ≤ _ at hc
  rw [profileIntegral_shift hu hs hst ht] at hc
  have herr := mul_le_mul_of_nonneg_left (reciprocal_interval_bound hs hst ht).2 hρ.le
  have hpay := mul_le_mul_of_nonneg_right
    (show profileIntegral u s t + ρ * (∫ v in (s - 1)..(t - 1), 1 / v) + ε / 2 ≤
      profileIntegral u s t + ε by linarith)
    (theta_nonneg hb (by omega) hη hδ)
  linarith only [hc,hpay]

end Wu18938Campaign.M1.Confirmed.Rebox
