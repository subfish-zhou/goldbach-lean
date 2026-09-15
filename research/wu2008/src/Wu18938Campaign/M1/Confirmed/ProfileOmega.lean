import Wu18938Campaign.M1.Confirmed.LowerProfile
import MathlibNt.Wu2008DoubleSieve.Omega2EffectiveIntegral

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Real MeasureTheory
open scoped Classical Interval

def profileJ (f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))

theorem profileJ_error {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 1 10))
    {s t ρ : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hρ : 0 ≤ ρ) :
    profileJ f s t - 10 * ρ ≤ profileJ (fun v => f v - ρ) s t := by
  have hab := sub_le_sub_left (one_div_le_one_div_of_le (by linarith : 0 < s) hst) 1
  have hi := omega2_integral_intervalIntegrable hf hs hst ht ht5
  have hk : IntervalIntegrable (fun u : ℝ => 1 / (u * (1 - u))) volume
      (1 - 1 / s) (1 - 1 / t) := by
    exact omega2_integral_intervalIntegrable (f := fun _ => (1 : ℝ))
      (fun _ _ _ _ _ => le_rfl) hs hst ht ht5
  have hK : (∫ u in (1 - 1 / s)..(1 - 1 / t), 1 / (u * (1 - u))) ≤ 10 := by
    have hle := intervalIntegral.integral_mono_on hab hk intervalIntegrable_const
      (fun u hu => (omega2_kernel_geometry hs hst ht5 (by rwa [Set.uIcc_of_le hab])).2.2.2)
    rw [intervalIntegral.integral_const,smul_eq_mul] at hle
    have ha := (omega2_kernel_geometry hs hst ht5
      (show 1 - 1 / s ∈ Set.uIcc (1 - 1 / s) (1 - 1 / t) by simp)).1
    have hb := (omega2_kernel_geometry hs hst ht5
      (show 1 - 1 / t ∈ Set.uIcc (1 - 1 / s) (1 - 1 / t) by simp)).2.1
    nlinarith
  have hid : profileJ (fun v => f v - ρ) s t =
      profileJ f s t - ρ * ∫ u in (1 - 1 / s)..(1 - 1 / t), 1 / (u * (1 - u)) := by
    unfold profileJ
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hi (hk.const_mul ρ)]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  rw [hid]
  have hh := mul_le_mul_of_nonneg_left hK hρ
  linarith

theorem profile_omega2_actual (f : ℝ → ℝ)
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
      (profileJ f s t - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  let ρ := min 1 (ε / 20)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : 10 * ρ ≤ ε / 2 := by
    have hh := min_le_right 1 (ε / 20)
    change ρ ≤ ε / 20 at hh
    linarith
  obtain ⟨T0,hT04,h0⟩ := node_integral m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := hn ρ hρ
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht ht5
  have hf' : MonotoneOn (fun v => f v - ρ) (Set.Icc 1 10) :=
    fun a ha b hb hab => sub_le_sub_right (hf ha hb hab) ρ
  have hfb' (v : ℝ) (hv : v ∈ Set.Icc (1 : ℝ) 10) : |f v - ρ| ≤ 11 := by
    rw [abs_le]
    have hh := hfb v hv
    constructor <;> linarith
  have hc := h0 N (by omega) heven i Δ V hb (fun v => f v - ρ) hf' hfb'
    (fun k U hu v hv hv10 => h1 N (by omega) heven k Δ U hu v hv hv10)
    s t hs hst ht ht5
  apply le_trans _ hc
  apply mul_le_mul_of_nonneg_right _ (theta_nonneg hb (by omega) hη hδ)
  have hh := profileJ_error hf hs hst ht ht5 hρ.le
  change profileJ f s t - ε ≤ profileJ (fun v => f v - ρ) s t - ε / 2
  linarith

end Wu18938Campaign.M1.Confirmed.Rebox
