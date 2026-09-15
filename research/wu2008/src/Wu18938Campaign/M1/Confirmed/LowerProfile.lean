import Wu18938Campaign.M1.Confirmed.Omega2Transfer
import MathlibNt.Wu2008DoubleSieve.Omega2CanonicalIntegral

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Interval

def classicalProfile (v : ℝ) : ℝ := log (max 1 (min v 4 - 1))

theorem classicalProfile_mono : Monotone classicalProfile := by
  intro a b hab
  exact log_le_log (zero_lt_one.trans_le (le_max_left _ _))
    (max_le_max le_rfl (sub_le_sub_right (min_le_min hab le_rfl) 1))

theorem classicalProfile_bounds (v : ℝ) : 0 ≤ classicalProfile v ∧ classicalProfile v ≤ 2 := by
  have hx : max 1 (min v 4 - 1) ≤ (3 : ℝ) :=
    max_le (by norm_num) (by linarith [min_le_right v 4])
  exact ⟨log_nonneg (le_max_left _ _),
    (log_le_sub_one_of_pos (zero_lt_one.trans_le (le_max_left _ _))).trans (by linarith)⟩

theorem classicalProfile_eq (v : ℝ) :
    classicalProfile v = wuLowerCoefficient (min v 4) := by
  by_cases hv2 : min v 4 ≤ 2
  · rw [classicalProfile,max_eq_left (by linarith)]
    simp only [log_one,wuLowerCoefficient,jr1965f_initial hv2,mul_zero,zero_div]
  · have hm : 2 ≤ min v 4 := (lt_of_not_ge hv2).le
    rw [classicalProfile,max_eq_right (by linarith)]
    exact (jr1965f_normalized_firstInterval hm (min_le_right _ _)).symm

theorem classicalProfile_log {v : ℝ} (hv : 2 ≤ v) (hv4 : v ≤ 4) :
    classicalProfile v = log (v - 1) := by
  rw [classicalProfile,min_eq_left hv4,max_eq_right (by linarith)]

theorem classicalProfile_node (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v →
      (classicalProfile v - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) v := by
  obtain ⟨T,hT4,hT⟩ := roughBox_lower_leaf m hη hδ he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb v hv
  rw [classicalProfile_eq]
  apply (hT N hN heven i Δ V hb (min v 4) (le_min hv (by norm_num)) (min_le_right _ _)).trans
  unfold wuBoxPhi convolutionSieveCount
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact gamma5Classical_source_count_antitone N d (d * N)
    (hb.cutoff_antitone (by omega) hη hδ hd (lt_min (by linarith) (by norm_num)) (min_le_left _ _))

theorem omega2_kernel_geometry {s t u : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) (ht5 : t ≤ 5)
    (hu : u ∈ Set.uIcc (1 - 1 / s) (1 - 1 / t)) :
    (1 / 2 : ℝ) ≤ u ∧ u ≤ 4 / 5 ∧ 0 < u * (1 - u) ∧
      1 / (u * (1 - u)) ≤ 10 := by
  have hab := sub_le_sub_left (one_div_le_one_div_of_le (by linarith : 0 < s) hst) 1
  rw [Set.uIcc_of_le hab] at hu
  have hsbound := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs
  have htbound := one_div_le_one_div_of_le (by linarith : 0 < t) ht5
  have hlu : (1 / 2 : ℝ) ≤ u := by linarith [hu.1]
  have hhu : u ≤ (4 / 5 : ℝ) := by linarith [hu.2]
  have hprod := mul_le_mul hlu (show (1 / 5 : ℝ) ≤ 1 - u by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 5) (by linarith : 0 ≤ u)
  have hp : 0 < u * (1 - u) := by nlinarith
  exact ⟨hlu,hhu,hp,(div_le_iff₀ hp).mpr (by nlinarith)⟩

theorem classicalProfile_integral_error {s t τ : ℝ} (hs : 2 ≤ s) (hst : s ≤ t)
    (ht5 : t ≤ 5) (hratio : 2 ≤ t - t / s) (hτ : 0 ≤ τ) :
    (∫ u in (1 - 1 / s)..(1 - 1 / t), log (t * u - 1) / (u * (1 - u))) -
      10 * τ ≤
    ∫ u in (1 - 1 / s)..(1 - 1 / t), (classicalProfile (t * u) - τ) / (u * (1 - u)) := by
  let a := 1 - 1 / s
  let b := 1 - 1 / t
  have hab : a ≤ b := sub_le_sub_left (one_div_le_one_div_of_le (by linarith : 0 < s) hst) 1
  have hlog : IntervalIntegrable (fun u => log (t * u - 1) / (u * (1 - u))) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro u hu
      have hh := omega2_canonical_parameter_mem hs hst ht5 hratio hu
      linarith [hh.1]
    · fun_prop
    · intro u hu
      exact (omega2_kernel_geometry hs hst ht5 hu).2.2.1.ne'
  have hk : IntervalIntegrable (fun u : ℝ => 1 / (u * (1 - u))) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu
    exact (omega2_kernel_geometry hs hst ht5 hu).2.2.1.ne'
  have hK : (∫ u in a..b, 1 / (u * (1 - u))) ≤ 10 := by
    have hle := intervalIntegral.integral_mono_on hab hk intervalIntegrable_const
      (fun u hu => (omega2_kernel_geometry hs hst ht5 (by rwa [Set.uIcc_of_le hab])).2.2.2)
    rw [intervalIntegral.integral_const,smul_eq_mul] at hle
    have ha := (omega2_kernel_geometry hs hst ht5 (show a ∈ Set.uIcc a b by simp)).1
    have hb := (omega2_kernel_geometry hs hst ht5 (show b ∈ Set.uIcc a b by simp)).2.1
    nlinarith
  have hid : (∫ u in a..b, (classicalProfile (t * u) - τ) / (u * (1 - u))) =
      (∫ u in a..b, log (t * u - 1) / (u * (1 - u))) -
        τ * ∫ u in a..b, 1 / (u * (1 - u)) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hlog (hk.const_mul τ)]
    apply intervalIntegral.integral_congr
    intro u hu
    have hh := omega2_canonical_parameter_mem hs hst ht5 hratio hu
    dsimp only
    rw [classicalProfile_log hh.1 hh.2]
    ring
  rw [hid]
  have hh := mul_le_mul_of_nonneg_left hK hτ
  linarith

theorem classical_omega2 (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t - t / s →
      ((∫ u in (1 - 1 / s)..(1 - 1 / t), log (t * u - 1) / (u * (1 - u))) - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  let τ := min 1 (ε / 20)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 20 := min_le_right _ _
  obtain ⟨T0,hT04,h0⟩ := classicalProfile_node (m + 1) (show 0 < η / 20 by positivity) hδ hτ
  obtain ⟨T1,_,h1⟩ := node_integral m hη hδ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht ht5 hratio
  have ha := h1 N (by omega) heven i Δ V hb (fun v => classicalProfile v - τ)
    (fun a _ b _ hab => sub_le_sub_right (classicalProfile_mono hab) τ) (by
      intro v _
      rw [abs_le]
      have h := classicalProfile_bounds v
      constructor <;> linarith)
    (fun k U hU v hv _ => h0 N (by omega) heven k Δ U hU v hv) s t hs hst ht ht5
  have hi := classicalProfile_integral_error hs hst ht5 hratio hτ.le
  have hp := mul_le_mul_of_nonneg_right
    (show (∫ u in (1 - 1 / s)..(1 - 1 / t), log (t * u - 1) / (u * (1 - u))) - ε ≤
      (∫ u in (1 - 1 / s)..(1 - 1 / t), (classicalProfile (t * u) - τ) / (u * (1 - u))) -
        ε / 2 by linarith only [hi,hτε])
    (theta_nonneg hb (by omega) hη hδ)
  exact hp.trans ha

end Wu18938Campaign.M1.Confirmed.Rebox
