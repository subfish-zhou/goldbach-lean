import Wu18938Campaign.M1.Confirmed.FiniteLowerSeed

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real MeasureTheory
open scoped Classical Interval

def seedProfile (v : ℝ) : ℝ :=
  if v < 3 then classicalProfile v
  else classicalProfile (min v (7 / 2)) + HighSixPhase7.seed / 26

theorem seedProfile_mono : Monotone seedProfile := by
  intro a b hab
  unfold seedProfile
  split_ifs with ha hb hb
  · exact classicalProfile_mono hab
  · have hh : a ≤ min b (7 / 2 : ℝ) := le_min hab (by linarith)
    have hm := classicalProfile_mono hh
    linarith only [hm,HighSixPhase7.seed_pos]
  · exact False.elim (ha (hab.trans_lt hb))
  · exact add_le_add (classicalProfile_mono (min_le_min hab le_rfl)) le_rfl

theorem seedProfile_bounds (v : ℝ) : 0 ≤ seedProfile v ∧ seedProfile v ≤ 3 := by
  unfold seedProfile
  split_ifs
  · have hh := classicalProfile_bounds v
    exact ⟨hh.1,hh.2.trans (by norm_num)⟩
  · have hh := classicalProfile_bounds (min v (7 / 2))
    have hp := HighSixPhase7.seed_pos
    constructor
    · exact add_nonneg hh.1 (div_nonneg hp.le (by norm_num))
    · dsimp [HighSixPhase7.seed]
      linarith only [hh.2]

theorem seedProfile_log {v : ℝ} (hv : 3 ≤ v) (hv7 : v ≤ 7 / 2) :
    seedProfile v = log (v - 1) + HighSixPhase7.seed / 26 := by
  rw [seedProfile,if_neg (not_lt_of_ge hv),min_eq_left hv7,
    classicalProfile_log (by linarith) (by linarith)]

theorem seedProfile_node (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v →
      (seedProfile v - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) v := by
  obtain ⟨T0,hT04,h0⟩ := seed_lower m hη hδ hδhi he
  obtain ⟨T1,_,h1⟩ := classicalProfile_node m hη hδ he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb v hv
  unfold seedProfile
  split_ifs with h3
  · exact h1 N (by omega) heven i Δ V hb v hv
  · have hv3 : 3 ≤ v := le_of_not_gt h3
    have hm3 : (3 : ℝ) ≤ min v (7 / 2) := le_min hv3 (by norm_num)
    have hm4 : min v (7 / 2 : ℝ) ≤ 4 := (min_le_right _ _).trans (by norm_num)
    rw [classicalProfile_eq,min_eq_left hm4]
    apply (h0 N (by omega) heven i Δ V hb (min v (7 / 2)) hm3 (min_le_right _ _)).trans
    unfold wuBoxPhi convolutionSieveCount
    apply sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact gamma5Classical_source_count_antitone N d (d * N)
      (hb.cutoff_antitone (by omega) hη hδ hd (by linarith) (min_le_left _ _))

theorem seedProfile_integral {τ : ℝ} (hτ : 0 ≤ τ) :
    (∫ u in (2 / 3 : ℝ)..(7 / 9), log ((9 / 2) * u - 1) / (u * (1 - u))) +
      HighSixPhase7.seed / 234 - 10 * τ ≤
    ∫ u in (2 / 3 : ℝ)..(7 / 9), (seedProfile ((9 / 2) * u) - τ) / (u * (1 - u)) := by
  have hgeom (u : ℝ) (hu : u ∈ Set.uIcc (2 / 3 : ℝ) (7 / 9)) :
      3 ≤ (9 / 2) * u ∧ (9 / 2) * u ≤ 7 / 2 ∧
      0 < u * (1 - u) ∧ 1 ≤ 1 / (u * (1 - u)) ∧
      1 / (u * (1 - u)) ≤ 10 := by
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hp : 0 < u * (1 - u) := mul_pos (by linarith [hu.1]) (by linarith [hu.2])
    refine ⟨by linarith [hu.1],by linarith [hu.2],hp,?_,?_⟩
    · apply (le_div_iff₀ hp).mpr
      nlinarith only [sq_nonneg (u - 1 / 2)]
    · apply (div_le_iff₀ hp).mpr
      have hh := mul_le_mul (show (2 / 3 : ℝ) ≤ u from hu.1)
        (show (2 / 9 : ℝ) ≤ 1 - u by linarith [hu.2]) (by norm_num) (by linarith [hu.1])
      nlinarith only [hh]
  have hk : IntervalIntegrable (fun u : ℝ => 1 / (u * (1 - u))) volume (2 / 3) (7 / 9) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    intro u hu
    exact (hgeom u hu).2.2.1.ne'
  have hl : IntervalIntegrable
      (fun u : ℝ => log ((9 / 2) * u - 1) / (u * (1 - u))) volume (2 / 3) (7 / 9) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro u hu
      linarith [(hgeom u hu).1]
    · fun_prop
    · intro u hu
      exact (hgeom u hu).2.2.1.ne'
  have hlo := intervalIntegral.integral_mono_on (by norm_num : (2 / 3 : ℝ) ≤ 7 / 9)
    (intervalIntegrable_const (c := (1 : ℝ))) hk (fun u hu =>
      (hgeom u (by rwa [Set.uIcc_of_le (by norm_num)])).2.2.2.1)
  have hhi := intervalIntegral.integral_mono_on (by norm_num : (2 / 3 : ℝ) ≤ 7 / 9)
    hk (intervalIntegrable_const (c := (10 : ℝ))) (fun u hu =>
      (hgeom u (by rwa [Set.uIcc_of_le (by norm_num)])).2.2.2.2)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hlo hhi
  have hid : (∫ u in (2 / 3 : ℝ)..(7 / 9),
      (seedProfile ((9 / 2) * u) - τ) / (u * (1 - u))) =
      (∫ u in (2 / 3 : ℝ)..(7 / 9), log ((9 / 2) * u - 1) / (u * (1 - u))) +
      (HighSixPhase7.seed / 26 - τ) * ∫ u in (2 / 3 : ℝ)..(7 / 9), 1 / (u * (1 - u)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hl (hk.const_mul (HighSixPhase7.seed / 26 - τ))]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [seedProfile_log (hgeom u hu).1 (hgeom u hu).2.1]
    ring
  rw [hid]
  have hp := mul_le_mul_of_nonneg_left hlo
    (show 0 ≤ HighSixPhase7.seed / 26 from div_nonneg HighSixPhase7.seed_pos.le (by norm_num))
  have he := mul_le_mul_of_nonneg_left hhi hτ
  nlinarith only [hp,he,hτ]

theorem seed_omega2 (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ((∫ u in (2 / 3 : ℝ)..(7 / 9), log ((9 / 2) * u - 1) / (u * (1 - u))) +
        HighSixPhase7.seed / 234 - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      wuOmega2Sum N δ 3 (9 / 2) (convolutionWuWindows N Δ V) := by
  let τ := min 1 (ε / 20)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : 10 * τ ≤ ε / 2 := by have := min_le_right 1 (ε / 20); dsimp [τ]; linarith
  obtain ⟨T0,hT04,h0⟩ := node_integral m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := seedProfile_node (m + 1) (show 0 < η / 20 by positivity) hδ hδhi hτ
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hf : MonotoneOn (fun v => seedProfile v - τ) (Set.Icc 1 10) :=
    fun _ _ _ _ hv => sub_le_sub_right (seedProfile_mono hv) _
  have hfb : ∀ v ∈ Set.Icc (1 : ℝ) 10, |seedProfile v - τ| ≤ 11 := by
    intro v _
    obtain ⟨hlo,hhi⟩ := seedProfile_bounds v
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hmain := h0 N (by omega) heven i Δ V hb (fun v => seedProfile v - τ) hf hfb
    (fun k U hU v hv _ => h1 N (by omega) heven k Δ U hU v hv)
    3 (9 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    show (1 : ℝ) - 1 / (9 / 2) = 7 / 9 by norm_num] at hmain
  have hi := seedProfile_integral hτ.le
  have hcoef : (∫ u in (2 / 3 : ℝ)..(7 / 9), log ((9 / 2) * u - 1) / (u * (1 - u))) +
      HighSixPhase7.seed / 234 - ε ≤
      (∫ u in (2 / 3 : ℝ)..(7 / 9), (seedProfile ((9 / 2) * u) - τ) / (u * (1 - u))) - ε / 2 := by
    linarith only [hi,hτε]
  exact (mul_le_mul_of_nonneg_right hcoef (theta_nonneg hb (by omega) hη hδ)).trans hmain

end Wu18938Campaign.M1.Confirmed.Rebox
