import Wu18938Campaign.M1.Confirmed.OriginalProfileIteration

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension
open scoped Classical Interval

def combinedUpper (H : ℝ → ℝ) (v : ℝ) : ℝ :=
  if v ≤ 3 then min (upperInput H v) (upperExtension H (aProfile H) 3)
  else upperExtension H (aProfile H) v

theorem combinedUpper_bounds {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16) (v : ℝ) :
    0 ≤ combinedUpper H v ∧ combinedUpper H v ≤ 10 := by
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  have ha := aProfile_bounds hH hb
  unfold combinedUpper
  split_ifs
  · exact ⟨le_min (upperInput_bounds hb1 v).1 (upperExtension_bounds hH hb ha.1 ha.2 3).1,
      (min_le_left _ _).trans ((upperInput_bounds hb1 v).2.trans (by norm_num))⟩
  · exact upperExtension_bounds hH hb ha.1 ha.2 v

theorem combinedUpper_mono {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16) :
    Monotone (combinedUpper H) := by
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  have hu := upperExtension_mono hH hb1 (aProfile_bounds hH hb).1
  intro a b hab
  by_cases hb3 : b ≤ 3
  · simp only [combinedUpper,if_pos hb3,if_pos (hab.trans hb3)]
    exact min_le_min (upperInput_mono hH hab) le_rfl
  · by_cases ha3 : a ≤ 3
    · simp only [combinedUpper,if_neg hb3,if_pos ha3]
      exact (min_le_right _ _).trans (hu (le_of_not_ge hb3))
    · simp only [combinedUpper,if_neg hb3,if_neg ha3]
      exact hu hab

theorem combinedUpper_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hHnode : UpperNodes δ (fun v => 1 - H v) 3) :
    UpperNodes δ (combinedUpper H) 5 := by
  have hu := (full_extensions_actual hH hb hδ hHnode).2
  intro m η ε hη he
  obtain ⟨T0,hT04,h0⟩ := hHnode m η ε hη he
  obtain ⟨T1,_,h1⟩ := hu m η ε hη he
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hbox v hv hv5
  unfold combinedUpper
  split_ifs with hv3
  · rcases le_total (upperInput H v) (upperExtension H (aProfile H) 3) with hh | hh
    · rw [min_eq_left hh,upperInput,min_eq_left hv3,max_eq_right hv]
      exact h0 N (by omega) heven i Δ V hbox v hv hv3
    · rw [min_eq_right hh]
      exact (phi_mono hbox (by omega) hη hδ (by linarith) hv3).trans
        (h1 N (by omega) heven i Δ V hbox 3 (by norm_num) (by norm_num))
  · exact h1 N (by omega) heven i Δ V hbox v hv hv5

def fullLower (H : ℝ → ℝ) (s : ℝ) : ℝ :=
  wuLowerCoefficient 6 - profileIntegral (combinedUpper H) s 6

def fullLowerGain (H : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ v in (s - 1)..5, (wuUpperCoefficient v - combinedUpper H v) / v

theorem fullLower_eq {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {s : ℝ} (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    fullLower H s = wuLowerCoefficient s + fullLowerGain H s := by
  have ha := wuUpperCoefficient_div_intervalIntegrable (by linarith : 0 < s - 1)
    (by linarith : s - 1 ≤ 5)
  have hu : IntervalIntegrable (fun v => combinedUpper H v / v) volume (s - 1) 5 := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using
      ((combinedUpper_mono hH hb).intervalIntegrable (μ := volume)).mul_continuousOn
        (reciprocal_continuous (by linarith : 0 < s - 1) (by linarith : s - 1 ≤ 5))
  have heq : fullLowerGain H s =
      (∫ v in (s - 1)..5, wuUpperCoefficient v / v) -
        (∫ v in (s - 1)..5, combinedUpper H v / v) := by
    unfold fullLowerGain
    simp_rw [sub_div]
    exact intervalIntegral.integral_sub ha hu
  have hc := wuLowerCoefficient_sub_eq_integral hs hs6
  norm_num only [show (6 : ℝ) - 1 = 5 by norm_num] at hc
  rw [heq]
  unfold fullLower profileIntegral
  norm_num only [show (6 : ℝ) - 1 = 5 by norm_num]
  linarith

theorem fullLower_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hHnode : UpperNodes δ (fun v => 1 - H v) 3)
    (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 6 →
      (wuLowerCoefficient s + fullLowerGain H s - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  have hu := combinedUpper_actual hH hb hδ hHnode
  obtain ⟨T0,hT04,h0⟩ := lower_buchstab_actual (combinedUpper H) 5
    ((combinedUpper_mono hH hb).monotoneOn _) (fun v _ => combinedUpper_bounds hH hb v)
    m hη hδ (half_pos he) (fun ρ hρ => hu (m + 1) (η / 20) ρ (by positivity) hρ)
  obtain ⟨T1,_,h1⟩ := roughBox_lower_leaf_bounded m hη hδ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hbox s hs hs6
  have hbase := h1 N (by omega) heven i Δ V hbox 6 (by norm_num) (by norm_num)
  have htrans := h0 N (by omega) heven i Δ V hbox s 6 hs hs6 (by norm_num) (by norm_num)
  rw [← fullLower_eq hH hb hs hs6]
  unfold fullLower
  nlinarith only [hbase,htrans]

theorem originalProfile_twentyone {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (n : ℕ) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Fin 21,
      (wuLowerCoefficient (rNode (j.val + 1)) +
          fullLowerGain (originalProfile δ n) (rNode (j.val + 1)) - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ V) (rNode (j.val + 1)) := by
  obtain ⟨T,hT4,hT⟩ := fullLower_actual (originalProfile_antitone δ n)
    (fun v _ => originalProfile_bounds δ n v) hδ (originalProfile_actual hδ hδhi n) m hη he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hbox j
  apply hT N hN heven i Δ V hbox
  · dsimp [rNode]; have hh := Nat.cast_nonneg (α := ℝ) (j.val + 1); linarith
  · exact (rNode_bounds (by omega : j.val + 1 ≤ 29)).2.trans (by norm_num)

end Wu18938Campaign.M1.Confirmed.FiniteProfile
