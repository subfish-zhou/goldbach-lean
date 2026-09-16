import Wu18938Campaign.M1.Confirmed.ProfileCycleCoefficients

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension Finset
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Interval

def UpperNodes (δ : ℝ) (u : ℝ → ℝ) (vmax : ℝ) : Prop :=
  ∀ (m : ℕ) (η ε : ℝ), 0 < η → 0 < ε →
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ vmax →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) v ≤
        (u v + ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)

def LowerNodes (δ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (m : ℕ) (η ε : ℝ), 0 < η → 0 < ε →
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
      (f v - ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) v

def FourNode (δ c : ℝ) : Prop :=
  ∀ (m : ℕ) (η ε : ℝ), 0 < η → 0 < ε →
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (log 3 + c - ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) 4

theorem fourNode_zero {δ : ℝ} (hδ : 0 < δ) : FourNode δ 0 := by
  intro m η ε hη he
  obtain ⟨T,hT4,hT⟩ := roughBox_lower_leaf_bounded m hη hδ he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb
  have hh := hT N hN heven i Δ V hb 4 (by norm_num) (by norm_num)
  have heq : wuLowerCoefficient 4 = log 3 := by
    change 4 * jr1965f 4 / (2 * exp eulerMascheroniConstant) = log 3
    convert jr1965f_normalized_firstInterval (s := 4) (by norm_num) le_rfl using 1
    norm_num
  simpa only [heq,add_zero] using hh

theorem phi_mono {m N i : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 0 < s) (hst : s ≤ t) :
    wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
      wuBoxPhi N δ (convolutionWuWindows N Δ V) t := by
  unfold wuBoxPhi convolutionSieveCount
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (gamma5Classical_source_count_antitone N d (d * N)
    (hb.cutoff_antitone (by omega) hη hδ hd hs hst)) (Nat.cast_nonneg _)

theorem lower_extension_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {δ c : ℝ} (hδ : 0 < δ)
    (hHnode : UpperNodes δ (fun v => 1 - H v) 3) (hcnode : FourNode δ c) :
    LowerNodes δ (lowerExtension H c) := by
  intro m η ε hη he
  obtain ⟨T0,hT04,h0⟩ := lower_buchstab_actual (upperInput H) 3
    ((upperInput_mono hH).monotoneOn _)
    (fun v _ => ⟨(upperInput_bounds hb v).1,(upperInput_bounds hb v).2.trans (by norm_num)⟩)
    m hη hδ (half_pos he) (by
      intro ρ hρ
      obtain ⟨T,hT4,hT⟩ := hHnode (m + 1) (η / 20) ρ (by positivity) hρ
      refine ⟨T,hT4,?_⟩
      intro N hN heven i Δ V hbox v hv hv3
      simpa only [upperInput,min_eq_left hv3,max_eq_right hv] using hT N hN heven i Δ V hbox v hv hv3)
  obtain ⟨T1,_,h1⟩ := hcnode m η (ε / 2) hη (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hbox v hv _hv10
  by_cases hv2 : v < 2
  · rw [lowerExtension,if_pos hv2,zero_sub]
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (theta_nonneg hbox (by omega) hη hδ)).trans (wuBoxPhi_nonneg N δ _ v)
  have hbase := h1 N (by omega) heven i Δ V hbox
  have htrans := h0 N (by omega) heven i Δ V hbox (min v 4) 4
    (le_min (not_lt.mp hv2) (by norm_num)) (min_le_right _ _) (by norm_num) (by norm_num)
  have hm := phi_mono hbox (by omega) hη hδ (lt_min (by linarith) (by norm_num)) (min_le_left v 4)
  rw [lowerExtension,if_neg hv2]
  nlinarith only [hbase,htrans,hm]

theorem upper_extension_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hc4 : c ≤ 1 / 4)
    (hfnode : LowerNodes δ (lowerExtension H c)) :
    UpperNodes δ (upperExtension H c) 5 := by
  intro m η ε hη he
  obtain ⟨T0,hT04,h0⟩ := upper_buchstab_actual (lowerExtension H c)
    ((lowerExtension_mono hH hb hc).monotoneOn _) (by
      intro v _
      have hh := lowerExtension_bounds hH hb hc v
      exact ⟨hh.1,hh.2.trans (by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)])⟩)
    m hη hδ (half_pos he)
    (fun ρ hρ => hfnode (m + 1) (η / 20) ρ (by positivity) hρ)
  obtain ⟨T1,_,h1⟩ := roughBox_upper_leaf_bounded m hη hδ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hbox v hv hv5
  let x := max 3 (min v 5)
  have hx : 3 ≤ x := le_max_left _ _
  have hx5 : x ≤ 5 := max_le (by norm_num) (min_le_right _ _)
  have hvx : v ≤ x := by simpa only [x,min_eq_left hv5] using le_max_right (3 : ℝ) v
  have hbase := h1 N (by omega) heven i Δ V hbox 5 (by norm_num) (by norm_num)
  have htrans := h0 N (by omega) heven i Δ V hbox x 5 (by linarith) hx5 (by norm_num) (by norm_num)
  have hm := phi_mono hbox (by omega) hη hδ (by linarith) hvx
  change _ ≤ (wuUpperCoefficient 5 - profileIntegral (lowerExtension H c) x 5 + ε) * _
  nlinarith only [hbase,htrans,hm]

end Wu18938Campaign.M1.Confirmed.FiniteProfile
