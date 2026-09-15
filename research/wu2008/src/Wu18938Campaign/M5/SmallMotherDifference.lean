import WR2SixthCountCarriers
import MathlibNt.Wu2008DoubleSieve.PhiBuchstab
import MathlibNt.Wu2008DoubleSieve.SingleUpperLowPacking
import MathlibNt.Wu2008DoubleSieve.ImprovementLimits

noncomputable section

namespace Wu18938Campaign.M5.SmallMotherDifference

open Real Finset Wu2008DoubleSieve WuPaper.R2SixthCount
open scoped Classical

def endpointCoefficient (δ s t : ℝ) : ℝ :=
  wuLowerCoefficient t + wuImprovementLimit false δ t -
    (wuUpperCoefficient s - wuImprovementLimit true δ s)

/-- Only the small mother is a source box; the newly selected prime is not reboxed. -/
theorem phi_difference_lower (k : ℕ) {δ s t ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 1 ≤ s) (hs10 : s ≤ 10) (ht : 1 ≤ t) (ht10 : t ≤ 10)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox (k + 1) δ N i Δ V →
        (endpointCoefficient δ s t - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ V) t -
            wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  obtain ⟨Tl, hl⟩ := wuImprovementLimit_sub_mem false k hδ hδhi ht ht10 (half_pos hε)
  obtain ⟨Tu, hu⟩ := wuImprovementLimit_sub_mem true k hδ hδhi hs hs10 (half_pos hε)
  refine ⟨max 4 (max Tl Tu), le_max_left _ _, ?_⟩
  intro N hN he i Δ V hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hTl : Tl ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hTu : Tu ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlow := hl N hTl hN4 he i Δ V hb
  have hupp := hu N hTu hN4 he i Δ V hb
  change (wuLowerCoefficient t + (wuImprovementLimit false δ t - ε / 2)) * _ ≤ _ at hlow
  change _ ≤ (wuUpperCoefficient s - (wuImprovementLimit true δ s - ε / 2)) * _ at hupp
  unfold endpointCoefficient
  nlinarith only [hlow, hupp]

theorem selected_child_le_original {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hzp : (N : ℝ) ^ alpha ≤ (p : ℝ))
    (hzq : (N : ℝ) ^ alpha ≤ (q : ℝ)) :
    sourceSieveCount N (p * q) ((p * q) * N) (q : ℝ) ≤
      sourceSieveCountLE N (p * q) N ((N : ℝ) ^ alpha) := by
  rw [selected_pair_source_eq_double_modulus hp hq hzp hzq]
  exact sourceSieveCount_antitone N (p * q) ((p * q) * N) hzq

theorem moving_window_subset {N p : ℕ} {δ s t v w : ℝ}
    (hlo : (N : ℝ) ^ v ≤ wuLocalCutoff N δ p t)
    (hhi : wuLocalCutoff N δ p s ≤ (N : ℝ) ^ w) :
    primeWindow (p * N) (wuLocalCutoff N δ p t) (wuLocalCutoff N δ p s) ⊆
      window N v w := by
  intro q hq
  obtain ⟨hp, hc, hl, hu⟩ := mem_primeWindow.mp hq
  exact mem_window.mpr ⟨hp, (Nat.coprime_mul_iff_right.mp hc).2,
    hlo.trans hl, hu.trans_le hhi⟩

/-- This comparison allows `s<2` and large q, with the original closed alpha sieve. -/
theorem phi_difference_le_rectangle {N : ℕ} {δ s t a b v w : ℝ}
    (hN : 1 ≤ N) (hs : 0 < s) (hst : s ≤ t)
    (ha : alpha ≤ a) (hv : alpha ≤ v)
    (hQ : ∀ p ∈ window N a b, 1 ≤ (N : ℝ) ^ (1 / 2 - δ) / p)
    (hlo : ∀ p ∈ window N a b, (N : ℝ) ^ v ≤ wuLocalCutoff N δ p t)
    (hhi : ∀ p ∈ window N a b, wuLocalCutoff N δ p s ≤ (N : ℝ) ^ w) :
    wuBoxPhi N δ (fun _ : Fin 1 => window N a b) t -
        wuBoxPhi N δ (fun _ : Fin 1 => window N a b) s ≤
      (rectangleCount N a b v w : ℝ) := by
  rw [SingleUpperLowPacking.phi_single, SingleUpperLowPacking.phi_single,
    ← sum_sub_distrib]
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsum := sum_le_sum (s := window N a b) (fun p hp => by
    have hcut : wuLocalCutoff N δ p t ≤ wuLocalCutoff N δ p s :=
      rpow_le_rpow_of_exponent_le (hQ p hp) (one_div_le_one_div_of_le hs hst)
    have hb := source_buchstab_selected_modulus N p hcut
    have hpa := mem_window.mp hp
    have hzp : (N : ℝ) ^ alpha ≤ (p : ℝ) :=
      (rpow_le_rpow_of_exponent_le hNR ha).trans hpa.2.2.1
    have hsub := moving_window_subset (hlo p hp) (hhi p hp)
    have hraw :
        (∑ q ∈ primeWindow (p * N) (wuLocalCutoff N δ p t) (wuLocalCutoff N δ p s),
          (sourceSieveCount N (p * q) ((p * q) * N) (q : ℝ) : ℝ)) ≤
        ∑ q ∈ window N v w, (sourceSieveCountLE N (p * q) N ((N : ℝ) ^ alpha) : ℝ) := by
      apply (sum_le_sum (fun q hq => ?_)).trans
        (sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by
          unfold sourceSieveCountLE
          positivity))
      have hqa := mem_window.mp (hsub hq)
      exact_mod_cast selected_child_le_original hpa.1 hqa.1 hzp
        ((rpow_le_rpow_of_exponent_le hNR hv).trans hqa.2.2.1)
    exact (le_of_eq (sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hb))).trans hraw)
  calc
    _ ≤ _ := hsum
    _ = (rectangleCount N a b v w : ℝ) := by
      rw [sum_comm]
      simp only [rectangleCount, Int.cast_sum]

theorem fixed_cutoff_bracket {N p : ℕ} {δ l u v w s t : ℝ}
    (hN : 1 ≤ N) (hp : 0 < p)
    (hpl : (N : ℝ) ^ l ≤ (p : ℝ)) (hpu : (p : ℝ) ≤ (N : ℝ) ^ u)
    (hu : u ≤ 1 / 2 - δ) (hs : 0 < s) (ht : 0 < t)
    (hvt : v * t ≤ (1 / 2 - δ) - u)
    (hws : (1 / 2 - δ) - l ≤ w * s) :
    1 ≤ (N : ℝ) ^ (1 / 2 - δ) / p ∧
      (N : ℝ) ^ v ≤ wuLocalCutoff N δ p t ∧
      wuLocalCutoff N δ p s ≤ (N : ℝ) ^ w := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlo : (N : ℝ) ^ ((1 / 2 - δ) - u) ≤ (N : ℝ) ^ (1 / 2 - δ) / p := by
    rw [rpow_sub hN0 (1 / 2 - δ) u]
    exact div_le_div_of_nonneg_left (rpow_nonneg hN0.le _) hp0 hpu
  have hhi : (N : ℝ) ^ (1 / 2 - δ) / p ≤ (N : ℝ) ^ ((1 / 2 - δ) - l) := by
    rw [rpow_sub hN0 (1 / 2 - δ) l]
    exact div_le_div_of_nonneg_left (rpow_nonneg hN0.le _) (rpow_pos_of_pos hN0 _) hpl
  refine ⟨(one_le_rpow hNR (sub_nonneg.mpr hu)).trans hlo, ?_, ?_⟩
  · change _ ≤ (_ / _) ^ (1 / t)
    calc
      (N : ℝ) ^ v ≤ (N : ℝ) ^ (((1 / 2 - δ) - u) * (1 / t)) := by
        apply rpow_le_rpow_of_exponent_le hNR
        simpa only [one_div, div_eq_mul_inv, one_mul] using
          (le_div_iff₀ ht).mpr hvt
      _ = ((N : ℝ) ^ ((1 / 2 - δ) - u)) ^ (1 / t) := rpow_mul hN0.le _ _
      _ ≤ _ := rpow_le_rpow (rpow_nonneg hN0.le _) hlo (by positivity)
  · change (_ / _) ^ (1 / s) ≤ _
    calc
      _ ≤ ((N : ℝ) ^ ((1 / 2 - δ) - l)) ^ (1 / s) :=
        rpow_le_rpow (by positivity) hhi (by positivity)
      _ = (N : ℝ) ^ (((1 / 2 - δ) - l) * (1 / s)) := (rpow_mul hN0.le _ _).symm
      _ ≤ _ := by
        apply rpow_le_rpow_of_exponent_le hNR
        simpa only [one_div, div_eq_mul_inv, one_mul] using (div_le_iff₀ hs).mpr hws

theorem rectangle_cell_lower {δ l u v w s t ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (hl : alpha ≤ l) (hv : alpha ≤ v) (hu : u ≤ (1 / 2 - δ) / 2)
    (hs : 1 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10)
    (hvt : v * t ≤ (1 / 2 - δ) - u)
    (hws : (1 / 2 - δ) - l ≤ w * s) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
      ∀ a b : ℝ, l ≤ a → a ≤ b → b ≤ u →
        (N : ℝ) ^ b / Δ = (N : ℝ) ^ a →
        (endpointCoefficient δ s t - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
              (convolutionWuWindows N Δ (fun _ : Fin 1 => (N : ℝ) ^ b)) ≤
          (rectangleCount N a b v w : ℝ) := by
  obtain ⟨T, hT4, hT⟩ := phi_difference_lower 0 hδ (by linarith)
    hs (hst.trans ht10) (hs.trans hst) ht10 hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he Δ hΔlo hΔhi a b hla hab hbu hcell
  have hN4 : 4 ≤ N := hT4.trans hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hV : ∀ _j : Fin 1, (N : ℝ) ^ (δ ^ (1 + 1)) ≤ (N : ℝ) ^ b := by
    intro _j
    apply rpow_le_rpow_of_exponent_le hNR
    have hd := pow_le_pow_left₀ hδ.le hδhi 2
    have hαb := hl.trans (hla.trans hab)
    norm_num [alpha, QuarterTrim.alpha] at hαb
    norm_num at hd
    norm_num
    linarith
  have hpref : boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ))
      (fun _ : Fin 1 => (N : ℝ) ^ b) := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp
    rw [pow_two, ← rpow_add hN0]
    exact rpow_le_rpow_of_exponent_le hNR (by linarith)
  have hbox := hT N hN he 1 Δ (fun _ : Fin 1 => (N : ℝ) ^ b)
    ⟨le_rfl, hΔlo, hΔhi, (fun _ _ _ => le_rfl), hV, hpref⟩
  have hw : convolutionWuWindows N Δ (fun _ : Fin 1 => (N : ℝ) ^ b) =
      (fun _ : Fin 1 => window N a b) := by
    funext j
    simp only [convolutionWuWindows, hcell, window]
  rw [hw] at hbox
  have hg (p : ℕ) (hp : p ∈ window N a b) :
      1 ≤ (N : ℝ) ^ (1 / 2 - δ) / p ∧
        (N : ℝ) ^ v ≤ wuLocalCutoff N δ p t ∧
        wuLocalCutoff N δ p s ≤ (N : ℝ) ^ w := by
    obtain ⟨hp, _, hpa, hpb⟩ := mem_window.mp hp
    exact fixed_cutoff_bracket (by omega) hp.pos
      ((rpow_le_rpow_of_exponent_le hNR hla).trans hpa)
      (hpb.le.trans (rpow_le_rpow_of_exponent_le hNR hbu))
      (by linarith) (by linarith) (by linarith) hvt hws
  rw [hw]
  exact hbox.trans (phi_difference_le_rectangle (by omega) (by linarith) hst
    (hl.trans hla) hv (fun p hp => (hg p hp).1)
    (fun p hp => (hg p hp).2.1) (fun p hp => (hg p hp).2.2))

set_option pp.universes true
set_option pp.fullNames true

#check @endpointCoefficient
#print axioms endpointCoefficient
#check @phi_difference_lower
#print axioms phi_difference_lower
#check @selected_child_le_original
#print axioms selected_child_le_original
#check @moving_window_subset
#print axioms moving_window_subset
#check @phi_difference_le_rectangle
#print axioms phi_difference_le_rectangle
#check @fixed_cutoff_bracket
#print axioms fixed_cutoff_bracket
#check @rectangle_cell_lower
#print axioms rectangle_cell_lower

end Wu18938Campaign.M5.SmallMotherDifference
