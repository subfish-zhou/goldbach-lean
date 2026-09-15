import MathlibNt.Wu2008DoubleSieve.PhiUpper

/-!
# The printed closed Phi and the full canonical upper base interval

Closed sifting only decreases Phi. Also Phi increases with `s`, since
`(Q/d)^(1/s)` decreases when `Q/d>=1`. The baseline at `s=3/2` thus
controls all `1<=s<=3/2` without applying a density theorem outside
its proved domain. No endpoint loss or common-level transport is assumed.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem sourceSieveCount_antitone (N d M : ℕ) :
    Antitone (sourceSieveCount N d M) := by
  intro z w hzw
  apply Int.ofNat_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hp, hprime, hd, hs⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp, hprime, hd,
    fun q hq hc hz => hs q hq hc (hz.trans_le hzw)⟩

theorem sourceSieveCarrierLE_subset_strict (N d M : ℕ) (z : ℝ) :
    sourceSieveCarrierLE N d M z ⊆ sourceSieveCarrier N d M z := by
  intro p hp
  obtain ⟨hp, hprime, hd, hs⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp, hprime, hd, fun q hq hc hz => hs q hq hc hz.le⟩

/-- Printed Wu08 (3.4), retaining its `q<=z` convention. -/
noncomputable def wuBoxPhiLE {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s : ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    (sourceSieveCountLE N d (d * N) (wuLocalCutoff N δ d s) : ℝ)

theorem wuBoxPhiLE_le_strict {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s : ℝ) :
    wuBoxPhiLE N δ W s ≤ wuBoxPhi N δ W s := by
  unfold wuBoxPhiLE wuBoxPhi convolutionSieveCount
  apply sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold sourceSieveCountLE sourceSieveCount
  exact_mod_cast card_le_card
    (sourceSieveCarrierLE_subset_strict N d (d * N) (wuLocalCutoff N δ d s))

theorem wuBoxPhi_mono_parameter {i N : ℕ} {δ s t : ℝ}
    (W : Fin i → Finset ℕ)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 ≤ (N : ℝ) ^ (1 / 2 - δ) / d)
    (hs : 0 < s) (hst : s ≤ t) :
    wuBoxPhi N δ W s ≤ wuBoxPhi N δ W t := by
  unfold wuBoxPhi convolutionSieveCount
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hcut : wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d s :=
    rpow_le_rpow_of_exponent_le (hQ d hd) (one_div_le_one_div_of_le hs hst)
  exact_mod_cast sourceSieveCount_antitone N d (d * N) hcut

/-- Both source conventions satisfy the actual standard upper baseline
on `[1,3]`. The extension below `3/2` is a finite monotonicity argument,
not an unproved near-one Rosser density assertion. -/
theorem wu_boxPhi_upper_source (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 1 ≤ s → s ≤ 3 →
          wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
              (1 + ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
                (convolutionWuWindows N Δ V) ∧
            wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s ≤
              (1 + ε) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
                (convolutionWuWindows N Δ V) := by
  obtain ⟨N0, hupper⟩ := wu_boxPhi_upper k hk hδ hδhi hε
  refine ⟨max 2 N0, ?_⟩
  intro N hN he i hik Δ hlo hhi V horder hV hprefix s hs hs3
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hbase := hupper N ((le_max_right _ _).trans hN) he i hik Δ hlo hhi
    V horder hV hprefix (max (3 / 2) s) (le_max_left _ _)
    (max_le (by norm_num) hs3)
  have hmono := wuBoxPhi_mono_parameter (convolutionWuWindows N Δ V)
    (fun d hd => (wuVariableRosserLevel_geometry hN2 hδ hδhi hV hprefix hd hs).2.1.le)
    (by linarith : 0 < s) (le_max_right (3 / 2) s)
  have h := hmono.trans hbase
  exact ⟨h, (wuBoxPhiLE_le_strict N δ _ s).trans h⟩

end Wu2008DoubleSieve
