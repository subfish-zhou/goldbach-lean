import MathlibNt.Wu2008DoubleSieve.RelativeSieveRemainder
import MathlibNt.Wu2008DoubleSieve.LocalProductWu

/-!
# Direct variable-level instantiation on the actual Wu boxes

Wu08 (3.4)--(3.5) use `z = (Q/d)^(1/s)`. We use one concrete Rosser
sieve of real level `Q/d` at each supported `d`, rather than reconstruct
the common-level well-factorable decomposition in Wu04 (3.11).
The ordinary AP producer already permits these varying levels.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def wuVariableRosserLevel (N : ℕ) (δ : ℝ) (d : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / 2 - δ) / d⌋₊ + 1

theorem wuVariableRosserLevel_eq_combined (N d : ℕ) (δ : ℝ) :
    wuVariableRosserLevel N δ d = convolutionModulusCutoff N δ / d + 1 := by
  simp only [wuVariableRosserLevel, convolutionModulusCutoff, Nat.floor_div_natCast]

theorem boxSquaredPrefixes_iff {i : ℕ} (Q : ℝ) (V : Fin i → ℝ) :
    boxSquaredPrefixes Q V ↔
      ∀ j, (∏ l, if l < j then V l else 1) * V j ^ 2 ≤ Q := by
  simp only [boxSquaredPrefixes, prod_filter]

/-- The actual density parameter is exactly `s`, not a common-level proxy. -/
theorem log_div_log_rpow_eq {q s : ℝ} (hq : 1 < q) (hs : 0 < s) :
    log q / log (q ^ (1 / s)) = s := by
  rw [log_rpow (by linarith : 0 < q)]
  have hl : log q ≠ 0 := (log_pos hq).ne'
  field_simp

theorem variableRosser_geometry {q s : ℝ} (hq : 1 < q) (hs : 1 ≤ s) :
    1 < ⌊q⌋₊ + 1 ∧ q ^ (1 / s) ≤ (⌊q⌋₊ + 1 : ℕ) ∧
      log q / log (q ^ (1 / s)) = s := by
  have hs0 : 0 < s := by linarith
  have hexp : 1 / s ≤ 1 := (div_le_one hs0).mpr hs
  have hpow : q ^ (1 / s) ≤ q := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hq.le hexp
  have hfloor : q < (⌊q⌋₊ + 1 : ℕ) := by exact_mod_cast Nat.lt_floor_add_one q
  refine ⟨?_, hpow.trans hfloor.le, log_div_log_rpow_eq hq hs0⟩
  exact_mod_cast hq.trans hfloor

/-- The real and natural geometry follows on every actual tuple fibre,
including depth zero. The complete `dq` cutoff is an equality. -/
theorem wuVariableRosserLevel_geometry {i k N d : ℕ} {Δ δ s : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hV : ∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j)
    (hprefix : boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 1 ≤ s) :
    0 < d ∧ 1 < (N : ℝ) ^ (1 / 2 - δ) / d ∧
      1 < wuVariableRosserLevel N δ d ∧
      wuLocalCutoff N δ d s ≤ (wuVariableRosserLevel N δ d : ℝ) ∧
      log ((N : ℝ) ^ (1 / 2 - δ) / d) / log (wuLocalCutoff N δ d s) = s ∧
      wuVariableRosserLevel N δ d = convolutionModulusCutoff N δ / d + 1 := by
  obtain ⟨hd0, _, hquot⟩ := wuLocal_support_bounds (by omega) hδ hδhi hV
    ((boxSquaredPrefixes_iff _ _).mp hprefix) hd
  have hq : 1 < (N : ℝ) ^ (1 / 2 - δ) / d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega))
      (wuLocalExponent_pos k hδ hδhi)).trans_le hquot
  obtain ⟨hD, hz, ht⟩ := variableRosser_geometry hq hs
  exact ⟨hd0, hq, hD, hz, ht, wuVariableRosserLevel_eq_combined N d δ⟩

/-- A single threshold makes every moving cutoff large, uniformly in the
source family and all `s` in `[1,10]`. -/
theorem wuLocalCutoff_eventually_large (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (Z : ℝ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
        (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
        boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
        ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
          ∀ s : ℝ, 1 ≤ s → s ≤ 10 → Z ≤ wuLocalCutoff N δ d s := by
  have hα : 0 < wuLocalExponent k δ / 10 :=
    div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have ht := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop Z)
  apply eventually_atTop.mp
  filter_upwards [ht, eventually_ge_atTop (1 : ℕ)] with N hZ hN
  intro i Δ V hV hprefix d hd s hs hs'
  have hb := wuLocal_support_bounds hN hδ hδhi hV
    ((boxSquaredPrefixes_iff _ _).mp hprefix) hd
  exact hZ.trans (wuLocalCutoff_lower hN hδ hδhi hs hs' hb.2.2)

/-- The `L=1` specialization pays the actual varying-level signed
remainder relative to the actual Theta, without a WF-family assumption. -/
theorem wu_variable_level_remainder_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ upper : Bool, ∀ z : ℕ → ℝ,
          |convolutionRosserRemainder N (convolutionWuWindows N Δ V)
            upper (wuVariableRosserLevel N δ) z| ≤
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
              (convolutionWuWindows N Δ V) := by
  obtain ⟨N0, h⟩ := wu_signed_rosser_remainder_relative k 1 hδ hδhi hε
  refine ⟨N0, ?_⟩
  intro N hN i hik Δ hlo hhi V hV hprefix upper z
  have hb := h N hN i hik Δ hlo hhi V hV hprefix
    (fun _ => upper) (fun _ => wuVariableRosserLevel N δ) (fun _ => z)
    (fun _ d _ => (wuVariableRosserLevel_eq_combined N d δ).le)
  simpa using hb

end Wu2008DoubleSieve
