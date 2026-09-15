import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySlowFactor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Ordinary mixed derivatives of the concrete normalized slow weight -/

noncomputable section

namespace LiLiuPrereqFouvry.SlowFactor

def mixedDeriv : List (Fin 5) → (Point → ℂ) → Point → ℂ
  | [], f => f
  | j :: js, f => fun x =>
      deriv (fun t => mixedDeriv js f (Function.update x j t)) (x j)

def inverseFactors (js : List (Fin 5)) (v : Point) : ℝ :=
  (js.map (fun j => (v j)⁻¹)).prod

def normalizedJet (A B : ℝ) (js : List (Fin 5)) (v : Point) : ℂ :=
  (inverseFactors js v : ℂ) * jet A B js amplitude (fun i => Real.log (v i))

theorem log_update (v : Point) (j : Fin 5) (t : ℝ) :
    (fun i => Real.log (Function.update v j t i)) =
      Function.update (fun i => Real.log (v i)) j (Real.log t) := by
  funext i
  by_cases h : i = j
  · subst i
    simp
  · simp [Function.update_of_ne h]

theorem inverseFactors_update (js : List (Fin 5)) (v : Point) (j : Fin 5)
    (hj : j ∉ js) (t : ℝ) :
    inverseFactors js (Function.update v j t) = inverseFactors js v := by
  unfold inverseFactors
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [Function.update_of_ne (show i ≠ j from fun h => hj (h ▸ hi))]

theorem inverseFactors_append (js : List (Fin 5)) (v : Point) (j : Fin 5) :
    inverseFactors (js ++ [j]) v = inverseFactors js v * (v j)⁻¹ := by
  simp [inverseFactors]

theorem normalizedJet_nil (A B : ℝ) (v : Point) (hv : ∀ i, 0 < v i) :
    normalizedJet A B [] v = normalizedWeight A B v := by
  simpa [normalizedJet, inverseFactors, jet, weight] using
    weight_log_eq_normalizedWeight A B v hv

/-- Ordinary differentiation in a coordinate not yet used. The reciprocal
factors are derived by the chain rule, not assumed as derivative bounds. -/
theorem hasDerivAt_normalizedJet (A B : ℝ) (js : List (Fin 5)) (v : Point)
    (j : Fin 5) (hj : j ∉ js) (hv : v j ≠ 0) :
    HasDerivAt (fun t => normalizedJet A B js (Function.update v j t))
      (normalizedJet A B (js ++ [j]) v) (v j) := by
  have hh := ((hasDerivAt_jet A B js amplitude (fun i => Real.log (v i)) j).scomp
    (v j) (Real.hasDerivAt_log hv)).const_mul (inverseFactors js v : ℂ)
  convert hh using 1
  · rfl
  · ext t
    simp only [normalizedJet, inverseFactors_update js v j hj, log_update,
      Function.comp_apply]
  · simp only [normalizedJet, inverseFactors_append, Complex.ofReal_mul,
      Complex.real_smul, mul_assoc]

theorem positive_update (v : Point) (hv : ∀ i, 0 < v i) (j : Fin 5)
    (t : ℝ) (ht : 0 < t) :
    ∀ i, 0 < Function.update v j t i := by
  intro i
  by_cases h : i = j
  · subst i
    simpa using ht
  · simpa [Function.update_of_ne h] using hv i

/-- Identification with recursively defined, ordinary coordinate derivatives.
`Nodup` is exactly the condition that each coordinate is differentiated at most
once. Reversing the list merely reconciles the two recursion conventions. -/
theorem mixedDeriv_normalizedWeight (A B : ℝ) (js : List (Fin 5))
    (hjs : js.Nodup) (v : Point) (hv : ∀ i, 0 < v i) :
    mixedDeriv js (normalizedWeight A B) v = normalizedJet A B js.reverse v := by
  induction js generalizing v with
  | nil => exact (normalizedJet_nil A B v hv).symm
  | cons j js ih =>
    obtain ⟨hj, hjs⟩ := List.nodup_cons.mp hjs
    have hj' : j ∉ js.reverse := by simpa using hj
    have hd := hasDerivAt_normalizedJet A B js.reverse v j hj' (hv j).ne'
    have heq : (fun t => mixedDeriv js (normalizedWeight A B) (Function.update v j t))
        =ᶠ[nhds (v j)] (fun t => normalizedJet A B js.reverse (Function.update v j t)) := by
      filter_upwards [eventually_gt_nhds (hv j)] with t ht
      exact ih hjs _ (positive_update v hv j t ht)
    simpa only [mixedDeriv, List.reverse_cons] using
      (hd.congr_of_eventuallyEq heq).deriv

theorem abs_inverseFactors_le_one (js : List (Fin 5)) (v : Point)
    (hv : ∀ i, 1 ≤ v i) :
    |inverseFactors js v| ≤ 1 := by
  induction js with
  | nil => simp [inverseFactors]
  | cons j js ih =>
    have hv0 : 0 < v j := by linarith [hv j]
    have hinv : |(v j)⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr hv0)]
      exact inv_le_one_of_one_le₀ (hv j)
    simpa only [inverseFactors, List.map_cons, List.prod_cons, abs_mul, mul_one] using
      mul_le_mul hinv ih (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem norm_normalizedJet_le_five (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (js : List (Fin 5)) (hn : js.length ≤ 5) (v : Point)
    (hv : ∀ i, 1 ≤ v i ∧ v i ≤ 2) :
    ‖normalizedJet A B js v‖ ≤ 64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 := by
  rw [normalizedJet, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |inverseFactors js v| * ‖jet A B js amplitude (fun i => Real.log (v i))‖ ≤
        1 * ‖jet A B js amplitude (fun i => Real.log (v i))‖ :=
      mul_le_mul_of_nonneg_right (abs_inverseFactors_le_one js v (fun i => (hv i).1))
        (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact normalized_log_mixed_bound A B V hV js hn v hv

/-- The complete five-variable, order-at-most-one-in-each-coordinate bound for
the actual nonseparable normalized weight. The only size assumption is on the
two explicit phase parameters. -/
theorem norm_mixedDeriv_normalizedWeight_le (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (js : List (Fin 5)) (hjs : js.Nodup) (v : Point)
    (hv : ∀ i, 1 ≤ v i ∧ v i ≤ 2) :
    ‖mixedDeriv js (normalizedWeight A B) v‖ ≤
      64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 := by
  rw [mixedDeriv_normalizedWeight A B js hjs v (fun i => by linarith [(hv i).1])]
  apply norm_normalizedJet_le_five A B V hV js.reverse _ v hv
  rw [List.length_reverse]
  exact le_trans (List.Nodup.length_le_card hjs) (by decide)

end LiLiuPrereqFouvry.SlowFactor
