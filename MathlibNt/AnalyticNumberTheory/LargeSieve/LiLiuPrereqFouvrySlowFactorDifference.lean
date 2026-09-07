import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySlowFactorNormalized
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Mixed rectangular increments of the actual slow weight

Each increment costs its side length, not the number of sampled points.
Consequently subdivision of any side does not increase the sum of these
bounds. This is the local analytic estimate used by rectangular summation.
-/

noncomputable section

namespace LiLiuPrereqFouvry.SlowFactor

def boxDiff : List (Fin 5) → Point → Point → (Point → ℂ) → Point → ℂ
  | [], _, _, f, x => f x
  | j :: js, lo, hi, f, x =>
      boxDiff js lo hi f (Function.update x j (hi j)) -
        boxDiff js lo hi f (Function.update x j (lo j))

def sideProduct (js : List (Fin 5)) (lo hi : Point) : ℝ :=
  (js.map (fun i => hi i - lo i)).prod

theorem hasDerivAt_boxDiff (A B : ℝ) (ds js : List (Fin 5)) (lo hi x : Point)
    (j : Fin 5) (hjd : j ∉ ds) (hjj : j ∉ js) (hxj : x j ≠ 0) :
    HasDerivAt
      (fun t => boxDiff js lo hi (normalizedJet A B ds) (Function.update x j t))
      (boxDiff js lo hi (normalizedJet A B (ds ++ [j])) x) (x j) := by
  induction js generalizing x with
  | nil => exact hasDerivAt_normalizedJet A B ds x j hjd hxj
  | cons i js ih =>
    have hji : j ≠ i := fun h => hjj (by simp [h])
    have hij : i ≠ j := hji.symm
    have hjjs : j ∉ js := fun h => hjj (by simp [h])
    have hu := ih (Function.update x i (hi i)) hjjs
      (by simpa [Function.update_of_ne hji] using hxj)
    have hl := ih (Function.update x i (lo i)) hjjs
      (by simpa [Function.update_of_ne hji] using hxj)
    simp only [Function.update_of_ne hji] at hu hl
    have hh := hu.sub hl
    convert hh using 1
    · rfl
    · ext t
      simp only [boxDiff, Pi.sub_apply, Function.update_comm hij]
    · rfl

theorem shell_update (x : Point) (hx : ∀ i, 1 ≤ x i ∧ x i ≤ 2)
    (j : Fin 5) (t : ℝ) (ht : 1 ≤ t ∧ t ≤ 2) :
    ∀ i, 1 ≤ Function.update x j t i ∧ Function.update x j t i ≤ 2 := by
  intro i
  by_cases h : i = j
  · subst i
    simpa using ht
  · simpa [Function.update_of_ne h] using hx i

/-- An explicit mixed-increment bound for every derivative still needed in
the repeated mean-value argument. All analytic hypotheses are proved by the
concrete calculus in the two preceding modules. -/
theorem norm_boxDiff_normalizedJet_le (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (ds js : List (Fin 5)) (hnd : (ds ++ js).Nodup) (lo hi x : Point)
    (hlohi : ∀ i, 1 ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ 2)
    (hx : ∀ i, 1 ≤ x i ∧ x i ≤ 2) :
    ‖boxDiff js lo hi (normalizedJet A B ds) x‖ ≤
      (64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5) * sideProduct js lo hi := by
  induction js generalizing ds x with
  | nil =>
    simp only [List.append_nil] at hnd
    simp only [boxDiff, sideProduct, List.map_nil, List.prod_nil, mul_one]
    exact norm_normalizedJet_le_five A B V hV ds
      ((List.Nodup.length_le_card hnd).trans (by decide)) x hx
  | cons j js ih =>
    have hjd : j ∉ ds := by
      intro hj
      have hd := (List.nodup_append.mp hnd).2.2
      exact hd j hj j (by simp) rfl
    have hjjs : j ∉ js := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
    have hn' : ((ds ++ [j]) ++ js).Nodup := by
      simpa only [List.append_assoc, List.singleton_append] using hnd
    have htbox (t : ℝ) (ht : t ∈ Set.Icc (lo j) (hi j)) :
        ∀ i, 1 ≤ Function.update x j t i ∧ Function.update x j t i ≤ 2 :=
      shell_update x hx j t ⟨(hlohi j).1.trans ht.1, ht.2.trans (hlohi j).2.2⟩
    have hd (t : ℝ) (ht : t ∈ Set.Icc (lo j) (hi j)) :
        HasDerivAt
          (fun u => boxDiff js lo hi (normalizedJet A B ds) (Function.update x j u))
          (boxDiff js lo hi (normalizedJet A B (ds ++ [j])) (Function.update x j t)) t := by
      have ht0 : t ≠ 0 := by linarith [ht.1, (hlohi j).1]
      simpa only [Function.update_self, Function.update_idem] using
        hasDerivAt_boxDiff A B ds js lo hi (Function.update x j t) j hjd hjjs
          (by simpa only [Function.update_self] using ht0)
    have hb (t : ℝ) (ht : t ∈ Set.Ico (lo j) (hi j)) :
        ‖boxDiff js lo hi (normalizedJet A B (ds ++ [j])) (Function.update x j t)‖ ≤
          (64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5) * sideProduct js lo hi :=
      ih (ds ++ [j]) hn' _ (htbox t ⟨ht.1, ht.2.le⟩)
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hd t ht).hasDerivWithinAt) hb (hi j) ⟨(hlohi j).2.1, le_rfl⟩
    simpa only [boxDiff, sideProduct, List.map_cons, List.prod_cons,
      mul_assoc, mul_left_comm, mul_comm] using hmv

theorem boxDiff_normalizedJet_nil (A B : ℝ) (js : List (Fin 5)) (lo hi x : Point)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, 0 < hi i) (hx : ∀ i, 0 < x i) :
    boxDiff js lo hi (normalizedJet A B []) x =
      boxDiff js lo hi (normalizedWeight A B) x := by
  induction js generalizing x with
  | nil => exact normalizedJet_nil A B x hx
  | cons j js ih =>
    simp only [boxDiff]
    rw [ih _ (positive_update x hx j (hi j) (hhi j)),
      ih _ (positive_update x hx j (lo j) (hlo j))]

/-- Concrete rectangular increment estimate, with a product of side lengths.
There is no interval-cardinality loss and no assumed variation bound. -/
theorem norm_boxDiff_normalizedWeight_le (A B V : ℝ) (hV : |A| + |B| ≤ V)
    (js : List (Fin 5)) (hjs : js.Nodup) (lo hi x : Point)
    (hlohi : ∀ i, 1 ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ 2)
    (hx : ∀ i, 1 ≤ x i ∧ x i ≤ 2) :
    ‖boxDiff js lo hi (normalizedWeight A B) x‖ ≤
      (64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5) * sideProduct js lo hi := by
  rw [← boxDiff_normalizedJet_nil A B js lo hi x
    (fun i => by linarith [(hlohi i).1])
    (fun i => by linarith [(hlohi i).1, (hlohi i).2.1])
    (fun i => by linarith [(hx i).1])]
  exact norm_boxDiff_normalizedJet_le A B V hV [] js hjs lo hi x hlohi hx

end LiLiuPrereqFouvry.SlowFactor
