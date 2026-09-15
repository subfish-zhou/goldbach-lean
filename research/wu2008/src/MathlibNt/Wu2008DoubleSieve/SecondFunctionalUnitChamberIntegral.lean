import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitGraphSymmetry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighIdentification
import Mathlib.Data.Fin.Tuple.Sort

open scoped BigOperators Classical
open MeasureTheory Set
namespace Wu2008DoubleSieve.HighUnit

/-- Distinct free coordinates tie only on a genuine Lebesgue-null affine face. -/
theorem free_tie_ae {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∀ᵐ t ∂volume, t ∈ continuousCube n → t i ≠ t j := by
  let c : Fin n → ℝ := fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)
  have hc : 1 ≤ |c i| := by simp [c, hij]
  have hn := (measure_eq_zero_iff_ae_notMem).mp (continuousHyperplane_null i c 0 hc)
  filter_upwards [hn] with t ht hcube heq
  apply ht
  refine ⟨hcube, ?_⟩
  simp [c, sub_mul, Finset.sum_sub_distrib, heq]

/-- A free/omitted tie has coefficient two on the selected coordinate. -/
theorem omitted_tie_ae {n : ℕ} (phi : ℝ) (j : Fin n) :
    ∀ᵐ t ∂volume, t ∈ continuousCube n → t j ≠ phi - ∑ k, t k := by
  let c : Fin n → ℝ := fun k => 1 + (if k = j then 1 else 0)
  have hc : 1 ≤ |c j| := by norm_num [c]
  have hn := (measure_eq_zero_iff_ae_notMem).mp (continuousHyperplane_null j c phi hc)
  filter_upwards [hn] with t ht hcube heq
  apply ht
  refine ⟨hcube, ?_⟩
  change ∑ k, c k * t k = phi
  simp only [c, add_mul, one_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

/-- All append coordinates are distinct almost everywhere on the actual compact cube. -/
theorem append_injective_ae {n : ℕ} (phi : ℝ) :
    ∀ᵐ t ∂volume, t ∈ continuousCube n → Function.Injective (append phi t) := by
  have hf : ∀ᵐ t ∂volume, ∀ i j : Fin n, i ≠ j →
      t ∈ continuousCube n → t i ≠ t j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases h : i = j
    · exact Filter.Eventually.of_forall (by simp [h])
    · exact (free_tie_ae i j h).mono (fun _ ht _ => ht)
  have hl := ae_all_iff.mpr (fun j : Fin n => omitted_tie_ae phi j)
  filter_upwards [hf, hl] with t ht hs hc
  intro i j he
  revert he
  refine Fin.lastCases ?_ (fun k => ?_) i
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · intro _; rfl
    · intro he
      exact (hs l hc (by simpa [append] using he.symm)).elim
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · intro he
      exact (hs k hc (by simpa [append] using he)).elim
    · intro he
      have hkl : k = l := by
        by_contra hne
        exact ht k l hne hc (by simpa [append] using he)
      exact congrArg Fin.castSucc hkl

/-- An injective real tuple has exactly one increasing permutation. -/
theorem unique_sorting {r : ℕ} (x : Fin r → ℝ) (hx : Function.Injective x) :
    ∃! p : Equiv.Perm (Fin r), Monotone (x ∘ p) := by
  refine ⟨Tuple.sort x, Tuple.monotone_sort x, ?_⟩
  intro p hp
  apply Equiv.ext
  intro i
  apply hx
  exact congrFun (Tuple.unique_monotone hp (Tuple.monotone_sort x)) i

/-- Pointwise complete weighted chamber partition, not a postulated factorial. -/
theorem weighted_sorting_partition {r : ℕ} (x : Fin r → ℝ) (hx : Function.Injective x) (w : ℝ) :
    (∑ p : Equiv.Perm (Fin r), if Monotone (x ∘ p) then w else 0) = w := by
  obtain ⟨p, hp, hu⟩ := unique_sorting x hx
  rw [Finset.sum_eq_single p]
  · simp [hp]
  · intro q _ hqp
    exact if_neg (fun hq => hqp (hu q hq))
  · simp

/-- The existing ordered domain is exactly the full box intersected with its closed chamber. -/
theorem D21_box_monotone (a b : ℝ) (x : Fin 6 → ℝ) :
    D21 a b x ↔ (∀ i, a ≤ x i ∧ x i ≤ b) ∧ Monotone x := by
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
    have hm : Monotone x := by
      rw [Fin.monotone_iff_le_succ]
      simpa [Fin.forall_fin_succ] using And.intro h1 ⟨h2,h3,h4,h5⟩
    exact ⟨fun i => ⟨h0.trans (hm (Fin.zero_le i)), (hm (Fin.le_last i)).trans h6⟩, hm⟩
  · rintro ⟨hb,hm⟩
    exact ⟨(hb 0).1, hm (by decide), hm (by decide), hm (by decide),
      hm (by decide), hm (by decide), (hb 5).2⟩

theorem D20_box_monotone (a2 a b : ℝ) (x : Fin 5 → ℝ) :
    D20 a2 a b x ↔ (∀ i : Fin 5, (Fin.cons a2 (fun _ => a) : Fin 5 → ℝ) i ≤ x i ∧
      x i ≤ (Fin.cons a (fun _ => b) : Fin 5 → ℝ) i) ∧ Monotone (fun j : Fin 4 => x j.succ) := by
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
    have hm : Monotone (fun j : Fin 4 => x j.succ) := by
      rw [Fin.monotone_iff_le_succ]
      simpa [Fin.forall_fin_succ] using And.intro h3 ⟨h4,h5⟩
    refine ⟨?_,hm⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨h0,h1⟩
    · exact ⟨h2.trans (hm (Fin.zero_le j)), (hm (Fin.le_last j)).trans h6⟩
  · rintro ⟨hb,hm⟩
    exact ⟨(hb 0).1, (hb 0).2, (hb 1).1, hm (show (0 : Fin 4) ≤ 1 by decide),
      hm (show (1 : Fin 4) ≤ 2 by decide), hm (show (2 : Fin 4) ≤ 3 by decide), (hb 4).2⟩

theorem section21_chamber (a b phi : ℝ) (t : Fin 5 → ℝ) :
    section21 a b phi t =
      if Monotone (append phi t) then graphWeight (fun _ => a) (fun _ => b) phi t else 0 := by
  unfold section21 graphWeight
  rw [D21_box_monotone]
  have hp : (∏ i, append phi t i) = (∏ i, t i) * (phi - ∑ i, t i) := by
    rw [Fin.prod_univ_castSucc]
    simp only [append, Fin.snoc_castSucc, Fin.snoc_last]
  rw [hp]
  unfold graphBox
  split_ifs <;> simp_all

theorem section20_chamber (a2 a b phi : ℝ) (t : Fin 4 → ℝ) :
    section20 a2 a b phi t =
      if Monotone (fun j : Fin 4 => append phi t j.succ) then
        graphWeight (Fin.cons a2 (fun _ => a)) (Fin.cons a (fun _ => b)) phi t else 0 := by
  unfold section20 graphWeight
  rw [D20_box_monotone]
  have hp : (∏ i, append phi t i) = (∏ i, t i) * (phi - ∑ i, t i) := by
    rw [Fin.prod_univ_castSucc]
    simp only [append, Fin.snoc_castSucc, Fin.snoc_last]
  rw [hp]
  unfold graphBox
  split_ifs <;> simp_all

end Wu2008DoubleSieve.HighUnit
