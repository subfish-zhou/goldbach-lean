import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Literal finite rectangles. No analytic distribution imports. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal
abbrev Label := Σ _ : ℕ × ℕ, ℕ
abbrev Key := ℕ × ℕ × ℕ

def originalAlpha : ℝ := 100 / 1327

def gridIndex (ρ t : ℝ) : ℕ := ⌊Real.log t / Real.log ρ⌋₊
def gridKey (ρ : ℝ) (x : Label) : Key :=
  (gridIndex ρ x.1.1, gridIndex ρ x.1.2, gridIndex ρ x.2)

theorem gridIndex_bounds {ρ t : ℝ} (hρ : 1 < ρ) (ht : 1 ≤ t) :
    ρ ^ gridIndex ρ t ≤ t ∧ t < ρ ^ (gridIndex ρ t + 1) := by
  have hr : 0 < ρ := lt_trans zero_lt_one hρ
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hl : 0 < Real.log ρ := Real.log_pos hρ
  have hq : 0 ≤ Real.log t / Real.log ρ := div_nonneg (Real.log_nonneg ht) hl.le
  constructor
  · apply (Real.log_le_log_iff (pow_pos hr _) ht0).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hl).mp (Nat.floor_le hq)
  · apply (Real.log_lt_log_iff ht0 (pow_pos hr _)).mp
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
    exact (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one (Real.log t / Real.log ρ))

/-- Whole integer interval carrying the prime indicator, not a singleton. -/
def shortPrimeSupport (N : ℕ) (ρ : ℝ) (k : Key) : Finset ℕ :=
  Ioc ⌊(⌈max (ρ^k.1) ((N : ℝ)^originalAlpha)⌉ : ℝ)-1⌋₊
    ⌊(⌈min (ρ^(k.1+1)) ((N : ℝ)^(1/10 : ℝ))⌉ : ℝ)-1⌋₊
def rectangleBeta (N n : ℕ) : ℝ := if n.Coprime N then (if n.Prime then 1 else 0) else 0

/-- The diagonal is retained, and only the original p2 copN mask is imposed. -/
def longLabels (N : ℕ) (ρ : ℝ) (k : Key) : Finset (ℕ × ℕ) := by
  classical
  exact ((range (N+1)) ×ˢ (range (N+1))).filter fun t =>
    t.1.Prime ∧ t.2.Prime ∧ t.1.Coprime N ∧ t.1 ≤ t.2 ∧
    (N : ℝ)^(1/3 : ℝ) ≤ t.1 ∧
    ρ^k.2.1 ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < ρ^(k.2.1+1) ∧
    ρ^k.2.2 ≤ (t.2 : ℝ) ∧ (t.2 : ℝ) < ρ^(k.2.2+1)
def longProducts (N : ℕ) (ρ : ℝ) (k : Key) : Finset ℕ := by
  classical
  exact (longLabels N ρ k).image fun t => t.1*t.2
def longAlpha (N : ℕ) (ρ : ℝ) (k : Key) (m : ℕ) : ℝ := by
  classical
  exact (((longLabels N ρ k).filter fun t => t.1*t.2=m).card : ℝ)

/-- Identical finite kernel to the modern weighted sieve (bridged separately). -/
def weightedSequenceSifted {ι : Type*} (I : Finset ι) (a : ι → ℕ)
    (w : ι → ℝ) (P : Finset ℕ) : ℝ :=
  ∑ i ∈ I, w i * (if (a i).Coprime (P.prod id) then 1 else 0)
def output (N n m : ℕ) : ℕ := ((N : ℤ)-(m : ℤ)*n).natAbs
def rectangleSifted (N : ℕ) (ρ : ℝ) (k : Key) (P : Finset ℕ) : ℝ :=
  weightedSequenceSifted (longProducts N ρ k ×ˢ shortPrimeSupport N ρ k)
    (fun t => output N t.2 t.1)
    (fun t => longAlpha N ρ k t.1 * rectangleBeta N t.2) P

theorem longAlpha_nonneg (N : ℕ) (ρ : ℝ) (k : Key) (m : ℕ) :
    0 ≤ longAlpha N ρ k m := by unfold longAlpha; positivity

theorem longAlpha_le_divisors (N : ℕ) (ρ : ℝ) (k : Key) (m : ℕ) :
    longAlpha N ρ k m ≤ (m.divisors.card : ℝ) := by
  classical
  unfold longAlpha
  apply Nat.cast_le.mpr
  apply card_le_card_of_injOn (fun t => t.1)
  · intro t ht
    obtain ⟨ht, he⟩ := mem_filter.mp ht
    have hp := (mem_filter.mp ht).2
    exact Nat.mem_divisors.mpr ⟨he ▸ dvd_mul_right t.1 t.2,
      he ▸ Nat.ne_of_gt (Nat.mul_pos hp.1.pos hp.2.1.pos)⟩
  · intro x hx y hy he
    obtain ⟨hx, hxm⟩ := mem_filter.mp hx
    obtain ⟨_, hym⟩ := mem_filter.mp hy
    apply Prod.ext he
    apply Nat.eq_of_mul_eq_mul_left (mem_filter.mp hx).2.1.pos
    change x.1 = y.1 at he
    calc
      x.1*x.2 = m := hxm
      _ = y.1*y.2 := hym.symm
      _ = x.1*y.2 := by rw [he]

theorem longAlpha_firstIndex (N : ℕ) (ρ : ℝ) (i i' j l m : ℕ) :
    longAlpha N ρ (i,j,l) m = longAlpha N ρ (i',j,l) m := rfl

/-- Exact fibre regrouping, valid for signed kernels and repeated products. -/
theorem long_sum (N : ℕ) (ρ : ℝ) (k : Key) (F : ℕ → ℝ) :
    (∑ t ∈ longLabels N ρ k, F (t.1*t.2)) =
      ∑ m ∈ longProducts N ρ k, longAlpha N ρ k m * F m := by
  classical
  have h := sum_fiberwise_of_maps_to
    (s := longLabels N ρ k) (t := longProducts N ρ k)
    (g := fun t : ℕ × ℕ => t.1*t.2)
    (fun t ht => mem_image_of_mem (fun t : ℕ × ℕ => t.1*t.2) ht)
    (fun t => F (t.1*t.2))
  rw [← h]
  apply sum_congr rfl
  intro m _
  calc
    _ = ∑ _t ∈ (longLabels N ρ k).filter (fun t => t.1*t.2=m), F m := by
      apply sum_congr rfl
      intro t ht
      rw [(mem_filter.mp ht).2]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, longAlpha]

/-- Expanded, label-preserving form of exactly the separated rectangle. -/
theorem rectangleSifted_labels (N : ℕ) (ρ : ℝ) (k : Key) (P : Finset ℕ) :
    rectangleSifted N ρ k P =
      ∑ n ∈ shortPrimeSupport N ρ k, ∑ t ∈ longLabels N ρ k,
        rectangleBeta N n * (if (output N n (t.1*t.2)).Coprime (P.prod id)
          then 1 else 0) := by
  classical
  unfold rectangleSifted weightedSequenceSifted
  rw [sum_product, sum_comm]
  apply sum_congr rfl
  intro n _
  rw [long_sum N ρ k (fun m => rectangleBeta N n *
    (if (output N n m).Coprime (P.prod id) then 1 else 0))]
  apply sum_congr rfl
  intro m _
  exact mul_assoc _ _ _

/-- All source labels in one rectangle inject into the separated label product. -/
theorem labels_le_rectangle {N : ℕ} {ρ : ℝ} {k : Key} {P : Finset ℕ}
    (S : Finset Label)
    (hS : ∀ x ∈ S, x.1.1 ∈ shortPrimeSupport N ρ k ∧
      (x.1.2,x.2) ∈ longLabels N ρ k ∧ x.1.1.Prime ∧ x.1.1.Coprime N ∧
      (output N x.1.1 (x.1.2*x.2)).Coprime (P.prod id)) :
    (S.card : ℝ) ≤ rectangleSifted N ρ k P := by
  classical
  rw [rectangleSifted_labels]
  let f : Label → ℕ × (ℕ × ℕ) := fun x => (x.1.1,x.1.2,x.2)
  let W : ℕ × (ℕ × ℕ) → ℝ := fun t => rectangleBeta N t.1 *
    (if (output N t.1 (t.2.1*t.2.2)).Coprime (P.prod id) then 1 else 0)
  have hf : Function.Injective f := by
    intro x y h
    obtain ⟨⟨a,b⟩,c⟩ := x
    obtain ⟨⟨d,e⟩,g⟩ := y
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
  have hsub : S.image f ⊆ shortPrimeSupport N ρ k ×ˢ longLabels N ρ k := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    exact mem_product.mpr ⟨(hS x hx).1,(hS x hx).2.1⟩
  have hw : ∀ t, 0 ≤ W t := by
    intro t
    dsimp [W, rectangleBeta]
    split_ifs <;> norm_num
  calc
    (S.card : ℝ) = ∑ x ∈ S, W (f x) := by
      calc
        _ = ∑ _x ∈ S, (1 : ℝ) := by simp
        _ = _ := ?_
      apply sum_congr rfl
      intro x hx
      obtain ⟨_,_,hp,hc,hs⟩ := hS x hx
      dsimp only [W,f]
      rw [if_pos hs]
      unfold rectangleBeta
      rw [if_pos hc, if_pos hp]
      norm_num
    _ = ∑ t ∈ S.image f, W t := (sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ ∑ t ∈ shortPrimeSupport N ρ k ×ˢ longLabels N ρ k, W t :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hw t)
    _ = _ := by rw [sum_product]
end U8Literal
