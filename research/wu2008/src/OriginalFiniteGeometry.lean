import OriginalMassConsumer
import MathlibNt.SieveTheory.LiLiuFouvryG9PrefixWeights

noncomputable section
open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8

def shortLabels (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : Finset ℕ :=
  (primeSupport N ρ k).filter fun n => n.Prime ∧ n.Coprime N

/-- Exact conversion of the whole ceil-minus-one interval and product fibres. -/
theorem rectangleMass_card (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) :
    rectangleMass N ρ k = ((shortLabels N ρ k ×ˢ labels N ρ k).card : ℝ) := by
  have h := alpha_sum (labels N ρ k) (fun _ => ∑ n ∈ primeSupport N ρ k, beta N n)
  simp only [mul_sum] at h
  rw [rectangleMass, ← h]
  have hs := short_sum N ρ k (fun _ => (1 : ℝ))
  simp only [mul_one] at hs
  change (∑ _ ∈ shortLabels N ρ k, (1 : ℝ)) = _ at hs
  rw [← hs]
  simp [sum_const, card_product, Nat.cast_mul, mul_comm]

/-- Each labelled triple has exactly one geometric cell, independently of alpha. -/
theorem original_label_unique {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k k' : ℕ × ℕ × ℕ} (hb : 3 ≤ ρ^k.1) (hb' : 3 ≤ ρ^k'.1)
    (hk : Occupied N e ρ k) (hk' : Occupied N e ρ k')
    {n : ℕ} {z : ℕ × ℕ} (hn : n ∈ shortLabels N ρ k) (hz : z ∈ labels N ρ k)
    (hn' : n ∈ shortLabels N ρ k') (hz' : z ∈ labels N ρ k') : k = k' := by
  have a := (primeSupport_mem hρ hρu k hb hk n).mp (mem_filter.mp hn).1
  have a' := (primeSupport_mem hρ hρu k' hb' hk' n).mp (mem_filter.mp hn').1
  have b := (labels_mem N ρ k z.1 z.2).mp hz
  have b' := (labels_mem N ρ k' z.1 z.2).mp hz'
  exact Prod.ext (fouvryG9RectanglePrefix_index_unique hρ ⟨a.1,a.2.2.1⟩ ⟨a'.1,a'.2.2.1⟩)
    (Prod.ext (fouvryG9RectanglePrefix_index_unique hρ
      ⟨b.2.2.2.2.2.2.1,b.2.2.2.2.2.2.2.1⟩
      ⟨b'.2.2.2.2.2.2.1,b'.2.2.2.2.2.2.2.1⟩)
      (fouvryG9RectanglePrefix_index_unique hρ
      ⟨b.2.2.2.2.2.2.2.2.1,b.2.2.2.2.2.2.2.2.2.1⟩
      ⟨b'.2.2.2.2.2.2.2.2.1,b'.2.2.2.2.2.2.2.2.2.1⟩))

/-- The full occupied rectangle, not just its physical witness, has rho-cubed product.
The weak ordering retains the diagonal p2=r. -/
theorem original_enlarged_geometry {N : ℕ} {e ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : ℕ × ℕ × ℕ}
    (hb : 3 ≤ ρ^k.1) (hk : Occupied N e ρ k)
    {n : ℕ} {z : ℕ × ℕ} (hn : n ∈ shortLabels N ρ k) (hz : z ∈ labels N ρ k) :
    (n : ℝ)*z.1*z.2 < ρ^3*(N : ℝ) ∧ (n : ℝ)*(z.1 : ℝ)^2 ≤ ρ^3*(N : ℝ) := by
  have a := (primeSupport_mem hρ hρu k hb hk n).mp (mem_filter.mp hn).1
  obtain ⟨m,w,hw,_,_,hml,_,_,hmN⟩ := hk
  have b := (labels_mem N ρ k z.1 z.2).mp hz
  have c := (labels_mem N ρ k w.1 w.2).mp hw
  have hr : 0 < ρ := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_filter.mp hn).2.1.pos
  have hs0 : (0 : ℝ) < z.1 := by exact_mod_cast b.2.2.1.pos
  have ht0 : (0 : ℝ) < z.2 := by exact_mod_cast b.2.2.2.1.pos
  have ha : (n : ℝ) < ρ*m := by
    have hl := (max_le_iff.mp hml).1
    have hu := a.2.2.1
    rw [pow_succ] at hu
    nlinarith [mul_le_mul_of_nonneg_left hl hr.le]
  have hs : (z.1 : ℝ) < ρ*w.1 := by
    have hl := c.2.2.2.2.2.2.1
    have hu := b.2.2.2.2.2.2.2.1
    rw [pow_succ] at hu
    nlinarith [mul_le_mul_of_nonneg_left hl hr.le]
  have ht : (z.2 : ℝ) < ρ*w.2 := by
    have hl := c.2.2.2.2.2.2.2.2.1
    have hu := b.2.2.2.2.2.2.2.2.2.1
    rw [pow_succ] at hu
    nlinarith [mul_le_mul_of_nonneg_left hl hr.le]
  have hab := mul_lt_mul ha hs.le hs0 (hn0.trans ha).le
  have habc := mul_lt_mul hab ht.le ht0 ((mul_pos hn0 hs0).trans hab).le
  have hp : (n : ℝ)*z.1*z.2 < ρ^3*N := by
    calc
      _ < (ρ*m*(ρ*w.1))*(ρ*w.2) := habc
      _ = ρ^3*((m : ℝ)*(w.1*w.2 : ℕ)) := by push_cast; ring
      _ < _ := mul_lt_mul_of_pos_left hmN (pow_pos hr _)
  refine ⟨hp, ?_⟩
  have hord : (z.1 : ℝ) ≤ z.2 := by exact_mod_cast b.2.2.2.2.2.2.2.2.2.2
  have hh := mul_le_mul_of_nonneg_left hord (mul_pos hn0 hs0).le
  nlinarith only [hp,hh]

/-- The original alpha is literal, not the modern 4/53 carrier. -/
def relaxedPairs (N : ℕ) (ρ : ℝ) : Finset (ℕ × ℕ) :=
  ((range (N+1)) ×ˢ (range (N+1))).filter fun rs =>
    rs.1.Prime ∧ rs.2.Prime ∧ (N : ℝ)^(100/1327 : ℝ) ≤ rs.1 ∧
    (rs.1 : ℝ) < (N : ℝ)^(1/10 : ℝ) ∧ (N : ℝ)^(1/3 : ℝ) ≤ rs.2 ∧
    (rs.1 : ℝ)*(rs.2 : ℝ)^2 ≤ ρ^3*(N : ℝ)

theorem original_pair_prefix {N : ℕ} {e ρ : ℝ} (hN : 1 ≤ (N : ℝ))
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : ℕ × ℕ × ℕ}
    (hb : 3 ≤ ρ^k.1) (hk : Occupied N e ρ k)
    {n : ℕ} {z : ℕ × ℕ} (hn : n ∈ shortLabels N ρ k) (hz : z ∈ labels N ρ k) :
    (n,z.1) ∈ relaxedPairs N ρ ∧ z.2.Prime ∧
      (z.2 : ℝ) ≤ ρ^3*(N : ℝ)/((n : ℝ)*z.1) := by
  have a := (primeSupport_mem hρ hρu k hb hk n).mp (mem_filter.mp hn).1
  have b := (labels_mem N ρ k z.1 z.2).mp hz
  have hp := (mem_filter.mp hn).2.1
  have hg := original_enlarged_geometry hρ hρu hb hk hn hz
  have hnu : n ≤ N := by
    have hpow : (N : ℝ)^(1/10 : ℝ) ≤ N := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1/10 : ℝ) ≤ 1)
    exact_mod_cast a.2.2.2.le.trans hpow
  refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hnu),
    mem_range.mpr (Nat.lt_succ_of_le b.1)⟩,hp,b.2.2.1,a.2.1,a.2.2.2,b.2.2.2.2.2.1,hg.2⟩,
    b.2.2.2.1,?_⟩
  apply (le_div_iff₀ (show 0 < (n : ℝ)*z.1 by exact_mod_cast Nat.mul_pos hp.pos b.2.2.1.pos)).mpr
  nlinarith only [hg.1]

end OriginalU8
