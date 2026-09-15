import Wu08FirstPrimeFourOriginalSource
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantActual

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.Normalization

/-- The fifth factor is the short prime, not a replacement of the rough n. -/
theorem product_fibre (N : ℕ) (L : Finset Long) (V : Finset ℕ)
    (hL : ∀ t ∈ L, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2) (v : ℕ) :
    (∑ p ∈ products L ×ˢ V, if p.1*p.2=v then alpha L p.1*beta N p.2 else 0) ≤
      (fouvryTau 9 v : ℝ) := by
  have hb (a : ℕ) := fouvryG9_prime_copN_beta_bounds N a
  change ∀ a : ℕ, 0 ≤ beta N a ∧ beta N a ≤ (fouvryTau 1 a : ℝ) at hb
  have ha (m : ℕ) : alpha L m ≤ (fouvryTau 8 m : ℝ) :=
    (le_abs_self _).trans (alpha_order_eight L hL m)
  by_cases hv : v=0
  · subst v
    have hz : ∀ p ∈ products L ×ˢ V,
        (if p.1*p.2=0 then alpha L p.1*beta N p.2 else 0)=0 := by
      intro p _
      split_ifs with hp
      · rcases Nat.mul_eq_zero.mp hp with hm | hn
        · have hzero : alpha L p.1=0 := le_antisymm (by simpa [hm] using ha p.1) (alpha_nonneg _ _)
          simp [hzero]
        · have hzero : beta N p.2=0 := le_antisymm (by simpa [hn] using (hb p.2).2) (hb p.2).1
          simp [hzero]
      · rfl
    simp only [sum_congr rfl hz, sum_const_zero]
    positivity
  · rw [← sum_filter]
    calc
      _ ≤ ∑ p ∈ (products L ×ˢ V).filter (fun p => p.1*p.2=v),
          (fouvryTau 8 p.1 : ℝ)*(fouvryTau 1 p.2 : ℝ) := by
        apply sum_le_sum
        intro p _
        exact mul_le_mul (ha p.1) (hb p.2).2 (hb p.2).1 (Nat.cast_nonneg _)
      _ ≤ ∑ p ∈ v.divisorsAntidiagonal,
          (fouvryTau 8 p.1 : ℝ)*(fouvryTau 1 p.2 : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hp).2,hv⟩
        · intro p _ _; positivity
      _ = _ := by
        norm_cast
        rw [← ArithmeticFunction.mul_apply]
        congr 1
        simp only [fouvryTau, ← pow_add]

/-- Zero output is kept; the two preimage products may coincide at r=0. -/
theorem output_fibre (N : ℕ) (L : Finset Long) (V : Finset ℕ)
    (hL : ∀ t ∈ L, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2) (r : ℕ) :
    (∑ p ∈ products L ×ˢ V, if output N p.1 p.2=r then alpha L p.1*beta N p.2 else 0) ≤
      (fouvryTau 9 (N+r) : ℝ)+(fouvryTau 9 (N-r) : ℝ) := by
  calc
    _ ≤ ∑ p ∈ products L ×ˢ V,
        ((if p.1*p.2=N+r then alpha L p.1*beta N p.2 else 0)+
        (if p.1*p.2=N-r then alpha L p.1*beta N p.2 else 0)) := by
      apply sum_le_sum
      intro p _
      have hw := mul_nonneg (alpha_nonneg L p.1) (beta_nonneg N p.2)
      by_cases hh : output N p.1 p.2=r
      · obtain hp | hm := fouvryG9_natAbs_product_values N p.1 p.2 r hh
        · simp only [if_pos hh,if_pos hp]; split_ifs <;> linarith
        · simp only [if_pos hh,if_pos hm]; split_ifs <;> linarith
      · simp only [if_neg hh]; split_ifs <;> linarith
    _ = _ := sum_add_distrib
    _ ≤ _ := add_le_add (product_fibre N L V hL (N+r)) (product_fibre N L V hL (N-r))

/-- Fixed exponent constant BEFORE every long label set, interval and output. -/
theorem output_fibre_uniform {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ L : Finset Long, ∀ V : Finset ℕ,
      (∀ t ∈ L, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2) →
      ∀ r : ℕ, r ≤ 4*N →
      (∑ p ∈ products L ×ˢ V, if output N p.1 p.2=r then alpha L p.1*beta N p.2 else 0) ≤
        2*C*(5*(N : ℝ))^κ := by
  obtain ⟨C,hC,hτ⟩ := fouvryTau_le_const_rpow (k := 9) (by norm_num) hκ
  refine ⟨C,hC,?_⟩
  intro N L V hL r hr
  have ht : ∀ v : ℕ, v ≤ 5*N → (fouvryTau 9 v : ℝ) ≤ C*(5*(N : ℝ))^κ := by
    intro v hv
    by_cases hv0 : v=0
    · subst v; simp only [fouvryTau,ArithmeticFunction.map_zero,Nat.cast_zero]; positivity
    · exact (hτ v (Nat.pos_of_ne_zero hv0)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg v) (by exact_mod_cast hv) hκ.le) hC.le)
  have hplus := ht (N+r) (by omega)
  have hminus := ht (N-r) (by omega)
  have hf := output_fibre N L V hL r
  linarith

/-- Actual new rectangle support, obtained from its retained product face. -/
theorem cell_output_support {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : Key} (hbig : 3 ≤ ρ^k.1)
    {p : ℕ × ℕ} (hp : p ∈ products (longCell N e ξ ρ k) ×ˢ shortCell ρ k) :
    output N p.1 p.2 ≤ 4*N := by
  obtain ⟨hm,ha⟩ := mem_product.mp hp
  obtain ⟨t,ht,he⟩ := mem_image.mp hm
  obtain ⟨_,_,_,_,_,hface,_⟩ := mem_filter.mp ht
  have hshort := (shortCell_mem hρ hρu k hbig p.2).mp ha
  have hbound : (p.2 : ℝ) ≤ (5/4 : ℝ)*ρ^k.1 := by
    have hh := hshort.2
    rw [pow_succ] at hh
    nlinarith [pow_pos (by linarith : 0 < ρ) k.1]
  have hmult := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg p.1)
  rw [he] at hface
  have hprod : (p.1 : ℝ)*p.2 ≤ 4*N := by nlinarith
  have hnat : p.1*p.2 ≤ 4*N := by exact_mod_cast hprod
  unfold output
  omega

/-- Genuine inverse-totient bound for the new order-nine output fibres.
No density estimate or remainder hypothesis is an input. -/
theorem cell_remainder_majorant {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ e : Bool, ∀ ξ ρ : ℝ,
      1 < ρ → ρ ≤ 5/4 → ∀ k : Key, 3 ≤ ρ^k.1 →
      ∀ d : ℕ, 0 < d → d ≤ N →
      |bilinearDiscrepancy (products (longCell N e ξ ρ k)) (shortCell ρ k)
        (alpha (longCell N e ξ ρ k)) (beta N) N d| ≤ C*(N : ℝ)^(1+κ)/d.totient := by
  obtain ⟨C,hC,hfib⟩ := output_fibre_uniform hκ
  refine ⟨20*C*(5 : ℝ)^κ,by positivity,?_⟩
  intro N hN e ξ ρ hρ hρu k hbig d hd hdN
  let L := longCell N e ξ ρ k
  let V := shortCell ρ k
  have hh := fouvryG9RemainderMajorant_discrepancy (products L) V (alpha L) (beta N) N hN
    (2*C*(5*(N : ℝ))^κ) (by positivity)
    (fun p _ => mul_nonneg (alpha_nonneg L p.1) (beta_nonneg N p.2))
    (fun _ hp => cell_output_support hρ hρu hbig hp)
    (hfib N L V (fun t ht => longLabels_positive (mem_filter.mp ht).1)) d hd hdN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  convert hh using 1
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hn.le,Real.rpow_add hn,Real.rpow_one]
  ring

#print axioms product_fibre
#print axioms cell_remainder_majorant
end Wu08FirstPrimeFour.Normalization
