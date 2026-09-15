import Wu08FourMainEpsilon
import Wu08SmallWeightedQuadrature

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace Wu08FirstPrimeFour.SmallGrid
open Normalization

/-- Physical rectangular enlargement; in particular no fixed prefix xi is
sent to zero by choosing N. Both product faces are kept explicit. -/
theorem rectangle_faces {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k : Key}
    (hk : k ∈ occupied N e ξ ρ) (hbig : 3 ≤ ρ^k.1)
    {t : Long} (ht : t ∈ longCell N e ξ ρ k)
    {a : ℕ} (ha : a ∈ shortCell ρ k) :
    LastPrimeFour.z N/ρ ≤ (a : ℝ) ∧
      (a : ℝ) < ρ*(N : ℝ)^(1/10 : ℝ) ∧ (a : ℝ) < ρ*t.1 ∧
      (a : ℝ)*(longProduct t : ℝ) < ρ*N ∧
      ξ*N < ρ*((a : ℝ)*(longProduct t : ℝ)) := by
  have hr : 0 < ρ := by linarith
  obtain ⟨hal,hau⟩ := (shortCell_mem hρ hρu k hbig a).mp ha
  obtain ⟨htL,_,_,_,hAb,hprod,hprefix⟩ := mem_filter.mp ht
  have hm : 0 < (longProduct t : ℝ) := by
    obtain ⟨hb,hc,hd,hn⟩ := longLabels_positive htL
    unfold longProduct
    positivity
  obtain ⟨x,hx,hkey⟩ := mem_image.mp hk
  obtain ⟨_,_,hz,hu,_,_,_⟩ := positive_data hx
  obtain ⟨hwl,hwu,_,_⟩ := grid_bounds hρ hx
  rw [hkey] at hwl hwu
  rw [pow_succ] at hau hwu hprefix
  have hAl : LastPrimeFour.z N ≤ ρ*ρ^k.1 := by nlinarith only [hz,hwu.le]
  have hAu : ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ) := hwl.trans hu
  refine ⟨(div_le_iff₀ hr).mpr ?_,?_,?_,?_,?_⟩
  · exact hAl.trans (by nlinarith only [mul_le_mul_of_nonneg_left hal hr.le])
  · exact hau.trans_le (by nlinarith only [mul_le_mul_of_nonneg_left hAu hr.le])
  · exact hau.trans (by nlinarith only [mul_lt_mul_of_pos_left hAb hr])
  · have h1 := mul_lt_mul_of_pos_right hau hm
    have h2 := mul_lt_mul_of_pos_left hprod hr
    nlinarith only [h1,h2]
  · have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hal hm.le) hr.le
    nlinarith only [hprefix,hh]

/-- Half-open real boxes admit a unique index; this pays no diagonal by
measure-zero reasoning and applies to every integer in the rectangle. -/
theorem index_unique {ρ x : ℝ} (hρ : 1 < ρ) {i j : ℕ}
    (hi : ρ^i ≤ x ∧ x < ρ^(i+1)) (hj : ρ^j ≤ x ∧ x < ρ^(j+1)) : i=j := by
  apply le_antisymm
  · by_contra h
    have hh : j+1 ≤ i := by omega
    have hp := pow_le_pow_right₀ hρ.le hh
    linarith only [hi.1,hj.2,hp]
  · by_contra h
    have hh : i+1 ≤ j := by omega
    have hp := pow_le_pow_right₀ hρ.le hh
    linarith only [hj.1,hi.2,hp]

theorem rectangle_key_unique {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) {k l : Key}
    (hkbig : 3 ≤ ρ^k.1) (hlbig : 3 ≤ ρ^l.1)
    {t : Long} (htk : t ∈ longCell N e ξ ρ k) (htl : t ∈ longCell N e ξ ρ l)
    {a : ℕ} (hak : a ∈ shortCell ρ k) (hal : a ∈ shortCell ρ l) : k=l := by
  apply Prod.ext
  · exact index_unique hρ ((shortCell_mem hρ hρu k hkbig a).mp hak)
      ((shortCell_mem hρ hρu l hlbig a).mp hal)
  · exact index_unique hρ ⟨(mem_filter.mp htk).2.1,(mem_filter.mp htk).2.2.1⟩
      ⟨(mem_filter.mp htl).2.1,(mem_filter.mp htl).2.2.1⟩

/-- Capped only outside the target endpoint; on the original small domain
this is exactly Wu's 36/5/(1-x), not the constant upper bound eight. -/
def atomWeight (N a : ℕ) : ℝ :=
  (36/5)/(1-min (log (a : ℝ)/log N) (1/10))

theorem atomWeight_nonneg (N a : ℕ) : 0 ≤ atomWeight N a := by
  unfold atomWeight
  apply div_nonneg (by norm_num)
  linarith [min_le_right (log (a : ℝ)/log N) (1/10 : ℝ)]

theorem cellWeight_le_atomWeight {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hN : (4 : ℝ) ≤ N) (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    {k : Key} (hk : k ∈ occupied N e ξ ρ) (hbig : 3 ≤ ρ^k.1)
    {a : ℕ} (ha : a ∈ shortCell ρ k) : cellWeight N ρ k ≤ atomWeight N a := by
  have hg := occupied_geometry hξ hρ hρu hk
  have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
  obtain ⟨_,hu,_⟩ := level_log_geometry (δ := 0) hN hT hg.2.2.2.2
  have hal := ((shortCell_mem hρ hρu k hbig a).mp ha).1
  have ht0 : 0 < (2/3 : ℝ)*ρ^k.1 := by linarith
  have hTa : (2/3 : ℝ)*ρ^k.1 ≤ (a : ℝ) := by linarith
  have hcoord : cellCoord N ρ k ≤ log (a : ℝ)/log N :=
    div_le_div_of_nonneg_right (log_le_log ht0 hTa) (log_nonneg (by linarith))
  have hm := le_min hcoord hu
  unfold cellWeight atomWeight
  exact div_le_div_of_nonneg_left (by norm_num)
    (by linarith [min_le_right (log (a : ℝ)/log N) (1/10 : ℝ)]) (by linarith)

#print axioms rectangle_faces
#print axioms rectangle_key_unique
#print axioms cellWeight_le_atomWeight
end Wu08FirstPrimeFour.SmallGrid
