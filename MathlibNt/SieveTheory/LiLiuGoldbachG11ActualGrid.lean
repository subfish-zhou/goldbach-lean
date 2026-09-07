import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleCover
import MathlibNt.SieveTheory.LiLiuGoldbachG11EffectiveProductSupport
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridIndex
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9IntervalEndpoints

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The first coordinate is the short-prime cell, the second the long-product cell. -/
def goldbachG11GridKey (ρ : ℝ) (v : ℕ × ℕ) : ℕ × ℕ :=
  (fouvryG9GridIndex ρ v.2, fouvryG9GridIndex ρ v.1)

def goldbachG11GridUsed (N : ℕ) (ε ρ : ℝ) : Finset (ℕ × ℕ) :=
  (goldbachG11PrimeProductAtoms N ε).image (goldbachG11GridKey ρ)

/-- Long coefficient support uses only geometry and roughness, never output primality. -/
def goldbachG11GridLong (N : ℕ) (ε ρ : ℝ) (k : ℕ × ℕ) : Finset ℕ :=
  (goldbachG11EffectiveProductSupport N ε).filter fun m =>
    ρ^k.2 ≤ (m : ℝ) ∧ (m : ℝ) < ρ^(k.2+1) ∧ ρ^k.1 ≤ (m.minFac : ℝ)

/-- Exact integer encoding of the short half-open cell, clipped at the original lower cutoff. -/
def goldbachG11GridShort (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ) : Finset ℕ :=
  primeSWInterval ((⌈max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ))⌉ : ℝ)-1)
    ((⌈ρ^(k.1+1)⌉ : ℝ)-1)

/-- Actual occupied atoms supply both logarithmic cells and their original strict window. -/
theorem goldbachG11GridUsed_witness {N : ℕ} {ε ρ : ℝ} (hρ : 1 < ρ)
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ) :
    ∃ m p : ℕ, m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ∧
      p ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m ∧
      ρ^k.1 ≤ (p : ℝ) ∧ (p : ℝ) < ρ^(k.1+1) ∧
      ρ^k.2 ≤ (m : ℝ) ∧ (m : ℝ) < ρ^(k.2+1) := by
  obtain ⟨⟨m,p⟩, hv, rfl⟩ := mem_image.mp hk
  obtain ⟨hmv, hpF⟩ := mem_filter.mp hv
  have hm := (mem_product.mp hmv).1
  have hm0 := (goldbachG11ProductSupport_data hm).1
  have hp := (mem_goldbachG11ProductFirstPrimeFiber_iff.mp hpF).1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  exact ⟨m,p,hm,hpF,(fouvryG9GridIndex_bounds hρ hp1).1,
    (fouvryG9GridIndex_bounds hρ hp1).2,(fouvryG9GridIndex_bounds hρ hm1).1,
    (fouvryG9GridIndex_bounds hρ hm1).2⟩

theorem goldbachG11GridUsed_short_gates {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ) :
    3 ≤ ρ^k.1 ∧ max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ)) ≤ ρ^(k.1+1) ∧
      ρ^(k.1+1) ≤ (4/3 : ℝ)*ρ^k.1 := by
  obtain ⟨m,p,_hm,hpF,hplo,hphi,_⟩ := goldbachG11GridUsed_witness hρ hk
  have hpz := (mem_goldbachG11ProductFirstPrimeFiber_iff.mp hpF).2.2.1
  have hT : 0 < ρ^k.1 := pow_pos (by linarith) _
  rw [pow_succ] at hphi ⊢
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · exact (max_le hplo hpz).trans hphi.le
  · nlinarith

def goldbachG11GridPrimeInterval {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    (k : ℕ × ℕ) (hk : k ∈ goldbachG11GridUsed N ε ρ) : PrimeC2Interval :=
  g9PrimeHalfOpenInterval (ρ^k.1) (max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ))) (ρ^(k.1+1))
    (goldbachG11GridUsed_short_gates hρ hρu hbig hk).1 (le_max_left _ _)
    (goldbachG11GridUsed_short_gates hρ hρu hbig hk).2.1
    (goldbachG11GridUsed_short_gates hρ hρu hbig hk).2.2

theorem goldbachG11GridShort_mem_iff {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ) (p : ℕ) :
    p ∈ goldbachG11GridShort N ρ k ↔
      max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) < ρ^(k.1+1) :=
  mem_g9PrimeHalfOpenInterval (ρ^k.1) (max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ)))
    (ρ^(k.1+1)) (goldbachG11GridUsed_short_gates hρ hρu hbig hk).1 (le_max_left _ _)
    (goldbachG11GridUsed_short_gates hρ hρu hbig hk).2.1
    (goldbachG11GridUsed_short_gates hρ hρu hbig hk).2.2 p

/-- Every actual prime/product atom, including closed arithmetic boundaries, is covered. -/
theorem goldbachG11_actual_grid_cover {N : ℕ} {ε ρ : ℝ} (hN : 2 ≤ N)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {m p : ℕ} (hm : m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)))
    (hpF : p ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m) :
    ∃ k ∈ goldbachG11GridUsed N ε ρ,
      m ∈ goldbachG11GridLong N ε ρ k ∧ p ∈ goldbachG11GridShort N ρ k := by
  obtain ⟨hp, _hpN, hpz, hpmin, _hε, hprod, _hout⟩ :=
    mem_goldbachG11ProductFirstPrimeFiber_iff.mp hpF
  have hm0 := (goldbachG11ProductSupport_data hm).1
  have hpm : p ≤ p*m := by simpa using Nat.mul_le_mul_left p hm0
  have hv : (m,p) ∈ goldbachG11PrimeProductAtoms N ε :=
    mem_filter.mpr ⟨mem_product.mpr ⟨hm,mem_range.mpr (hpm.trans_lt hprod)⟩,hpF⟩
  let k := goldbachG11GridKey ρ (m,p)
  have hk : k ∈ goldbachG11GridUsed N ε ρ := mem_image.mpr ⟨(m,p),hv,rfl⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hmb := fouvryG9GridIndex_bounds hρ hm1
  have hpb := fouvryG9GridIndex_bounds hρ hp1
  refine ⟨k,hk,?_,(goldbachG11GridShort_mem_iff hρ hρu hbig hk p).2 ?_⟩
  · apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨hm,goldbachG11_product_active_bounds hN hm hpF⟩,hmb.1,hmb.2,?_⟩
    exact hpb.1.trans (by exact_mod_cast hpmin)
  · exact ⟨max_le hpb.1 hpz,hpb.2⟩

/-- The coverage premise is now supplied for the original good G11 count. -/
theorem goldbachG11GoodSwitchedTotal_le_actual_grid {N : ℕ} {ε ρ : ℝ}
    (hN : 2 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ)) :
    (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      ∑ k ∈ goldbachG11GridUsed N ε ρ,
        goldbachG11RectanglePrimeMass N (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k) :=
  goldbachG11GoodSwitchedTotal_le_rectanglePrimeMass_cover N ε _ _ _
    (fun _ hm _ hp => goldbachG11_actual_grid_cover hN hρ hρu hbig hm hp)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig