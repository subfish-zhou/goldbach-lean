import MathlibNt.SieveTheory.LiLiuGoldbachG11GridGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleFibres
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantDiscrepancy

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The natural absolute difference retains overhanging and zero outputs. -/
theorem goldbachG11Grid_natAbs_support {N : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ)
    {v : ℕ × ℕ} (hv : v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k) :
    ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs ≤ 4*N := by
  obtain ⟨hm,hp⟩ := mem_product.mp hv
  have h := goldbachG11Grid_pair_product_bound hρ hρu hbig hk hm hp
  omega

/-- A literal modulus-by-modulus remainder majorant on every occupied G11
rectangle. The imported finite-fibre lemma supplies the mass and centre bounds. -/
theorem goldbachG11Grid_remainder_majorant {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ε ρ : ℝ,
      1 < ρ → ρ ≤ 5/4 → 4 ≤ (N : ℝ)^(4/53 : ℝ) →
      ∀ k ∈ goldbachG11GridUsed N ε ρ, ∀ d : ℕ, 0 < d → d ≤ N →
      |bilinearDiscrepancy (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k)
        (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
        (fun p => if p.Coprime N then primeSWBeta p else 0) N d| ≤
        C*(N : ℝ)^(1+κ)/(d.totient : ℝ) := by
  obtain ⟨C₀,hC₀,hfib⟩ := goldbachG11Rectangle_fibres_subpower hκ
  refine ⟨8000*C₀*(5 : ℝ)^κ,by positivity,?_⟩
  intro N hN ε ρ hρ hρu hbig k hk d hd hdN
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h := fouvryG9RemainderMajorant_discrepancy
    (goldbachG11GridLong N ε ρ k) (goldbachG11GridShort N ρ k)
    (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
    (fun p => if p.Coprime N then primeSWBeta p else 0) N hN
    (800*C₀*(5*(N : ℝ))^κ) (by positivity)
    (fun v _ => goldbachG11RectangleWeight_nonneg N v)
    (fun v hv => goldbachG11Grid_natAbs_support hρ hρu hbig hk hv)
    (fun r hr => hfib N _ _ r hr) d hd hdN
  calc
    _ ≤ 10*(800*C₀*(5*(N : ℝ))^κ)*(N : ℝ)/(d.totient : ℝ) := h
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hn.le,
        Real.rpow_add hn,Real.rpow_one]
      ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig