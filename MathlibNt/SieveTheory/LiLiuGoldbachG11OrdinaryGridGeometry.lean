import MathlibNt.SieveTheory.LiLiuGoldbachG11GridGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDistribution

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11GridProfileLo (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ) : ℝ :=
  (⌈max (ρ^k.1) ((N : ℝ)^(4/53 : ℝ))⌉ : ℝ)-1

def goldbachG11GridProfileHi (ρ : ℝ) (k : ℕ × ℕ) : ℝ :=
  (⌈ρ^(k.1+1)⌉ : ℝ)-1

theorem goldbachG11GridShort_eq_profiles (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ) :
    goldbachG11GridShort N ρ k =
      primeSWInterval (goldbachG11GridProfileLo N ρ k) (goldbachG11GridProfileHi ρ k) := rfl

/-- Move to analysis size 4N without changing the original coefficient or
residue N. The already proved eta=2/53 common-profile source fits this support. -/
theorem goldbachG11GridLong_balanced_fourN {N m : ℕ} {ε ρ : ℝ} {k : ℕ × ℕ}
    (hN : 4 ≤ N) (hm : m ∈ goldbachG11GridLong N ε ρ k) :
    (4*(N : ℝ))^(2/53 : ℝ) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ (4*(N : ℝ))^(1-(2/53 : ℝ)) := by
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hs := goldbachG11Linked_balanced_support (mem_filter.mp hm).1
  constructor
  · calc
      _ ≤ ((N : ℝ)^2)^(2/53 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
      _ = (N : ℝ)^(4/53 : ℝ) := by
        rw [← Real.rpow_natCast (N : ℝ) 2,← Real.rpow_mul hn0]
        norm_num
      _ ≤ _ := hs.1
  · calc
      _ ≤ (N : ℝ)^(1-(4/53 : ℝ)) := hs.2
      _ ≤ (N : ℝ)^(1-(2/53 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow hn0 (by linarith) (by norm_num)

/-- Both complete prime-count profiles obey the same enlarged-size budget. -/
theorem goldbachG11Grid_profiles_fourN {N m : ℕ} {ε ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hbig : 4 ≤ (N : ℝ)^(4/53 : ℝ))
    {k : ℕ × ℕ} (hk : k ∈ goldbachG11GridUsed N ε ρ)
    (hm : m ∈ goldbachG11GridLong N ε ρ k) :
    (2 ≤ goldbachG11GridProfileHi ρ k ∧
      (m : ℝ)*goldbachG11GridProfileHi ρ k ≤ 4*N) ∧
    (2 ≤ goldbachG11GridProfileLo N ρ k ∧
      (m : ℝ)*goldbachG11GridProfileLo N ρ k ≤ 4*N) ∧
    goldbachG11GridProfileLo N ρ k ≤ goldbachG11GridProfileHi ρ k := by
  let z := goldbachG11GridPrimeInterval hρ hρu hbig k hk
  have ht0 := goldbachG11Grid_short_scale_lower hρ hρu hk
  have ht : 2 ≤ z.scale := by change 2 ≤ (2/3 : ℝ)*ρ^k.1; linarith
  have hlo : 2 ≤ z.lower := ht.trans z.scale_le_lower
  have hhi : 2 ≤ z.upper := hlo.trans z.lower_le_upper
  have hmu := (goldbachG11GridLong_rectangle hρ hρu k hm).2
  have hmul := mul_le_mul hmu z.upper_le_twice (by linarith : 0 ≤ z.upper)
    (by positivity : 0 ≤ 2*ρ^k.2)
  have hx := (goldbachG11GridPhysicalScale_window hρ hρu hk).2
  have hh : (m : ℝ)*z.upper ≤ 4*N := by
    have he : 2*ρ^k.2*(2*z.scale) = goldbachG11GridPhysicalScale ρ k := by
      change 2*ρ^k.2*(2*((2/3 : ℝ)*ρ^k.1)) = _
      unfold goldbachG11GridPhysicalScale
      ring
    rw [he] at hmul
    exact hmul.trans hx
  have hl : (m : ℝ)*z.lower ≤ 4*N :=
    (mul_le_mul_of_nonneg_left z.lower_le_upper (Nat.cast_nonneg m)).trans hh
  exact ⟨⟨hhi,hh⟩,⟨hlo,hl⟩,z.lower_le_upper⟩

theorem goldbachG11ProductCoefficient_abs_le_400 (N m : ℕ) :
    |(goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ)| ≤ 400 := by
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast goldbachG11ProductCoefficient_le_four_hundred N m

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig