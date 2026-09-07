import MathlibNt.SieveTheory.LiLiuGoldbachG11OrdinaryGridGeometry

open Finset Filter
open scoped BigOperators Classical
open Wu2004MeanValue
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Two complete ordinary prime-centered prefixes, with the original G11
coefficient. The main term here counts all short primes, not prime/copN. -/
def goldbachG11OrdinaryRectangleResidual (N : ℕ) (ε ρ : ℝ) (k : ℕ × ℕ) (d b : ℕ) : ℝ :=
  primeCenteredAPSum (goldbachG11GridLong N ε ρ k)
    (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ)) (fun _ => goldbachG11GridProfileHi ρ k) d b -
  primeCenteredAPSum (goldbachG11GridLong N ε ρ k)
    (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ)) (fun _ => goldbachG11GridProfileLo N ρ k) d b

/-- Reuse the frozen ordinary source at size 4N. All endpoint and coefficient
conditions are supplied; the residues remain arbitrary reduced residues. -/
theorem goldbachG11OrdinaryRectangleResidual_weighted (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε ρ : ℝ, 1 < ρ → ρ ≤ 5/4 →
      ∀ k ∈ goldbachG11GridUsed N ε ρ, ∀ (Q : ℕ) (b : ℕ → ℕ),
      (Q : ℝ) ≤ Real.sqrt (4*(N : ℝ))/Real.log (4*(N : ℝ))^B →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d*|goldbachG11OrdinaryRectangleResidual N ε ρ k d (b d)|) ≤
        C*(N : ℝ)/Real.log (4*(N : ℝ))^A := by
  obtain ⟨B,C,hB,hC,M,hs⟩ := balanced_common_profile_primeCentered_natural A (2/53) 400 hA
    (by norm_num) (by norm_num)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨B,8*C,hB,by positivity,max 4 (max M K),le_max_left _ _,?_⟩
  intro N hN ε ρ hρ hρu k hk Q b hQ hb
  have hn4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hnM : M ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hnK : K ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  have hnsource : M ≤ 4*N := by omega
  have hbig := hK N hnK
  let U := goldbachG11GridLong N ε ρ k
  let α := fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) m : ℝ)
  have hQ' : (Q : ℝ) ≤ Real.sqrt ((4*N : ℕ) : ℝ)/Real.log ((4*N : ℕ) : ℝ)^B := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hQ
  have hsupport : ∀ m ∈ U, (((4*N : ℕ) : ℝ)^(2/53 : ℝ) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ ((4*N : ℕ) : ℝ)^(1-(2/53 : ℝ))) := by
    intro m hm
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using goldbachG11GridLong_balanced_fourN hn4 hm
  have hcoeff : ∀ m ∈ U, |α m| ≤ 400 := fun m _ => goldbachG11ProductCoefficient_abs_le_400 N m
  have hhi := hs (4*N) hnsource Q U α (fun _ => goldbachG11GridProfileHi ρ k) b hQ'
    hsupport hcoeff (fun m hm => by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using
        (goldbachG11Grid_profiles_fourN hρ hρu hbig hk hm).1) hb
  have hlo := hs (4*N) hnsource Q U α (fun _ => goldbachG11GridProfileLo N ρ k) b hQ'
    hsupport hcoeff (fun m hm => by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using
        (goldbachG11Grid_profiles_fourN hρ hρu hbig hk hm).2.1) hb
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d*
        (|primeCenteredAPSum U α (fun _ => goldbachG11GridProfileHi ρ k) d (b d)|+
         |primeCenteredAPSum U α (fun _ => goldbachG11GridProfileLo N ρ k) d (b d)|) := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (wuModulusWeight_nonneg d)
    _ = (∑ d ∈ Icc 1 Q,wuModulusWeight d*|primeCenteredAPSum U α (fun _ => goldbachG11GridProfileHi ρ k) d (b d)|)+
        ∑ d ∈ Icc 1 Q,wuModulusWeight d*|primeCenteredAPSum U α (fun _ => goldbachG11GridProfileLo N ρ k) d (b d)| := by
      simp only [mul_add,sum_add_distrib]
    _ ≤ C*((4*N : ℕ) : ℝ)/Real.log ((4*N : ℕ) : ℝ)^A+
        C*((4*N : ℕ) : ℝ)/Real.log ((4*N : ℕ) : ℝ)^A := add_le_add hhi hlo
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_ofNat]; ring

/-- Unweight only squarefree moduli and keep the on-carrier residue equal to N. -/
theorem goldbachG11OrdinaryRectangleResidual_squarefree (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε ρ : ℝ, 1 < ρ → ρ ≤ 5/4 →
      ∀ k ∈ goldbachG11GridUsed N ε ρ, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt (4*(N : ℝ))/Real.log (4*(N : ℝ))^B →
      (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG11OrdinaryRectangleResidual N ε ρ k d N|) ≤
        C*(N : ℝ)/Real.log (4*(N : ℝ))^A := by
  obtain ⟨B,C,hB,hC,M,hM,hs⟩ := goldbachG11OrdinaryRectangleResidual_weighted A hA
  refine ⟨B,C,hB,hC,M,hM,?_⟩
  intro N hN ε ρ hρ hρu k hk Q hQ
  have h := hs N hN ε ρ hρ hρu k hk Q (goldbachG11LinkedCompletedResidue N) hQ
    (fun d _ => goldbachG11LinkedCompletedResidue_coprime N d)
  calc
    _ ≤ ∑ d ∈ goldbachG11LinkedModuli N Q,wuModulusWeight d*
        |goldbachG11OrdinaryRectangleResidual N ε ρ k d (goldbachG11LinkedCompletedResidue N d)| := by
      apply sum_le_sum
      intro d hd
      obtain ⟨_,hsq,hcop⟩ := mem_filter.mp hd
      rw [goldbachG11LinkedCompletedResidue_eq hcop]
      exact le_mul_of_one_le_left (abs_nonneg _) (goldbachG11Linked_one_le_weight hsq)
    _ ≤ ∑ d ∈ Icc 1 Q,wuModulusWeight d*
        |goldbachG11OrdinaryRectangleResidual N ε ρ k d (goldbachG11LinkedCompletedResidue N d)| := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset _ _
      · intro d _ _
        exact mul_nonneg (wuModulusWeight_nonneg d) (abs_nonneg _)
    _ ≤ _ := h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig