import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelMeshLimit

open Set

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11PrimeKernel_le_integral_eventually (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG11PrimeKernel h N ≤ goldbachG11PrimeIntegral h + ν := by
  have hhalf : 0 < ν / 2 := half_pos hν
  obtain ⟨n, hn⟩ := goldbachG11MeshUpperSum_exists_le_integral h hh hpos (ν / 2) hhalf
  obtain ⟨N₀, hN₀, hbound⟩ := goldbachG11PrimeKernel_le_fixedCover_eventually
    (goldbachG11MeshCells n) h hpos (goldbachG11MeshLo n) (goldbachG11MeshHi n)
    (goldbachG11MeshCoeff h n)
    (fun _ _ _ => goldbachG11MeshPoint_pos _ _)
    (fun _ _ _ => goldbachG11MeshPoint_strictMono n (Nat.lt_succ_self _))
    (fun j _ => goldbachG11MeshCoeff_nonneg h hh hpos n j)
    (fun j _ _ hr _ hq => goldbachG11MeshCoeff_majorant h hh hpos n j hr hq)
    (fun N hN v hv => goldbachG11Mesh_prime_cover n N hN v hv) (ν / 2) hhalf
  refine ⟨N₀, hN₀, fun N hN => ?_⟩
  have he := hbound N hN
  change goldbachG11PrimeKernel h N ≤ goldbachG11MeshUpperSum h n + ν / 2 at he
  linarith

theorem goldbachG11PrimeKernel_one_le_integral_eventually (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG11PrimeKernel (fun _ => 1) N ≤ goldbachG11PrimeIntegral (fun _ => 1) + ν :=
  goldbachG11PrimeKernel_le_integral_eventually (fun _ => 1) continuousOn_const
    (fun _ _ => zero_le_one) ν hν

theorem goldbachG11PrimeKernel_author_le_integral_eventually (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG11PrimeKernel goldbachG11AuthorWeight N ≤
        goldbachG11PrimeIntegral goldbachG11AuthorWeight + ν :=
  goldbachG11PrimeKernel_le_integral_eventually goldbachG11AuthorWeight
    continuousOn_goldbachG11AuthorWeight (fun x _ => goldbachG11AuthorWeight_nonneg x) ν hν

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig