import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossMesh

open Set

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Continuous nonnegative first-coordinate weights on the original cross.
The prime-to-box limit, mesh cover, and exact cross integral are all proved internally. -/
theorem goldbachG12PrimeKernel_le_integral_eventually (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG12PrimeKernel h N ≤ goldbachG12PrimeIntegral h + ν := by
  have hhalf : 0 < ν / 2 := half_pos hν
  obtain ⟨n, hn⟩ := goldbachG12MeshUpperSum_exists_le_integral h hh hpos (ν / 2) hhalf
  obtain ⟨N₀, hN₀, hbound⟩ := goldbachG12PrimeKernel_le_fixedCover_eventually
    (goldbachG12MeshCells n) h hpos (goldbachG12MeshLo n) (goldbachG12MeshHi n)
    (goldbachG11MeshCoeff h n)
    (fun j _ i => goldbachG12MeshLo_pos n j i)
    (fun j _ i => goldbachG12MeshLo_lt_hi n j i)
    (fun j _ => goldbachG11MeshCoeff_nonneg h hh hpos n j)
    (fun j _ _ hr _ hq => goldbachG11MeshCoeff_majorant h hh hpos n j hr hq)
    (fun N hN v hv => goldbachG12Mesh_prime_cover n N hN v hv) (ν / 2) hhalf
  refine ⟨N₀, hN₀, fun N hN => ?_⟩
  have he := hbound N hN
  change goldbachG12PrimeKernel h N ≤ goldbachG12MeshUpperSum h n + ν / 2 at he
  linarith

theorem goldbachG12PrimeKernel_one_le_integral_eventually (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG12PrimeKernel (fun _ => 1) N ≤ goldbachG12PrimeIntegral (fun _ => 1) + ν :=
  goldbachG12PrimeKernel_le_integral_eventually (fun _ => 1) continuousOn_const
    (fun _ _ => zero_le_one) ν hν

theorem goldbachG12PrimeKernel_author_le_integral_eventually (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG12PrimeKernel goldbachG11AuthorWeight N ≤
        goldbachG12PrimeIntegral goldbachG11AuthorWeight + ν :=
  goldbachG12PrimeKernel_le_integral_eventually goldbachG11AuthorWeight
    continuousOn_goldbachG11AuthorWeight (fun x _ => goldbachG11AuthorWeight_nonneg x) ν hν

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig