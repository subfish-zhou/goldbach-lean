import Wu08LargeCountTerminal

noncomputable section
open Real
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.Large

/-- Actual Q10+Q11 port after the large-first-prime and fixed-prefix payment.
The two original properMain terms and the pre-existing rectangle/raw exceptions
remain explicit; no unproved small-domain integral is supplied. -/
theorem original_pair_large_prefix_paid {σ ξmax : ℝ} (hσ : 0 < σ) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧
      ∀ (A : ℕ) (ρ ε δ η κ : ℝ),
      1 < ρ → ρ ≤ 5/4 → 0 < ε → ε < truncatedSixthLowerAlpha → ε < δ →
      δ < 1/2 → 0 < η → η < 1/8 → 0 < κ →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
        (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
          Normalization.properMain N false ξ ρ δ η+
          Normalization.properMain N true ξ ρ δ η+
          (8*(I false+I true)+σ)*(wuSingularSeries N*N/log N^2)+
          (N : ℝ)/log (N : ℝ)^A+κ*wuSingularSeries N*N/log N^2 := by
  obtain ⟨ξ,hξ,hξu,T,_,hpaid⟩ := properPairCore_large_prefix_paid hσ hmax
  refine ⟨ξ,hξ,hξu,?_⟩
  intro A ρ ε δ η κ hρ hρu hε hεa hεδ hδ hη hηu hκ
  have hξ1 : ξ ≤ 1 := (hξu.trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨N₀,hraw⟩ := Normalization.original_pair_paid_upper A hξ hξ1 hρ hρu
    hε hεa hεδ hδ hη hηu hκ
  refine ⟨max N₀ (T : ℝ),?_⟩
  intro N hN he
  have hNT : T ≤ N := by exact_mod_cast ((le_max_right N₀ (T : ℝ)).trans hN)
  have hp := hpaid N hNT he ρ δ η
  have hr := hraw N ((le_max_left _ _).trans hN) he
  linarith only [hp,hr]

#print axioms original_pair_large_prefix_paid
end Wu08FirstPrimeFour.Large
