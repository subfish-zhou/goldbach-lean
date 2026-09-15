import Wu08LargeMassQuadrature

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour.Large

/-- The actual large-prime cardinalities at the original N and singular series.
All analytic and sieve tolerances are chosen before one common threshold. -/
theorem large_card_integral {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ e : Bool,
      ((large N e).card : ℝ) ≤ (8*I e+ε)*(wuSingularSeries N*N/log N^2) := by
  let H := I false+I true+10
  have h0 := integral_nonneg false
  have h1 := integral_nonneg true
  have hH : 0 < H := by dsimp [H]; linarith only [h0,h1]
  let η := min 1 (ε/H)
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε hH)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hbudget : η*H ≤ ε := (le_div_iff₀ hH).mp (min_le_right _ _)
  obtain ⟨T1,hT1,hs⟩ := coefficient_eight hη
  obtain ⟨T2,_,hm⟩ := actual_mass_integral_paid hη
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN he e
  have hn : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hS := wuSingularSeries_pos N hn
  have hscale : 0 ≤ wuSingularSeries N*N/log N^2 := by positivity
  have hi : I e+10 ≤ H := by cases e <;> dsimp [H] <;> linarith only [h0,h1]
  have hpay : (8+η)*(I e+η)+η ≤ 8*I e+ε := by
    have hp := mul_le_mul_of_nonneg_left hi hη.le
    have hsq := mul_le_mul_of_nonneg_left hη1 hη.le
    nlinarith only [hp,hsq,hbudget]
  have hp := mul_le_mul_of_nonneg_left (hm N (by omega) e)
    (show 0 ≤ (8+η)*wuSingularSeries N/log N by positivity)
  calc
    _ ≤ ((8+η)*wuSingularSeries N/log N)*(family N e).mass+
        η*(wuSingularSeries N*N/log N^2) := hs N (by omega) he e
    _ ≤ ((8+η)*wuSingularSeries N/log N)*((I e+η)*((N : ℝ)/log N))+
        η*(wuSingularSeries N*N/log N^2) := add_le_add hp le_rfl
    _ = ((8+η)*(I e+η)+η)*(wuSingularSeries N*N/log N^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpay hscale

theorem large_pair_integral {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((large N false).card : ℝ)+(large N true).card ≤
        (8*(I false+I true)+ε)*(wuSingularSeries N*N/log N^2) := by
  obtain ⟨T,hT,h⟩ := large_card_integral (show 0 < ε/2 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN he
  calc
    _ ≤ (8*I false+ε/2)*(wuSingularSeries N*N/log N^2)+
        (8*I true+ε/2)*(wuSingularSeries N*N/log N^2) :=
      add_le_add (h N hN he false) (h N hN he true)
    _ = _ := by ring

/-- Both large domains and the two actual prefixes are paid jointly. The same
positive xi is fixed before the shared threshold; no small-domain mass is assumed. -/
theorem large_prefix_joint {ε ξmax : ℝ} (hε : 0 < ε) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧ ∃ T : ℕ, 512 ≤ T ∧
      ∀ N : ℕ, T ≤ N → Even N →
        ((large N false).card : ℝ)+(large N true).card+
          (smallPrefix N false ξ).card+(smallPrefix N true ξ).card ≤
            (8*(I false+I true)+ε)*(wuSingularSeries N*N/log N^2) := by
  obtain ⟨ξ,hξ,hξu,T1,_,h1⟩ := Prefix.smallPrefix_pair_payment
    (show 0 < ε/2 by positivity) hmax
  obtain ⟨T2,hT2,h2⟩ := large_pair_integral (show 0 < ε/2 by positivity)
  refine ⟨ξ,hξ,hξu,max T1 T2,hT2.trans (le_max_right _ _),?_⟩
  intro N hN he
  have hp := h1 N (by omega) he
  have hl := h2 N (by omega) he
  linarith only [hp,hl]

/-- Literal properPairCore consumer: only the two unchanged small-first-prime
properMain terms remain. This theorem does not claim that their integrals are paid. -/
theorem properPairCore_large_prefix_paid {ε ξmax : ℝ} (hε : 0 < ε) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧ ∃ T : ℕ, 512 ≤ T ∧
      ∀ N : ℕ, T ≤ N → Even N → ∀ ρ δ η : ℝ,
        Normalization.properPairCore N ξ ρ δ η ≤
          Normalization.properMain N false ξ ρ δ η+
          Normalization.properMain N true ξ ρ δ η+
          (8*(I false+I true)+ε)*(wuSingularSeries N*N/log N^2) := by
  obtain ⟨ξ,hξ,hξu,T,hT,h⟩ := large_prefix_joint hε hmax
  refine ⟨ξ,hξ,hξu,T,hT,?_⟩
  intro N hN he ρ δ η
  have hp := h N hN he
  unfold Normalization.properPairCore
  linarith only [hp]

#print axioms large_card_integral
#print axioms large_pair_integral
#print axioms large_prefix_joint
#print axioms properPairCore_large_prefix_paid
end Wu08FirstPrimeFour.Large
