import WSrcFourRoot
import WSrcBuchstabRoot

noncomputable section
namespace WuSource.FourBuchstabAccepted
open Wu2008DoubleSieve Wu08OriginalFourWeights

def sourceCap : ℝ := SrcFour.fineCap (561522/1000000)

theorem original_pair_upper : original10+original11 ≤ sourceCap :=
  SrcFour.original_pair_fineCap (by norm_num) (by norm_num)
    (fun _ h => SrcBuchstab.buchstab_le_source_fine h)

theorem original_pair_lt_688 : original10+original11 < (86/125 : ℝ) :=
  SrcFour.original_pair_5616_conditional
    (fun _ h => (SrcBuchstab.buchstab_le_source_fine h).trans (by norm_num))

theorem actual_pair_upper {σ : ℝ} (hσ : 0 < σ) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        (sourceCap+σ)*U8CanonicalMother.M N :=
  SrcFour.actual_pair_fineCap (by norm_num) (by norm_num)
    (fun _ h => SrcBuchstab.buchstab_le_source_fine h) hσ

/-- Legacy mother gains are retained here; no full source G_i payment is asserted. -/
theorem ordinary_P2 {ζ dmax : ℝ} (hζ : 0 < ζ) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (SrcFour.replacementCoefficient (561522/1000000)-ζ)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  SrcFour.ordinary_P2_conditional (by norm_num) (by norm_num)
    (fun _ h => SrcBuchstab.buchstab_le_source_fine h) hζ hdmax

end WuSource.FourBuchstabAccepted
