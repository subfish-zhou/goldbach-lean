import HighCrossFinite
import MathlibNt.Wu2008DoubleSieve.ReboxingNormalization

namespace HighCross
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- A finite cover retains every original prime label. Overlap may only
increase the positive upper sum; no remainder absolute value is restricted. -/
theorem finite_cover_count_le {β : Type*} [DecidableEq β]
    (B : Finset β) (S : Finset ℕ) (P : β → Finset ℕ)
    (f : ℕ → ℝ) (g : β → ℕ → ℝ)
    (hg : ∀ b ∈ B, ∀ p, 0 ≤ g b p)
    (hcover : ∀ p ∈ S, ∃ b ∈ B, p ∈ P b ∧ f p ≤ g b p) :
    ∑ p ∈ S, f p ≤ ∑ b ∈ B, ∑ p ∈ P b, g b p := by
  calc
    _ ≤ ∑ p ∈ S, ∑ b ∈ B, if p ∈ P b then g b p else 0 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨b,hb,hpB,hfg⟩ := hcover p hp
      have hone : (if p ∈ P b then g b p else 0) ≤
          ∑ c ∈ B, if p ∈ P c then g c p else 0 :=
        single_le_sum (f := fun c => if p ∈ P c then g c p else 0)
          (fun c hc => by split_ifs; exact hg c hc p; exact le_rfl) hb
      rw [if_pos hpB] at hone
      exact hfg.trans hone
    _ = ∑ b ∈ B, ∑ p ∈ S, if p ∈ P b then g b p else 0 := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro b hb
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (mem_filter.mp hp).2
      · intro p _ _
        exact hg b hb p

/-- Literal Buchstab raw mass is bounded by actual inserted Phi counts,
not by independent coefficient suprema or a substituted asymptotic kernel. -/
theorem buchstab_raw_le_inserted {i N : ℕ} {δ s t : ℝ}
    {β : Type*} [DecidableEq β] (W : Fin i → Finset ℕ)
    (B : Finset β) (P : β → Finset ℕ) (u : β → ℝ)
    (hcover : ∀ d ∈ boxConvolutionSupport W,
      ∀ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∃ b ∈ B, p ∈ P b ∧ wuLocalCutoff N δ (d*p) (u b) ≤ (p : ℝ)) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        (sourceSieveCount N (d*p) ((d*p)*N) p : ℝ)) ≤
      ∑ b ∈ B, wuBoxPhi N δ (Fin.cons (P b) W) (u b) := by
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ b ∈ B, ∑ p ∈ P b,
          (sourceSieveCount N (d*p) ((d*p)*N) (wuLocalCutoff N δ (d*p) (u b)) : ℝ) := by
      apply sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply finite_cover_count_le
      · intro b _ p
        unfold sourceSieveCount
        positivity
      · intro p hp
        obtain ⟨b,hb,hpB,hcut⟩ := hcover d hd p hp
        refine ⟨b,hb,hpB,?_⟩
        exact_mod_cast sourceSieveCount_antitone N (d*p) ((d*p)*N) hcut
    _ = _ := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      simpa only [mul_sum] using (wuBoxPhi_cons N δ (u b) (P b) W).symm

/-- An actual count cross-lower, with every inserted upper gain added once.
Only finite geometric covering and already constructed arithmetic bounds occur. -/
theorem cross_lower_from_counts {i N : ℕ} {δ ε C s t : ℝ}
    {β : Type*} [DecidableEq β] (W : Fin i → Finset ℕ)
    (B : Finset β) (P : β → Finset ℕ) (u R G : β → ℝ)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 ≤ (N : ℝ)^(1/2-δ)/d)
    (hs : 0 < s) (hst : s ≤ t)
    (hcover : ∀ d ∈ boxConvolutionSupport W,
      ∀ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∃ b ∈ B, p ∈ P b ∧ wuLocalCutoff N δ (d*p) (u b) ≤ (p : ℝ))
    (hupper : ∀ b ∈ B, wuBoxPhi N δ (Fin.cons (P b) W) (u b) ≤ R b - G b)
    (hlower : LowerSourcePaid N δ ε C t W) :
    convolutionRosserMain N W false (wuVariableRosserLevel N δ)
        (fun d => wuLocalCutoff N δ d t) - C*N/log (N : ℝ)^(18 : ℝ) -
      (∑ b ∈ B, R b) + (∑ b ∈ B, G b) ≤ wuBoxPhi N δ W s := by
  have hbuch := wuBoxPhi_buchstab W hQ hs hst
  have hraw := buchstab_raw_le_inserted W B P u hcover
  have hu := sum_le_sum hupper
  rw [sum_sub_distrib] at hu
  have hl := hlower.2
  linarith

/-- Closed Phi pays its genuine original endpoint once after cross transport. -/
theorem cross_lower_closed {i N : ℕ} {δ ε C s t : ℝ}
    {β : Type*} [DecidableEq β] (W : Fin i → Finset ℕ)
    (B : Finset β) (P : β → Finset ℕ) (u R G : β → ℝ)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 ≤ (N : ℝ)^(1/2-δ)/d)
    (hs : 0 < s) (hst : s ≤ t)
    (hcover : ∀ d ∈ boxConvolutionSupport W,
      ∀ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∃ b ∈ B, p ∈ P b ∧ wuLocalCutoff N δ (d*p) (u b) ≤ (p : ℝ))
    (hupper : ∀ b ∈ B, wuBoxPhi N δ (Fin.cons (P b) W) (u b) ≤ R b - G b)
    (hlower : LowerSourcePaid N δ ε C t W) (hend : PhiEndpointPaid N δ ε s W) :
    convolutionRosserMain N W false (wuVariableRosserLevel N δ)
        (fun d => wuLocalCutoff N δ d t) - C*N/log (N : ℝ)^(18 : ℝ) -
      (∑ b ∈ B, R b) + (∑ b ∈ B, G b) -
      ε * boxTheta N ((N : ℝ)^(1/2-δ)) W ≤ wuBoxPhiLE N δ W s := by
  have hc := cross_lower_from_counts W B P u R G hQ hs hst hcover hupper hlower
  have he := hend.2
  linarith

end
end HighCross
