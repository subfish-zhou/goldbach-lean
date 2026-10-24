import WR2XiSourceNodePanels

noncomputable section
namespace WuPaper.R2Xi.SourceRational
open Real NodeExtension Finset WuTarget.W02
open scoped Classical

def panelTerm (S : ℝ) (k : Fin 9) (j : Fin 8) : ℝ :=
  let a := tailLeft S k
  let b := upperNode k
  if a < b then RationalCandidate.lowerH k *
    SourceLogChord.cell (SourceTailPanels.grid a b j) (SourceTailPanels.grid a b (j.val+1))
      (SourceLogRational.lower ((SourceTailPanels.grid a b j+1)/(S-1)))
      (SourceLogRational.lower ((SourceTailPanels.grid a b (j.val+1)+1)/(S-1)))
  else 0

theorem nodeLower_expansion (S : ℝ) : nodeLower S =
    (1105570288/1000000000000)*SourceLogRational.lower (4/(S-1))+
      ∑ k : Fin 9, ∑ j : Fin 8, panelTerm S k j := by
  unfold nodeLower
  congr 1
  apply sum_congr rfl
  intro k _
  unfold panelTerm SourceTailPanels.panels
  dsimp only
  split_ifs
  · simp [Fin.sum_univ_succ, Finset.sum_range_succ]
    ring
  · simp

/-- Numeric cells can be checked independently, then added without giant fractions. -/
theorem certificate {i : ℕ} (hi : 11 ≤ i) (hi29 : i ≤ 29)
    {s : ℝ} {q : Fin 9 → Fin 8 → ℝ}
    (hs : s ≤ (1105570288/1000000000000)*SourceLogRational.lower (4/(rNode i-1)))
    (hq : ∀ k j, q k j ≤ panelTerm (rNode i) k j) :
    s+(∑ k : Fin 9, ∑ j : Fin 8, q k j) ≤ extendedNode RationalCandidate.lowerH i := by
  apply le_trans _ (nodeLower_le_extended hi hi29)
  rw [nodeLower_expansion]
  exact add_le_add hs (sum_le_sum (fun k _ => sum_le_sum (fun j _ => hq k j)))

end WuPaper.R2Xi.SourceRational
#print axioms WuPaper.R2Xi.SourceRational.certificate
