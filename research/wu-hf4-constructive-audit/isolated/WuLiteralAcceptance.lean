import WR2ClassicalCertificate

theorem WuLiteralAcceptance :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ r ^ 5000 ≤ q ^ 4469 :=
  WuPaper.ClassicalSlots.one8938

theorem WuLegacyLiteralAcceptance :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ r ^ 500 ≤ q ^ 447 :=
  WuPaper.ClassicalSlots.one894

#print axioms WuLegacyLiteralAcceptance
#print axioms WuPaper.ClassicalSlots.one8938
#print axioms WuLiteralAcceptance
#print axioms WuPaper.ClassicalSlots.one894
#print axioms WuPaper.ClassicalSlots.classical_lower
