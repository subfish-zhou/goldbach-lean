import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9RectangleC2

noncomputable section
open Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Absolute integer differences allow overhanging positive rectangles,
including zero values, without truncated natural subtraction. -/
theorem g9IntegerFibre_dvd_iff (a : ℤ) (q m n : ℕ) :
    q ∣ (a-(m : ℤ)*n).natAbs ↔ Int.ModEq q ((m : ℤ)*n) a := by
  rw [← Int.natCast_dvd, Int.modEq_iff_dvd]

/-- On the original product window this is literally the original natural difference. -/
theorem g9IntegerFibre_original (N m n : ℕ) (h : m*n ≤ N) :
    ((N : ℤ)-(m : ℤ)*n).natAbs = N-m*n := by
  rw [← Nat.cast_mul, ← Nat.cast_sub h]
  simp

/-- Weighted divisibility mass on the actual product-indexed sequence. -/
def g9IntegerFibreDivisibility (U V : Finset ℕ) (α β : ℕ → ℝ) (a : ℤ) (q : ℕ) : ℝ :=
  ∑ p ∈ U ×ˢ V, if q ∣ (a-(p.1 : ℤ)*p.2).natAbs then α p.1*β p.2 else 0

theorem g9IntegerFibreDivisibility_eq (U V : Finset ℕ) (α β : ℕ → ℝ) (a : ℤ) (q : ℕ) :
    g9IntegerFibreDivisibility U V α β a q =
      ∑ m ∈ U, ∑ n ∈ V, if Int.ModEq q ((m : ℤ)*n) a then α m*β n else 0 := by
  unfold g9IntegerFibreDivisibility
  rw [sum_product]
  simp only [g9IntegerFibre_dvd_iff]

/-- The center remains the true coprime mass, not a new scalar-density hypothesis. -/
def g9IntegerFibreCenter (U V : Finset ℕ) (α β : ℕ → ℝ) (q : ℕ) : ℝ :=
  (∑ m ∈ U, ∑ n ∈ V, if (m*n).Coprime q then α m*β n else 0)/(q.totient : ℝ)

theorem g9IntegerFibre_centered_eq (U V : Finset ℕ) (α β : ℕ → ℝ) (a : ℤ) (q : ℕ) :
    g9IntegerFibreDivisibility U V α β a q-g9IntegerFibreCenter U V α β q =
      bilinearDiscrepancy U V α β a q := by
  rw [g9IntegerFibreDivisibility_eq]
  rfl

theorem g9IntegerFibre_signedError (U V Q : Finset ℕ) (α β c : ℕ → ℝ) (a : ℤ) :
    (∑ q ∈ reducedModuli Q a, c q *
      (g9IntegerFibreDivisibility U V α β a q-g9IntegerFibreCenter U V α β q)) =
      signedError U V Q α β c a := by
  simp only [g9IntegerFibre_centered_eq, signedError]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
