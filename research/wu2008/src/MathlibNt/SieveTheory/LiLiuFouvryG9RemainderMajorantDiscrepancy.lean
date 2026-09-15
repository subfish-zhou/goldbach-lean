import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantCounting

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A finite-fiber estimate for the literal coprime-centered discrepancy.
Neither label injectivity nor a total-mass assumption is required. -/
theorem fouvryG9RemainderMajorant_discrepancy
    (U V : Finset ℕ) (α β : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (J : ℝ) (hJ : 0 ≤ J)
    (hw : ∀ p ∈ U ×ˢ V, 0 ≤ α p.1*β p.2)
    (ha : ∀ p ∈ U ×ˢ V, ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs ≤ 4*N)
    (hf : ∀ r ≤ 4*N, (∑ p ∈ U ×ˢ V,
      if ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs = r then α p.1*β p.2 else 0) ≤ J)
    (d : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    |bilinearDiscrepancy U V α β N d| ≤ 10*J*(N : ℝ)/(d.totient : ℝ) := by
  classical
  let S := U ×ˢ V
  let a := fun p : ℕ × ℕ => ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs
  let w := fun p : ℕ × ℕ => α p.1*β p.2
  have hcount : ∀ q : ℕ, 0 < q → q ≤ N →
      (∑ p ∈ S, if q ∣ a p then w p else 0) ≤ 5*J*(N : ℝ)/q := by
    intro q hq hqN
    have h := fouvryG9RemainderMajorant_divCount S a w (4*N) q hq J ha hf
    have hc := fouvryG9RemainderMajorant_multipleCount hq hqN
    calc
      _ ≤ J*(((4*N)/q : ℕ)+1 : ℕ) := h
      _ ≤ J*(5*(N : ℝ)/q) := mul_le_mul_of_nonneg_left hc hJ
      _ = _ := by ring
  have hmass : (∑ p ∈ S, w p) ≤ 5*J*(N : ℝ) := by
    simpa only [one_dvd, if_true, Nat.cast_one, div_one] using hcount 1 (by omega) hN
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφd : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hA0 : 0 ≤ g9IntegerFibreDivisibility U V α β N d := by
    apply sum_nonneg
    intro p hp
    split_ifs
    · exact hw p hp
    · exact le_rfl
  have hA : g9IntegerFibreDivisibility U V α β N d ≤ 5*J*(N : ℝ)/(d.totient : ℝ) := by
    exact (hcount d hd hdN).trans
      (div_le_div_of_nonneg_left (by positivity) hφ hφd)
  have hB0 : 0 ≤ g9IntegerFibreCenter U V α β d := by
    apply div_nonneg _ hφ.le
    apply sum_nonneg
    intro m hm
    apply sum_nonneg
    intro n hn
    split_ifs
    · exact hw (m,n) (mem_product.mpr ⟨hm,hn⟩)
    · exact le_rfl
  have hB : g9IntegerFibreCenter U V α β d ≤ 5*J*(N : ℝ)/(d.totient : ℝ) := by
    apply div_le_div_of_nonneg_right _ hφ.le
    calc
      _ ≤ ∑ m ∈ U, ∑ n ∈ V, α m*β n := by
        apply sum_le_sum
        intro m hm
        apply sum_le_sum
        intro n hn
        split_ifs
        · exact le_rfl
        · exact hw (m,n) (mem_product.mpr ⟨hm,hn⟩)
      _ = ∑ p ∈ S, w p := (sum_product U V w).symm
      _ ≤ _ := hmass
  rw [← g9IntegerFibre_centered_eq]
  have htwice : 10*J*(N : ℝ)/(d.totient : ℝ) =
      5*J*(N : ℝ)/(d.totient : ℝ) + 5*J*(N : ℝ)/(d.totient : ℝ) := by ring
  rw [htwice]
  apply abs_le.mpr
  constructor <;> linarith only [hA0, hA, hB0, hB]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
