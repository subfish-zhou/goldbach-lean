import CoverMassGeometry

namespace CoverMass
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

private theorem sum_window_split (N : ℕ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N a c, f p) =
    (∑ p ∈ primeWindow N a b, f p)+(∑ p ∈ primeWindow N b c, f p) := by
  have he : primeWindow N a c = primeWindow N a b ∪ primeWindow N b c := by
    ext p
    simp only [mem_union,mem_primeWindow]
    constructor
    · rintro ⟨hp,hN,ha,hc⟩
      by_cases h : (p : ℝ) < b
      · exact Or.inl ⟨hp,hN,ha,h⟩
      · exact Or.inr ⟨hp,hN,le_of_not_gt h,hc⟩
    · rintro (⟨hp,hN,ha,hb⟩ | ⟨hp,hN,hb,hc⟩)
      · exact ⟨hp,hN,ha,hb.trans_le hbc⟩
      · exact ⟨hp,hN,hab.trans hb,hc⟩
  rw [he,sum_union]
  exact disjoint_left.mpr (fun p hp hq =>
    (not_lt_of_ge (mem_primeWindow.mp hq).2.2.1) (mem_primeWindow.mp hp).2.2.2)

/-- The actual large interval is split at the original two local endpoints.
Both short bands are retained; the middle is enlarged only in its modulus. -/
theorem kernel_window_split {N : ℕ} {a c e b D : ℝ}
    (hac : a ≤ c) (hce : c ≤ e) (heb : e ≤ b)
    (hK : ∀ p ∈ primeWindow 1 a b,
      0 ≤ 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D)) ∧
      1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D)) ≤ 8/(p : ℝ)) :
    (∑ p ∈ primeWindow N a b, 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D))) ≤
      (∑ p ∈ primeWindow 1 c e, 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D))) +
      8*((∑ p ∈ primeWindow N a c, (1 : ℝ)/p)+(∑ p ∈ primeWindow N e b, (1 : ℝ)/p)) := by
  let K := fun p : ℕ => 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log D))
  have lift {M : ℕ} {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b)
      {p : ℕ} (hp : p ∈ primeWindow M u v) : p ∈ primeWindow 1 a b := by
    obtain ⟨hpp,_,hpu,hpv⟩ := mem_primeWindow.mp hp
    exact mem_primeWindow.mpr ⟨hpp,Nat.coprime_one_right p,hu.trans hpu,hpv.trans_le hv⟩
  have hmid : (∑ p ∈ primeWindow N c e, K p) ≤ ∑ p ∈ primeWindow 1 c e, K p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp,_,hpu,hpv⟩ := mem_primeWindow.mp hp
      exact mem_primeWindow.mpr ⟨hpp,Nat.coprime_one_right p,hpu,hpv⟩
    · intro p hp _
      exact (hK p (lift hac heb hp)).1
  have hband {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) :
      (∑ p ∈ primeWindow N u v, K p) ≤ 8*∑ p ∈ primeWindow N u v, (1 : ℝ)/p := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    simpa only [mul_one_div] using (hK p (lift hu hv hp)).2
  have hlo := hband (u := a) (v := c) le_rfl (hce.trans heb)
  have hhi := hband (u := e) (v := b) (hac.trans hce) le_rfl
  change (∑ p ∈ primeWindow N a b, K p) ≤ _
  rw [sum_window_split N hac (hce.trans heb),sum_window_split N hce heb]
  dsimp [K] at hmid hlo hhi ⊢
  linarith

/-- Exact repeated-prime factor is bounded above, not discarded. Its whole
positive lane survives in the all-prime kernel and is paid by modulus deletion. -/
theorem inserted_fibre_kernel {N d : ℕ} {Q : ℝ} (P : Finset ℕ)
    (hN : 0 < N) (hd : 0 < d) (hQ : 1 < Q/d)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p.Coprime N ∧ 0 < 1-log (p : ℝ)/log (Q/d)) :
    (∑ p ∈ P, wuSingularSeries ((d*p)*N)/((Nat.totient (d*p) : ℝ)*log (Q/((d : ℝ)*p)))) ≤
      (wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d))) *
      ∑ p ∈ P, 1/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d))) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpp,hp2,hpN,hgap⟩ := hP p hp
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have ha : 0 ≤ wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d)) :=
    div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos hd hN)).le
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hQ).le)
  rw [wu_inserted_theta_weight hN hd hpp hp2 hpN hQ]
  apply mul_le_mul_of_nonneg_left _ ha
  rw [← div_div]
  apply div_le_div_of_nonneg_right _ hgap.le
  split_ifs
  · exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · exact le_rfl

/-- Nonnegative inserted Theta on a full prime window with an actual log gap. -/
theorem inserted_theta_nonneg {i N : ℕ} {Q : ℝ} (W : Fin i → Finset ℕ) (P : Finset ℕ)
    (hN : 4 ≤ N)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hp : ∀ p ∈ P, 0 < p)
    (hgap : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P, 1 < Q/((d : ℝ)*p)) :
    0 ≤ boxTheta N Q (Fin.cons P W) := by
  rw [boxTheta_cons]
  have hli := box_trueLi_lower hN
  have hli0 : 0 ≤ AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N/(2*log N)).trans hli
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro d hdm
  apply mul_nonneg (Nat.cast_nonneg _)
  apply sum_nonneg
  intro p hpm
  exact div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos (Nat.mul_pos (hd d hdm) (hp p hpm)) (by omega))).le
    (mul_nonneg (Nat.cast_nonneg _) (log_pos (hgap d hdm p hpm)).le)

end
end CoverMass
