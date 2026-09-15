import MathlibNt.Wu2008DoubleSieve.Omega3R1Source

/-! Actual cofactor geometry from total product slack, with no squared prefix.
The hypotheses refer to the original prime windows, not to balanced profiles. -/
namespace HighBoxRecovery
open Finset Real Wu2008DoubleSieve
open scoped Classical
noncomputable section

/-- The local cutoff only uses total cofactor size. -/
theorem cutoff_lower {N d : ℕ} {δ η t : ℝ}
    (hN : 2 ≤ N) (hd : 0 < d) (hη : 0 < η) (ht : 0 < t) (htop : t ≤ 10)
    (hsize : (d : ℝ) ≤ (N : ℝ) ^ (1/2-δ-10*η)) :
    (N : ℝ)^η ≤ wuLocalCutoff N δ d t := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase : (N : ℝ)^(10*η) ≤ (N : ℝ)^(1/2-δ) / d := by
    apply (le_div_iff₀ hdr).mpr
    calc
      _ ≤ (N : ℝ)^(10*η) * (N : ℝ)^(1/2-δ-10*η) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = (N : ℝ)^(1/2-δ) := by rw [← rpow_add hNr]; congr 1; ring
  unfold wuLocalCutoff
  calc
    (N : ℝ)^η ≤ (N : ℝ)^((10*η)*(1/t)) := by
      apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      rw [mul_one_div]
      apply (le_div_iff₀ ht).mpr
      nlinarith
    _ = ((N : ℝ)^(10*η))^(1/t) := rpow_mul hNr.le _ _
    _ ≤ _ := rpow_le_rpow (by positivity) hbase (by positivity)

/-- Literal full cofactor and interval endpoints, including empty prime fibres. -/
theorem actual_profile {i N : ℕ} {δ η s t : ℝ} (W : Fin i → Finset ℕ)
    (hN : 2 ≤ N)
    (hW : ∀ j p, p ∈ W j → p.Prime)
    (hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t)
    {c : Omega3CofactorIndex} (hc : c ∈ omega3CofactorLabels N δ s t W) :
    0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
    (N : ℝ)^η ≤ omega3CofactorValue c ∧
    (omega3CofactorValue c : ℝ) ≤ (N : ℝ)^(1-η) ∧
    2 ≤ (c.2.1 : ℝ) ∧
    (c.2.1 : ℝ) ≤ min ((N : ℝ)/omega3CofactorValue c) (wuLocalCutoff N δ c.1 s) ∧
    (omega3CofactorValue c : ℝ) *
      min ((N : ℝ)/omega3CofactorValue c) (wuLocalCutoff N δ c.1 s) ≤ N := by
  rcases c with ⟨d,p2,p1,n⟩
  obtain ⟨hd,h2,h1,_,hn,hsize,_⟩ := mem_omega3CofactorLabels.mp hc
  have hdpos := boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd
  have hp1 := (mem_primeWindow.mp h1).1.pos
  have hp2 := (mem_primeWindow.mp h2).1.pos
  have hepos : 0 < omega3CofactorValue ⟨d,p2,p1,n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos hn) hp1) hp2
  have her : (0 : ℝ) < omega3CofactorValue ⟨d,p2,p1,n⟩ := by exact_mod_cast hepos
  have heN : omega3CofactorValue ⟨d,p2,p1,n⟩ ≤ N :=
    (Nat.le_mul_of_pos_right _ hp2).trans hsize
  have hp2e : p2 ≤ omega3CofactorValue ⟨d,p2,p1,n⟩ :=
    Nat.le_mul_of_pos_left p2 (Nat.mul_pos (Nat.mul_pos hdpos hn) hp1)
  have hp2lower := (hcut d hd).trans (mem_primeWindow.mp h2).2.2.1
  have hsizeR : (omega3CofactorValue ⟨d,p2,p1,n⟩ : ℝ)*p2 ≤ N := by exact_mod_cast hsize
  refine ⟨hepos,heN,hp2lower.trans (by exact_mod_cast hp2e),
    omega3_cofactor_power_gap (by omega) hp2lower hsize,
    by exact_mod_cast (mem_primeWindow.mp h2).1.two_le, ?_, ?_⟩
  · exact le_min ((le_div_iff₀ her).mpr (by simpa only [mul_comm] using hsizeR))
      (mem_primeWindow.mp h2).2.2.2.le
  · have hu := (le_div_iff₀ her).mp
      (min_le_left ((N : ℝ)/omega3CofactorValue ⟨d,p2,p1,n⟩) (wuLocalCutoff N δ d s))
    simpa only [mul_comm] using hu

/-- Full weighted fibre mass, before any absolute value is taken. -/
theorem actual_fibre_weight {i k N : ℕ} {δ η s t : ℝ} (W : Fin i → Finset ℕ)
    (hik : i ≤ k) (hN : 2 ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p)
    (hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t)
    (e : ℕ) :
    (∑ c ∈ omega3LayerFibre (omega3CofactorLabels N δ s t W) e,
      (convolutionCoeff W c.1 : ℝ)) ≤ (max 1 (1/η))^(k+2) := by
  by_cases hne : (omega3LayerFibre (omega3CofactorLabels N δ s t W) e).Nonempty
  · obtain ⟨c,hc⟩ := hne
    obtain ⟨hc,he⟩ := mem_filter.mp hc
    have hg := actual_profile W hN (fun j p hp => (hW j p hp).1) hcut hc
    exact omega3_cofactor_subcarrier_weight_le W _ _ _
      (omega3_cofactor_labels_subset N δ s t W e) hik (by omega)
      (he ▸ hg.1) (he ▸ hg.2.1) hη hW hcut
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
    positivity

/-- Every divisor of the full cofactor is large; repeated p1/p2 in n are retained. -/
theorem actual_prime_lower {i N : ℕ} {δ η s t : ℝ} (W : Fin i → Finset ℕ)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p)
    (hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t)
    {c : Omega3CofactorIndex} (hc : c ∈ omega3CofactorLabels N δ s t W)
    {r : ℕ} (hr : r.Prime) (hrc : r ∣ omega3CofactorValue c) :
    (N : ℝ)^η ≤ r := by
  rcases c with ⟨d,p2,p1,n⟩
  obtain ⟨hd,h2,h1,_,_,_,hgood⟩ := mem_omega3CofactorLabels.mp hc
  exact omega3_cofactor_prime_lower (mem_primeWindow.mp h1).1 (mem_primeWindow.mp h2).1
    (fun r hr hrd => omega3_support_prime_lower W hW hd hr hrd)
    ((hcut d hd).trans (mem_primeWindow.mp h1).2.2.1)
    ((hcut d hd).trans (mem_primeWindow.mp h2).2.2.1) hgood.2.2 hr hrc

end
end HighBoxRecovery
