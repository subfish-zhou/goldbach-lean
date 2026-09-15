import MathlibNt.Wu2008DoubleSieve.ImprovementFamilies

/-!
# Exact permutation transport for reboxing

Wu04's proof following (3.15) sorts an inserted window among the old ones.
The arithmetic convolution and all actual consumers must survive this
sorting with their full ordered-tuple multiplicity. These exact identities
provide that transport; they do not assert squared-prefix admissibility
of the sorted upper endpoints or pay a reboxing boundary.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem convolutionCoeff_permute {i : ℕ} (W : Fin i → Finset ℕ)
    (e : Equiv.Perm (Fin i)) (d : ℕ) :
    convolutionCoeff (W ∘ e) d = convolutionCoeff W d := by
  unfold convolutionCoeff
  apply card_bij (fun t _ => t ∘ e.symm)
  · intro t ht
    obtain ⟨ht, hprod⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      simpa using Fintype.mem_piFinset.mp ht (e.symm j)
    · simpa only [Function.comp_apply, Equiv.prod_comp] using hprod
  · intro t ht u hu heq
    funext j
    have h := congrFun heq (e j)
    simpa using h
  · intro t ht
    obtain ⟨ht, hprod⟩ := mem_filter.mp ht
    refine ⟨t ∘ e, mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩, ?_⟩
    · intro j
      exact Fintype.mem_piFinset.mp ht (e j)
    · simpa only [Function.comp_apply, Equiv.prod_comp] using hprod
    · ext j
      simp

theorem boxConvolutionSupport_permute {i : ℕ} (W : Fin i → Finset ℕ)
    (e : Equiv.Perm (Fin i)) :
    boxConvolutionSupport (W ∘ e) = boxConvolutionSupport W := by
  ext d
  simp only [mem_boxConvolutionSupport, convolutionCoeff_permute]

theorem boxTheta_permute {i : ℕ} (N : ℕ) (Q : ℝ) (W : Fin i → Finset ℕ)
    (e : Equiv.Perm (Fin i)) :
    boxTheta N Q (W ∘ e) = boxTheta N Q W := by
  simp only [boxTheta, boxConvolutionSupport_permute, convolutionCoeff_permute]

theorem wuBoxPhi_permute {i : ℕ} (N : ℕ) (δ s : ℝ) (W : Fin i → Finset ℕ)
    (e : Equiv.Perm (Fin i)) :
    wuBoxPhi N δ (W ∘ e) s = wuBoxPhi N δ W s := by
  change (∑ d ∈ boxConvolutionSupport (W ∘ e), (convolutionCoeff (W ∘ e) d : ℝ) *
      (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d s) : ℝ)) =
    ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d s) : ℝ)
  simp only [boxConvolutionSupport_permute, convolutionCoeff_permute]

theorem wuBoxPhiLE_permute {i : ℕ} (N : ℕ) (δ s : ℝ) (W : Fin i → Finset ℕ)
    (e : Equiv.Perm (Fin i)) :
    wuBoxPhiLE N δ (W ∘ e) s = wuBoxPhiLE N δ W s := by
  simp only [wuBoxPhiLE, boxConvolutionSupport_permute, convolutionCoeff_permute]

theorem convolutionWuWindows_permute {i : ℕ} (N : ℕ) (Δ : ℝ) (V : Fin i → ℝ)
    (e : Equiv.Perm (Fin i)) :
    convolutionWuWindows N Δ (V ∘ e) = convolutionWuWindows N Δ V ∘ e := rfl

/-- The inserted window has the same exact Dirichlet convolution after
any permutation, including repeated or overlapping prime windows. -/
theorem convolutionCoeff_insert_permute {i : ℕ} (P : Finset ℕ) (W : Fin i → Finset ℕ)
    (e : Equiv.Perm (Fin (i + 1))) (hP : ∀ p ∈ P, 0 < p) (d : ℕ) :
    convolutionCoeff (Fin.cons P W ∘ e) d =
      ∑ p ∈ P, if p ∣ d then convolutionCoeff W (d / p) else 0 := by
  rw [convolutionCoeff_permute, convolutionCoeff_cons P W hP]

end Wu2008DoubleSieve
