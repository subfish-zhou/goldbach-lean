import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovHasse
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual finite-dimensional Stepanov equations

The two polynomial families have degree strictly less than the integer `B`.
The `k`th equation is Harcos (22), with its two distinct Hasse operators.
No rank or nonzero-solution hypothesis is imposed on the equation matrix.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset Module

variable {F : Type*} [Field F]

def stepanovConstraint (f : F[X]) (hf : f ≠ 0) (ell e : ℕ) (a : F)
    (k : ℕ) {J : ℕ} (r s : Fin J → F[X]) : F[X] :=
  ∑ j, (stepanovHasseOperator f hf ell k (r j) +
    a • stepanovHasseOperator f hf (ell + e) k (s j)) * X ^ j.val

theorem stepanovConstraint_degree_lt (f : F[X]) (hf : f ≠ 0)
    (ell e B J k : ℕ) (a : F) (hk : k ≤ ell) (hm : 1 ≤ f.natDegree)
    (hJ : 0 < J) (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (stepanovConstraint f hf ell e a k r s).degree <
      ((B + k * (f.natDegree - 1) + (J - 1) : ℕ) : WithBot ℕ) := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_degreeLT.mpr
  rw [degree_mul_X_pow]
  have hr' := stepanovHasseOperator_degree_lt f hf ell k B hk hm (r j) (hr j)
  have hs' := stepanovHasseOperator_degree_lt f hf (ell + e) k B
    (by omega) hm (s j) (hs j)
  have hd := (degree_add_le _ _).trans_lt
    (max_lt hr' ((degree_smul_le a _).trans_lt hs'))
  calc
    _ < ((B + k * (f.natDegree - 1) : ℕ) : WithBot ℕ) + (j.val : WithBot ℕ) :=
      WithBot.add_lt_add_right (by simp) hd
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact_mod_cast Nat.add_le_add_left (show j.val ≤ J - 1 by omega) _

abbrev StepanovCoefficients (F : Type*) [Field F] (J B : ℕ) :=
  Fin J → degreeLT F B × degreeLT F B

def stepanovConstraintMap (f : F[X]) (hf : f ≠ 0)
    (ell e B J : ℕ) (a : F) (hm : 1 ≤ f.natDegree) (hJ : 0 < J) :
    StepanovCoefficients F J B →ₗ[F]
      (k : Fin ell) → degreeLT F (B + k.val * (f.natDegree - 1) + (J - 1)) where
  toFun v k := ⟨stepanovConstraint f hf ell e a k.val
      (fun j => (v j).1) (fun j => (v j).2),
    mem_degreeLT.mpr (stepanovConstraint_degree_lt f hf ell e B J k.val a
      (Nat.le_of_lt k.is_lt) hm hJ _ _
      (fun j => mem_degreeLT.mp (v j).1.property)
      (fun j => mem_degreeLT.mp (v j).2.property))⟩
  map_add' v w := by
    funext k
    apply Subtype.ext
    simp only [stepanovConstraint, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add, map_add, smul_add, add_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  map_smul' c v := by
    funext k
    apply Subtype.ext
    simp only [stepanovConstraint, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Submodule.coe_smul, map_smul, RingHom.id_apply,
      Finset.smul_sum, smul_comm a c]
    apply sum_congr rfl
    intro j _
    rw [← smul_mul_assoc, smul_add]

theorem stepanovCoefficients_finrank (J B : ℕ) :
    finrank F (StepanovCoefficients F J B) = 2 * J * B := by
  have hB : finrank F (degreeLT F B) = B := by
    simpa using (finrank_eq_card_basis (degreeLT.basis F B))
  simp only [StepanovCoefficients, finrank_pi_fintype, finrank_prod, hB, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  ring

theorem stepanovConstraints_finrank (ell B J m : ℕ) :
    finrank F ((k : Fin ell) → degreeLT F (B + k.val * (m - 1) + (J - 1))) =
      ∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) := by
  rw [finrank_pi_fintype]
  apply sum_congr rfl
  intro k _
  simpa using (finrank_eq_card_basis
    (degreeLT.basis F (B + k.val * (m - 1) + (J - 1))))

/-- The precise integer equation count, strictly smaller than the `2JB`
unknown coefficients, produces a nontrivial solution of Harcos (22). -/
theorem stepanov_exists_coefficients (f : F[X]) (hf : f ≠ 0)
    (ell e B J : ℕ) (a : F) (hm : 1 ≤ f.natDegree) (hJ : 0 < J)
    (hcount : (∑ k : Fin ell, (B + k.val * (f.natDegree - 1) + (J - 1))) <
      2 * J * B) :
    ∃ r s : Fin J → F[X],
      (∀ j, (r j).degree < (B : WithBot ℕ)) ∧
      (∀ j, (s j).degree < (B : WithBot ℕ)) ∧
      (∃ j, r j ≠ 0 ∨ s j ≠ 0) ∧
      ∀ k < ell, stepanovConstraint f hf ell e a k r s = 0 := by
  classical
  let L := stepanovConstraintMap f hf ell e B J a hm hJ
  have hn : ¬ Function.Injective L := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    rw [stepanovCoefficients_finrank, stepanovConstraints_finrank] at hd
    exact (not_lt_of_ge hd) hcount
  have hex : ∃ v, L v = 0 ∧ v ≠ 0 := by
    by_contra h
    apply hn
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv'
    exact h ⟨v, hv, hv'⟩
  obtain ⟨v, hv, hv0⟩ := hex
  refine ⟨(fun j => (v j).1), (fun j => (v j).2),
    (fun j => mem_degreeLT.mp (v j).1.property),
    (fun j => mem_degreeLT.mp (v j).2.property), ?_, ?_⟩
  · by_contra hn
    apply hv0
    funext j
    apply Prod.ext <;> apply Subtype.ext
    · by_contra h
      exact hn ⟨j, Or.inl h⟩
    · by_contra h
      exact hn ⟨j, Or.inr h⟩
  · intro k hk
    have he := congrArg (fun w => ((w ⟨k, hk⟩ :
      degreeLT F (B + k * (f.natDegree - 1) + (J - 1))) : F[X])) hv
    exact he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
