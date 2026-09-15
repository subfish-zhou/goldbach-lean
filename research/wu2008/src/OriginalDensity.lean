import OriginalSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9MainNormalization
import MathlibNt.SieveTheory.LiLiuFouvryG9AnalyticDensity
import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrection
import MathlibNt.SieveTheory.LiLiuFouvryG9MainScalar

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8

def actualCenter (N : ℕ) (ρ δ η : ℝ) (k : ℕ × ℕ × ℕ) (P : Finset ℕ) (z : ℝ) : ℝ :=
  ∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
    ∑ d ∈ (P.prod id).divisors,
      externalTerm true P (externalInternalLevel (level N ρ δ k) η) η z t d * center N ρ k d

def rectangleMass (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) : ℝ :=
  ∑ m ∈ products (labels N ρ k), ∑ n ∈ primeSupport N ρ k,
    alpha (labels N ρ k) m * beta N n

def eulerMass (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (P : Finset ℕ) : ℝ :=
  ∑ m ∈ products (labels N ρ k), ∑ n ∈ primeSupport N ρ k,
    alpha (labels N ρ k) m * beta N n * (∏ p ∈ P, (1-progressionDensity (m*n) p))

theorem beta_nonneg (N n : ℕ) : 0 ≤ beta N n := by
  unfold beta primeSWBeta
  split_ifs <;> norm_num

theorem rectangleMass_nonneg (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) :
    0 ≤ rectangleMass N ρ k := by
  exact sum_nonneg fun m _ => sum_nonneg fun n _ =>
    mul_nonneg (alpha_nonneg _ m) (beta_nonneg N n)

/-- Exchange the entire signed family, never one-sided individual divisors. -/
theorem actualCenter_eq_density (N : ℕ) (ρ δ η : ℝ) (k : ℕ × ℕ × ℕ)
    (P : Finset ℕ) (z : ℝ) :
    actualCenter N ρ δ η k P z =
      ∑ m ∈ products (labels N ρ k), ∑ n ∈ primeSupport N ρ k,
        alpha (labels N ρ k) m * beta N n *
          externalDensity true P (externalInternalLevel (level N ρ δ k) η) η z
            (progressionDensity (m*n)) :=
  g9IntegerFibreCenter_externalDensity true P _ η z _ _ _ _

/-- The literal ordered labels and whole interval; beta alone filters short copN. -/
theorem actualCenter_eq_labels (N : ℕ) (ρ δ η : ℝ) (k : ℕ × ℕ × ℕ)
    (P : Finset ℕ) (z : ℝ) :
    actualCenter N ρ δ η k P z =
      ∑ q ∈ labels N ρ k, ∑ n ∈ primeSupport N ρ k,
        beta N n * externalDensity true P (externalInternalLevel (level N ρ δ k) η)
          η z (progressionDensity ((q.1*q.2)*n)) := by
  rw [actualCenter_eq_density]
  have h := alpha_sum (labels N ρ k) (fun m =>
    ∑ n ∈ primeSupport N ρ k, beta N n *
      externalDensity true P (externalInternalLevel (level N ρ δ k) η) η z
        (progressionDensity (m*n)))
  simp only [mul_sum] at h
  simpa only [mul_assoc] using h.symm

/-- Every deletion is paid, including repeated labels and primes outside P. -/
theorem eulerMass_le {N : ℕ} {e ρ : ℝ} (hN : 1 ≤ (N : ℝ))
    (he : 0 < e) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hne : Occupied N e ρ k)
    (h8 : 8 ≤ (N : ℝ)^(100/1327 : ℝ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    eulerMass N ρ k P ≤ g9BaseEuler P *
      (1+1/((N : ℝ)^(100/1327 : ℝ)/2-2))^3 * rectangleMass N ρ k := by
  obtain ⟨_,_,_,hlo,_⟩ := geometry he hρ hρu hne
  have hbig : 3 ≤ ρ^k.1 := by linarith
  apply g9_weighted_euler_three_primes_le P _ _ hP
    (alpha (labels N ρ k)) (beta N)
    (fun m _ => alpha_nonneg _ m) (fun n _ => beta_nonneg N n) (by linarith)
  · intro m hm _
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hm
    obtain ⟨_,_,hp,hr,_,hpN,_,_,_,_,hpr⟩ := (labels_mem N ρ k q.1 q.2).mp hq
    have ha : (N : ℝ)^(100/1327 : ℝ) ≤ (N : ℝ)^(1/3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    have hpr' : (q.1 : ℝ) ≤ q.2 := by exact_mod_cast hpr
    exact ⟨q.1,q.2,hp,hr,rfl,by linarith,by linarith⟩
  · intro n hn hb
    have hp : n.Prime := by
      by_contra hp
      simp [beta,primeSWBeta,hp] at hb
    have hnlo := ((primeSupport_mem hρ hρu k hbig hne n).mp hn).2.1
    exact ⟨hp,by linarith⟩

/-- Common N, actual original occupied boxes, original global and internal levels.
The analytic producer chooses its constants before eta, delta and all cells. -/
theorem actualCenter_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧
      ∀ δ η : ℝ, 0 ≤ δ → δ < 1/4 → 0 < η → η < 1/8 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      ∀ e ρ : ℝ, 0 < e → 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k →
      let Q := level N ρ δ k
      let P := fouvryG9SievePrimes N (Real.sqrt N)
      2 ≤ externalInternalLevel Q η ∧
      0 ≤ fouvryG9UpperFactor N Q C K η ∧
      actualCenter N ρ δ η k P (Real.sqrt N) ≤
        fouvryG9UpperFactor N Q C K η *
          (fouvryG9BaseEuler N (Real.sqrt N) *
            (1+1/((N : ℝ)^(100/1327 : ℝ)/2-2))^3 * rectangleMass N ρ k) := by
  obtain ⟨C,hC,K,hK,hden⟩ := g9ProgressionDensity_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro δ η hδ hδu hη hηu
  obtain ⟨Q₀,hQ₀,hupper⟩ := hden η hη hηu
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ (by linarith) hη Q₀
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 8 0 (100/1327) (by norm_num))
  refine ⟨max Nw (max Ng 4),?_⟩
  intro N hN hEven e ρ he hρ hρu k hne
  have hNw := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNg := (le_max_left _ _).trans hrest
  have hN4 : (4 : ℝ) ≤ N := (le_max_right _ _).trans hrest
  have h8 : 8 ≤ (N : ℝ)^(100/1327 : ℝ) := by simpa using hg N hNg
  let T := (2/3 : ℝ)*ρ^k.1
  let Q := level N ρ δ k
  let P := fouvryG9SievePrimes N (Real.sqrt N)
  obtain ⟨_,_,_,hlo,hhi⟩ := geometry he hρ hρu hne
  have hT : 1 ≤ T := by dsimp [T]; linarith
  obtain ⟨_,_,hQq,hD,hQN⟩ := hw N T hNw hT hhi
  have hQ4 : 4 ≤ Q := hQ₀.trans hQq
  obtain ⟨hz,hzQ⟩ := g9WF_sqrt_cutoff hN4 hT hhi hδ hδu
  have hfactor : 0 ≤ fouvryG9UpperFactor N Q C K η := by
    unfold fouvryG9UpperFactor
    have hh := (fouvryG9MainScalar_initial (by linarith : 1 < (N : ℝ))
      (by linarith : 1 < Q) hQN).2
    have hF := (Real.exp_pos _).le.trans hh
    have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
    exact add_nonneg hF (mul_nonneg hC.le (by positivity))
  refine ⟨hD,hfactor,?_⟩
  have hmain : actualCenter N ρ δ η k P (Real.sqrt N) ≤
      fouvryG9UpperFactor N Q C K η * eulerMass N ρ k P := by
    rw [actualCenter_eq_density]
    unfold eulerMass
    simp only [mul_sum]
    apply sum_le_sum
    intro m _
    apply sum_le_sum
    intro n _
    have hp := hupper Q hQq (m*n) P (fouvryG9SievePrimes_odd hEven _)
      (Real.sqrt N) hz hzQ (fun p hp => (fouvryG9SievePrimes_mem N p _ |>.mp hp).2.2)
    have hh := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (alpha_nonneg (labels N ρ k) m) (beta_nonneg N n))
    exact hh.trans_eq (by unfold fouvryG9UpperFactor; ring)
  exact hmain.trans (mul_le_mul_of_nonneg_left
    (eulerMass_le (by linarith) he hρ hρu k hne h8 P (fouvryG9SievePrimes_odd hEven _)) hfactor)

#print axioms actualCenter_eq_labels
#print axioms eulerMass_le
#print axioms actualCenter_upper
end OriginalU8
