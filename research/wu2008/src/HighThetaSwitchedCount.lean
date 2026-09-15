import HighThetaMainMass
import MathlibNt.Wu2008DoubleSieve.Omega3SieveSource

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery Filter
open scoped Classical Topology
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

/-- An elementary finite bound for the actual local product. -/
theorem local_product_bounds (N : ℕ) (Z : ℝ) :
    0 ≤ localSieveProduct N Z ∧ localSieveProduct N Z ≤ 1 := by
  have hf : ∀ p ∈ localSievePrimes N Z,
      0 ≤ 1-1/((p : ℝ)-1) ∧ 1-1/((p : ℝ)-1) ≤ 1 := by
    intro p hp
    have hprime := (mem_localSievePrimes N p Z).mp hp |>.2.1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hi : 1/((p : ℝ)-1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hi0 : 0 ≤ 1/((p : ℝ)-1) := div_nonneg (by norm_num) (by linarith)
    constructor <;> linarith
  exact ⟨prod_nonneg (fun p hp => (hf p hp).1),
    prod_le_one (fun p hp => (hf p hp).1) (fun p hp => (hf p hp).2)⟩

/-- Exact source-level local density; delta remains in Q and sqrt Q. -/
def switchedDensity (N : ℕ) (δ ρ : ℝ) : ℝ :=
  (jurkatRichertUpperLinearSieveFactor 2+ρ)*
    localSieveProduct N (sqrt ((N : ℝ)^(1/2-δ)))

theorem switchedDensity_abs_le (N : ℕ) (δ ρ : ℝ) :
    |switchedDensity N δ ρ| ≤ |jurkatRichertUpperLinearSieveFactor 2+ρ|+1 := by
  have hb := local_product_bounds N (sqrt ((N : ℝ)^(1/2-δ)))
  unfold switchedDensity
  rw [abs_mul, abs_of_nonneg hb.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hb.2).trans (by linarith)

/-- Both actual switched counts, with all errors paid and true-li centre. -/
def SwitchedUpperPaid {i : ℕ} (N : ℕ) (δ ε ρ s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  let Z := sqrt ((N : ℝ)^(1/2-δ))
  let M := liX N δ s t W*switchedDensity N δ ρ + ε*boxTheta N ((N : ℝ)^(1/2-δ)) W
  omega3SwitchedSiftedCountLE N δ s t Z W ≤ M ∧
    omega3SwitchedSiftedCount N δ s t Z W ≤ M

/-- Physical finite sieve consumed on every original box and occupied inserted
box. No Uk membership, independent improvement suprema or h gain is assumed. -/
theorem original_and_inserted_switched_upper {δ ε ρ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        SwitchedUpperPaid N δ ε ρ s t (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          SwitchedUpperPaid N δ ε ρ s t (convolutionWuWindows N Δ (Fin.cons U V)) := by
  let A : ℝ := |jurkatRichertUpperLinearSieveFactor 2+ρ|+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hδhalf : δ < 1/2 := lt_of_le_of_lt hδhi (by norm_num [highEta])
  obtain ⟨T1,hT14,hR⟩ := original_and_inserted_relative hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hM⟩ := original_and_inserted_main_mass hδ hδhi
    (show 0 < ε/(2*A) by positivity)
  obtain ⟨Z0,hden⟩ := omega3_switched_upper_density hρ
  obtain ⟨T3,hZ⟩ := eventually_atTop.mp
    ((omega3_source_sqrt_tendsto hδhalf).eventually (eventually_ge_atTop (max Z0 2)))
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN4 := hT14.trans hN1
  have hr := hR N hN1 Δ hlo hhi V hV hrect s t hs hst ht
  have hm := hM N hN2 Δ hlo hhi V hV hrect s t hs hst ht
  have hz := hZ N hN3
  have hg := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhalf
  have hconsume : ∀ {i : ℕ} (W : Fin i → Finset ℕ),
      (∀ j p, p ∈ W j → p.Prime) →
      RelativeRemainders N δ (ε/2) s t W → MainMassPaid N δ (ε/(2*A)) s t W →
      SwitchedUpperPaid N δ ε ρ s t W := by
    intro i W hW hrem hmass
    have hfinite := hden N he i δ s t (sqrt ((N : ℝ)^(1/2-δ)))
      ((N : ℝ)^(1/2-δ)) 2 W ((le_max_left _ _).trans hz)
      ((le_max_right _ _).trans hz) (by positivity)
      hg.2.2.2.2.2.2.2.symm (by norm_num) (by norm_num)
    have hprod : (omega3SieveX N δ s t W-liX N δ s t W)*switchedDensity N δ ρ ≤
        ε/2*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
      calc
        _ ≤ |(omega3SieveX N δ s t W-liX N δ s t W)*switchedDensity N δ ρ| := le_abs_self _
        _ = |omega3SieveX N δ s t W-liX N δ s t W| * |switchedDensity N δ ρ| := abs_mul _ _
        _ ≤ (ε/(2*A)*boxTheta N ((N : ℝ)^(1/2-δ)) W)*A :=
          mul_le_mul hmass.1 (switchedDensity_abs_le N δ ρ) (abs_nonneg _) ((abs_nonneg _).trans hmass.1)
        _ = _ := by field_simp
    have hclosed : omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W ≤
        liX N δ s t W*switchedDensity N δ ρ + ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
      change _ ≤ omega3SieveX N δ s t W*switchedDensity N δ ρ + _ + _ at hfinite
      dsimp [RelativeRemainders] at hrem
      nlinarith
    refine ⟨hclosed,?_⟩
    exact (omega3_switched_sifted_le_closed N δ s t _ W
      (fun d hd => boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd)).trans hclosed
  refine ⟨hconsume _ (fun j p hp => (mem_convolutionWuWindows.mp hp).1) hr.1 hm.1,?_⟩
  intro U hw
  exact hconsume _ (fun j p hp => (mem_convolutionWuWindows.mp hp).1) (hr.2 U hw) (hm.2 U hw)

end
end HighTheta
