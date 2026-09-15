import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeUnitFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalParameters

/-! The literal restored four-prime source, its prime-only closed envelope,
and same-weight payment. This is not a nonunit switched-X construction. -/
namespace Wu2008DoubleSieve.FourPrimeUnit
open Finset Real
open scoped Classical

noncomputable def actualProfiles {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : Finset Gamma16Profile :=
  profiles N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

noncomputable def actualFibre (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (j : Fin 4) : Gamma16Profile → Finset ℕ :=
  fibre N (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

noncomputable def actualSource {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : ℝ :=
  source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

noncomputable def actualEnvelope {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : ℝ :=
  envelope N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) (word j)

theorem actual_envelope_eq {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (j : Fin 4) : actualEnvelope N δ p W j =
    ∑ x ∈ (actualProfiles N δ p W j).filter (fun x => x.2.2.2.2 = 1),
      (convolutionCoeff W x.1 : ℝ) * (actualFibre N δ p j x).card := by
  simp only [actualProfiles, profiles_filter]
  rfl

theorem actual_profiles_geometry {i N : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    {W : Fin i → Finset ℕ} {j : Fin 4} {x : Gamma16Profile}
    (hx : x ∈ actualProfiles N δ p W j) :
    x.1 ∈ boxConvolutionSupport W ∧
    (0 < x.2.1 ∧ (x.2.1 : ℝ) ≤ wuLocalCutoff N δ x.1 p.s) ∧
    (0 < x.2.2.1 ∧ (x.2.2.1 : ℝ) ≤ wuLocalCutoff N δ x.1 p.s) ∧
    (0 < x.2.2.2.1 ∧ (x.2.2.2.1 : ℝ) ≤ wuLocalCutoff N δ x.1 p.s) :=
  profiles_geometry hx

/-- The old source-box support gives R>=1, so the last two parameter cuts are ordered. -/
theorem actual_last_cuts {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} (hp : p.MotherAdmissible)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    wuLocalCutoff N δ d p.kappa3 ≤ wuLocalCutoff N δ d p.s := by
  obtain ⟨hdpos,hdQ⟩ := omega3_source_support_le_Q hN hδ hδhi hb hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdpos
  unfold wuLocalCutoff
  apply rpow_le_rpow_of_exponent_le
  · exact (le_div_iff₀ hd0).mpr (by simpa using hdQ)
  · exact one_div_le_one_div_of_le (by linarith [hp.one_le_s]) hp.s_le_kappa3

theorem actual_fibre_geometry {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} (hp : p.MotherAdmissible)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) {j : Fin 4} {x : Gamma16Profile}
    (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j)
    {q : ℕ} (hq : q ∈ actualFibre N δ p j x) :
    0 < q ∧ (q : ℝ) ≤ wuLocalCutoff N δ x.1 p.s :=
  fibre_geometry (actual_last_cuts hp hN hδ hδhi hb (actual_profiles_geometry hx).1) hq

theorem actual_source_le {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (j : Fin 4) :
    actualSource N δ p (convolutionWuWindows N Δ V) j ≤
      actualEnvelope N δ p (convolutionWuWindows N Δ V) j :=
  source_le_envelope (fun _ hd => (omega3_source_support_le_Q hN hδ hδhi hb hd).1) j

theorem actual_envelope_mass {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (j : Fin 4) :
    actualEnvelope N δ p (convolutionWuWindows N Δ V) j ≤
      ((N : ℝ) ^ (1/2-δ)) ^ (4/p.s) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  rw [actual_envelope_eq]
  exact secondFunctionalUnit_mass_le _ _ _ (rpow_nonneg (Nat.cast_nonneg N) _) hs hs3
    (fun d hd => (omega3_source_support_le_Q hN hδ hδhi hb hd).1)
    (fun _ hx _ => actual_profiles_geometry hx)
    (fun _ hx _ _ hq => actual_fibre_geometry hp hN hδ hδhi hb hx hq)

theorem actual_source_mass {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (j : Fin 4) :
    actualSource N δ p (convolutionWuWindows N Δ V) j ≤
      ((N : ℝ) ^ (1/2-δ)) ^ (4/p.s) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
  (actual_source_le p hN hδ hδhi hb j).trans
    (actual_envelope_mass hp hs hs3 hN hδ hδhi hb j)

/-- No cancellation by the reciprocal mass, including zero-mass boxes. -/
theorem actual_zero_mass {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hM : boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) = 0) (j : Fin 4) :
    actualSource N δ p (convolutionWuWindows N Δ V) j = 0 ∧
      actualEnvelope N δ p (convolutionWuWindows N Δ V) j = 0 := by
  have hE := actual_envelope_mass hp hs hs3 hN hδ hδhi hb j
  have hS := actual_source_mass hp hs hs3 hN hδ hδhi hb j
  rw [hM, mul_zero] at hE hS
  exact ⟨le_antisymm hS (source_nonneg _ _ _ _ _ _ _ _),
    le_antisymm hE (envelope_nonneg _ _ _ _ _ _ _ _)⟩

/-- Three payment scales; every occurrence uses exactly W's original weights and Theta. -/
def Paid {i : ℕ} (N : ℕ) (δ K ε : ℝ) (W : Fin i → Finset ℕ) (X : ℝ) : Prop :=
  X ≤ ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W ∧
  X * (K * wuSingularSeries N / log N) ≤ ε * boxTheta N ((N : ℝ)^(1/2-δ)) W ∧
  X ≤ ε * boxTheta N ((N : ℝ)^(1/2-δ)) W

theorem paid_mono {i N : ℕ} {δ K ε X Y : ℝ} {W : Fin i → Finset ℕ}
    (hXY : X ≤ Y) (hd : 0 ≤ K * wuSingularSeries N / log N)
    (h : Paid N δ K ε W Y) : Paid N δ K ε W X :=
  ⟨hXY.trans h.1, (mul_le_mul_of_nonneg_right hXY hd).trans h.2.1, hXY.trans h.2.2⟩

/-- Exact four-way allocation, not four independently charged epsilons. -/
theorem paid_sum_four {i N : ℕ} {δ K ε : ℝ} {W : Fin i → Finset ℕ}
    (X : Fin 4 → ℝ) (h : ∀ j, Paid N δ K (ε/4) W (X j)) :
    Paid N δ K ε W (∑ j, X j) := by
  have h1 := sum_le_sum (s := (univ : Finset (Fin 4))) (fun j _ => (h j).1)
  have h2 := sum_le_sum (s := (univ : Finset (Fin 4))) (fun j _ => (h j).2.1)
  have h3 := sum_le_sum (s := (univ : Finset (Fin 4))) (fun j _ => (h j).2.2)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul] at h1 h2 h3
  unfold Paid
  constructor
  · nlinarith only [h1]
  constructor <;> nlinarith only [h2, h3]

/-- Parameters precede T; all boxes and every actual dictionary word follow T.
Both FOUR-TERM sums, including their density multiples, share this one threshold. -/
theorem common_payment (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (k : ℕ) {δ K ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      (∀ j : Fin 4, actualSource N δ p W j ≤ actualEnvelope N δ p W j ∧
        Paid N δ K (ε/4) W (actualSource N δ p W j) ∧
        Paid N δ K (ε/4) W (actualEnvelope N δ p W j)) ∧
      Paid N δ K ε W (∑ j : Fin 4, actualSource N δ p W j) ∧
      Paid N δ K ε W (∑ j : Fin 4, actualEnvelope N δ p W j) := by
  obtain ⟨T,hT4,hT⟩ := secondFunctionalUnit_common_payment k hδ hδhi hs hK
    (show 0 < ε/4 by positivity)
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb
  dsimp only
  have hN4 : 4 ≤ N := hT4.trans hN
  have hdens : 0 ≤ K * wuSingularSeries N / log N :=
    div_nonneg (mul_nonneg hK (wuSingularSeries_pos N (by omega)).le)
      (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hbase := hT N hN i Δ V hb
  have hE : ∀ j : Fin 4, Paid N δ K (ε/4) (convolutionWuWindows N Δ V)
      (actualEnvelope N δ p (convolutionWuWindows N Δ V) j) := by
    intro j
    exact paid_mono (actual_envelope_mass hp hs hs3 (by omega) hδ hδhi hb j) hdens hbase
  have hSE := fun j => actual_source_le p (by omega) hδ hδhi hb j
  have hS : ∀ j : Fin 4, Paid N δ K (ε/4) (convolutionWuWindows N Δ V)
      (actualSource N δ p (convolutionWuWindows N Δ V) j) :=
    fun j => paid_mono (hSE j) hdens (hE j)
  exact ⟨fun j => ⟨hSE j,hS j,hE j⟩, paid_sum_four _ hS, paid_sum_four _ hE⟩

end Wu2008DoubleSieve.FourPrimeUnit
