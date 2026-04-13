import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

section FiniteMarkov

variable {Ω : Type*}
variable [MeasurableSpace Ω]

variable {N : ℕ}
abbrev S (N : ℕ) := Fin N

def IsTransitionMatrix (P : S N → S N → ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧
  (∀ x, (∑ y, P x y) = 1)

noncomputable def stepOp (P : S N → S N → ℝ) (f : S N → ℝ) : S N → ℝ :=
  fun x => ∑ y, P x y * f y

def IsHomogeneousMarkov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (X : ℕ → Ω → S N)
    (P : S N → S N → ℝ) : Prop :=
  Adapted ℱ X ∧
  ∀ n (f : S N → ℝ),
    Measurable f →
    Integrable (fun ω => f (X (n + 1) ω)) μ →
    μ[(fun ω => f (X (n + 1) ω))|ℱ n] =ᵐ[μ]
      fun ω => stepOp P f (X n ω)

lemma condexp_next_eq_step
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (X : ℕ → Ω → S N)
    (P : S N → S N → ℝ)
    (hM : IsHomogeneousMarkov (N := N) μ ℱ X P)
    (n : ℕ) (f : S N → ℝ)
    (hf_meas : Measurable f)
    (hf_int : Integrable (fun ω => f (X (n + 1) ω)) μ) :
    μ[(fun ω => f (X (n + 1) ω))|ℱ n] =ᵐ[μ]
      fun ω => stepOp P f (X n ω) :=
by
  exact hM.2 n f hf_meas hf_int

noncomputable def natFiltration
    (X : ℕ → Ω → S N)
    (hX : ∀ i, StronglyMeasurable (X i)) :
    Filtration ℕ (by infer_instance : MeasurableSpace Ω) :=
  Filtration.natural X hX

noncomputable def matMul (P Q : S N → S N → ℝ) : S N → S N → ℝ :=
  fun x z => ∑ y, P x y * Q y z

noncomputable def matPow (P : S N → S N → ℝ) : ℕ → S N → S N → ℝ
  | 0     => fun x z => if x = z then 1 else 0
  | n + 1 => matMul (matPow P n) P

lemma matPow_succ (P : S N → S N → ℝ) (n : ℕ) :
    matPow (N := N) P (n + 1) = matMul (matPow P n) P := by
  rfl

def IsHarmonic (P : S N → S N → ℝ) (h : S N → ℝ) : Prop :=
  ∀ x, stepOp P h x = h x

lemma harmonic_condexp_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (X : ℕ → Ω → S N)
    (P : S N → S N → ℝ)
    (hM : IsHomogeneousMarkov (N := N) μ ℱ X P)
    (h : S N → ℝ)
    (hharm : IsHarmonic (N := N) P h)
    (n : ℕ)
    (hint : Integrable (fun ω => h (X (n + 1) ω)) μ) :
    μ[(fun ω => h (X (n + 1) ω))|ℱ n] =ᵐ[μ]
      fun ω => h (X n ω) := by
  have h1 :=
    hM.2 n h (by simpa using measurable_of_finite h) hint
  filter_upwards [h1] with ω hω
  exact hω.trans (hharm (X n ω))

end FiniteMarkov

section TwoState

abbrev S2 := Fin 2

def P2 (a b : ℝ) : S2 → S2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 1 - a
  | ⟨0, _⟩, ⟨1, _⟩ => a
  | ⟨1, _⟩, ⟨0, _⟩ => b
  | ⟨1, _⟩, ⟨1, _⟩ => 1 - b

lemma P2_isTransitionMatrix
    {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    IsTransitionMatrix (N := 2) (P2 a b) := by
  constructor
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [P2, sub_nonneg, ha0, ha1, hb0, hb1]
  · intro x
    fin_cases x <;> simp [P2]

end TwoState
