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
    Integrable (fun ω => f (X (n+1) ω)) μ →
    μ[(fun ω => f (X (n+1) ω))|ℱ n] =ᵐ[μ]
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
