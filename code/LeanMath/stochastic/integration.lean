import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.StrongLaw


/-
Ziele:
- Grundidee eines Wahrscheinlichkeitsraums
- Zufallsvariablen als messbare Funktionen
- Wahrscheinlichkeitsmaß und Ereignisse
- Erwartungswert (Integral)
- Schwaches Gesetz der großen Zahlen (informell)
-/


open scoped BigOperators
open scoped ProbabilityTheory
open scoped Topology
open scoped Function
open Set MeasureTheory
open Filter
-- filepath: /Users/johannesriesterer/Documents/code/KI_Agenten_Demo/powerset_measurable.lean

variable {α : Type*}

-- Die Potenzmenge ist die diskrete σ-Algebra: „jede Menge ist messbar“.
def powersetMeasurableSet (_s : Set α) : Prop :=
  True

-- Daraus bauen wir eine `MeasurableSpace`-Struktur explizit.
def powersetMeasurableSpace : MeasurableSpace α where
  MeasurableSet' := powersetMeasurableSet (α := α)
  measurableSet_empty := trivial
  measurableSet_compl := by
    intro s hs
    trivial
  measurableSet_iUnion := by
    intro f hf
    trivial

-- Alternativ: In Mathlib gibt es bereits die Instanz
#check (⊤ : MeasurableSpace α) -- die diskrete σ-Algebra: alle Mengen sind messbar

-- Beweis: Jede Teilmenge ist messbar
example (s : Set α) : MeasurableSet[powersetMeasurableSpace] s :=
  by simp [powersetMeasurableSpace]

/- ## 1) Wahrscheinlichkeitsraum -/

section ProbabilitySpace

/- Abstraktes Ergebnisraum `Ω` mit messbarer Struktur. -/
variable (Ω : Type*) [MeasurableSpace Ω]

/- Ein Wahrscheinlichkeitsmaß ist ein Maß mit Gesamtmasse 1. -/
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/- Ereignisse sind messbare Mengen. -/
#check (MeasurableSet : Set Ω → Prop)

/- Wahrscheinlichkeit eines Ereignisses. -/
#check (μ : Measure Ω)
#check (μ (Set.univ))
#check (μ (Set.univ) = (1 : ENNReal))

end ProbabilitySpace

/- ## 2) Zufallsvariablen -/

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω]
variable {β : Type*} [MeasurableSpace β]

/- Zufallsvariable: messbare Funktion in einen messbaren Raum. -/
def RandomVariable (X : Ω → β) : Prop := Measurable X

/- Der Standardtyp: reellwertige Zufallsvariable. -/
#check (Measurable : (Ω → ℝ) → Prop)

end RandomVariables

/- ## 3) Erwartungswert -/

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/- Erwartungswert als Integral. -/
noncomputable def Erwartungswert (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂μ

#check (∫ _ : Ω, (0 : ℝ) ∂μ)
#check (Erwartungswert μ)

end Expectation

/- ## 4) Begriffe: Konvergenz, Unabhängigkeit, Varianz -/

section Basics

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/- Konvergenz in Wahrscheinlichkeit (Definition). -/
def KonvInWahrscheinlichkeit (X : ℕ → Ω → ℝ) (Xlim : Ω → ℝ) : Prop :=
  ∀ ε > 0,
    Tendsto (fun n => μ {ω | ε < |X n ω - Xlim ω|}) atTop (𝓝 0)

/- Unabhängigkeit zweier Ereignisse (Definition). -/
def UnabhaengigEreignisse (A B : Set Ω) : Prop :=
  μ (A ∩ B) = μ A * μ B

/- Varianz als Erwartungswert der quadratischen Abweichung. -/
noncomputable def Varianz (X : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - (Erwartungswert μ X))^2 ∂μ

end Basics

/- ## 5) Wahrscheinlichkeitsmaß auf endlichen Räumen (informell) -/

/-
In endlichen Ergebnisräumen kann man ein Wahrscheinlichkeitsmaß durch
Zuweisung von Gewichten an jedes Element angeben. In mathlib existieren
geeignete Strukturen, z. B. über diskrete Maße oder PMFs.

Wir bleiben hier auf der konzeptionellen Ebene.
-/

/- ## 6) Schwaches Gesetz der großen Zahlen (informell) -/

/-
Informeller Inhalt:
Sei `(X_n)` eine Folge i.i.d. Zufallsvariablen mit endlichem Erwartungswert.
Dann konvergiert der Stichprobenmittelwert

$$\bar X_n = \frac{1}{n}\sum_{k=1}^n X_k$$

in Wahrscheinlichkeit gegen `E[X_1]`.

In mathlib gibt es Resultate zur Konvergenz in Wahrscheinlichkeit und zu
Gesetzen großer Zahlen. Für eine Lehrveranstaltung ist es sinnvoll, die
notwendigen Begriffe (Konvergenzarten, Unabhängigkeit, Varianz, etc.)
schrittweise aufzubauen und dann auf existierende Sätze zu verweisen.
-/

/- ## 7) Schwaches Gesetz der großen Zahlen (formal) -/

section WeakLaw

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
/-- Schwaches Gesetz der großen Zahlen (als Konvergenz in Wahrscheinlichkeit).
    Beweis: starkes Gesetz (fast sicher) ⇒ Konvergenz in Wahrscheinlichkeit. -/
theorem weak_law_in_probability
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω => ((∑ i ∈ Finset.range n, X i) / n) ω)
      atTop
      (fun _ => μ[X 0]) := by
  have hAE :
      ∀ᵐ ω ∂μ, Tendsto (fun n => ((∑ i ∈ Finset.range n, X i) / n) ω) atTop (𝓝 μ[X 0]) := by
    simpa using (ProbabilityTheory.strong_law_ae_real X hint hindep hident)
  have hmeas :
      ∀ n, AEStronglyMeasurable (fun ω => ((∑ i ∈ Finset.range n, X i) / n) ω) μ := by
    intro n
    classical
    have hXi : ∀ i, AEStronglyMeasurable (X i) μ := by
      intro i
      have hInt : Integrable (X i) μ := ((hident i).integrable_iff).2 hint
      exact hInt.aestronglyMeasurable
    have hsum_fun :
        AEStronglyMeasurable (∑ i ∈ Finset.range n, X i) μ := by
      refine Finset.aestronglyMeasurable_sum (s := Finset.range n) (f := fun i => X i) ?_
      intro i hi
      exact hXi i
    simpa [div_eq_mul_inv] using hsum_fun.mul_const ((n : ℝ)⁻¹)
  exact tendstoInMeasure_of_tendsto_ae (μ := μ)
    (f := fun n ω => ((∑ i ∈ Finset.range n, X i) / n) ω)
    (g := fun _ => μ[X 0]) hmeas hAE

end WeakLaw


variable {α : Type _} [MeasurableSpace α]
variable (μ : Measure α)

example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
Iff.rfl
