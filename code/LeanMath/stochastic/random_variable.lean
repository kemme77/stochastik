import Mathlib

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory

/-!
# Stochastik_Theorie_Leitfaden

Diese Datei ist ein Lean-Leitfaden zur abstrakten Theorie hinter den Folien.
Sie ist absichtlich als "Lese-Datei" aufgebaut:

1. Mengen und Ereignissprache
2. σ-Algebren und Erzeuger
3. Wahrscheinlichkeitsmaße
4. Zählmaß und endliche Beispiele
5. Produkt-σ-Algebra und Produktmaß
6. Zufallsvariablen, Gesetze und Unabhängigkeit
7. Eindimensionale Integrale über Intervalle

Die großen allgemeinen Resultate kommen in mathlib meist schon fertig vor.
Darum mischt diese Datei:

* kleine eigene Beweise,
* konkrete Beispiele,
* `#check`-Zeilen zum Auffinden der zentralen mathlib-Begriffe.
-/

namespace StochastikTheorie

/-! ## 1. Ereignissprache als Mengenrechnung -/

section EventLanguage

variable {Ω : Type*}
variable (A B : Set Ω)

example : A ∩ B ⊆ A := by
  intro ω h
  exact h.1

example : A ∩ B ⊆ B := by
  intro ω h
  exact h.2

example : A ⊆ A ∪ B := by
  intro ω h
  exact Or.inl h

example : B ⊆ A ∪ B := by
  intro ω h
  exact Or.inr h

example : A ∩ Aᶜ = (∅ : Set Ω) := by
  ext ω
  simp

example : A ∪ Aᶜ = (Set.univ : Set Ω) := by
  ext ω
  simp

end EventLanguage

/-! ## 2. σ-Algebren und Erzeuger -/

section SigmaAlgebras

#check MeasurableSpace
#check MeasurableSpace.generateFrom

/-- Ein konkretes Erzeugersystem auf `ℝ`: alle linken Halbstrahlen `(-∞, a]`. -/
def halfLineGenerators : Set (Set ℝ) := Set.range Set.Iic

/-- Die davon erzeugte σ-Algebra. -/
def sigmaFromIic : MeasurableSpace ℝ := MeasurableSpace.generateFrom halfLineGenerators

example (a : ℝ) : Set.Iic a ∈ halfLineGenerators := by
  exact ⟨a, rfl⟩

/- In mathlib ist die Borel-σ-Algebra auf linearen Ordnungen durch Halbstrahlen erzeugt. -/
#check borel_eq_generateFrom_Iic

/-- Für `ℝ` bekommt man also genau die Borel-σ-Algebra. -/
example : borel ℝ = sigmaFromIic := by
  simpa [sigmaFromIic, halfLineGenerators] using (borel_eq_generateFrom_Iic (α := ℝ))

end SigmaAlgebras

/-! ## 3. Wahrscheinlichkeitsmaße -/

section ProbabilityMeasures

#check Measure
#check IsProbabilityMeasure
#check MeasureTheory.ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

/-- In mathlib heißt "Wahrscheinlichkeitsmaß" genau `μ univ = 1`. -/
example [IsProbabilityMeasure μ] : μ Set.univ = 1 := by
  simp [MeasureTheory.IsProbabilityMeasure.measure_univ (μ := μ)]

/-- Ein ganz kleines Beispiel: das Dirac-Maß auf `PUnit` ist ein Wahrscheinlichkeitsmaß. -/
example : (Measure.dirac PUnit.unit : Measure PUnit) Set.univ = 1 := by
  simp

end ProbabilityMeasures

/-! ## 4. Zählmaß und endliche Beispiele -/

section CountingMeasure

#check Measure.count

/-- Auf endlichen Mengen ist das Zählmaß besonders anschaulich. -/
example : (Measure.count : Measure ℕ) ({0} : Set ℕ) = 1 := by
  simp

example : (Measure.count : Measure ℕ) ({0, 1, 2} : Set ℕ) = 3 := by
  rw [Measure.count_apply_finite _ (by simp)]
  norm_num

example : (Measure.count : Measure ℕ) (∅ : Set ℕ) = 0 := by
  simp

end CountingMeasure

/-! ## 5. Produkt-σ-Algebra -/

section ProductSigma

#check generateFrom_prod

/-- Rechtecke im Produktraum werden in Lean als `s ×ˢ t` geschrieben. -/
example : ({0} : Set ℕ) ×ˢ ({1, 2} : Set ℕ) =
    {p : ℕ × ℕ | p.1 = 0 ∧ (p.2 = 1 ∨ p.2 = 2)} := by
  ext p
  rcases p with ⟨m, n⟩
  constructor
  · intro h
    rcases h with ⟨hm, hn⟩
    have hm' : m = 0 := by simpa using hm
    have hn' : n = 1 ∨ n = 2 := by simpa using hn
    exact ⟨hm', hn'⟩
  · rintro ⟨hm, hn⟩
    have hm' : m = 0 := by simpa using hm
    have hn' : n = 1 ∨ n = 2 := by simpa using hn
    simp [hm', hn']

/- Die Produkt-σ-Algebra wird von messbaren Rechtecken erzeugt. -/

end ProductSigma

/-! ## 6. Produktmaß -/

section ProductMeasure

#check Measure.prod
#check Measure.prod_apply
#check Measure.prod_prod

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β)

/-- Das Produktmaß in mathlib ist `μ.prod ν`. -/
noncomputable def myProd : Measure (α × β) := μ.prod ν

/-- Auf Rechtecken ist die Maßformel genau die erwartete Produktformel. -/
example [SFinite ν] (s : Set α) (t : Set β) :
    (μ.prod ν) (s ×ˢ t) = μ s * ν t := by
  simp [Measure.prod_prod (μ := μ) (ν := ν) s t]

/-- Konkretes Beispiel mit Zählmaß: ein 2x3-Rechteck hat Maß 6. -/
example :
    ((Measure.count : Measure ℕ).prod Measure.count)
      (((( {0, 1} : Finset ℕ) : Set ℕ)) ×ˢ (((( {10, 11, 12} : Finset ℕ) : Set ℕ)))) = 6 := by
  rw [Measure.prod_prod]
  rw [Measure.count_apply_finite _ (by simp), Measure.count_apply_finite _ (by simp)]
  norm_num

end ProductMeasure

/-! ## 7. Zufallsvariablen und Gesetze -/

section Laws

#check Measurable
#check AEMeasurable
#check Measure.map
#check ProbabilityTheory.HasLaw

variable {Ω α β : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
variable (P : Measure Ω)
variable (X : Ω → α) (Y : Ω → β)

/-- Die gemeinsame Verteilung ist das Bildmaß der Paarabbildung. -/
noncomputable def jointLaw : Measure (α × β) := Measure.map (fun ω => (X ω, Y ω)) P

/- `HasLaw` ist die mathlib-Sprache für "X hat unter P die Verteilung μ". -/
#check ProbabilityTheory.HasLaw.id

example (μ : Measure α) : HasLaw (id : α → α) μ μ := by
  simpa using (ProbabilityTheory.HasLaw.id (μ := μ))

end Laws

/-! ## 8. Unabhängigkeit -/

section Independence

#check Indep
#check iIndep
#check IndepFun
#check iIndepFun
#check ProbabilityTheory.IndepFun.hasLaw_add

variable {Ω α β : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
variable (P : Measure Ω)
variable (X : Ω → α) (Y : Ω → β)

/- Die Aussage selbst ist schon ein gutes Vorlesungsobjekt. -/
#check IndepFun X Y P

end Independence

/-! ## 9. Intervalle und eindimensionale Integrale -/

section IntervalIntegrals

#check intervalIntegral.integral_const
#check intervalIntegral.integral_zero

/-- Das Integral der konstanten Funktion 1 über [0,1] ist 1. -/
example : ∫ _ in (0 : ℝ)..1, (1 : ℝ) = 1 := by
  norm_num

/-- Das Integral der konstanten Funktion 3 über [0,2] ist 6. -/
example : ∫ _ in (0 : ℝ)..2, (3 : ℝ) = 6 := by
  norm_num

/-- Orientierung spielt bei Intervallintegralen eine Rolle. -/
example : ∫ _ in (2 : ℝ)..0, (1 : ℝ) = -2 := by
  norm_num

/-- Hinter `intervalIntegral.integral_const` steckt die Formel `(b-a) • c`. -/
example (a b c : ℝ) : ∫ _ in a..b, c = (b - a) * c := by
  simp [intervalIntegral.integral_const (a := a) (b := b) (c := c)]

end IntervalIntegrals

/-! ## 10. Mini-Brücke zum Laplace-Experiment -/

section FiniteProbabilityDemo

inductive Coin where
  | K
  | Z
  deriving DecidableEq, Fintype

open Coin

abbrev Ω2 := Fin 2 → Coin

/-- Auf einem endlichen diskreten Raum ist jede Funktion messbar. -/
instance : MeasurableSpace Ω2 := ⊤

instance : Nonempty Ω2 := ⟨fun _ => K⟩

/-- Das Laplace-Maß auf `Ω2`: alle vier Ausgänge sind gleich wahrscheinlich. -/
noncomputable def laplaceMeasure : Measure Ω2 := uniformOn (Set.univ : Set Ω2)

/-- Im mathlib-Sinn ist das Laplace-Maß ein Wahrscheinlichkeitsmaß. -/
noncomputable instance : IsProbabilityMeasure laplaceMeasure :=
  uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty

/-- Also gilt insbesondere `μ univ = 1`. -/
example : laplaceMeasure Set.univ = 1 := by
  simp [MeasureTheory.IsProbabilityMeasure.measure_univ (μ := laplaceMeasure)]

/-- Zwei einfache 0-1-Funktionen. -/
def X1 : Ω2 → ℝ := fun ω => if ω ⟨0, by decide⟩ = K then 1 else 0

def X2 : Ω2 → ℝ := fun ω => if ω ⟨1, by decide⟩ = K then 1 else 0

/-- Das Bildmaß von `X1` unter dem Laplace-Maß. -/
noncomputable def lawX1 : Measure ℝ := Measure.map X1 laplaceMeasure

example : Measurable X1 := by
  simpa using measurable_of_finite X1

example : Measurable X2 := by
  simpa using measurable_of_finite X2

/-- `X1` hat unter dem Laplace-Maß die Verteilung `lawX1`. -/
example : HasLaw X1 lawX1 laplaceMeasure := by
  refine ⟨?_, rfl⟩
  simpa using (measurable_of_finite X1).aemeasurable

/-- Die Wahrscheinlichkeit des Werts `1` im Bildmaß ist die Wahrscheinlichkeit von `X1 = 1`. -/
example : lawX1 {1} = laplaceMeasure {ω | X1 ω = 1} := by
  rw [lawX1, Measure.map_apply (measurable_of_finite X1) (measurableSet_singleton 1)]
  rfl

/-- Das Integral über das Bildmaß ist das Integral der Zufallsvariable selbst. -/
example : ∫ x, x ∂ lawX1 = ∫ ω, X1 ω ∂ laplaceMeasure := by
  rw [lawX1]
  simpa using
    (integral_map ((measurable_of_finite X1).aemeasurable) aestronglyMeasurable_id :
      ∫ x, x ∂ Measure.map X1 laplaceMeasure = ∫ ω, X1 ω ∂ laplaceMeasure)

/- Auf endlichen diskreten Räumen ist das genau das formale Gegenstück zur
Vorlesungsintuition "jede 0-1-Anzeige ist eine Zufallsvariable". -/

end FiniteProbabilityDemo

end StochastikTheorie
