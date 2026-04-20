import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Kernel.IndepFun
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Basic

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory Topology
open Set MeasureTheory

noncomputable section

/-!
# Stochastik in Lean / mathlib

Diese Datei spiegelt einen Teil der Vorlesungsfolien zu Wahrscheinlichkeitstheorie,
Maßtheorie, Topologie und Integration in Lean 4 / mathlib wider.

Ziel:
- die wichtigsten Definitionen in mathlib sichtbar machen,
- zentrale Sätze in Lean-Notation formulieren,
- einige Beweise direkt in Lean geben,
- an mehreren Stellen kommentieren, was mathlib bereits fertig bereitstellt.

Die Datei ist bewusst zugleich:
1. ein Lean-Skript,
2. ein kommentiertes Lernskript.

Nicht jeder Folienbeweis wird hier 1:1 formalisiert; an mehreren Stellen verweist mathlib auf
bereits vorhandene Standardtheoreme.
-/

namespace StochastikMathlib

/-! ## 1. σ-Algebra und Messbarkeit -/

/-
In den Folien wird eine σ-Algebra als Mengensystem eingeführt.
In mathlib ist die entsprechende Struktur `MeasurableSpace α`.
-/

example (Ω : Type*) [m : MeasurableSpace Ω] : MeasurableSpace Ω := m

/-
Messbarkeit einer Funktion `f : Ω → ℝ` heißt in mathlib schlicht `Measurable f`.
-/
example {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Prop := Measurable X

/-
Ein messbarer Raum liefert den Begriff `MeasurableSet`.
-/
example {Ω : Type*} [MeasurableSpace Ω] (A : Set Ω) : Prop := MeasurableSet A

/-! ## 2. Erzeugte σ-Algebren -/

/-
Die auf den Folien definierte erzeugte σ-Algebra ist in mathlib
`MeasurableSpace.generateFrom G`, wobei `G : Set (Set Ω)` ein Mengensystem ist.
-/
example (Ω : Type*) (G : Set (Set Ω)) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom G

/-
Jedes Erzeugersystem ist in der erzeugten σ-Algebra messbar.
-/
example {Ω : Type*} (G : Set (Set Ω)) {A : Set Ω} (hA : A ∈ G) :
    @MeasurableSet Ω (MeasurableSpace.generateFrom G) A := by
  exact MeasurableSpace.measurableSet_generateFrom hA

/-
Minimalität der erzeugten σ-Algebra:
Wenn `m` eine σ-Algebra ist, die alle Erzeuger aus `G` enthält,
dann liegt `generateFrom G ≤ m`.
-/
example {Ω : Type*} (G : Set (Set Ω)) (m : MeasurableSpace Ω)
    (hG : ∀ A ∈ G, @MeasurableSet Ω m A) :
    MeasurableSpace.generateFrom G ≤ m := by
  exact MeasurableSpace.generateFrom_le hG

/-
Das ist genau die Lean-Version der Existenz- und Minimalitätsaussage
für die erzeugte σ-Algebra aus den Folien.
-/

/-! ## 3. Topologische Räume und Borel-σ-Algebra -/

/-
Ein topologischer Raum in mathlib ist eine Instanz von `TopologicalSpace X`.
-/
example (X : Type*) [TopologicalSpace X] : TopologicalSpace X := inferInstance

/-
Offene Mengen heißen in mathlib `IsOpen`.
-/
example {X : Type*} [TopologicalSpace X] (U : Set X) : Prop := IsOpen U

/-
Die borelsche σ-Algebra auf einem topologischen Raum `X` heißt `borel X`.
-/
example (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X

/-
Definitionell ist die borelsche σ-Algebra die von den offenen Mengen erzeugte σ-Algebra.
-/
example (X : Type*) [TopologicalSpace X] :
    borel X = MeasurableSpace.generateFrom {U : Set X | IsOpen U} := rfl

/-
Spezialfall `ℝ`.
-/
example : MeasurableSpace ℝ := borel ℝ

/-
Auch auf `Fin n → ℝ` (also kanonisch `ℝ^n`) gibt es die borelsche σ-Algebra.
-/
example (n : ℕ) : MeasurableSpace (Fin n → ℝ) := borel (Fin n → ℝ)

/-
Ein offenes Intervall in `ℝ` ist borel-messbar.
-/
example (a b : ℝ) : @MeasurableSet ℝ (borel ℝ) (Set.Ioo a b) := by
  exact IsOpen.measurableSet isOpen_Ioo

/-
Ein abgeschlossener Halbstrahl `(-∞, a] = Iic a` ist borel-messbar.
-/
example (a : ℝ) : @MeasurableSet ℝ (borel ℝ) (Set.Iic a) := by
  exact measurableSet_Iic

/-! ## 4. Messbarkeit über Erzeuger -/

/-
Die Folien enthalten den Satz:

Ist `𝓔 = σ(G)`, dann reicht es für die Messbarkeit von `X : Ω → E`,
die Urbilder der Erzeuger `G` zu kontrollieren.

Das kann man in Lean sehr prägnant formulieren.
-/
theorem measurable_of_generateFrom
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    {G : Set (Set E)} {X : Ω → E}
    (hG : ∀ A ∈ G, MeasurableSet (X ⁻¹' A)) :
    @Measurable Ω E mΩ (MeasurableSpace.generateFrom G) X := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  intro S hS
  rcases hS with ⟨A, hA, rfl⟩
  exact hG A hA

/-
Die "Hinrichtung" ist ebenfalls direkt klar:
Ist `X` messbar in die erzeugte σ-Algebra, dann sind die Urbilder der Erzeuger messbar.
-/
theorem measurableSet_preimage_of_mem_generateFrom
    {Ω E : Type*} [MeasurableSpace Ω]
    {G : Set (Set E)} {X : Ω → E}
    (hX : @Measurable Ω E _ (MeasurableSpace.generateFrom G) X)
    {A : Set E} (hA : A ∈ G) :
    MeasurableSet (X ⁻¹' A) := by
  exact (MeasurableSpace.measurableSet_generateFrom hA).preimage hX

/-
Zusammengefasst erhält man die Äquivalenz aus den Folien.
-/
theorem measurable_iff_generateFrom
    {Ω E : Type*} [MeasurableSpace Ω]
    {G : Set (Set E)} {X : Ω → E} :
    @Measurable Ω E _ (MeasurableSpace.generateFrom G) X
      ↔ ∀ A ∈ G, MeasurableSet (X ⁻¹' A) := by
  constructor
  · intro hX A hA
    exact measurableSet_preimage_of_mem_generateFrom hX hA
  · intro hG
    exact measurable_of_generateFrom hG

/-
Praktisch sehr wichtig ist der Spezialfall der borelschen σ-Algebra auf `ℝ`,
erzeugt von den Halbstrahlen `(-∞, a]`.
mathlib stellt dafür direkt den Standardsatz `measurable_of_Iic` bereit.
-/
example {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} :
    Measurable X ↔ ∀ a : ℝ, MeasurableSet (X ⁻¹' Set.Iic a) := by
  constructor
  · intro hX a
    exact measurableSet_Iic.preimage hX
  · intro hX
    refine measurable_of_Iic ?_
    intro a
    exact hX a

/-! ## 5. Maß und Wahrscheinlichkeitsmaß -/

/-
Ein Maß ist in mathlib `Measure Ω`.
-/
example (Ω : Type*) [MeasurableSpace Ω] : Type _ := Measure Ω

/-
Ein Wahrscheinlichkeitsmaß ist `ProbabilityMeasure Ω`.
-/
example (Ω : Type*) [MeasurableSpace Ω] : Type _ := ProbabilityMeasure Ω

/-
Man kann ein Wahrscheinlichkeitsmaß als gewöhnliches Maß auffassen.
-/
example {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω) : Measure Ω := P.toMeasure

/-
Die Gesamtmasse eines Wahrscheinlichkeitsmaßes ist 1.
-/
set_option trace.Meta.Tactic.simp true in
example {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω) :
    P.toMeasure univ = 1 := by
  simp

/-! ## 6. Zufallsvariable, Verteilung und Bildmaß -/

/-
Auf den Folien ist eine Zufallsvariable eine messbare Abbildung.
In mathlib gibt es dafür keine neue primitive Struktur; man arbeitet direkt mit
messbaren Funktionen.
-/
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (X : Ω → E) : Prop :=
  Measurable X

/-
Die induzierte Verteilung / das Bildmaß einer messbaren Funktion `X` ist `Measure.map X μ`.
-/
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) : Measure E := Measure.map X μ

/-
Die Definition auf den Folien lautet:
  P_X(B) = P(X ∈ B) = P(X⁻¹(B)).
Genau das ist die Definition von `Measure.map`.
-/
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) {X : Ω → E} (hX : Measurable X) (B : Set E) (hB : MeasurableSet B) :
    Measure.map X μ B = μ (X ⁻¹' B) := by
  simpa using Measure.map_apply hX hB

/-! ## 7. Einfache Funktionen und Integral -/

/-
Die Folien führen einfache Funktionen ein. In mathlib ist der zentrale Typ
`SimpleFunc α β`. Für die Theorie des Integrals benutzt mathlib intern auch
`AEEqFun`, `ℒp`, `lintegral`, `integral`, usw.

Hier zeigen wir nur exemplarisch, dass es den Typ der einfachen Funktionen gibt.
-/
example (Ω : Type*) [MeasurableSpace Ω] : Type _ := SimpleFunc Ω ℝ≥0∞

/-
Nichtnegatives Integral: `∫⁻ x, f x ∂μ`
Gewöhnliches Integral:   `∫ x,  f x ∂μ`
-/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, f x ∂μ

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ x, f x ∂μ

/-
Integrierbarkeit heißt `Integrable f μ`.
-/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  Integrable f μ

/-
Diskreter Spezialfall auf den Folien: Summenformel für endliche Räume.
Das direkt in voller Allgemeinheit zu formalisieren ist etwas aufwendiger;
wir zeigen stattdessen einfache Integrationsregeln, die mathlib direkt kennt.
-/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    ∫ _ : Ω, (0 : ℝ) ∂μ = 0 := by
  simp

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) [IsFiniteMeasure μ] :
    ∫ _ : Ω, c ∂μ = μ.real univ * c := by
  simp [mul_comm]

/-! ## 8. Monotone Approximation des nichtnegativen Integrals -/

/-
Für nichtnegative messbare Funktionen kann man das Integral mit monoton wachsenden
Folgen berechnen. Das ist die Lean-Version des Satzes von der monotonen Konvergenz.
-/
theorem lintegral_eq_iSup_of_monotone
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (φ : ℕ → Ω → ℝ≥0∞)
    (hφm : ∀ n, Measurable (φ n))
    (hφmono : Monotone φ)
    (hφsup : ∀ x, (⨆ n, φ n x) = f x) :
    ∫⁻ x, f x ∂μ = ⨆ n, ∫⁻ x, φ n x ∂μ := by
  have hf : f = fun x => ⨆ n, φ n x := by
    funext x
    exact (hφsup x).symm
  rw [hf]
  simpa using lintegral_iSup hφm hφmono

/-
Haben zwei monotone Approximationen dieselbe Grenzfunktion `f`, dann liefern beide
denselben Integralwert.
-/
theorem monotone_approximation_unique
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞)
    (φ ψ : ℕ → Ω → ℝ≥0∞)
    (hφm : ∀ n, Measurable (φ n))
    (hφmono : Monotone φ)
    (hψm : ∀ n, Measurable (ψ n))
    (hψmono : Monotone ψ)
    (hφsup : ∀ x, (⨆ n, φ n x) = f x)
    (hψsup : ∀ x, (⨆ n, ψ n x) = f x) :
    (⨆ n, ∫⁻ x, φ n x ∂μ) = ⨆ n, ∫⁻ x, ψ n x ∂μ := by
  calc
    (⨆ n, ∫⁻ x, φ n x ∂μ) = ∫⁻ x, f x ∂μ := by
      symm
      exact lintegral_eq_iSup_of_monotone μ f φ hφm hφmono hφsup
    _ = (⨆ n, ∫⁻ x, ψ n x ∂μ) := by
      exact lintegral_eq_iSup_of_monotone μ f ψ hψm hψmono hψsup

/-
Der Spezialfall des Satzes von der monotonen Konvergenz:
Das Integral des punktweisen Supremums ist das Supremum der Integrale.
-/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (φ : ℕ → Ω → ℝ≥0∞)
    (hφm : ∀ n, Measurable (φ n))
    (hφmono : Monotone φ) :
    ∫⁻ x, ⨆ n, φ n x ∂μ = ⨆ n, ∫⁻ x, φ n x ∂μ := by
  simpa using lintegral_iSup hφm hφmono

/-! ## 9. Produktmaß, Lebesgue-Maß und Fubini -/

/-
Produktmaß: `μ.prod ν`
-/
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) : Measure (α × β) := μ.prod ν

/-
Der Spezialfall auf Rechtecken:
(μ × ν)(A ×ˢ B) = μ(A) * ν(B)
-/
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] {A : Set α} {B : Set β} :
    μ.prod ν (A ×ˢ B) = μ A * ν B := by
  exact Measure.prod_prod (μ := μ) (ν := ν) A B

/-
Das Lebesgue-Maß auf `ℝ` heißt in mathlib `volume`.
-/
example : Measure ℝ := volume

/-
Auf dem Produktraum `ℝ × ℝ` ist `volume.prod volume` das zugehörige Produktmaß.
-/
example : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume

/-
Für Rechtecke in `ℝ × ℝ` ergibt das Produktmaß das Produkt der Längen.
-/
example (A B : Set ℝ) [SFinite (volume : Measure ℝ)] :
    ((volume : Measure ℝ).prod volume) (A ×ˢ B) = volume A * volume B := by
  exact Measure.prod_prod (μ := (volume : Measure ℝ)) (ν := volume) A B

/-
Fubini / Tonelli stehen in mathlib in vielen Varianten bereit.
Eine sehr typische Formel ist:
-/
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (f : α × β → ℝ)
    (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  simpa using (MeasureTheory.integral_integral (f := fun x y => f (x, y)) hf).symm

/-! ## 10. Gleichverteilung auf einem Intervall -/

/-
In den Folien wird die Gleichverteilung auf `[a,b]` als Maß mit Dichte bezüglich
des Lebesgue-Maßes beschrieben. In Lean ist dafür `withDensity volume p` die
passende Konstruktion.
-/
example (a b : ℝ) : Measure ℝ :=
  Measure.withDensity volume
    (fun x =>
      (ENNReal.ofReal (b - a))⁻¹ *
        Set.indicator (Set.Icc a b) (fun _ => (1 : ℝ≥0∞)) x)

/-
Für die Vorlesung ist meist die inhaltliche Aussage wichtiger:
man integriert die Dichte gegen `volume`, also gegen das Lebesgue-Maß auf `ℝ`.
-/

/-! ## 11. Dichten -/

/-
In den Folien ist eine Dichte `p` eines Maßes `μ` bezüglich des Lebesgue-Maßes durch
  μ(A) = ∫_A p dλ
gegeben.

In mathlib ist die saubere abstrakte Sprache dafür der Radon–Nikodym-Ableitung
`μ.rnDeriv ν`. Für konkrete elementare Vorlesungsnotizen ist es oft nützlich,
die elementare Formel einfach als Eigenschaft zu formulieren.
-/

def HasDensityRn {n : ℕ} (μ : Measure (Fin n → ℝ)) (p : (Fin n → ℝ) → ℝ≥0∞) : Prop :=
  μ = Measure.withDensity volume p

/-
`withDensity volume p` ist genau das Maß mit Dichte `p` bezüglich des Lebesgue-Maßes.
-/
example {n : ℕ} (p : (Fin n → ℝ) → ℝ≥0∞) : Measure (Fin n → ℝ) :=
  Measure.withDensity volume p

/-
Integration mit Dichte:
-/
example {n : ℕ} (p : (Fin n → ℝ) → ℝ≥0∞) (f : (Fin n → ℝ) → ℝ≥0∞)
    (hp : Measurable p) (hf : Measurable f) :
    ∫⁻ x, f x ∂(Measure.withDensity volume p) = ∫⁻ x, f x * p x ∂volume := by
  simpa [Pi.mul_apply, mul_comm] using
    (lintegral_withDensity_eq_lintegral_mul volume hp hf)

/-
Für reellwertige Integrale existieren entsprechende Sätze, meist unter Integrabilitätsannahmen.
-/

/-! ## 12. Bildmaß und Transformationssatz -/

/-
Der Transformationssatz der Folien lautet allgemein:

∫_Y f d(T#μ) = ∫_X f∘T dμ.

In mathlib ist das genau `lintegral_map` bzw. `integral_map`.
-/
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {T : X → Y} (hT : Measurable T) (f : Y → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(Measure.map T μ) = ∫⁻ x, f (T x) ∂μ := by
  simpa using lintegral_map hf hT

/-
Für integrierbare reellwertige Funktionen gibt es die analoge Formel.
-/
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {T : X → Y} (hT : Measurable T) (f : Y → ℝ)
    (hf : Integrable f (Measure.map T μ)) :
    ∫ y, f y ∂(Measure.map T μ) = ∫ x, f (T x) ∂μ := by
  simpa using integral_map hT.aemeasurable hf.aestronglyMeasurable

/-
Spezialfall Zufallsvariable:
Die Verteilung ist das Bildmaß von `P` unter `X`.
-/
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) {X : Ω → E} (hX : Measurable X) (g : E → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(Measure.map X P) = ∫⁻ ω, g (X ω) ∂P := by
  simpa using lintegral_map hg hX

/-! ## 13. Unabhängigkeit -/

/-
Auf den Folien wird Unabhängigkeit über Rechtecke definiert.
mathlib hat dafür die Begriffe `Indep`, `iIndep`, `IndepFun`, `IndepSet`, ...
-/
example {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  ProbabilityTheory.IndepFun X Y μ

/-
Eine Standardcharakterisierung ist, dass unabhängige Zufallsvariablen ein Produktmaß
als gemeinsame Verteilung besitzen. Dieses Resultat ist in mathlib in vorhandenen Sätzen
über `IndepFun` und `map` / `comap` verteilt.

Hier zeigen wir zunächst nur die Definitionsebene.
-/

/-! ## 14. Kleine konkrete Beispiele -/

/-
### Beispiel 1: Erwartungswert einer Konstanten
-/
example (c : ℝ) :
    ∫ _ : ℝ in (Set.univ : Set ℝ), c ∂(volume.restrict (Set.Icc 0 1)) = c := by
  simp

/-
### Beispiel 2: Integral von x^2 auf [0,1]

Dieses Beispiel entspricht inhaltlich der Folie
  E[X^2] = ∫_0^1 x^2 dx = 1/3
für X ~ U([0,1]).

Die exakte Formalisierung des Intervallintegrals läuft in Lean meist über
`intervalIntegral` statt direkt über ein Wahrscheinlichkeitsmaß.
-/
example : ∫ x in (0 : ℝ)..1, x^2 = (1 : ℝ) / 3 := by
  rw [integral_pow]
  norm_num

/-
### Beispiel 3: Substitutionsidee in 1D

Das klassische Beispiel
  ∫_0^1 2x cos(x^2) dx = sin(1)
lässt sich in Lean sehr bequem mit dem Hauptsatz und der Kettenregel über
`intervalIntegral` zeigen.
-/
example : ∫ x in (0 : ℝ)..1, (2 * x) * Real.cos (x^2) = Real.sin 1 := by
  have hsub :
      ∫ x in (0 : ℝ)..1, (Real.cos ∘ fun x : ℝ => x^2) x * (2 * x)
        = ∫ u in ((0 : ℝ)^2)..((1 : ℝ)^2), Real.cos u := by
    exact intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ => x^2) (f' := fun x : ℝ => 2 * x) (g := Real.cos)
      (fun x _ => by
        simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using hasDerivAt_pow 2 x)
      ((continuous_const.mul continuous_id).continuousOn)
      Real.continuous_cos
  have hsub' :
      ∫ x in (0 : ℝ)..1, (2 * x) * Real.cos (x^2)
        = ∫ u in ((0 : ℝ)^2)..((1 : ℝ)^2), Real.cos u := by
    convert hsub using 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x hx
    simp [Function.comp, mul_assoc, mul_comm]
  calc
    ∫ x in (0 : ℝ)..1, (2 * x) * Real.cos (x^2)
        = ∫ u in ((0 : ℝ)^2)..((1 : ℝ)^2), Real.cos u := hsub'
    _ = Real.sin 1 := by
      rw [integral_cos]
      norm_num [Real.sin_zero]

/-
### Beispiel 4: Transformationssatz in Lean-Notation
-/
example (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(Measure.map (fun x : ℝ => x^2) volume)
      = ∫⁻ x, f (x^2) ∂volume := by
  simpa using lintegral_map hf (show Measurable fun x : ℝ => x^2 by fun_prop)

/-
### Beispiel 5: Borel-Messbarkeit einer stetigen Funktion

Stetige Funktionen zwischen topologischen Räumen mit Borel-σ-Algebren sind messbar.
-/
example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f := by
  exact hf.measurable

/-
### Beispiel 6: Einfache Anwendung des Erzeugersatzes

Eine Funktion nach `ℝ` ist messbar, wenn alle Urbilder der Mengen `Iic a`
messbar sind.
-/
example {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ)
    (hX : ∀ a : ℝ, MeasurableSet (X ⁻¹' Set.Iic a)) :
    Measurable X := by
  exact measurable_of_Iic hX

/-
### Beispiel 7: Monotone Approximation berechnet das Integral

Wenn `φ n` punktweise monoton gegen `f` wächst, dann ist das Integral von `f`
das Supremum der Integrale der `φ n`.
-/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (φ : ℕ → Ω → ℝ≥0∞)
    (hφm : ∀ n, Measurable (φ n))
    (hφmono : Monotone φ)
    (hφsup : ∀ x, (⨆ n, φ n x) = f x) :
    ∫⁻ x, f x ∂μ = ⨆ n, ∫⁻ x, φ n x ∂μ := by
  exact lintegral_eq_iSup_of_monotone μ f φ hφm hφmono hφsup

/-
### Beispiel 8: Zwei monotone Approximationen liefern denselben Wert
-/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞)
    (φ ψ : ℕ → Ω → ℝ≥0∞)
    (hφm : ∀ n, Measurable (φ n))
    (hφmono : Monotone φ)
    (hψm : ∀ n, Measurable (ψ n))
    (hψmono : Monotone ψ)
    (hφsup : ∀ x, (⨆ n, φ n x) = f x)
    (hψsup : ∀ x, (⨆ n, ψ n x) = f x) :
    (⨆ n, ∫⁻ x, φ n x ∂μ) = ⨆ n, ∫⁻ x, ψ n x ∂μ := by
  exact monotone_approximation_unique μ f φ ψ hφm hφmono hψm hψmono hφsup hψsup

/-! ## 15. Hinweise für die Vorlesung / zum Weiterlesen

1. **σ-Algebra** in Lean heißt `MeasurableSpace`.
2. **erzeugte σ-Algebra** heißt `MeasurableSpace.generateFrom`.
3. **Topologie** heißt `TopologicalSpace`.
4. **borelsche σ-Algebra** heißt `borel X`.
5. **Zufallsvariable** = messbare Funktion.
6. **Verteilung** = `Measure.map`.
7. **nichtnegatives Integral** = `lintegral` / `∫⁻`.
8. **gewöhnliches Integral** = `integral` / `∫`.
9. **Produktmaß** heißt `μ.prod ν`.
10. **Lebesgue-Maß auf ℝ** ist in Lean `volume`.
11. **Dichte** wird abstrakt über `withDensity` oder `rnDeriv` behandelt.
12. **monotone Approximationen** berechnet man in Lean über `lintegral_iSup`.
13. **Eindeutigkeit des Integralwerts** folgt daraus, dass jede solche Approximation
    denselben Wert `∫⁻ f dμ` liefert.
14. **Transformationssatz** ist in mathlib bereits als Standardresultat vorhanden.
15. **Substitutionssätze** in konkreten 1D-Beispielen zeigt man häufig über `intervalIntegral`.

Für eine vertiefte Formalisierung der mehrdimensionalen Transformationsformel müsste man noch
stärker mit Analysis-Resultaten über Diffeomorphismen, Jacobian und `MeasurePreserving`-artigen
Strukturen arbeiten.
-/

end StochastikMathlib
