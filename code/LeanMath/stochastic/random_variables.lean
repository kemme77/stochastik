/-
  Stochastik und Integration in Lean / Mathlib

  Diese Datei ist ein kommentiertes Lean-Skript, das die Vorlesungsfolien
  zur Wahrscheinlichkeitstheorie und Maßtheorie in Lean 4 / Mathlib widerspiegelt.

  Gliederung (passend zu den Folien):
   1. σ-Algebra und MeasurableSpace
   2. Erzeugte σ-Algebra
   3. Topologische Räume
   4. Borelsche σ-Algebra
   5. Messbarkeit (allgemein und über Erzeuger)
   6. Maß
   7. Restringiertes Maß
   8. Wahrscheinlichkeitsmaß
   9. Zufallsvariable, Verteilung, Bildmaß
  10. Einfache Funktionen und Integraldefinition
  11. Nichtnegatives Lebesgue-Integral (lintegral)
  12. Integration über Mengen
  13. Monotonie des Integrals
  14. Satz von der monotonen Konvergenz
  15. Reellwertige Funktionen und Bochner-Integral
  16. Integrierbarkeit
  17. Produktmaß und Fubini
  18. Lebesgue-Maß
  19. Dichten
  20. Transformationssatz und Substitution
  21. Stochastische Unabhängigkeit
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

namespace StochastikVorlesung

/-! ================================================================
## 1. σ-Algebra und MeasurableSpace
================================================================

Folie: Eine σ-Algebra 𝒜 ⊆ 𝒫(Ω) erfüllt:
  1. Ω ∈ 𝒜
  2. A ∈ 𝒜 ⟹ Aᶜ ∈ 𝒜
  3. A₁, A₂, … ∈ 𝒜 ⟹ ⋃ₙ Aₙ ∈ 𝒜

In Lean / Mathlib: `MeasurableSpace α`
-/

section SigmaAlgebra

example (Ω : Type*) [m : MeasurableSpace Ω] : MeasurableSpace Ω := m

-- Eine Menge ist messbar, wenn sie in der σ-Algebra liegt.
example {Ω : Type*} [MeasurableSpace Ω] (A : Set Ω) : Prop := MeasurableSet A

/-!
### Beispiel: Die Potenzmenge als σ-Algebra

Die Potenzmenge 𝒫(Ω) ist die größte σ-Algebra.
Wir implementieren das direkt als `MeasurableSpace`-Instanz.
-/

/-- Die Potenzmenge-σ-Algebra: jede Teilmenge ist messbar. -/
def potenzmengenSigmaAlgebra (Ω : Type*) : MeasurableSpace Ω where
  MeasurableSet' := fun _ => True
  measurableSet_empty := True.intro
  measurableSet_compl := fun _s _hs => True.intro
  measurableSet_iUnion := fun _f _hf => True.intro

-- In dieser σ-Algebra ist jede Menge messbar:
example (Ω : Type*) (A : Set Ω) :
    @MeasurableSet Ω (potenzmengenSigmaAlgebra Ω) A := True.intro

-- Äquivalenz zur maximalen σ-Algebra `⊤` aus Mathlib:
example (Ω : Type*) : potenzmengenSigmaAlgebra Ω = ⊤ := by
  ext A
  simp [potenzmengenSigmaAlgebra, MeasurableSpace.measurableSet_top]

-- Jede andere σ-Algebra ist ≤ der Potenzmenge:
example (Ω : Type*) (m : MeasurableSpace Ω) : m ≤ ⊤ := le_top

end SigmaAlgebra


/-! ================================================================
## 2. Erzeugte σ-Algebra
================================================================

Folie: Für ein Mengensystem 𝒢 ⊆ 𝒫(Ω) bezeichnet σ(𝒢) die kleinste
σ-Algebra auf Ω, die 𝒢 enthält.

In Lean: `MeasurableSpace.generateFrom G`
-/

section ErzeugteSigmaAlgebra

-- Die erzeugte σ-Algebra eines Mengensystems:
example (Ω : Type*) (G : Set (Set Ω)) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom G

-- Erzeugersystem liegt in der erzeugten σ-Algebra:
example {Ω : Type*} (G : Set (Set Ω)) {A : Set Ω} (hA : A ∈ G) :
    @MeasurableSet Ω (MeasurableSpace.generateFrom G) A := by
  exact MeasurableSpace.measurableSet_generateFrom hA

-- Minimalität: Enthält eine σ-Algebra m alle Erzeuger, dann ist generateFrom G ≤ m.
example {Ω : Type*} (G : Set (Set Ω)) (m : MeasurableSpace Ω)
    (hG : ∀ A ∈ G, @MeasurableSet Ω m A) :
    MeasurableSpace.generateFrom G ≤ m := by
  exact MeasurableSpace.generateFrom_le hG

end ErzeugteSigmaAlgebra


/-! ================================================================
## 3. Topologische Räume
================================================================

Folie: Ein topologischer Raum (X, τ) hat:
  1. ∅ ∈ τ und X ∈ τ
  2. beliebige Vereinigungen offener Mengen sind offen
  3. endliche Durchschnitte offener Mengen sind offen

In Lean: `TopologicalSpace X`
-/

section TopologischerRaum

example (X : Type*) [TopologicalSpace X] : TopologicalSpace X := inferInstance

-- Offene Mengen:
example {X : Type*} [TopologicalSpace X] (U : Set X) : Prop := IsOpen U

/-!
### Beispiel: Die diskrete Topologie (Potenzmenge)
-/

/-- Die diskrete Topologie: jede Teilmenge ist offen. -/
def potenzmengenTopologie (X : Type*) : TopologicalSpace X where
  -- Jede Menge wird per Definition als offen erklärt.
  IsOpen := fun _ => True
  -- Insbesondere ist der ganze Raum offen.
  isOpen_univ := True.intro
  -- Der Schnitt zweier offener Mengen ist wieder offen, hier trivial,
  -- weil ohnehin jede Menge offen ist.
  isOpen_inter := fun _s _t _hs _ht => True.intro
  -- Ebenso ist jede beliebige Vereinigung offen.
  isOpen_sUnion := fun _S _hS => True.intro

example (X : Type*) (U : Set X) :
    @IsOpen X (potenzmengenTopologie X) U := True.intro

-- Äquivalenz zur diskreten Topologie `⊥` in Mathlib:
example (X : Type*) : potenzmengenTopologie X = ⊥ := by
  ext U
  simp [potenzmengenTopologie]

/-!
### Beispiel: Die Klumpentopologie

Die Klumpentopologie ist die grobste Topologie: Offen sind nur `∅` und `univ`.
-/

/-- Die Klumpentopologie: nur `∅` und `univ` sind offen. -/
def klumpenTopologie (X : Type*) : TopologicalSpace X where
  -- Eine Menge `U` heißt genau dann offen, wenn sie entweder leer ist
  -- oder der ganze Raum `univ`; mehr offene Mengen gibt es hier nicht.
  IsOpen := fun U => U = ∅ ∨ U = univ
  isOpen_univ := Or.inr rfl
  isOpen_inter := by
    -- Beim Schnitt der einzigen offenen Mengen bleiben wieder nur `∅` oder `univ` übrig.
    intro s t hs ht
    -- `hs` und `ht` liefern jeweils die zwei Fälle `= ∅` oder `= univ`;
    -- nach dieser Vier-Fälle-Unterscheidung löst `simp` alle Schnitte sofort auf.
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp
  isOpen_sUnion := by
    -- Für eine beliebige Vereinigung gibt es genau zwei Fälle:
    -- Entweder `univ` ist schon dabei, dann ist die Vereinigung `univ`,
    -- oder alle Mengen aus der Familie sind leer, dann ist die Vereinigung `∅`.
    intro S hS
    by_cases h_univ : univ ∈ S
    · right
      ext x
      constructor
      -- Jede Vereinigung liegt als Menge ohnehin in `univ`.
      · intro _hx
        simp
      -- Weil `univ ∈ S`, liegt jedes `x` auch in der Vereinigungsmenge.
      · intro _hx
        exact ⟨univ, h_univ, by simp⟩
    · left
      ext x
      constructor
      · intro hx
        rcases hx with ⟨U, hU, hxU⟩
        rcases hS U hU with hUempty | hUuniv
        -- Ist `U = ∅`, dann kann `x ∈ U` nicht passieren.
        · simp [hUempty] at hxU
        -- Ist `U = univ`, widerspricht das der Annahme `h_univ`.
        · exact (h_univ (hUuniv ▸ hU)).elim
      -- Aus `x ∈ ∅` folgt sofort alles.
      · intro hx
        simp at hx

example (X : Type*) : @IsOpen X (klumpenTopologie X) (∅ : Set X) := Or.inl rfl

example (X : Type*) : @IsOpen X (klumpenTopologie X) (univ : Set X) := Or.inr rfl

example (X : Type*) (U : Set X) (hU : @IsOpen X (klumpenTopologie X) U) :
    U = ∅ ∨ U = univ := hU

end TopologischerRaum


/-! ================================================================
## 4. Borelsche σ-Algebra
================================================================

Folie: ℬ(X) := σ(τ) – die von den offenen Mengen erzeugte σ-Algebra.

In Lean: `borel X`
-/

section BorelSigmaAlgebra

-- Die borelsche σ-Algebra auf einem topologischen Raum:
example (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X

-- Definitionell ist sie die von offenen Mengen erzeugte σ-Algebra:
example (X : Type*) [TopologicalSpace X] :
    borel X = MeasurableSpace.generateFrom {U : Set X | IsOpen U} := rfl

/-!
### Detaillierte Erklärung: `borel X`

**Schritt 1: Was ist `generateFrom`?**
`MeasurableSpace.generateFrom G` erzeugt die kleinste σ-Algebra, die alle Mengen
in `G` enthält. Induktiv enthält sie:
- jede Menge aus `G` (Erzeuger)
- das Komplement jeder enthaltenen Menge
- abzählbare Vereinigungen enthaltener Mengen
- die leere Menge

**Schritt 2: Was ist `borel X`?**
`borel X` ist definiert als `generateFrom {U : Set X | IsOpen U}`.
Das heißt: Nimm alle offenen Mengen der Topologie als Erzeuger,
und bilde daraus die kleinste σ-Algebra.

**Schritt 3: Warum ist das nützlich?**
Die Borel-σ-Algebra enthält alle „geometrisch natürlichen" Mengen:
- offene Mengen (direkt als Erzeuger)
- abgeschlossene Mengen (als Komplemente offener Mengen)
- Intervalle wie (a,b), [a,b], (a,b], (-∞, a] auf ℝ
- abzählbare Durchschnitte/Vereinigungen davon (Gδ, Fσ, ...)
-/

-- ══════════════════════════════════════════════════════════════════
-- Schritt-für-Schritt: Die Bausteine von `borel X`
-- ══════════════════════════════════════════════════════════════════

-- (a) Das Erzeugersystem: die Menge aller offenen Mengen
example (X : Type*) [TopologicalSpace X] :
    {U : Set X | IsOpen U} = {U | IsOpen U} := rfl

-- (b) `generateFrom` angewendet auf dieses Erzeugersystem liefert eine σ-Algebra:
example (X : Type*) [TopologicalSpace X] :
    MeasurableSpace X :=
  MeasurableSpace.generateFrom {U : Set X | IsOpen U}

-- (c) Jede offene Menge ist in der erzeugten σ-Algebra messbar:
example (X : Type*) [TopologicalSpace X] (U : Set X) (hU : IsOpen U) :
    @MeasurableSet X (borel X) U := by
  -- U ist ein Erzeuger, also direkt messbar:
  exact MeasurableSpace.measurableSet_generateFrom hU

-- (d) Jede abgeschlossene Menge ist borel-messbar (als Komplement einer offenen):
example (X : Type*) [TopologicalSpace X] (F : Set X) (hF : IsClosed F) :
    @MeasurableSet X (borel X) F := by
  -- F ist abgeschlossen ⟺ Fᶜ ist offen ⟹ Fᶜ ist messbar ⟹ F ist messbar
  have hFc : @MeasurableSet X (borel X) Fᶜ :=
    MeasurableSpace.measurableSet_generateFrom hF.isOpen_compl
  rwa [MeasurableSet.compl_iff] at hFc

-- (e) Abzählbare Vereinigungen messbarer Mengen sind messbar:
example (X : Type*) [TopologicalSpace X] (A : ℕ → Set X)
    (hA : ∀ n, @MeasurableSet X (borel X) (A n)) :
    @MeasurableSet X (borel X) (⋃ n, A n) := by
  exact MeasurableSet.iUnion hA

-- (f) Abzählbare Durchschnitte messbarer Mengen sind messbar:
example (X : Type*) [TopologicalSpace X] (A : ℕ → Set X)
    (hA : ∀ n, @MeasurableSet X (borel X) (A n)) :
    @MeasurableSet X (borel X) (⋂ n, A n) := by
  exact MeasurableSet.iInter hA

-- ══════════════════════════════════════════════════════════════════
-- Konkrete Beispiele auf ℝ
-- ══════════════════════════════════════════════════════════════════

-- Offenes Intervall (a,b) ist offen, also borel-messbar:
example (a b : ℝ) : @MeasurableSet ℝ (borel ℝ) (Ioo a b) := by
  exact MeasurableSpace.measurableSet_generateFrom (mem_setOf.mpr isOpen_Ioo)

-- Offener Halbraum (a, +∞) ist offen, also borel-messbar:
example (a : ℝ) : @MeasurableSet ℝ (borel ℝ) (Ioi a) := by
  exact MeasurableSpace.measurableSet_generateFrom (mem_setOf.mpr isOpen_Ioi)

-- Abgeschlossenes Intervall [a,b] ist abgeschlossen, also borel-messbar:
example (a b : ℝ) : @MeasurableSet ℝ (borel ℝ) (Icc a b) :=
  IsClosed.measurableSet isClosed_Icc

-- Einzelpunkt {x} ist abgeschlossen, also borel-messbar:
example (x : ℝ) : @MeasurableSet ℝ (borel ℝ) {x} :=
  IsClosed.measurableSet isClosed_singleton

-- Halboffenes Intervall (a,b] = (a,b) ∪ {b}, Vereinigung messbarer Mengen:
example (a b : ℝ) : @MeasurableSet ℝ (borel ℝ) (Ioc a b) :=
  measurableSet_Ioc

-- ══════════════════════════════════════════════════════════════════
-- Minimalität: `borel X` ist die KLEINSTE σ-Algebra über den offenen Mengen
-- ══════════════════════════════════════════════════════════════════

-- Wenn eine σ-Algebra m jede offene Menge enthält, dann ist borel X ≤ m:
example (X : Type*) [TopologicalSpace X] (m : MeasurableSpace X)
    (hm : ∀ U : Set X, IsOpen U → @MeasurableSet X m U) :
    borel X ≤ m := by
  exact MeasurableSpace.generateFrom_le hm

-- Spezialfall ℝ:
example : MeasurableSpace ℝ := borel ℝ

-- Spezialfall ℝⁿ = Fin n → ℝ:
example (n : ℕ) : MeasurableSpace (Fin n → ℝ) := borel (Fin n → ℝ)

-- Offene Intervalle sind borel-messbar:
example (a b : ℝ) : @MeasurableSet ℝ (borel ℝ) (Ioo a b) := by
  exact IsOpen.measurableSet isOpen_Ioo

-- Halbstrahlen (-∞, a] sind borel-messbar:
example (a : ℝ) : @MeasurableSet ℝ (borel ℝ) (Iic a) := by
  exact measurableSet_Iic

end BorelSigmaAlgebra


/-! ================================================================
## 5. Messbarkeit
================================================================

Folie: Eine Abbildung X : Ω → E heißt messbar, wenn
  X⁻¹(B) ∈ 𝒜 für alle B ∈ ℰ.

In Lean: `Measurable X`
-/

section Messbarkeit

-- Messbarkeit einer Funktion:
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (X : Ω → E) : Prop :=
  Measurable X

/-!
### Messbarkeit über Erzeuger prüfen

Folie: Ist ℰ = σ(𝒢), dann ist X genau dann messbar, wenn
  X⁻¹(G) ∈ 𝒜 für alle G ∈ 𝒢.
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

theorem measurable_iff_generateFrom
    {Ω E : Type*} [MeasurableSpace Ω]
    {G : Set (Set E)} {X : Ω → E} :
    @Measurable Ω E _ (MeasurableSpace.generateFrom G) X
      ↔ ∀ A ∈ G, MeasurableSet (X ⁻¹' A) := by
  constructor
  · intro hX A hA
    exact (MeasurableSpace.measurableSet_generateFrom hA).preimage hX
  · intro hG
    exact measurable_of_generateFrom hG

/-!
### Praktisches Kriterium für ℝ

Folie: X : Ω → ℝ ist messbar ⟺ {ω : X(ω) ≤ a} ∈ 𝒜 für alle a ∈ ℝ.
-/

example {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} :
    Measurable X ↔ ∀ a : ℝ, MeasurableSet (X ⁻¹' Iic a) := by
  constructor
  · intro hX a
    exact measurableSet_Iic.preimage hX
  · intro hX
    refine measurable_of_Iic ?_
    intro a
    exact hX a

-- Stetige Funktionen sind messbar (Borel-Messbarkeit):
example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f := hf.measurable

end Messbarkeit


/-! ================================================================
## 6. Maß
================================================================

Folie: Ein Maß μ : 𝒜 → [0, ∞] mit:
  1. μ(A) ≥ 0 für alle A ∈ 𝒜
  2. μ(∅) = 0
  3. σ-Additivität für paarweise disjunkte Mengen

In Lean: `Measure α`
-/

section Mass

variable {α : Type*} [MeasurableSpace α]

#check MeasurableSpace α
#check Measure α

variable (μ : Measure α)

-- Das Maß des gesamten Raums:
#check μ univ

-- Leere Menge hat Maß 0:
example : μ ∅ = 0 := measure_empty

end Mass


/-! ================================================================
## 7. Restringiertes Maß
================================================================

Folie: Das auf s restringierte Maß μ|_s ist definiert durch
  μ|_s(A) := μ(A ∩ s).

In Lean: `μ.restrict s`
Kernlemma: `Measure.restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t ∩ s)`
-/

section RestringiertesMass

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable (s t : Set α)

-- Definition: Das Maß eingeschränkt auf `s`.
#check μ.restrict s
#check @Measure.restrict α _ μ s

-- Kernlemma: Auswertung des restringierten Maßes.
#check Measure.restrict_apply
#check Measure.restrict_apply'

-- Wenn `t` messbar ist:
example (ht : MeasurableSet t) :
    μ.restrict s t = μ (t ∩ s) := by
  exact Measure.restrict_apply ht

-- Wenn `s` messbar ist:
example (hs : MeasurableSet s) :
    μ.restrict s t = μ (t ∩ s) := by
  exact Measure.restrict_apply' hs

-- μ|_∅ = 0:
example : (μ.restrict s) ∅ = 0 := measure_empty

-- Einschränkung auf den ganzen Raum ändert nichts:
example : μ.restrict univ = μ := Measure.restrict_univ

-- Das restringierte Maß ist ≤ dem Originalmaß:
example : μ.restrict s ≤ μ := Measure.restrict_le_self

-- Monotonie: s ⊆ t ⟹ μ|_s ≤ μ|_t
example (h : s ⊆ t) : μ.restrict s ≤ μ.restrict t :=
  Measure.restrict_mono_set μ h

end RestringiertesMass


/-! ================================================================
## 8. Wahrscheinlichkeitsmaß
================================================================

Folie: Ein Wahrscheinlichkeitsmaß ℙ hat ℙ(Ω) = 1.

In Lean: `IsProbabilityMeasure μ` oder `ProbabilityMeasure Ω`.
-/

section Wahrscheinlichkeitsmass

variable {Ω : Type*} [MeasurableSpace Ω]

-- Typ:
example : Type _ := ProbabilityMeasure Ω

-- Auffassen als gewöhnliches Maß:
example (P : ProbabilityMeasure Ω) : Measure Ω := P.toMeasure

-- Gesamtmasse = 1:
example (P : ProbabilityMeasure Ω) :
    P.toMeasure univ = 1 := by
  simp

-- Alternativ über Typeclass:
#check @IsProbabilityMeasure.measure_univ

end Wahrscheinlichkeitsmass


/-! ================================================================
## 9. Zufallsvariable, Verteilung und Bildmaß
================================================================

Folie: Eine Zufallsvariable X : Ω → E ist eine messbare Abbildung.
Die induzierte Verteilung ist ℙ_X(B) = ℙ(X⁻¹(B)).
Das Bildmaß T#μ(B) := μ(T⁻¹(B)).

In Lean:
- Zufallsvariable = `Measurable X`
- Verteilung / Bildmaß = `Measure.map X μ`
-/

section Zufallsvariable

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

-- Eine Zufallsvariable ist eine messbare Funktion:
example (X : Ω → E) : Prop := Measurable X

-- Die induzierte Verteilung / das Bildmaß:
example (μ : Measure Ω) (X : Ω → E) : Measure E := Measure.map X μ

-- Definition: map_apply gibt ℙ_X(B) = ℙ(X⁻¹(B))
example (μ : Measure Ω) {X : Ω → E} (hX : Measurable X)
    (B : Set E) (hB : MeasurableSet B) :
    Measure.map X μ B = μ (X ⁻¹' B) := by
  simpa using Measure.map_apply hX hB

end Zufallsvariable


/-! ================================================================
## 10. Einfache Funktionen und Integraldefinition
================================================================

Folie: Eine einfache Funktion φ = Σᵢ aᵢ · 1_{Aᵢ} hat das Integral
  ∫ φ dμ = Σᵢ aᵢ · μ(Aᵢ).

Das nichtnegative Lebesgue-Integral ist definiert als
  ∫ f dμ := sup { ∫ φ dμ : 0 ≤ φ ≤ f, φ einfach }.

In Lean:
- `SimpleFunc α ℝ≥0∞` für einfache Funktionen
- `lintegral_def` für die Supremumsdefinition
-/

section EinfacheFunktionen

variable {α : Type*} [MeasurableSpace α]

-- Typ der einfachen Funktionen:
example : Type _ := SimpleFunc α ℝ≥0∞

-- Integral einer einfachen Funktion:
#check SimpleFunc.lintegral

-- Die Supremumsdefinition des lintegral:
#check MeasureTheory.lintegral_def

end EinfacheFunktionen


/-! ================================================================
## 11. Nichtnegatives Lebesgue-Integral (lintegral)
================================================================

Folie: Für f : Ω → [0, ∞] messbar:
  ∫⁻ x, f x ∂μ : ℝ≥0∞

Notation: `∫⁻ x, f x ∂μ`
Typ: `f : α → ℝ≥0∞`, Ergebnis: `ℝ≥0∞`
-/

section LIntegral

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable (f : α → ℝ≥0∞)

#check MeasureTheory.lintegral
#check ∫⁻ x, f x ∂μ

-- Die Integralnotation ist nur Notation für `MeasureTheory.lintegral`:
example : (∫⁻ x, f x ∂μ) = MeasureTheory.lintegral μ f := rfl

-- Integral der Nullfunktion:
example : (∫⁻ _ : α, (0 : ℝ≥0∞) ∂μ) = 0 := by simp

-- Konstante Funktionen: ∫ c dμ = c · μ(Ω)
#check MeasureTheory.lintegral_const

example (c : ℝ≥0∞) :
    (∫⁻ _ : α, c ∂μ) = c * μ univ := by
  simp [MeasureTheory.lintegral_const]

end LIntegral


/-! ================================================================
## 12. Integration über Mengen
================================================================

Folie: ∫_A f dμ := ∫ f · 1_A dμ

In Lean wird das über das restringierte Maß realisiert:
  ∫⁻ x in s, f x ∂μ  =  ∫⁻ x, f x ∂(μ.restrict s)
-/

section IntegrationMenge

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) (s : Set α) (f : α → ℝ≥0∞)

example : (∫⁻ x in s, f x ∂μ) = ∫⁻ x, f x ∂(μ.restrict s) := rfl

end IntegrationMenge


/-! ================================================================
## 13. Monotonie des Integrals
================================================================

Folie: Sind f, g : Ω → [0, ∞] messbar mit f ≤ g, dann gilt
  ∫ f dμ ≤ ∫ g dμ.

In Lean: `lintegral_mono`
-/

section Monotonie

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable (f g : α → ℝ≥0∞)

#check lintegral_mono

example (hfg : f ≤ g) :
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := by
  exact lintegral_mono hfg

-- Punktweise:
example (hfg : ∀ x, f x ≤ g x) :
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := by
  exact lintegral_mono hfg

end Monotonie


/-! ================================================================
## 14. Satz von der monotonen Konvergenz
================================================================

Folie: Seien fₙ : Ω → [0, ∞] messbar mit fₙ ↑ f. Dann gilt
  ∫ f dμ = lim_{n→∞} ∫ fₙ dμ.

Mathlib formuliert das über das punktweise Supremum:
  ∫⁻ x, (⨆ n, f n x) ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ

unter: ∀ n, Measurable (f n) und Monotone f.

### Die leichte Ungleichung (≤)
  ⨆ n, ∫ fₙ dμ ≤ ∫ (⨆ n, fₙ) dμ

### Die schwierige Ungleichung (≥)
  Folien-Beweis: Levelmengen, Stetigkeit des Maßes, c ↑ 1.
-/

section MonotoneKonvergenz

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable (f : ℕ → α → ℝ≥0∞)

#check MeasureTheory.lintegral_iSup

-- Hauptsatz:
example (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    (∫⁻ x, (⨆ n, f n x) ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ := by
  exact MeasureTheory.lintegral_iSup hf hmono

-- Leichte Ungleichung:
#check iSup_lintegral_le

example : (⨆ n, ∫⁻ x, f n x ∂μ) ≤ ∫⁻ x, (⨆ n, f n x) ∂μ := by
  exact iSup_lintegral_le _

/-!
### Monotone Approximation berechnet das Integral

Wächst φₙ punktweise monoton gegen f, dann ist ∫ f dμ = ⨆ n, ∫ φₙ dμ.
-/

theorem lintegral_eq_iSup_of_monotone
    (g : α → ℝ≥0∞) (φ : ℕ → α → ℝ≥0∞)
    (hφm : ∀ n, Measurable (φ n))
    (hφmono : Monotone φ)
    (hφsup : ∀ x, (⨆ n, φ n x) = g x) :
    ∫⁻ x, g x ∂μ = ⨆ n, ∫⁻ x, φ n x ∂μ := by
  have hg : g = fun x => ⨆ n, φ n x := by
    funext x; exact (hφsup x).symm
  rw [hg]
  simpa using lintegral_iSup hφm hφmono

/-!
### Eindeutigkeit: Zwei monotone Approximationen liefern denselben Wert
-/

theorem monotone_approximation_unique
    (g : α → ℝ≥0∞)
    (φ ψ : ℕ → α → ℝ≥0∞)
    (hφm : ∀ n, Measurable (φ n)) (hφmono : Monotone φ)
    (hψm : ∀ n, Measurable (ψ n)) (hψmono : Monotone ψ)
    (hφsup : ∀ x, (⨆ n, φ n x) = g x)
    (hψsup : ∀ x, (⨆ n, ψ n x) = g x) :
    (⨆ n, ∫⁻ x, φ n x ∂μ) = ⨆ n, ∫⁻ x, ψ n x ∂μ := by
  calc
    (⨆ n, ∫⁻ x, φ n x ∂μ) = ∫⁻ x, g x ∂μ := by
      symm; exact lintegral_eq_iSup_of_monotone μ g φ hφm hφmono hφsup
    _ = (⨆ n, ∫⁻ x, ψ n x ∂μ) := by
      exact lintegral_eq_iSup_of_monotone μ g ψ hψm hψmono hψsup

/-!
### Fast-überall-Version

In Anwendungen: nur AEMeasurable und fast-überall monoton.
-/

#check MeasureTheory.lintegral_iSup'

example (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n => f n x) :
    (∫⁻ x, (⨆ n, f n x) ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ := by
  exact MeasureTheory.lintegral_iSup' hf hmono

/-!
### Grenzwert-Version mit Tendsto
-/

#check MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone

/-!
### Mini-Beispiel: Konstante Folge
-/

private def constSeq (c : ℝ≥0∞) : ℕ → α → ℝ≥0∞ := fun _ _ => c

example (c : ℝ≥0∞) : Monotone (constSeq (α := α) c) := by
  intro n m _hnm x; rfl

example (c : ℝ≥0∞) : ∀ n, Measurable (constSeq (α := α) c n) := by
  intro _n; exact measurable_const

example (c : ℝ≥0∞) :
    (∫⁻ x, (⨆ n, constSeq (α := α) c n x) ∂μ) =
    ⨆ n, ∫⁻ x, constSeq (α := α) c n x ∂μ := by
  apply MeasureTheory.lintegral_iSup
  · intro _n; exact measurable_const
  · intro _n _m _hnm x; rfl

end MonotoneKonvergenz


/-! ================================================================
## 15. Reellwertige Funktionen und Bochner-Integral
================================================================

Folie: Für f : Ω → ℝ mit f = f⁺ - f⁻ setzt man
  ∫ f dμ := ∫ f⁺ dμ - ∫ f⁻ dμ.

In Lean: Das Bochner-Integral `∫ x, f x ∂μ`.
-/

section BochnerIntegral

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) (f : α → ℝ)

#check integral
#check ∫ x, f x ∂μ

example : (∫ x, f x ∂μ) = integral μ f := rfl

-- Integral der Null:
example : ∫ _ : α, (0 : ℝ) ∂μ = 0 := by simp

-- Integral einer Konstanten (für endliche Maße):
example (c : ℝ) [IsFiniteMeasure μ] :
    ∫ _ : α, c ∂μ = μ.real univ * c := by
  simp [mul_comm]

end BochnerIntegral


/-! ================================================================
## 16. Integrierbarkeit
================================================================

Folie: f heißt integrierbar, wenn ∫ |f| dμ < ∞.

In Lean: `Integrable f μ`
-/

section Integrierbarkeit

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)

#check Integrable f μ

end Integrierbarkeit


/-! ================================================================
## 17. Produktmaß und Fubini
================================================================

Folie: Für Maßräume (E, ℰ, μ) und (F, ℱ, ν) ist das Produktmaß
μ ⊗ ν das Maß auf E × F mit (μ ⊗ ν)(A × B) = μ(A) · ν(B).

Fubini:
  ∫_{E×F} f d(μ ⊗ ν) = ∫_E (∫_F f(x,y) dν) dμ

In Lean: `μ.prod ν`
-/

section ProduktmassFubini

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

-- Produktmaß:
example (μ : Measure α) (ν : Measure β) : Measure (α × β) := μ.prod ν

-- Produktmaß auf Rechtecken: (μ × ν)(A ×ˢ B) = μ(A) · ν(B)
example (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {A : Set α} {B : Set β} :
    μ.prod ν (A ×ˢ B) = μ A * ν B := by
  exact Measure.prod_prod (μ := μ) (ν := ν) A B

-- Fubini (Bochner-Integral):
example (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  simpa using (MeasureTheory.integral_integral (f := fun x y => f (x, y)) hf).symm

end ProduktmassFubini


/-! ================================================================
## 18. Lebesgue-Maß
================================================================

Folie: Das Lebesgue-Maß λ auf ℝ mit λ((a,b]) = b - a.
Auf ℝⁿ: λⁿ = λ ⊗ ⋯ ⊗ λ.

In Lean: `volume` (das Standardmaß, auf ℝ das Lebesgue-Maß).
-/

section LebesgueMass

-- Das Lebesgue-Maß auf ℝ:
example : Measure ℝ := volume

-- Auf dem Produktraum ℝ × ℝ:
example : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume

-- Produktmessung auf Rechtecken:
example (A B : Set ℝ) [SFinite (volume : Measure ℝ)] :
    ((volume : Measure ℝ).prod volume) (A ×ˢ B) = volume A * volume B := by
  exact Measure.prod_prod (μ := (volume : Measure ℝ)) (ν := volume) A B

end LebesgueMass


/-! ================================================================
## 19. Dichten
================================================================

Folie: p heißt Dichte von μ bzgl. λⁿ, wenn μ(A) = ∫_A p dλⁿ.
Schreibweise: dμ(x) = p(x) dx.

In Lean: `Measure.withDensity volume p`
-/

section Dichten

-- Maß mit Dichte p:
example (p : ℝ → ℝ≥0∞) : Measure ℝ := Measure.withDensity volume p

-- Gleichverteilung auf [a,b]:
example (a b : ℝ) : Measure ℝ :=
  Measure.withDensity volume
    (fun x =>
      (ENNReal.ofReal (b - a))⁻¹ *
        indicator (Icc a b) (fun _ => (1 : ℝ≥0∞)) x)

-- Integration mit Dichte: ∫ f dμ_p = ∫ f · p dλ
example (p : ℝ → ℝ≥0∞) (f : ℝ → ℝ≥0∞)
    (hp : Measurable p) (hf : Measurable f) :
    ∫⁻ x, f x ∂(Measure.withDensity volume p) = ∫⁻ x, f x * p x ∂volume := by
  simpa [Pi.mul_apply, mul_comm] using
    (lintegral_withDensity_eq_lintegral_mul volume hp hf)

end Dichten


/-! ================================================================
## 20. Transformationssatz und Substitution
================================================================

Folie (allgemein): ∫_Y f d(T#μ) = ∫_X f∘T dμ.

In Lean: `lintegral_map` bzw. `integral_map`.
-/

section Transformationssatz

-- Nichtnegative Version:
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {T : X → Y} (hT : Measurable T) (f : Y → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(Measure.map T μ) = ∫⁻ x, f (T x) ∂μ := by
  simpa using lintegral_map hf hT

-- Reellwertige Version:
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {T : X → Y} (hT : Measurable T) (f : Y → ℝ)
    (hf : Integrable f (Measure.map T μ)) :
    ∫ y, f y ∂(Measure.map T μ) = ∫ x, f (T x) ∂μ := by
  simpa using integral_map hT.aemeasurable hf.aestronglyMeasurable

-- Spezialfall Zufallsvariable: ∫ g dℙ_X = ∫ g∘X dℙ
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) {X : Ω → E} (hX : Measurable X)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g x ∂(Measure.map X P) = ∫⁻ ω, g (X ω) ∂P := by
  simpa using lintegral_map hg hX

/-!
### Substitution in 1D

Folie: ∫_{T(a)}^{T(b)} f(y) dy = ∫_a^b f(T(x)) |T'(x)| dx.
-/

-- Beispiel: ∫₀¹ x² dx = 1/3
example : ∫ x in (0 : ℝ)..1, x ^ 2 = (1 : ℝ) / 3 := by
  rw [integral_pow]
  norm_num

-- Beispiel: ∫₀¹ 2x cos(x²) dx = sin(1)
example : ∫ x in (0 : ℝ)..1, (2 * x) * Real.cos (x ^ 2) = Real.sin 1 := by
  have hsub :
      ∫ x in (0 : ℝ)..1, (Real.cos ∘ fun x : ℝ => x ^ 2) x * (2 * x)
        = ∫ u in ((0 : ℝ) ^ 2)..((1 : ℝ) ^ 2), Real.cos u := by
    exact intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ => x ^ 2) (f' := fun x : ℝ => 2 * x) (g := Real.cos)
      (fun x _ => by
        simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using hasDerivAt_pow 2 x)
      ((continuous_const.mul continuous_id).continuousOn)
      Real.continuous_cos
  have hsub' :
      ∫ x in (0 : ℝ)..1, (2 * x) * Real.cos (x ^ 2)
        = ∫ u in ((0 : ℝ) ^ 2)..((1 : ℝ) ^ 2), Real.cos u := by
    convert hsub using 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x _hx
    simp [Function.comp, mul_assoc, mul_comm]
  calc
    ∫ x in (0 : ℝ)..1, (2 * x) * Real.cos (x ^ 2)
        = ∫ u in ((0 : ℝ) ^ 2)..((1 : ℝ) ^ 2), Real.cos u := hsub'
    _ = Real.sin 1 := by
      rw [integral_cos]
      norm_num [Real.sin_zero]

-- Transformationssatz in Lean-Notation:
example (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(Measure.map (fun x : ℝ => x ^ 2) volume)
      = ∫⁻ x, f (x ^ 2) ∂volume := by
  simpa using lintegral_map hf (show Measurable fun x : ℝ => x ^ 2 by fun_prop)

end Transformationssatz


/-! ================================================================
## 21. Stochastische Unabhängigkeit
================================================================

Folie: X, Y heißen unabhängig, wenn
  ℙ(X ∈ A, Y ∈ B) = ℙ(X ∈ A) · ℙ(Y ∈ B) für alle A, B.

Äquivalent: ℙ_{(X,Y)} = ℙ_X ⊗ ℙ_Y.

In Lean: `ProbabilityTheory.IndepFun X Y μ`
-/

section Unabhaengigkeit

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

example (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  ProbabilityTheory.IndepFun X Y μ

end Unabhaengigkeit


/-! ================================================================
## Zusammenfassung: Lean ↔ Mathematik
================================================================

| Mathematik                  | Lean / Mathlib                          |
|-----------------------------|----------------------------------------|
| σ-Algebra                   | `MeasurableSpace`                       |
| erzeugte σ-Algebra σ(𝒢)    | `MeasurableSpace.generateFrom G`        |
| Topologie                   | `TopologicalSpace`                       |
| Borel-σ-Algebra ℬ(X)       | `borel X`                                |
| Messbarkeit                 | `Measurable f`                           |
| Maß                         | `Measure α`                              |
| Restringiertes Maß μ|_s    | `μ.restrict s`                           |
| Wahrscheinlichkeitsmaß      | `IsProbabilityMeasure` / `ProbabilityMeasure` |
| Zufallsvariable             | messbare Funktion                        |
| Verteilung / Bildmaß T#μ   | `Measure.map T μ`                        |
| Einfache Funktion           | `SimpleFunc α ℝ≥0∞`                     |
| Nichtneg. Integral ∫⁻ f dμ | `∫⁻ x, f x ∂μ`                          |
| Bochner-Integral ∫ f dμ    | `∫ x, f x ∂μ`                           |
| Integrierbarkeit            | `Integrable f μ`                         |
| Produktmaß μ ⊗ ν           | `μ.prod ν`                               |
| Lebesgue-Maß auf ℝ         | `volume`                                 |
| Dichte                      | `Measure.withDensity volume p`           |
| Monotone Konvergenz         | `lintegral_iSup`                         |
| Transformationssatz         | `lintegral_map` / `integral_map`         |
| Unabhängigkeit              | `IndepFun X Y μ`                         |
-/

end StochastikVorlesung
