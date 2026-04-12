import Mathlib

open MeasureTheory ProbabilityTheory BigOperators
open Filter
open scoped Topology BigOperators

noncomputable section

/-!
# Schwaches vs. starkes Gesetz der großen Zahlen

Dieses File soll nicht einen neuen tiefen Satz beweisen, sondern den Unterschied zwischen dem
schwachen und dem starken Gesetz der großen Zahlen klar herausarbeiten.

Die Grundfrage ist in beiden Fällen dieselbe:

Wenn `X 0, X 1, X 2, ...` Zufallsvariablen mit demselben Erwartungswert sind,
konvergieren dann ihre empirischen Mittelwerte

`(X 0 + ... + X (n-1)) / n`

gegen diesen Erwartungswert?

Der Unterschied liegt darin, **welche Art von Konvergenz** man fordert.
-/

section Comparison

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Das empirische Mittel der ersten `n` Zufallsvariablen. -/
def empiricalAvg (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.sum (Finset.range n) (fun i => X i ω)) / n

/-!
## 1. Schwaches Gesetz

Beim schwachen Gesetz betrachtet man für jedes feste `ε > 0` die Wahrscheinlichkeit,
dass das empirische Mittel mehr als `ε` vom Erwartungswert abweicht.

Man fordert also nicht punktweise Konvergenz für einzelne `ω`, sondern nur, dass diese
Abweichungswahrscheinlichkeiten gegen `0` gehen.
-/

/--
Informelle Lean-Definition des schwachen Gesetzes:
Die empirischen Mittel konvergieren in Wahrscheinlichkeit gegen `m`.
-/
def WeakLaw (X : ℕ → Ω → ℝ) (m : ℝ) : Prop :=
  ∀ ε > 0,
    Tendsto (fun n => μ {ω | ε ≤ |empiricalAvg X n ω - m|}) atTop (𝓝 0)

/-!
### Typische Beweisidee beim schwachen Gesetz

Für einen Chebyshev-Beweis geht man grob so vor:

1. Man zeigt, dass `E[empiricalAvg X n] = m`.
2. Man berechnet `Var(empiricalAvg X n)` und erhält typischerweise eine Schranke der Form
   `Var(empiricalAvg X n) = Var(X 0) / n`.
3. Mit Chebyshev folgt

   `P(|empiricalAvg X n - m| ≥ ε) ≤ Var(X 0) / (n * ε^2)`.

4. Die rechte Seite geht gegen `0`, also folgt Konvergenz in Wahrscheinlichkeit.

Das ist genau die Strategie im Chebyshev-Beweis des schwachen Gesetzes.
-/

/-!
## 2. Starkes Gesetz

Beim starken Gesetz ist die Aussage deutlich stärker. Man fordert, dass für fast jedes `ω`
die Zahlenfolge

`empiricalAvg X n ω`

tatsächlich gegen `m` konvergiert.

Das ist eine punktweise Aussage über fast alle Realisierungen, nicht nur über
Abweichungswahrscheinlichkeiten.
-/

/--
Informelle Lean-Definition des starken Gesetzes:
Die empirischen Mittel konvergieren fast sicher gegen `m`.
-/
def StrongLaw (X : ℕ → Ω → ℝ) (m : ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => empiricalAvg X n ω) atTop (𝓝 m)

/-!
## 3. Der eigentliche Unterschied

Die beiden Aussagen sehen ähnlich aus, aber sie liegen logisch auf verschiedenen Ebenen:

* Beim **schwachen Gesetz** steht das Maß `μ` außen:
  Für jedes `ε` betrachtet man eine Menge schlechter `ω` und verlangt, dass ihre
  Wahrscheinlichkeit klein wird.

* Beim **starken Gesetz** steht die punktweise Konvergenz innen:
  Für fast jedes einzelne `ω` muss die Zahlenfolge wirklich konvergieren.

Darum ist das starke Gesetz eine wesentlich stärkere Aussage.
-/

/-!
## 4. Weitere Konvergenzbegriffe

Im Umfeld des Gesetzes der großen Zahlen tauchen mehrere Konvergenzarten auf. Für eine Folge
`f n : Ω → ℝ` und einen Grenzwert `g : Ω → ℝ` sind besonders wichtig:

* **Fast sichere Konvergenz**:
  Für fast jedes `ω` konvergiert die Zahlenfolge `f n ω` gegen `g ω`.

* **Konvergenz in Wahrscheinlichkeit**:
  Für jedes `ε > 0` geht die Wahrscheinlichkeit der Menge
  `{ω | ε ≤ |f n ω - g ω|}` gegen `0`.

* **Konvergenz in `L^p`**:
  Der `L^p`-Abstand zwischen `f n` und `g` geht gegen `0`.

* **Konvergenz in Verteilung**:
  Die Verteilungen von `f n` nähern sich der Verteilung von `g` an.

Für das schwache Gesetz ist die natürliche Sprache die Konvergenz in Wahrscheinlichkeit.
Für das starke Gesetz ist die natürliche Sprache die fast sichere Konvergenz.
-/

/-- Allgemeine fast sichere Konvergenz einer Folge von Zufallsvariablen. -/
def ConvergesAlmostSurely (f : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))

/-- Allgemeine Konvergenz in Wahrscheinlichkeit. -/
def ConvergesInProbability (f : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  TendstoInMeasure μ f atTop g

/-!
Für das empirische Mittel ist also:

* `StrongLaw X m` eine spezielle Form von fast sicherer Konvergenz,
* `WeakLaw X m` die ausgeschriebene Form von Konvergenz in Wahrscheinlichkeit zum konstanten
  Grenzwert `m`.

In Mathlib ist die Konvergenz in Wahrscheinlichkeit durch `TendstoInMeasure` organisiert.
-/

lemma strongLaw_implies_weakLaw
    (X : ℕ → Ω → ℝ) (m : ℝ)
    (h : StrongLaw (μ := μ) X m)
    (hmeas : ∀ n, AEStronglyMeasurable (empiricalAvg X n) μ) :
    TendstoInMeasure μ (fun n => empiricalAvg X n) atTop (fun _ => m) := by
  exact tendstoInMeasure_of_tendsto_ae (μ := μ)
    (f := fun n => empiricalAvg X n) (g := fun _ => m) hmeas h

/-!
### Wichtige Implikationen

Zwischen diesen Konvergenzarten gelten typischerweise folgende Implikationen:

* fast sicher `⇒` in Wahrscheinlichkeit,
* `L^p`-Konvergenz (für `p > 0`) `⇒` in Wahrscheinlichkeit,
* in Wahrscheinlichkeit `⇒` in Verteilung.

Die Umkehrungen gelten im Allgemeinen **nicht**.

Besonders wichtig für das Gesetz der großen Zahlen ist:

* Das starke Gesetz liefert fast sichere Konvergenz.
* Daraus folgt automatisch das schwache Gesetz.

Genau diesen Schritt formalisiert das obige Lemma `strongLaw_implies_weakLaw`, das den allgemeinen
Mathlib-Satz `tendstoInMeasure_of_tendsto_ae` benutzt.

Ebenfalls wichtig ist, was **nicht** gilt:

* Konvergenz in Wahrscheinlichkeit ist im Allgemeinen zu schwach, um fast sichere Konvergenz zu
  folgern.
* Fast sichere Konvergenz allein liefert ohne zusätzliche Abschätzungen noch keine `L^1`- oder
  `L^2`-Konvergenz.

Deshalb sind schwaches und starkes Gesetz zwar verwandt, aber nicht nur zwei Formulierungen
derselben Aussage.
-/

/-!
## 5. Warum der Beweis des starken Gesetzes schwerer ist

Der Chebyshev-Beweis des schwachen Gesetzes reicht für fast sichere Konvergenz nicht aus.
Aus einer Schranke der Form

`P(|empiricalAvg X n - m| ≥ ε) ≤ C / n`

folgt im Allgemeinen noch keine fast sichere Konvergenz.

Für das starke Gesetz braucht man zusätzliche Ideen. In Mathlib wird für reellwertige
Zufallsvariablen die fast sichere Version über einen deutlich tieferen Beweis geführt.
Eine typische grobe Struktur ist:

1. Große Ausreißer werden zunächst durch **Trunkierung** abgeschnitten.
2. Für die abgeschnittenen Zufallsvariablen zeigt man ein starkes Gesetz.
3. Dann zeigt man, dass das Abschneiden asymptotisch nichts Wesentliches verändert.
4. Schließlich setzt man positive und negative Teile wieder zusammen.

Genau diese Trunkierungs-Idee taucht im Mathlib-File zum starken Gesetz auf.
-/

/-
Mathlib stellt das starke Gesetz direkt als fast sichere Konvergenz bereit.

Für reellwertige Zufallsvariablen lautet die Form grob:

* Integrabilität von `X 0`
* paarweise Unabhängigkeit
* identische Verteilung

impliziert fast sichere Konvergenz der empirischen Mittel gegen den Erwartungswert.
-/
#check ProbabilityTheory.strong_law_ae_real

/-!
## 6. Merksatz

* Das **schwache Gesetz** ist oft mit Varianzabschätzungen und Chebyshev zugänglich.
* Das **starke Gesetz** ist inhaltlich stärker und braucht typischerweise tiefere Argumente.
* Fast sichere Konvergenz impliziert Konvergenz in Wahrscheinlichkeit, aber nicht umgekehrt.

Für ein erstes Verständnis ist daher der Chebyshev-Beweis des schwachen Gesetzes ideal.
Für das starke Gesetz arbeitet man meist mit bereits etablierten tieferen Sätzen.
-/

end Comparison
