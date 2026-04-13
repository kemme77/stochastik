import LeanMath.stochastic.weak_law_chebyshev

open MeasureTheory ProbabilityTheory

section FiniteProbabilitySpace

local notation "Ω₂" => Fin 2

local instance : MeasurableSpace Ω₂ := ⊤

/-- Die beiden elementaren Ereignisse im endlichen Raum `Fin 2`. -/
def zeroEvent : Set Ω₂ := {0}

def oneEvent : Set Ω₂ := {1}

/-- Ein einfaches Wahrscheinlichkeitsmaß auf dem endlichen Raum `Fin 2` mit Potenzmenge als
messbarer Struktur. Beide Punkte erhalten Masse `1/2`. -/
noncomputable def fairBitMeasure : Measure Ω₂ :=
  ((1 : ENNReal) / 2) • Measure.dirac 0 + ((1 : ENNReal) / 2) • Measure.dirac 1

/-- Eine einfache Zufallsvariable auf dem endlichen Raum. -/
def bitValue : Ω₂ → ℝ := fun ω => if ω = 0 then 0 else 1

/-!
# Glossar zu `weak_law_chebyshev`

Dieses File sammelt die wichtigsten Begriffe und Taktiken, die im Beweis des schwachen Gesetzes
der großen Zahlen verwendet werden, aber nicht direkt dort definiert sind.

Die Datei ist bewusst als Lesebegleitung gedacht: Sie führt keine neue Theorie ein, sondern
erklärt die Mathlib-Bausteine und die Lean-Beweissprache, die im Hauptfile vorkommen.

## Zentrale mathematische Begriffe

### Wahrscheinlichkeitsmaß `μ : Measure Ω` mit `[IsProbabilityMeasure μ]`

Ein Wahrscheinlichkeitsmaß ordnet jedem Ereignis eine Wahrscheinlichkeit zu.

- Ein Ereignis ist eine messbare Menge `A : Set Ω`.
- `μ A` ist dann die Wahrscheinlichkeit von `A`.
- Die Zusatzannahme `[IsProbabilityMeasure μ]` sagt insbesondere, dass der gesamte Raum
  Wahrscheinlichkeit `1` hat.

Einfaches Beispiel:

- `Ω = {Kopf, Zahl}` bei einem fairen Münzwurf.
- Dann ist `μ {Kopf} = 1 / 2`, `μ {Zahl} = 1 / 2` und `μ Ω = 1`.

Endliches Beispiel mit Potenzmenge:

- Nimm `Ω = Fin 2 = {0, 1}`.
- Als σ-Algebra verwenden wir die Potenzmenge, in Lean also die diskrete messbare Struktur `⊤`.
- Dann sind wirklich alle Teilmengen messbar: `∅`, `{0}`, `{1}`, `{0,1}`.
- Ein faires Wahrscheinlichkeitsmaß erhält man, indem man jedem Punkt die Masse `1 / 2` gibt.
- Also gilt:
  `μ ∅ = 0`, `μ {0} = 1 / 2`, `μ {1} = 1 / 2`, `μ {0,1} = 1`.
-/

/-- Beim diskreten endlichen Raum sind alle Teilmengen messbar. -/
example (s : Set Ω₂) : MeasurableSet s := by
  change True
  trivial

/-- Die leere Menge hat Wahrscheinlichkeit `0`. -/
example : fairBitMeasure (∅ : Set Ω₂) = 0 := by
  simp [fairBitMeasure]

/-- Der gesamte Raum hat Wahrscheinlichkeit `1`. -/
example : fairBitMeasure Set.univ = 1 := by
  simp [fairBitMeasure]
  simpa using ENNReal.add_halves (1 : ENNReal)

/-- Jeder der beiden Punkte hat Wahrscheinlichkeit `1/2`. -/
example : fairBitMeasure zeroEvent = 1 / 2 := by
  simp [fairBitMeasure, zeroEvent]

/-- Auch der andere Punkt hat Wahrscheinlichkeit `1/2`. -/
example : fairBitMeasure oneEvent = 1 / 2 := by
  simp [fairBitMeasure, oneEvent]

/-!
### Zufallsvariable `X : Ω → ℝ`

Eine Zufallsvariable ist in Lean zunächst einfach eine Funktion vom Ergebnisraum `Ω` in die reellen
Zahlen.

Mathematisch kommt noch hinzu, dass sie messbar sein soll. Das stellt sicher, dass Aussagen wie
`{ω | X ω ≤ 3}` tatsächlich Ereignisse sind, denen man eine Wahrscheinlichkeit zuordnen kann.

Einfaches Beispiel:

- Bei einem Würfelwurf sei `Ω = {1, 2, 3, 4, 5, 6}`.
- Die Funktion `X ω := ω` ist die Augenzahl als Zufallsvariable.
- Die Funktion `Y ω := if ω = 6 then 1 else 0` ist die Indikator-Zufallsvariable für das Ereignis
  „Es fällt eine 6“.
-/

example : bitValue 0 = 0 := by
  simp [bitValue]

example : bitValue 1 = 1 := by
  simp [bitValue]

example : Measurable bitValue := by
  simpa using measurable_of_finite bitValue

/-- Eine konstante reellwertige Funktion ist ebenfalls messbar. -/
example : Measurable (fun _ : ℕ => (3 : ℝ)) := by
  exact measurable_const

/-!
### `Tendsto f atTop (𝓝 a)`

Das bedeutet: Die Folge oder Funktion `f` konvergiert gegen `a`.

- `atTop` steht bei Folgen `ℕ → ...` für den Grenzübergang `n → ∞`.
- `𝓝 a` ist die Umgebung von `a`, also der Ziel-Filter für Konvergenz gegen `a`.

Im File `weak_law_chebyshev.lean` bedeutet

`Tendsto (fun n => μ {ω | ε ≤ |avg X n.succ ω - m|}) atTop (𝓝 0)`

genau: Die Abweichungswahrscheinlichkeiten gehen gegen `0`.

Einfaches Beispiel:

- Die Folge `f n = 1 / (n + 1)` konvergiert gegen `0`.
- In Lean schreibt man das als `Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)`.

### Konvergenz in Wahrscheinlichkeit

Eine Folge von Zufallsvariablen `Y n` konvergiert in Wahrscheinlichkeit gegen `Y`, wenn für jedes
`ε > 0` die Wahrscheinlichkeiten

`μ {ω | ε ≤ |Y n ω - Y ω|}`

gegen `0` gehen.

Genau diese Formulierung erscheint im Schlusssatz des Files.

Einfaches Beispiel:

- Sei `Y n` das Mittel der ersten `n` Münzwürfe, wobei Kopf als `1` und Zahl als `0` kodiert wird.
- Dann sagt Konvergenz in Wahrscheinlichkeit gegen `1 / 2`: Für großes `n` ist es sehr
  unwahrscheinlich, dass dieses Mittel noch deutlich von `1 / 2` abweicht.

### `IdentDistrib (X n) (X 0) μ μ`

`IdentDistrib` heißt: zwei Zufallsvariablen sind identisch verteilt.

Das ist schwächer als punktweise Gleichheit. Es fordert nicht, dass

`X n ω = X 0 ω`

für jedes `ω` gilt, sondern nur, dass beide dieselbe Verteilung besitzen. Deshalb haben sie zum
Beispiel denselben Erwartungswert und dieselbe Varianz.

Einfaches Beispiel:

- `X 0` sei der erste faire Würfelwurf und `X 1` der zweite faire Würfelwurf.
- Dann sind `X 0` und `X 1` identisch verteilt, auch wenn sie im konkreten Versuch verschiedene
	Werte annehmen können.

### `Pairwise fun i j => IndepFun (X i) (X j) μ`

`Pairwise` bedeutet: die angegebene Eigenschaft gilt für alle verschiedenen Indizes `i ≠ j`.

`IndepFun (X i) (X j) μ` bedeutet: die Zufallsvariablen `X i` und `X j` sind unabhängig.

Zusammen heißt die Aussage also: Die Folge ist paarweise unabhängig.

Einfaches Beispiel:

- Bei wiederholten unabhängigen Münzwürfen sind der erste und der dritte Wurf unabhängig.
- Ebenso sind dann allgemeiner je zwei verschiedene Würfe unabhängig.

### `MeasureTheory.MemLp (X n) 2 μ`

`MemLp f p μ` bedeutet: `f` liegt im Raum `L^p(μ)`.

Für `p = 2` heißt das anschaulich: `f` hat ein endliches zweites Moment. Das ist genau die
natürliche Voraussetzung, damit Varianzformeln sauber funktionieren.

Einfaches Beispiel:

- Eine beschränkte Zufallsvariable wie ein Würfelwurf liegt sicher in `L²`, denn `X²` bleibt immer
	endlich.
- Dagegen können sehr schwere Verteilungen existieren, deren zweites Moment unendlich ist; diese
	würden nicht in `L²` liegen.

### `Integrable f μ`

`Integrable` bedeutet: `f` ist bezüglich `μ` integrierbar.

Für reellwertige Zufallsvariablen ist das die Voraussetzung dafür, dass der Erwartungswert

`∫ ω, f ω ∂μ`

wohldefiniert ist.

Einfaches Beispiel:

- Ein Würfelwurf ist integrierbar, weil nur die Werte `1` bis `6` auftreten.
- Sein Erwartungswert ist dann das bekannte Mittel `3.5`.

### `variance X μ`

Das ist die Varianz der Zufallsvariable `X` bezüglich des Maßes `μ`.

Inhaltlich misst die Varianz die mittlere quadratische Abweichung vom Erwartungswert. Im File wird
vor allem benutzt, dass

- die Varianz einer Summe unabhängiger Zufallsvariablen die Summe der Varianzen ist,
- sich bei Multiplikation mit einer Konstante die Varianz quadratisch skaliert.

Einfaches Beispiel:

- Eine konstante Zufallsvariable hat Varianz `0`, weil sie nie vom Mittelwert abweicht.
- Ein fairer Münzwurf mit Werten `0` und `1` hat positive Varianz, weil beide Werte tatsächlich
	auftreten.

### `μ {ω | ... }`

Das ist die Wahrscheinlichkeit des Ereignisses `{ω | ... }`.

Die Schreibweise `{ω | ... }` ist eine Mengenbeschreibung: alle `ω`, für die die Bedingung gilt.

Einfaches Beispiel:

- Bei einem Würfelwurf ist `{ω | X ω ≥ 5}` gerade das Ereignis `{5, 6}`.
- Dann ist `μ {ω | X ω ≥ 5} = 2 / 6 = 1 / 3`.

### `ENNReal.ofReal r`

Mathlib verwendet für Maße oft den Typ `ℝ≥0∞` der erweiterten nichtnegativen reellen Zahlen.

`ENNReal.ofReal r` bettet einen reellen Wert `r ≥ 0` in diesen Typ ein. Das ist nötig, weil ein Maß
wie `μ A` nicht in `ℝ`, sondern in `ℝ≥0∞` lebt.

Einfaches Beispiel:

- Wenn eine Rechnung die reelle Schranke `1 / 4` liefert, schreibt Mathlib sie für Maße oft als
	`ENNReal.ofReal (1 / 4)`.

## Wichtige Lean- und Mathlib-Bausteine

### `fun ω => ...`

Das ist eine anonyme Funktion. In Wahrscheinlichkeitstheorie sind Zufallsvariablen in Lean einfach
Funktionen, daher taucht diese Form ständig auf.

Einfaches Beispiel:

- `fun ω => 2 * ω` ist die Funktion, die jeden Wert verdoppelt.
-/

example : (fun x : ℝ => 2 * x) 3 = 6 := by
  norm_num

/-!
### `Finset.range n`

Die endliche Menge `{0, 1, ..., n-1}` als `Finset`. Sie wird benutzt, um endliche Summen zu
formulieren.

Einfaches Beispiel:

- `Finset.range 4` steht für die Indizes `0, 1, 2, 3`.

### `Finset.sum (Finset.range n) (fun i => ...)`

Das ist die endliche Summe

`... + ... + ...`

über die Indizes `0` bis `n - 1`. Im File ist das die technische Lean-Form der Partialsumme.

Einfaches Beispiel:

- `Finset.sum (Finset.range 3) (fun i => i + 1)` ist `1 + 2 + 3 = 6`.
-/

example : Finset.sum (Finset.range 3) (fun i : ℕ => i + 1) = 6 := by
  norm_num

/-!
### `∫ ω, f ω ∂μ`

Das ist das Integral von `f` bezüglich `μ`. In probabilistischer Sprache ist das der
Erwartungswert, wenn `f` eine integrierbare Zufallsvariable ist.

Einfaches Beispiel:

- Für einen fairen Würfel ist `∫ ω, X ω ∂μ` einfach der Erwartungswert der Augenzahl, also `3.5`.

### `avg X n` und `partialSum X n`

Diese beiden Begriffe werden im Hauptfile selbst definiert:

- `partialSum X n` ist die Summe der ersten `n` Zufallsvariablen,
- `avg X n` ist ihr empirisches Mittel.

Das Glossar erwähnt sie nur, damit die externen Begriffe darum herum leichter lesbar sind.

Einfaches Beispiel:

- Wenn `X 0 ω = 2`, `X 1 ω = 4`, `X 2 ω = 7`, dann ist `partialSum X 3 ω = 13`.
- Entsprechend ist `avg X 3 ω = 13 / 3`.

## Wichtige Taktiken im Beweis

### `intro`

Führt Annahmen oder Variablen in den lokalen Kontext ein. Wenn das Ziel zum Beispiel eine
Implikation oder ein Allquantor ist, beginnt ein Beweis oft mit `intro`.

Einfaches Beispiel:

- Um `ε > 0 → ...` zu zeigen, beginnt man oft mit `intro hε`.

### `have h : ... := by ...`

Erzeugt ein Hilfslemma `h` im laufenden Beweis. Das ist die Standardmethode, um längere Beweise in
kleinere Zwischenschritte zu zerlegen.

Einfaches Beispiel:

- `have hε2 : ε ^ 2 ≠ 0 := by positivity` speichert eine später benötigte Nebenrechnung.

### `exact h`

Schließt das aktuelle Ziel direkt mit einem bereits vorhandenen Beweis `h`.

Einfaches Beispiel:

- Wenn das Ziel genau `A` ist und im Kontext bereits `h : A` steht, genügt `exact h`.

### `rw [...]`

Schreibt mit Gleichheiten um. Das ist die elementare Ersetzungstaktik in Lean.

Einfaches Beispiel:

- Mit `h : a = b` ersetzt `rw [h]` den Ausdruck `a` durch `b` im Ziel.
-/

example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

/-!
### `simpa [...] using h`

`simpa` bedeutet: vereinfache das Ziel und den Beweis `h`, dann versuche den Abschluss.

Das ist besonders nützlich, wenn Mathlib fast genau den gewünschten Satz liefert, aber die Form
noch leicht umgeschrieben werden muss.

Einfaches Beispiel:

- Wenn Mathlib einen Satz in leicht anderer Schreibweise liefert, kann `simpa [foo] using h` den
  letzten kleinen Umbau automatisch erledigen.

### `calc`

Erlaubt eine Rechnungskette mit mehreren Gleichungen oder Abschätzungen. Das ist im Hauptfile die
wichtigste Taktik für strukturierte Umformungen von Integralen und Varianzen.

Einfaches Beispiel:

- Man kann schreiben: zuerst ist `a = b`, dann `b = c`, also insgesamt `a = c`.

### `ext ω`

Für Funktionen bedeutet `ext`: Zwei Funktionen sind gleich, wenn sie an jedem Punkt denselben Wert
haben. Danach bleibt typischerweise ein punktweiser Beweis in `ω` übrig.

Einfaches Beispiel:

- Um `f = g` zu zeigen, reicht nach `ext ω` oft die Gleichung `f ω = g ω`.
-/

example (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g := by
  ext n
  exact h n

/-!
### `congr`

Zeigt Gleichheit, indem gleiche äußere Struktur auf gleiche Teilstücke reduziert wird. Im File wird
das benutzt, um Summanden oder Integranden gliedweise zu identifizieren.

Einfaches Beispiel:

- Wenn zwei Summen dieselbe Form haben, reduziert `congr` den Beweis oft auf die Gleichheit der
  einzelnen Summanden.

### `refine`

Wendet einen Satz oder Konstruktor an, lässt aber Teilziele offen. Das ist hilfreich, wenn die grobe
Form des Beweises klar ist, die Nebenbedingungen aber separat gezeigt werden sollen.

Einfaches Beispiel:

- Mit `refine foo ?_ ?_` legt man fest, dass `foo` benutzt werden soll, und beweist danach die zwei
  entstehenden Lücken.

### `convert h using 1`

Verwendet einen vorhandenen Beweis `h`, erlaubt aber vorher eine kontrollierte Anpassung des Ziels.
Das ist praktisch, wenn zwei Ausdrücke mathematisch gleich sind, aber nicht exakt dieselbe Lean-
Form haben.

Einfaches Beispiel:

- Wenn das Ziel fast wie `h` aussieht, aber an einer Stelle `n + 1` statt `Nat.succ n` steht, kann
  `convert` die Lücke überbrücken.

### `field_simp`

Vereinfacht rationale Ausdrücke, insbesondere mit Divisionen und Brüchen. Dafür braucht Lean meist
Nichtverschwindensannahmen wie `n ≠ 0` oder `ε ^ 2 ≠ 0`.

Einfaches Beispiel:

- Ausdrücke wie `a / b / c` oder `a / (b * c)` werden damit oft in eine besser handhabbare Form
  gebracht.

### `positivity`

Versucht automatisch, Positivität oder Nichtnegativität zu beweisen. Im Hauptfile wird das genutzt,
um etwa zu zeigen, dass aus `ε > 0` auch `ε ^ 2 ≠ 0` folgt.

Einfaches Beispiel:

- Aus `hε : 0 < ε` kann `positivity` oft direkt Folgerungen wie `0 < ε ^ 2` gewinnen.
-/

example (ε : ℝ) (hε : 0 < ε) : ε ^ 2 ≠ 0 := by
  positivity

/-!
## Lesestrategie für das Hauptfile

Wenn ein Beweisschritt unklar ist, lohnt sich meist diese Reihenfolge:

1. Zuerst die mathematische Aussage der Zeile lesen.
2. Dann prüfen, ob nur mit `rw`, `simpa` oder `calc` umgeschrieben wird.
3. Erst danach die Lean-spezifischen Details wie `congr`, `ext` oder Typumwandlungen ansehen.

So trennt man den mathematischen Kern von der formalen Verpackung.
-/

end FiniteProbabilitySpace
