import Mathlib

/-!
#  Typentheorie, Curry-Howard und Beweisen in Lean


## Gliederung

1. Typen und Terme
2. Induktive Typen
3. Abhängige Typen
4. Der Typ `Prop` – Aussagen in Lean
5. Gleichheit in Lean
6. Die Curry-Howard-Korrespondenz
7. Vorwärts- und Rückwärtsbeweise
8. Grundlegende Taktiken
9. Logische Junktoren als Typkonstruktionen
10. Quantoren
11. Mengen in Lean (`Set α`)
12. Mengenbeweise
13. Zusammenfassung

Alle Beispiele sind bewusst einfach gehalten und zum
Ausprobieren gedacht.
-/

-- ============================================================================
/-! ## 1. Typen und Terme -/
-- ============================================================================

/-
Lean ist eine typisierte formale Sprache.
Das bedeutet: **Jeder Ausdruck hat einen Typ.**

Ein Typ beschreibt, welche Art von Objekt ein Ausdruck ist.
Ein Term ist ein konkreter Ausdruck dieses Typs.

Man kann sich einen Typ grob als „Klasse erlaubter
Ausdrücke" vorstellen.
-/

/-! ### 1.1 Erste Typchecks -/

/-
Mit `#check` kann man den Typ eines Ausdrucks anzeigen.
-/

#check 3          -- 3 : Nat
#check true       -- true : Bool
#check Nat        -- Nat : Type
#check Bool       -- Bool : Type

/-
Man liest:
- `3` ist ein Term vom Typ `Nat`.
- `true` ist ein Term vom Typ `Bool`.
- `Nat` ist selbst ein Typ.
-/

/-! ### 1.2 Typen sind selbst Objekte -/

/-
In Lean sind Typen selbst wieder Objekte, über die man
sprechen kann. Es gibt eine Hierarchie von Typ-Universen:
-/

#check Prop       -- Prop : Type    (Typ der Aussagen)
#check Type       -- Type : Type 1
#check Type 1     -- Type 1 : Type 2

/-
`Prop` ist der Typ aller logischen Aussagen –
dazu kommen wir in Abschnitt 4.
-/

-- ============================================================================
/-! ## 2. Induktive Typen -/
-- ============================================================================

/-
Viele wichtige Typen in Lean sind **induktive Typen**.

Die Grundidee: Man gibt an, wie Elemente dieses Typs
erzeugt werden dürfen, nämlich durch **Konstruktoren**.
-/

/-! ### 2.1 Die natürlichen Zahlen `Nat` -/

/-
Die natürlichen Zahlen werden durch zwei Konstruktoren
aufgebaut:

- `Nat.zero` – die Zahl 0 (Basisfall)
- `Nat.succ n` – der Nachfolger von `n` (rekursiver Fall)

Anschaulich:
- `0` ist eine natürliche Zahl.
- Wenn `n` eine natürliche Zahl ist, dann auch `Nat.succ n`.
-/

#check Nat.zero
#check Nat.succ

#eval Nat.zero                              -- 0
#eval Nat.succ Nat.zero                     -- 1
#eval Nat.succ (Nat.succ Nat.zero)          -- 2

/-
Die natürlichen Zahlen entstehen also schrittweise:

    Nat.zero
    Nat.succ Nat.zero
    Nat.succ (Nat.succ Nat.zero)
    ...

Die übliche Schreibweise `0`, `1`, `2`, ... ist nur
angenehme Notation.
-/

example : Nat := Nat.zero
example : Nat := Nat.succ Nat.zero
example : Nat := Nat.succ (Nat.succ Nat.zero)

/-! ### 2.2 Warum heißt das „induktiv"? -/

/-
Weil man über solche Typen per **Fallunterscheidung** und
**Induktion** argumentieren kann.

Für `Nat` bedeutet das:
- Man behandelt den Basisfall `0`.
- Man zeigt den Schritt von `n` zu `n + 1`.
-/

example (n : Nat) : n = n := by
  rfl

/-! ### 2.3 Ein eigener induktiver Typ: `MeineListe` -/

/-
Wie `Nat` hat auch eine Liste einen Basisfall und einen
rekursiven Fall. Hier definieren wir eine einfache Liste
natürlicher Zahlen:
-/

inductive MeineListe where
  | leer  : MeineListe
  | cons  : Nat → MeineListe → MeineListe

/-
- `leer` ist die leere Liste (vergleichbar mit `Nat.zero`).
- `cons n l` hängt eine Zahl `n` vorne an die Liste `l` an
  (vergleichbar mit `Nat.succ n`).

Die Liste `[3, 1, 2]` entsteht also schrittweise:
-/

#check MeineListe.leer
#check MeineListe.cons 3
  (MeineListe.cons 1
    (MeineListe.cons 2 MeineListe.leer))

/-! ### 2.4 Rekursive Funktionen durch Pattern Matching -/

/-
Wie bei `Nat` kann man rekursive Funktionen definieren,
indem man die Fälle der Konstruktoren unterscheidet.
-/

def MeineListe.laenge : MeineListe → Nat
  | MeineListe.leer     => 0
  | MeineListe.cons _ l => 1 + l.laenge

def MeineListe.summe : MeineListe → Nat
  | MeineListe.leer     => 0
  | MeineListe.cons n l => n + l.summe

#eval MeineListe.leer.laenge
#eval (MeineListe.cons 3
  (MeineListe.cons 1
    (MeineListe.cons 2 MeineListe.leer))).laenge
#eval (MeineListe.cons 3
  (MeineListe.cons 1
    (MeineListe.cons 2 MeineListe.leer))).summe

example : MeineListe.leer.laenge = 0 := by rfl
example :
  (MeineListe.cons 5 MeineListe.leer).laenge = 1 := by
  rfl
example :
  (MeineListe.cons 3
    (MeineListe.cons 7 MeineListe.leer)).summe = 10 := by
  rfl

/-
Das Muster ist dasselbe wie bei `Nat`:
- Ein Basisfall (`leer` / `zero`)
- Ein rekursiver Konstruktor (`cons` / `succ`)
- Funktionen durch Fallunterscheidung und Rekursion
-/

-- ============================================================================
/-! ## 3. Abhängige Typen -/
-- ============================================================================

/-
In einer gewöhnlichen typisierten Sprache hängt der Typ
eines Ausdrucks meist nicht von einem Wert ab.

In der Typentheorie dürfen Typen aber auch **von Daten
abhängen**. Das nennt man **abhängige Typen**.

Eine der wichtigsten Grundformen ist:

    (x : α) → β x

Hier hängt der Ergebnistyp `β x` vom Wert `x` ab.
-/

/-! ### 3.1 Nicht-abhängig vs. abhängig -/

/-
Eine gewöhnliche Funktion hat einen festen Rückgabetyp:
-/

#check fun x : Nat => x + 1
-- Typ: Nat → Nat
-- Der Rückgabetyp ist immer `Nat`, egal was `x` ist.

/-
Bei einer abhängigen Funktion **hängt der Rückgabetyp
vom Eingabewert ab**:
-/

#check fun x : Nat => (rfl : x = x)
-- Typ: (x : Nat) → x = x
-- Für x=0 ist der Rückgabetyp `0 = 0`
-- Für x=3 ist der Rückgabetyp `3 = 3`
-- Das sind jeweils verschiedene Typen!

/-! ### 3.2 Beispiel: typisierte Listen -/

/-
Noch anschaulicher wird es mit Listen, deren Länge schon
im Typ steht.

`ListeN n` soll der Typ aller Listen mit genau `n`
Einträgen sein.
Dann sind `ListeN 2` und `ListeN 5` verschiedene Typen.
-/

inductive ListeN : Nat → Type where
  | leer : ListeN 0
  | cons : Nat → ListeN n → ListeN (n + 1)

/-
Die Konstruktoren sagen:
- `leer` ist eine Liste der Länge `0`
- `cons x xs` hängt vorne ein Element an und erhöht die
  Länge um `1`

Der Längenindex steht also direkt im Typ.
-/

#check ListeN 0
#check ListeN 3

#check ListeN.leer
#check ListeN.cons

/-
Jetzt definieren wir eine abhängige Funktion:
Zu jeder Zahl `n` erzeugen wir eine Liste der Länge `n`,
die nur aus Nullen besteht.
-/

def nullListe : (n : Nat) → ListeN n
  | 0 => ListeN.leer
  | n + 1 => ListeN.cons 0 (nullListe n)

#check nullListe
#check nullListe 0    -- ListeN 0
#check nullListe 3    -- ListeN 3
#check nullListe 5    -- ListeN 5

/-
Hier sieht man die Abhängigkeit sehr direkt:
- `nullListe 0` hat Typ `ListeN 0`
- `nullListe 3` hat Typ `ListeN 3`
- `nullListe 5` hat Typ `ListeN 5`

Der **Wert** `n` bestimmt also, welchen **Rückgabetyp**
die Funktion hat. Genau das ist eine abhängige Funktion.
-/

/-! ### 3.3 Der Allquantor als abhängige Funktion -/

/-
Der gewöhnliche Allquantor `∀ x : α, P x` ist genau so
eine abhängige Funktion, nur dass der Ergebnistyp jetzt
eine Aussage ist.
-/

example : ∀ x : Nat, x = x := by
  intro x
  rfl

/-
Auch hier hängt der Rückgabetyp `x = x` vom Wert `x` ab.
`∀` ist also in Lean keine fremde logische Operation,
sondern eine spezielle Form einer abhängigen Funktion.
-/

-- ============================================================================
/-! ## 4. Der Typ `Prop` – Aussagen in Lean -/
-- ============================================================================

/-
In Lean gibt es einen speziellen Typ `Prop`.
Er enthält **logische Aussagen** (Propositionen).

Ausdrücke vom Typ `Prop` sind keine Daten,
sondern **Behauptungen**.
Ein Term vom Typ einer Proposition ist ein **Beweis**
dieser Behauptung.
-/

/-! ### 4.1 Aussagen als Typen -/

#check (1 = 1 : Prop)
#check (2 < 5 : Prop)
#check (True : Prop)
#check (False : Prop)

/-
Aussagen wie `1 = 1`, `True` oder `False` sind selbst
Ausdrücke, deren Typ `Prop` ist.
-/

/-! ### 4.2 Aussagen kombinieren -/

variable (P Q R : Prop)

#check P
#check P → Q         -- Implikation
#check P ∧ Q         -- Konjunktion (Und)
#check P ∨ Q         -- Disjunktion (Oder)
#check ¬ P           -- Negation

/-
Aus einzelnen Aussagen kann man neue Aussagen bauen:
- `P → Q` – wenn P, dann Q
- `P ∧ Q` – P und Q
- `P ∨ Q` – P oder Q
- `¬ P` – nicht P (definiert als `P → False`)
-/

/-! ### 4.3 Beweise mit `theorem` und `example` -/

/-
Mit `theorem` gibt man einer bewiesenen Aussage einen
Namen. Das ist nützlich, wenn man den Beweis später
wiederverwenden will.
-/

theorem eins_gleich_eins : 1 = 1 := by
  rfl

theorem addition_kommutativ (a b : Nat) :
    a +  b = b + a := by
  omega

/-
Mit `example` formuliert man einen anonymen Beweis –
ohne Namen, nur zum Zeigen.
-/

example : 2 = 2 := by
  rfl

example : (1 = 1 : Prop) := by
  rfl

example : (True : Prop) := by
  trivial

/-
Man kann benannte Theoreme später in anderen Beweisen
wiederverwenden:
-/

example : 1 = 1 := eins_gleich_eins

example (x y : Nat) : x + y = y + x :=
  addition_kommutativ x y

/-
`example` ist wie `theorem`, nur ohne Namen.
Anstatt den Beweis neu zu führen, wird hier ein
existierender Beweis eingesetzt – das ist die
Wiederverwendung, die `theorem` ermöglicht.
-/

/-! ### 4.4 Zusammenfassung -/

/-
- `Prop` ist der Typ aller logischen Aussagen.
- `theorem name : Aussage := Beweis` definiert einen
  benannten Beweis.
- `example : Aussage := Beweis` formuliert einen
  anonymen Beweis.
- Jeder Beweis ist ein Term, dessen Typ die bewiesene
  Aussage ist.
-/

-- ============================================================================
/-! ## 5. Gleichheit in Lean -/
-- ============================================================================

/-
Auch Gleichheit ist in Lean selbst ein Typ, genauer eine
Aussage in `Prop`.

Wenn `a b : α` sind, dann ist `a = b` ein Ausdruck vom
Typ `Prop`. Ein Beweis von `a = b` ist also ein Term
dieses Typs.
-/

#check Eq
#check (2 = 2)
#check (2 = 3)

/-! ### 5.1 Reflexivität mit `rfl` -/

/-
Die wichtigste elementare Taktik für Gleichheit ist `rfl`.

`rfl` steht für Reflexivität und beweist Gleichheiten,
bei denen beide Seiten definitional auf dieselbe Form
reduziert werden können.
-/

example : 2 = 2 := by
  rfl

example (x : Nat) : x = x := by
  rfl

example : 2 + 3 = 5 := by
  rfl

/-! ### 5.2 Umschreiben mit `rw` -/

/-
Man kann Gleichheiten zum Umschreiben verwenden.
Die Taktik `rw [h]` ersetzt Vorkommen der linken Seite
von `h` durch die rechte.
-/

example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

/-
Gleichheit ist in Lean also nicht nur ein Zeichen, sondern
eine Aussage, mit der man genauso arbeiten kann wie mit
anderen Propositionen.
-/

-- ============================================================================
/-! ## 6. Die Curry-Howard-Korrespondenz -/
-- ============================================================================

/-
Die zentrale Idee der Curry-Howard-Korrespondenz lautet:

> **Aussagen entsprechen Typen.**
> **Beweise entsprechen Termen dieser Typen.**

Insbesondere ist eine Implikation `P → Q` genau der Typ
von Funktionen, die einen Beweis von `P` in einen Beweis
von `Q` verwandeln.
-/

/-! ### 6.1 Implikation = Funktion -/

example (h : P → Q) (hp : P) : Q :=
  h hp

/-
Hier ist `h` eine Funktion:
- Input: ein Beweis von `P`
- Output: ein Beweis von `Q`

Und `h hp` ist genau **Modus Ponens**.
-/

/-! ### 6.2 Transitivität als Funktion -/

/-
Wenn man zwei Implikationen hat,

- `h₁ : P → Q`
- `h₂ : Q → R`

dann kann man sie hintereinander ausführen.
Genau das ist die Transitivität:

    P → Q,   Q → R   ergibt   P → R

In Lean ist das einfach Funktionskomposition.
-/

example (h₁ : P → Q) (h₂ : Q → R) : P → R :=
  fun hp => h₂ (h₁ hp)

/-
Man startet mit einem Beweis `hp : P`.
Dann macht `h₁` daraus einen Beweis von `Q`.
Danach macht `h₂` daraus einen Beweis von `R`.

Also ist die Transitivität von Implikationen nichts anderes
als das Hintereinanderausführen von Funktionen.
-/

/-! ### 6.3 Beweis = Term -/

example (h : P) : P := h

/-
Ein Beweis einer Aussage ist einfach ein Term dieses Typs.
-/

example : True := True.intro

-- ============================================================================
/-! ## 7. Vorwärts- und Rückwärtsbeweise -/
-- ============================================================================

/-
Beim Arbeiten in Lean sind zwei Blickrichtungen wichtig:

**Rückwärtsbeweis:** Man startet mit dem Ziel und fragt:
> Was müsste ich zeigen, damit dieses Ziel folgt?

Taktiken in Lean arbeiten oft auf diese Weise:
Sie ersetzen das aktuelle Ziel durch einfachere Teilziele.

**Vorwärtsbeweis:** Man startet mit den Annahmen und fragt:
> Was kann ich aus diesen Annahmen direkt gewinnen?

Dabei erzeugt man aus vorhandenen Beweisen neue Beweise.

In der Praxis benutzt man meist beide Ansätze zusammen.
-/

/-! ### 7.1 Beispiel: Rückwärtsbeweis -/

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  /-
  Anfangsziel:   ⊢ Q

  `apply h` sagt: Um `Q` zu zeigen, reicht es
  wegen `h : P → Q`, `P` zu zeigen.
  Neues Ziel:    ⊢ P
  -/
  apply h
  /-
  Jetzt ist das Ziel `P`.
  Das ist als Annahme `hp` vorhanden.
  -/
  exact hp

/-! ### 7.2 Beispiel: Vorwärtsbeweis -/

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  /-
  Statt vom Ziel rückwärts zu arbeiten, gewinnen wir
  erst neue Information aus den Annahmen.
  -/
  have hq : Q := h hp
  exact hq

/-! ### 7.3 Direkter Vergleich -/

-- Rückwärtsbeweis:
example (P Q R : Prop)
    (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R := by
  apply h₂
  apply h₁
  exact hp

-- Vorwärtsbeweis:
example (P Q R : Prop)
    (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R := by
  have hq : Q := h₁ hp
  have hr : R := h₂ hq
  exact hr

/-
Beide Beweise verwenden dieselben mathematischen
Informationen, aber die Denkweise ist unterschiedlich.
-/

/-! ### 7.4 Wie Taktiken Beweisterme konstruieren -/

/-
Man kann sich einen Taktikbeweis als schrittweise
Konstruktion eines Terms vorstellen.
-/

example (P Q : Prop) : P → Q → P := by
  intro hp
  intro _hq
  exact hp

/-
Was passiert:

1. `intro hp` – verschiebt `P` aus dem Ziel in den
   Kontext als `hp : P`. Neues Ziel: `Q → P`

2. `intro _hq` – verschiebt `Q` aus dem Ziel in den
   Kontext als `_hq : Q`. Neues Ziel: `P`

3. `exact hp` – löst das Ziel `P` durch `hp`.

Der fertige Beweis entspricht dem Term:
-/

example (P Q : Prop) : P → Q → P :=
  fun hp => fun _hq => hp

/-
Taktiken konstruieren also denselben Beweisterm,
nur in schrittweiser, interaktiver Form.
-/

/-! ### 7.5 Gemischter Beweis -/

example (P Q R : Prop)
    (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R := by
  have hq : Q := h₁ hp   -- Vorwärtsschritt
  apply h₂                -- Rückwärtsschritt
  exact hq

/-
Das ist typisch für Lean: Ein Taktikbeweis ist oft
eine Mischung aus Vorwärts- und Rückwärtsdenken.
-/

-- ============================================================================
/-! ## 8. Grundlegende Taktiken -/
-- ============================================================================

/-
Hier sind die wichtigsten elementaren Taktiken,
die man zum Beweisen braucht.
-/

/-! ### 8.1 `intro` – Annahme einführen -/

example : P → Q → P := by
  intro hp _hq
  exact hp

/-
`intro` verschiebt eine Annahme aus dem Ziel in den
Kontext. Bei einem Ziel `P → Q → P` führt `intro hp`
einen Beweis `hp : P` ein.
-/

/-! ### 8.2 `exact` – Ziel direkt lösen -/

example (h : P) : P := by
  exact h

/-
`exact t` bedeutet: Der Term `t` beweist das aktuelle
Ziel genau.
-/

/-! ### 8.3 `assumption` – Annahme automatisch finden -/

example (h : P) : P := by
  assumption

/-
Wenn das Ziel als Annahme im Kontext vorhanden ist,
findet `assumption` es automatisch.
-/

/-! ### 8.4 `apply` – Rückwärts anwenden -/

example (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp

/-
`apply h` reduziert das aktuelle Ziel unter Verwendung
von `h` auf ein neues, einfacheres Ziel.
-/

/-! ### 8.5 `constructor` – Konjunktion beweisen -/

example (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

/-
Bei einer Konjunktion `P ∧ Q` muss man beide Teile
beweisen. `constructor` erzeugt zwei Unterziele.
-/

/-! ### 8.6 `cases` – Fallunterscheidung -/

example (h : P ∧ Q) : P := by
  cases h with
  | intro hp hq =>
      exact hp

example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

/-
`cases` zerlegt eine Annahme nach ihren Konstruktoren.
- Bei `P ∧ Q` bekommt man `hp : P` und `hq : Q`.
- Bei `P ∨ Q` entstehen zwei Fälle:
  `inl` (links) und `inr` (rechts).
-/

/-! ### 8.7 `left` und `right` – Disjunktion beweisen -/

example (hp : P) : P ∨ Q := by
  left
  exact hp

example (hq : Q) : P ∨ Q := by
  right
  exact hq

/-
Bei einer Disjunktion `P ∨ Q` muss man sich für eine
Seite entscheiden.
-/

/-! ### 8.8 `rfl` – Reflexive Gleichheit -/

example : 2 + 3 = 5 := by
  rfl

/-
`rfl` beweist Gleichheiten, wenn beide Seiten
auf dieselbe Form reduziert werden können.
-/

/-! ### 8.9 `rw` – Umschreiben -/

example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

/-
`rw [h]` schreibt mit der Gleichheit `h` um.
-/

/-! ### 8.10 `have` – Zwischenschritt einfügen -/

example (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R := by
  have hq : Q := h₁ hp
  have hr : R := h₂ hq
  exact hr

/-
`have` erzeugt einen benannten Zwischenschritt im
Beweis (Vorwärtsschritt).
-/

-- ============================================================================
/-! ## 9. Logische Junktoren als Typkonstruktionen -/
-- ============================================================================

/-
Im Sinne der Curry-Howard-Korrespondenz kann man lesen:

- `P → Q`
  entspricht einer Funktion von `P`-Beweisen nach `Q`-Beweisen.

- `P ∧ Q`
  entspricht einem Paar aus Beweis von `P` und Beweis von `Q`.

- `P ∨ Q`
  entspricht entweder einem Beweis von `P` oder einem Beweis von `Q`.

- `False`
  ist ein Typ ohne Beweise.

- `¬ P`
  ist eine Abkürzung für `P → False`.

- `∀ x, P x`
  ist eine Funktion, die zu jedem `x` einen Beweis von `P x` liefert.

- `∃ x, P x`
  ist ein Zeuge `x` zusammen mit einem Beweis von `P x`.
-/

/-! ### 9.1 Kontraposition -/

example : (P → Q) → (¬ Q → ¬ P) := by
  intro hpq hnq hp
  apply hnq
  exact hpq hp

-- ============================================================================
/-! ## 10. Quantoren -/
-- ============================================================================

/-! ### 10.1 Allquantor `∀` -/

example : ∀ n : Nat, n = n := by
  intro n
  rfl

/-
Beim Allquantor `∀` führt `intro` ein beliebiges Element
ein. Man muss die Aussage für dieses allgemeine Element
beweisen.
-/

/-! ### 10.2 Existenzquantor `∃` -/

example : ∃ n : Nat, n = 0 := by
  refine ⟨0, ?_⟩
  rfl

/-
Beim Existenzquantor `∃` muss man einen konkreten Zeugen
angeben und dann zeigen, dass er die gewünschte Eigenschaft
erfüllt.
-/

-- ============================================================================
/-! ## 11. Mengen in Lean -/
-- ============================================================================

/-
In Lean/Mathlib ist eine Menge auf einem Typ `α` im
Wesentlichen ihre Indikator-Eigenschaft:

    Set α = α → Prop

Das bedeutet:
Eine Menge `A : Set α` ist eine Funktion, die jedem
`x : α` eine Aussage `A x : Prop` zuordnet.
Diese Aussage bedeutet: „x ist Element von A".

Die Schreibweise `x ∈ A` ist also letztlich nur Notation
für `A x`.

**Das ist die wichtigste Idee für Mengen in Lean.**
-/

/-! ### 11.1 Mengen als Eigenschaften -/

#check Set
#check Set Nat
#check (fun x : Nat => x = 0)

example : Set Nat := fun x : Nat => x = 0

/-
Die Menge `{0}` kann man als Eigenschaft definieren:
Sie enthält genau die Zahlen `x`, für die `x = 0` gilt.
-/

/-! ### 11.2 Die Mengen-Notation `{x | P x}` -/

example : Set Nat := {x : Nat | x = 0}

/-
`{x : α | P x}` bedeutet die Menge aller `x`,
für die `P x` gilt.
-/

/-! ### 11.3 Elementschaft -/

example : 0 ∈ ({x : Nat | x = 0} : Set Nat) := by
  rfl

example : 1 ∉ ({x : Nat | x = 0} : Set Nat) := by
  intro h
  simp at h

example : 2 ∈ ({x : Nat | x = 2} : Set Nat) := by
  rfl

/-
- `0 ∈ ...` bedeutet, dass die Aussage wahr ist.
- `1 ∉ ...` bedeutet, dass die Aussage nicht wahr ist.
-/

-- ============================================================================
/-! ## 12. Mengenbeweise -/
-- ============================================================================

variable {α : Type}
variable (A B C : Set α)
variable (x : α)

/-! ### 12.1 Elementschaft und Teilmengen -/

/-
`A ⊆ B` bedeutet in Lean:

    ∀ x, x ∈ A → x ∈ B

Das ist eine Allaussage, die man als Implikation bzw.
Funktion auf Beweisen lesen kann.
-/

example (h : x ∈ A) : x ∈ A := by
  exact h

example (hA : x ∈ A) (hAB : A ⊆ B) : x ∈ B := by
  exact hAB hA

/-! ### 12.2 Schnittmenge -/

/-
Mitgliedschaft in `A ∩ B` ist im Wesentlichen eine
**Konjunktion**.
-/

example (hx : x ∈ A ∩ B) : x ∈ A := by
  exact hx.1

example (hx : x ∈ A ∩ B) : x ∈ B := by
  exact hx.2

example (hA : x ∈ A) (hB : x ∈ B) : x ∈ A ∩ B := by
  constructor
  · exact hA
  · exact hB

/-! ### 12.3 Vereinigung -/

/-
Mitgliedschaft in `A ∪ B` ist im Wesentlichen eine
**Disjunktion**.
-/

example (hA : x ∈ A) : x ∈ A ∪ B := by
  left
  exact hA

example (hB : x ∈ B) : x ∈ A ∪ B := by
  right
  exact hB

example (hx : x ∈ A ∪ B) : x ∈ B ∪ A := by
  cases hx with
  | inl hA =>
      right
      exact hA
  | inr hB =>
      left
      exact hB

/-! ### 12.4 Leere Menge -/

example : x ∉ (∅ : Set α) := by
  intro hx
  exact hx

/-
Mitgliedschaft in der leeren Menge liefert einen
Widerspruch.
-/

/-! ### 12.5 Mengengleichheit und Extensionalität -/

/-
Zwei Mengen sind gleich, wenn sie dieselben Elemente
haben. Die Taktik `ext` drückt diese Extensionalität aus.
-/

example : A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

/-! ### 12.6 Transitivität von Teilmengen -/

example (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  intro x hx
  apply h₂
  apply h₁
  exact hx

/-
Als Term geschrieben:
-/

example (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C :=
  fun _x hx => h₂ (h₁ hx)

/-
Die Transitivität von Teilmengen ist einfach eine
**Funktionskomposition** – Curry-Howard in Aktion!
-/

/-! ### 12.7 Teilmenge der Vereinigung -/

example : A ⊆ A ∪ B := by
  intro x hx
  left
  exact hx

example : B ⊆ A ∪ B := by
  intro x hx
  right
  exact hx

/-! ### 12.8 Schnittmenge ist Teilmenge -/

example : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1

example : A ∩ B ⊆ B := by
  intro x hx
  exact hx.2

/-! ### 12.9 Teilmenge und Schnittmenge -/

/-
Wenn `A ⊆ B`, dann ist `A ∩ B = A`.
Schneiden mit einer Obermenge ändert nichts.
-/

example (h : A ⊆ B) : A ∩ B = A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, h hx⟩

/-! ### 12.10 Teilmenge und Vereinigung -/

/-
Wenn `A ⊆ B`, dann ist `A ∪ B = B`.
-/

example (h : A ⊆ B) : A ∪ B = B := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl ha => exact h ha
    | inr hb => exact hb
  · intro hx
    right
    exact hx

/-! ### 12.11 Distributivgesetz -/

/-
`A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`
-/

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro ⟨ha, hbc⟩
    cases hbc with
    | inl hb => left; exact ⟨ha, hb⟩
    | inr hc => right; exact ⟨ha, hc⟩
  · intro h
    cases h with
    | inl hab => exact ⟨hab.1, Or.inl hab.2⟩
    | inr hac => exact ⟨hac.1, Or.inr hac.2⟩

/-! ### 12.12 Neutrale Elemente und `simp` -/

/-
`simp` ist ein Taktik-Automatismus, der viele einfache
Gleichungen aus einer Datenbank bekannter Lemmata löst.
-/

example : A ∪ ∅ = A := by
  ext x
  simp

example : A ∩ Set.univ = A := by
  ext x
  simp

example (a : Nat) : a + 0 = a := by
  simp

example (P : Prop) : P ∧ True ↔ P := by
  simp

example (A : Set α) : A ∩ A = A := by
  ext x
  simp

/-
`simp` ist sehr nützlich, sollte aber erst eingesetzt
werden, wenn man die elementaren Taktiken verstanden hat.
-/

-- ============================================================================
/-! ## 13. Zusammenfassung -/
-- ============================================================================

/-
**Kernideen dieser Vorlesung:**

1. In Lean hat **jeder Ausdruck** einen Typ.
2. Induktive Typen werden durch **Konstruktoren** aufgebaut.
3. Abhängige Typen erlauben es, dass Typen
   **von Werten abhängen**.
4. `Prop` ist der Typ der **logischen Aussagen**.
5. Die **Curry-Howard-Korrespondenz** identifiziert
   Aussagen mit Typen und Beweise mit Termen.
6. Beweise in Lean können **vorwärts** oder **rückwärts**
   geführt werden.
7. **Taktiken** konstruieren Beweisterme schrittweise.
8. Mengen in Lean sind Funktionen `α → Prop` –
   Mengenoperationen entsprechen logischen Operationen.
-/
