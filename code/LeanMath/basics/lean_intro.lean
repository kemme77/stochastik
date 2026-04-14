import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat


#eval (some (fun x : Int => x + 3) : Option (Int → Int)) <*> (some 2)  -- some 5
#check (1 + 2 : Int)
#check Type
#check Type 1
-- Lean-Code: Eine Funktion, die eine natürliche Zahl in eine reelle Zahl umwandelt
example : ℕ → ℝ :=
fun n => (n : ℝ) + 0.5  -- Gebe das Ergebnis `n + 0.5` zurück, was ein reeller Wert ist


-- Beispiel für `refl` mit natürlichen Zahlen
example : 5 = 5 := by
  rfl  -- Beweise, dass 5 gleich 5 ist

example : 2 + 3 = 5 := by
  rfl  -- Beweise, dass 5 gleich 5 ist

example {A : Prop} : (¬ A = A) → False := by
  intro ha
  exact ha rfl

example {A : Prop} : A = A → True := by
  intro h
  trivial

example {A : Prop} : True → (A = A) := by
  intro h
  rfl

example {A : Prop} : A → True := by
  intro h
  exact True.intro

example {α : Type} (h : IsEmpty α) (x : α) : False := by
  exact h.elim x

example {α : Type} (h1 : Nonempty α) (h2 : ¬ Nonempty α) : False := by
  exact h2 h1

example {A : Prop} : (¬ A) = (A → False) := by
  rfl  -- Beweise, dass die Negation von A gleich der Aussage "A impliziert False" ist


-- Beispiel für `exact` mit natürlichen Zahlen
example (a b : ℕ) (h : a = b) : b = a := by
  exact h.symm  -- Verwende die Symmetrie der Gleichheit


-- Beispiel für `simp` mit natürlichen Zahlen
example : 2 + 2 = 4 := by
  simp  -- Vereinfache den Ausdruck

-- Beispiel für `apply` mit natürlichen Zahlen
example (a b c : ℕ) (h : a = b) (h2 : b = c) : a = c := by
  apply Eq.trans h  -- Wende die Transitivität der Gleichheit an
  exact h2          -- Beweise, dass `b = c`


-- Beispiel für `cases` mit natürlichen Zahlen
example (n : ℕ) : n = 0 ∨ n ≠ 0 := by
  cases n with
  | zero => left; rfl  -- Fall `n = 0`
  | succ k => right;
                  intro h;
                  contradiction  -- Fall `n = succ k` (n ist der Nachfolger von k)

-- Beispiel für `intro` mit natürlichen Zahlen
example (a b : ℕ) : a = b → b = a := by
  intro h  -- Führe die Annahme `h : a = b` ein
  exact h.symm  -- Verwende die Symmetrie der Gleichheit

-- Beispiel für `rw` mit natürlichen Zahlen
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]  -- Ersetze `a` durch `b` in der Gleichung


open Set -- Öffne den `Set`-Namespace für eine einfachere Syntax




variable {α : Type*}  -- Definiere eine Typvariable `α`


/-!
## Mengen in Lean

Eine Menge von Elementen eines Typs `α` ist in Lean ein Ausdruck vom Typ `Set α`.
Wichtig ist: Eine Menge ist intern einfach ihre Zugehörigkeitsfunktion.

Das heißt:

* `Set α` ist im Kern dasselbe wie `α → Prop`
* zu jedem Element `x : α` sagt die Menge, ob `x` dazugehört

Wenn `A : Set α` und `x : α` sind, dann bedeutet

* `x ∈ A`: `x` liegt in der Menge `A`
* `x ∉ A`: `x` liegt nicht in `A`

Eine Menge kann man daher oft durch eine Bedingung definieren.
Zum Beispiel ist `{n : ℕ | n < 5}` die Menge aller natürlichen Zahlen kleiner als `5`.
-/


example (A : Set α) (x : α) : x ∈ A ↔ A x := by
  rfl

/-- Eine Menge kann direkt als Funktion `ℕ → Prop` definiert werden. -/
def PositiveNatSet : Set ℕ := fun n => 0 < n

example : 2 ∈ PositiveNatSet := by
  change 0 < 2
  norm_num

example : 0 ∉ PositiveNatSet := by
  change ¬ (0 < 0)
  norm_num

/-- Die Menge der geraden natürlichen Zahlen. -/
def EvenNatSet : Set ℕ := {n | n % 2 = 0}

example : 4 ∈ EvenNatSet := by
  simp [EvenNatSet]

example : 5 ∉ EvenNatSet := by
  simp [EvenNatSet]

/-- Die Menge aller natürlichen Zahlen kleiner als `5`. -/
def SmallNatSet : Set ℕ := {n | n < 5}

example : 3 ∈ SmallNatSet := by
  simp [SmallNatSet]

example : 7 ∉ SmallNatSet := by
  simp [SmallNatSet]

example : 2 ∈ SmallNatSet ∩ EvenNatSet := by
  constructor
  · simp [SmallNatSet]
  · simp [EvenNatSet]

example : 4 ∈ SmallNatSet ∪ EvenNatSet := by
  left
  simp [SmallNatSet]

example {α : Type*} (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro hx
    constructor
    · intro hxA
      exact hx (Or.inl hxA)
    · intro hxB
      exact hx (Or.inr hxB)
  · intro hx hxAB
    cases hxAB with
    | inl hxA => exact hx.1 hxA
    | inr hxB => exact hx.2 hxB

example {α : Type*} (A B : Set α) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp

example {α : Type*} (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  · intro hx
    by_cases hxA : x ∈ A
    · right
      intro hxB
      exact hx ⟨hxA, hxB⟩
    · left
      exact hxA
  · intro hx hxAB
    cases hx with
    | inl hxA => exact hxA hxAB.1
    | inr hxB => exact hxB hxAB.2



-- Intro
example {α : Type*} (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx -- Führe `x` und die Annahme `hx : x ∈ A ∩ B` ein
  exact hx.1 -- Zeige, dass `x ∈ A` gilt


-- Exact, rewrite, ext
example {α : Type*} (A B : Set α) : A ∩ B = B ∩ A := by
  ext x  -- Verwende Extensionalität
  rw [mem_inter_iff, mem_inter_iff]  -- Wende die Definition der Schnittmenge an
  exact and_comm  -- Verwende die Kommutativität der Konjunktion

def B : Set ℕ := { x | x < 5 }

-- simp
example : 3 ∈ B := by
  unfold B  -- Wandle `A` in seine Definition um
  simp      -- Zeige, dass 3 < 5 gilt

-- apply
example {α : Type*} (A B : Set α) (h : A ⊆ B) : A ∩ A ⊆ B := by
  intro x hx
  apply h  -- Wende die Hypothese `h` an
  exact hx.1

--cases
example {α : Type*} (A B : Set α) (x : α) (h : x ∈ A ∪ B) : x ∈ A ∨ x ∈ B := by
  cases h with
  | inl ha => left; exact ha  -- Fall `x ∈ A`
  | inr hb => right; exact hb -- Fall `x ∈ B`

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  exact le_trans h₀ h₁

example {α : Type*} (A B : Set α) (x : α)
    (hxA : x ∈ A) (hxB : x ∉ B) : ¬ (A ⊆ B) := by
  intro hAB
  have hx_in_B : x ∈ B := hAB hxA
  exact hxB hx_in_B


/-!
## Endliche Mengen

In Lean ist eine endliche Menge eine Menge `A : Set α` zusammen mit einem Beweis
`A.Finite`. Inhaltlich heißt das: Die Menge hat nur endlich viele Elemente.

Besonders einfach sind konkrete Mengen wie `{0, 1, 2}`. Auch Mengen wie
`{n : ℕ | n < 4}` sind endlich, weil dort nur die Zahlen `0, 1, 2, 3` vorkommen.
-/

example : Set.Finite ({0, 1, 2} : Set ℕ) := by
  simp

example : Set.Finite ({n : ℕ | n < 4} : Set ℕ) := by
  simpa using (Finset.Iio 4).finite_toSet

example : ¬ Set.Infinite ({n : ℕ | n < 4} : Set ℕ) := by
  have hfinite : Set.Finite ({n : ℕ | n < 4} : Set ℕ) := by
    simpa [Finset.mem_Iio] using
      ((Finset.Iio 4).finite_toSet : Set.Finite ((Finset.Iio 4 : Finset ℕ) : Set ℕ))
  exact hfinite.not_infinite

example (A : Set ℕ) (hA : Set.Finite A) : Set.Finite (A ∪ {7}) := by
  exact hA.union (Set.finite_singleton 7)

example : Set.Finite (Set.univ : Set (Fin 4)) := by
  simpa using (Set.finite_univ : Set.Finite (Set.univ : Set (Fin 4)))

example : Fintype.card (Fin 4) = 4 := by
  simp


/-!
## `Fin n`

`Fin n` ist der Typ der natürlichen Zahlen, die echt kleiner als `n` sind.
Man kann `Fin n` also als die endliche Menge `{0, 1, ..., n-1}` verstehen.

Ein Element von `Fin n` besteht in Lean aus

* einer natürlichen Zahl und
* einem Beweis, dass diese Zahl kleiner als `n` ist.

Darum ist `Fin n` die typische Indexmenge für endliche Objekte.
Außerdem kann man auf `Fin n` genauso Mengen betrachten wie auf jedem anderen Typ:
Eine Menge von Indizes ist einfach ein Ausdruck vom Typ `Set (Fin n)`.
-/

example : Fin 3 := ⟨0, by decide⟩

example : Fin 3 := ⟨2, by decide⟩

example (i : Fin 5) : i.1 < 5 := by
  exact i.2

/-- Eine Menge von erlaubten Indizes in `Fin 5`. -/
def smallIndices : Set (Fin 5) := { i | i.1 ≤ 2 }

example : (⟨1, by decide⟩ : Fin 5) ∈ smallIndices := by
  simp [smallIndices]

example : (⟨4, by decide⟩ : Fin 5) ∉ smallIndices := by
  intro h
  unfold smallIndices at h
  have h' : ¬ (((⟨4, by decide⟩ : Fin 5) : ℕ) ≤ 2) := by decide
  exact h' h

/-- Eine Funktion auf `Fin 3` kann man als endliche Liste mit drei Positionen lesen. -/
def valuesOnFin3 : Fin 3 → ℕ
  | ⟨0, _⟩ => 10
  | ⟨1, _⟩ => 20
  | ⟨2, _⟩ => 30

example : valuesOnFin3 ⟨1, by decide⟩ = 20 := by
  rfl
