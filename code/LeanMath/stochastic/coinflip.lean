import Mathlib

open BigOperators
open Finset
open scoped BigOperators

/-!
# Stochastik_Muenzwurf_Leitfaden

Diese Datei ist als Vorlesungsbegleitung für den n-fachen Münzwurf gedacht.

* Ergebnisraum = alle Folgen von `K` und `Z`
* Ereignisse = Mengen von vollständigen Abläufen
* `X i` = Kopf-Anzeige des i-ten Wurfs als 0-1-Funktion
* `S n` = Gesamtzahl der Köpfe

-/

namespace StochastikMuenzwurf

/-- Ein einzelner Münzwurf: Kopf oder Zahl. -/
inductive Coin where
  | K
  | Z
  deriving DecidableEq, Fintype, Repr

open Coin

/-- Ein vollständiger Ablauf von `n` Münzwürfen. -/
abbrev Ω (n : ℕ) := Fin n → Coin

/-- Beispiel: ein Ablauf von drei Münzwürfen, nämlich Kopf-Zahl-Kopf. -/
example : Ω 3 :=
  fun
    | ⟨0, _⟩ => K
    | ⟨1, _⟩ => Z
    | ⟨2, _⟩ => K

/-- Ereignisse sind Mengen von vollständigen Abläufen. -/
abbrev Event (n : ℕ) := Set (Ω n)

/-- Die Anzahl aller vollständigen Abläufe ist `2^n`. -/
example (n : ℕ) : Fintype.card (Ω n) = 2 ^ n := by
  have hCoin : Fintype.card Coin = 2 := by decide
  simp [Ω, hCoin]

/-- Das Ereignis: an Stelle `i` fällt Kopf. -/
def headAt {n : ℕ} (i : Fin n) : Event n := fun ω => ω i = K

/-- Das Ereignis: an Stelle `i` fällt Zahl. -/
def tailAt {n : ℕ} (i : Fin n) : Event n := fun ω => ω i = Z

/-- Das Komplement von "Kopf an Stelle i" ist "Zahl an Stelle i". -/
example {n : ℕ} (i : Fin n) : (headAt i)ᶜ = tailAt i := by
  ext ω
  change (ω i ≠ K) ↔ (ω i = Z)
  cases ω i <;> simp

/-- Die 0-1-Anzeige des `i`-ten Wurfs. -/
def X {n : ℕ} (i : Fin n) : Ω n → ℕ := fun ω =>
  if ω i = K then 1 else 0

/-- Die Gesamtzahl der Köpfe. -/
def S (n : ℕ) : Ω n → ℕ := fun ω => ∑ i : Fin n, X i ω

section TwoThrows

/-- Vier konkrete Abläufe für `n = 2`. -/
def ωKK : Ω 2 := fun _ => K

def ωKZ : Ω 2
  | ⟨0, _⟩ => K
  | ⟨1, _⟩ => Z

def ωZK : Ω 2
  | ⟨0, _⟩ => Z
  | ⟨1, _⟩ => K

def ωZZ : Ω 2 := fun _ => Z

/-- Konkrete Auswertung der Kopf-Anzeigen. -/
example : X ⟨0, by decide⟩ ωKK = 1 := by
  simp [X, ωKK]

example : X ⟨1, by decide⟩ ωKZ = 0 := by
  simp [X, ωKZ]

example : X ⟨0, by decide⟩ ωZK = 0 := by
  simp [X, ωZK]

example : X ⟨1, by decide⟩ ωZZ = 0 := by
  simp [X, ωZZ]

/-- Konkrete Auswertung der Kopfzahl `S 2`. -/
example : S 2 ωKK = 2 := by
  simp [S, X, ωKK]

example : S 2 ωKZ = 1 := by
  decide

example : S 2 ωZK = 1 := by
  decide

example : S 2 ωZZ = 0 := by
  simp [S, X, ωZZ]

/-- Alle vier Abläufe in einer endlichen Liste. -/
def allOmega2 : Finset (Ω 2) := {ωKK, ωKZ, ωZK, ωZZ}

example : allOmega2.card = 4 := by
  decide

/-- Das Ereignis: erster Wurf ist Kopf. -/
def AfirstHead2 : Event 2 := headAt ⟨0, by decide⟩

/- In `n = 2` hat dieses Ereignis genau zwei Elemente. -/
open Classical in
example : Fintype.card {ω : Ω 2 // AfirstHead2 ω} = 2 := by
  let e : {ω : Ω 2 // AfirstHead2 ω} ≃ Coin :=
    { toFun := fun x => x.1 ⟨1, by decide⟩
      invFun := fun c =>
        ⟨
          fun
            | ⟨0, _⟩ => K
            | ⟨1, _⟩ => c,
          by simp [AfirstHead2, headAt]
        ⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        fin_cases i
        · simpa [eq_comm, AfirstHead2, headAt] using x.2
        · rfl
      right_inv := by
        intro c
        rfl }
  calc
    Fintype.card {ω : Ω 2 // AfirstHead2 ω} = Fintype.card Coin := Fintype.card_congr e
    _ = 2 := by decide

/-- Gemeinsame Betrachtung zweier Würfe. -/
def pairX : Ω 2 → ℕ × ℕ := fun ω => (X ⟨0, by decide⟩ ω, X ⟨1, by decide⟩ ω)

example : pairX ωKK = (1, 1) := by simp [pairX, X, ωKK]
example : pairX ωKZ = (1, 0) := by simp [pairX, X, ωKZ]
example : pairX ωZK = (0, 1) := by simp [pairX, X, ωZK]
example : pairX ωZZ = (0, 0) := by simp [pairX, X, ωZZ]

end TwoThrows

section EventLanguage

variable {n : ℕ} (A B : Event n)

/- Sprachlich: "A oder B". -/
#check A ∪ B

/- Sprachlich: "A und B". -/
#check A ∩ B

/- Sprachlich: "nicht A". -/
#check Aᶜ

end EventLanguage

/-- Das Ereignis: genau `k` Köpfe. -/
def exactlyKHeads (n k : ℕ) : Event n := fun ω => S n ω = k

/-- Das Ereignis: mindestens ein Kopf. -/
def atLeastOneHead (n : ℕ) : Event n := fun ω => 0 < S n ω

/-- Das sichere Ereignis. -/
def sureEvent (n : ℕ) : Event n := Set.univ

/-- Das unmögliche Ereignis. -/
def impossibleEvent (n : ℕ) : Event n := ∅

example (n : ℕ) : (sureEvent n)ᶜ = impossibleEvent n := by
  ext ω
  simp [sureEvent, impossibleEvent]

end StochastikMuenzwurf
