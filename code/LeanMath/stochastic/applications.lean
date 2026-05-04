/-
  Diskrete Wahrscheinlichkeitsverteilung – Bayes, Totale Wahrscheinlichkeit, Spam-Filter

  Diese Datei ist ein kommentiertes Lean-Skript, das die Vorlesungsfolien
  zu folgenden Themen in Lean 4 / Mathlib widerspiegelt:

  1. Hash-Kollision und Geburtstags-Paradoxon
  2. Satz der totalen Wahrscheinlichkeit
  3. Satz von Bayes
  4. Stochastische Unabhängigkeit (Erinnerung)
  5. Naiver Bayes'scher Spam-Filter
-/

import Mathlib

open MeasureTheory ProbabilityTheory BigOperators
open Finset Set MeasureTheory
open scoped ENNReal Topology BigOperators MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace BayesSpam

/-! ================================================================
## 1. Hash-Kollision und Geburtstags-Paradoxon
================================================================

Folie: Beim Hashing werden zufällig k Daten auf n Speicherplätze verteilt.
Das komplementäre Ereignis einer Kollision ist, dass alle k Daten auf
verschiedene Plätze fallen (Variation ohne Wiederholung).

P(A^c_{k,n}) = n! / ((n-k)! · n^k) = ∏_{i=0}^{k-1} (1 - i/n)

Abschätzung:
  P(A^c_{k,n}) ≤ exp(- k(k-1) / (2n))

Geburtstags-Paradoxon: Für n=365, k=23 ist P(A_{k,n}) > 1/2.
-/

/-- Anzahl der Variationen ohne Wiederholung: n · (n-1) · ... · (n-k+1) -/
def variationenOhneWdh (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n - i)

/-- Anzahl der Variationen mit Wiederholung: n^k -/
def variationenMitWdh (n k : ℕ) : ℕ := n ^ k

/-- Die Wahrscheinlichkeit keiner Kollision ist VoW / VmW = ∏_{i=0}^{k-1} (1 - i/n). -/
def probKeineKollision (n k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (1 - (i : ℚ) / n)

/-- Beispiel: Für n=365, k=23 berechnen wir P(keine Kollision). -/
#eval probKeineKollision 365 23
-- Ergebnis < 0.5, also P(Kollision) > 0.5

/-- Die Ungleichung ln(1-x) ≤ -x für 0 ≤ x < 1 ist der Schlüssel zur Abschätzung.
    In Mathlib: `Real.log_le_sub_one_of_le` bzw. `Real.add_one_le_exp`. -/
example (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) : Real.log (1 - x) ≤ -x := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by
    rw [show (1 : ℝ) - x = 1 + (-x) from by ring]
    exact Real.add_one_le_exp (-x)
  calc Real.log (1 - x)
      ≤ Real.log (Real.exp (-x)) := by
          apply Real.log_le_log h1 h2
    _ = -x := Real.log_exp (-x)


/-! ================================================================
## 2. Satz der totalen Wahrscheinlichkeit
================================================================

Folie: Für eine Zerlegung Ω = ⋃_{j=1}^n B_j mit B_i ∩ B_k = ∅ für i ≠ k gilt:
  P(A) = ∑_{j=1}^n P(A | B_j) · P(B_j)

In Mathlib wird dies über `MeasureTheory.Measure.sum` und bedingte
Wahrscheinlichkeiten ausgedrückt.
-/

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Satz der totalen Wahrscheinlichkeit (endliche Zerlegung):

Wenn B₁, ..., Bₙ eine messbare Partition von Ω bilden, gilt
  μ(A) = ∑ j, μ(A ∩ Bⱼ)

Dies folgt direkt aus der σ-Additivität des Maßes.
-/
theorem totale_wahrscheinlichkeit {n : ℕ}
    (B : Fin n → Set Ω)
    (hB_meas : ∀ j, MeasurableSet (B j))
    (hB_disj : Pairwise (Disjoint on B))
    (hB_cover : ⋃ j, B j = Set.univ)
    (A : Set Ω) (hA : MeasurableSet A) :
    μ A = ∑ j, μ (A ∩ B j) := by
  have hAeq : A = ⋃ j, (A ∩ B j) := by
    ext x; simp [hB_cover, mem_iUnion]
    constructor
    · intro hx
      have : x ∈ ⋃ j, B j := hB_cover ▸ Set.mem_univ x
      rw [Set.mem_iUnion] at this
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hx, hj⟩
    · rintro ⟨j, hx, -⟩
      exact hx
  rw [hAeq]
  apply measure_iUnion
  · intro i j hij
    exact Disjoint.mono (Set.inter_subset_right) (Set.inter_subset_right) (hB_disj hij)
  · intro j
    exact hA.inter (hB_meas j)

/-! ================================================================
## 3. Satz von Bayes
================================================================

Folie: Für A,B ∈ 𝒜 mit P(B) > 0 gilt
  P(A | B) = P(B | A) · P(A) / P(B)

Beweis:
  P(A | B) = P(A ∩ B) / P(B)
           = P(A ∩ B) · P(A) / (P(A) · P(B))
           = P(B | A) · P(A) / P(B)
-/

/-- Bedingte Wahrscheinlichkeit: P(A | B) = μ(A ∩ B) / μ(B) -/
def condProb (A B : Set Ω) : ENNReal :=
  μ (A ∩ B) / μ B

notation:50 "P[" A " | " B "]" => condProb _ A B

/-- Satz von Bayes: P(A|B) = P(B|A) · P(A) / P(B) -/
theorem bayes
    (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hB_pos : μ B ≠ 0) (hA_pos : μ A ≠ 0)
    (hA_fin : μ A ≠ ⊤) (hB_fin : μ B ≠ ⊤) :
    condProb μ A B = condProb μ B A * μ A / μ B := by
  unfold condProb
  rw [Set.inter_comm B A]
  ring_nf
  rw [ENNReal.div_div]

/-- Hilfssatz: P(A ∩ B) = P(A | B) · P(B) -/
theorem condProb_mul_measure
    (A B : Set Ω)
    (hB_pos : μ B ≠ 0) (hB_fin : μ B ≠ ⊤) :
    condProb μ A B * μ B = μ (A ∩ B) := by
  unfold condProb
  rw [ENNReal.div_mul_cancel hB_pos hB_fin]


/-! ================================================================
## 4. Stochastische Unabhängigkeit
================================================================

Folie: Zwei Ereignisse A,B heißen stochastisch unabhängig, falls
  P(A ∩ B) = P(A) · P(B)

Gleichbedeutend damit ist P(A|B) = P(A) und P(B|A) = P(B).
-/

/-- Stochastische Unabhängigkeit: μ(A ∩ B) = μ(A) · μ(B) -/
def StochUnabhaengig (A B : Set Ω) : Prop :=
  μ (A ∩ B) = μ A * μ B

/-- Wenn A und B unabhängig sind, gilt P(A|B) = P(A). -/
theorem unabh_implies_condProb_eq
    (A B : Set Ω)
    (hB_pos : μ B ≠ 0) (hB_fin : μ B ≠ ⊤)
    (h : StochUnabhaengig μ A B) :
    condProb μ A B = μ A := by
  unfold condProb
  unfold StochUnabhaengig at h
  rw [h]
  rw [ENNReal.mul_div_cancel_right _ hB_pos hB_fin]

/-- Die Mathlib-Definition von Unabhängigkeit (`IndepSets`) stimmt
    mit unserer elementaren Definition überein. -/
example (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : IndepSets {A} {B} μ) :
    μ (A ∩ B) = μ A * μ B := by
  exact h (mem_singleton A) (mem_singleton B)


/-! ================================================================
## 5. Naiver Bayes'scher Spam-Filter
================================================================

Folie: Gegeben ist eine E-Mail E. Wir möchten anhand des Vorkommens
bestimmter Wörter A₁, ..., Aₙ entscheiden, ob es sich um Spam (S)
oder Ham (H) handelt.

Naive Annahme (bedingte Unabhängigkeit):
  P(A₁ ∩ ... ∩ Aₙ | S) = P(A₁|S) · ... · P(Aₙ|S)
  P(A₁ ∩ ... ∩ Aₙ | H) = P(A₁|H) · ... · P(Aₙ|H)

Mit P(S) = P(H) = 1/2 und Bayes:
  P(S | A₁ ∩...∩ Aₙ) =
    P(A₁|S)·...·P(Aₙ|S) / (P(A₁|H)·...·P(Aₙ|H) + P(A₁|S)·...·P(Aₙ|S))

Bemerkung: P(H | A₁ ∩...∩ Aₙ) = 1 - P(S | A₁ ∩...∩ Aₙ)
-/

/-- Modell: Klassifikation einer Mail als Spam oder Ham. -/
inductive MailKlasse where
  | Spam
  | Ham
  deriving DecidableEq, Repr

open MailKlasse

/-- Bedingte Wortwahrscheinlichkeiten: P(Wort_i | Klasse) -/
structure SpamFilterParams (n : ℕ) where
  /-- P(A_i | Spam) für jedes Wort i -/
  pWortGivenSpam : Fin n → ℚ
  /-- P(A_i | Ham) für jedes Wort i -/
  pWortGivenHam  : Fin n → ℚ
  /-- Alle Wahrscheinlichkeiten liegen in (0,1) -/
  hSpam_pos : ∀ i, 0 < pWortGivenSpam i
  hSpam_lt  : ∀ i, pWortGivenSpam i < 1
  hHam_pos  : ∀ i, 0 < pWortGivenHam i
  hHam_lt   : ∀ i, pWortGivenHam i < 1

/-- Naive Bayes Spam-Wahrscheinlichkeit:
    P(S | A₁ ∩...∩ Aₙ) = pS / (pH + pS)
    wobei pS = ∏ P(Aᵢ|S) und pH = ∏ P(Aᵢ|H) -/
def naiveBayesSpamProb {n : ℕ} (params : SpamFilterParams n)
    (woerterVorhanden : Fin n → Bool) : ℚ :=
  let pS := ∏ i ∈ Finset.univ.filter (fun i => woerterVorhanden i),
              params.pWortGivenSpam i
  let pH := ∏ i ∈ Finset.univ.filter (fun i => woerterVorhanden i),
              params.pWortGivenHam i
  pS / (pH + pS)

/-- Bemerkung: P(H | ...) = 1 - P(S | ...) -/
def naiveBayesHamProb {n : ℕ} (params : SpamFilterParams n)
    (woerterVorhanden : Fin n → Bool) : ℚ :=
  1 - naiveBayesSpamProb params woerterVorhanden

/-- Beispiel: 3 Wörter ("reich", "casino", "Vergrösserung")
    mit fiktiven Wahrscheinlichkeiten. -/
def beispielParams : SpamFilterParams 3 where
  pWortGivenSpam := ![0.8, 0.7, 0.6]
  pWortGivenHam  := ![0.1, 0.05, 0.01]
  hSpam_pos := by decide
  hSpam_lt  := by decide
  hHam_pos  := by decide
  hHam_lt   := by decide

/-- Alle drei Wörter kommen vor → hohe Spam-Wahrscheinlichkeit -/
#eval naiveBayesSpamProb beispielParams (fun _ => true)
-- Erwartetes Ergebnis: nahe 1

/-- Kein Wort kommt vor → Produkt ist leer (= 1), also P(S) = 0.5 -/
#eval naiveBayesSpamProb beispielParams (fun _ => false)
-- Erwartetes Ergebnis: 1/2

/-! ================================================================
## Zusammenfassung der Formeln (Folien-Referenz)
================================================================

• Hash-Kollision:
  P(Aᶜ_{k,n}) = ∏_{i=0}^{k-1} (1 - i/n) ≤ exp(-k(k-1)/(2n))

• Geburtstags-Paradoxon:
  n=365, k=23 ⟹ P(A_{k,n}) > 1/2

• Totale Wahrscheinlichkeit:
  P(A) = ∑_j P(A|Bⱼ) · P(Bⱼ)

• Bayes:
  P(A|B) = P(B|A) · P(A) / P(B)

• Stochastische Unabhängigkeit:
  P(A ∩ B) = P(A) · P(B) ⟺ P(A|B) = P(A)

• Naiver Bayes Spam-Filter:
  P(S|A₁∩...∩Aₙ) = ∏P(Aᵢ|S) / (∏P(Aᵢ|H) + ∏P(Aᵢ|S))
-/

end BayesSpam
