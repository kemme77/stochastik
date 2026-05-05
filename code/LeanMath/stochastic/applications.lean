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

open MeasureTheory ProbabilityTheory BigOperators Function
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

-- Beispiel: Für n=365, k=23 berechnen wir P(keine Kollision).
-- Ergebnis < 0.5, also P(Kollision) > 0.5
#eval probKeineKollision 365 23

/-- Die Ungleichung ln(1-x) ≤ -x für 0 ≤ x < 1 ist der Schlüssel zur Abschätzung.
    In Mathlib: `Real.add_one_le_exp`. -/
lemma log_one_sub_le_neg (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  calc Real.log (1 - x)
      ≤ Real.log (Real.exp (-x)) := Real.log_le_log h1 h2
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
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hB_cover : ⋃ j, B j = Set.univ)
    (A : Set Ω) (hA : MeasurableSet A) :
    μ A = ∑ j, μ (A ∩ B j) := by
  have hAeq : A = ⋃ j ∈ Finset.univ, (A ∩ B j) := by
    simp only [Finset.mem_univ, iUnion_true]
    rw [← Set.inter_iUnion, hB_cover, Set.inter_univ]
  have hPD : PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (fun j => A ∩ B j) := by
    intro i _ j _ hij
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hB_disj i j hij)
  conv_lhs => rw [hAeq]
  rw [measure_biUnion_finset hPD (fun j _ => hA.inter (hB_meas j))]

/-! ================================================================
## 3. Satz von Bayes
================================================================

Folie: Für A,B ∈ 𝒜 mit P(B) > 0 gilt
  P(A | B) = P(B | A) · P(A) / P(B)

Beweis:
  P(A | B) = P(A ∩ B) / P(B)
           = P(A ∩ B) · P(A) / (P(A) · P(B))
           = P(B | A) · P(A) / P(B)

In Mathlib ist die bedingte Wahrscheinlichkeit über das restringierte Maß definiert:
  `ProbabilityTheory.cond μ s = (μ s)⁻¹ • μ.restrict s`

Die Notation `μ[t|s]` steht für P(t | s):
  `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)`
-/

/-- Erinnerung: `ProbabilityTheory.cond` ist definiert als
    `cond μ s = (μ s)⁻¹ • μ.restrict s`

Die Auswertung auf einer Menge t ergibt:
    `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)`

Das ist äquivalent zu `μ(t ∩ s) / μ(s)`, der Schul-Formel der bedingten Wahrscheinlichkeit.
-/
example (s t : Set Ω) (hs : MeasurableSet s) :
    μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) :=
  cond_apply hs μ t

/-- Satz von Bayes (Mathlib-Version):
    μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t

    Umgeschrieben:  P(A|B) = P(B|A) · P(A) / P(B)
-/
example (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    [IsFiniteMeasure μ] :
    μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t :=
  cond_eq_inv_mul_cond_mul hs ht μ

/-- Hilfssatz (Mathlib): μ[t|s] * μ s = μ (s ∩ t)
    (Multiplikationssatz der bedingten Wahrscheinlichkeit) -/
example (s t : Set Ω) (hs : MeasurableSet s) [IsFiniteMeasure μ] :
    μ[t|s] * μ s = μ (s ∩ t) :=
  cond_mul_eq_inter hs t μ

/-- Totale Wahrscheinlichkeit (Mathlib-Version für Komplement-Zerlegung):
    μ[t|s] * μ s + μ[t|sᶜ] * μ sᶜ = μ t -/
example (s t : Set Ω) (hs : MeasurableSet s) [IsFiniteMeasure μ] :
    μ[t|s] * μ s + μ[t|sᶜ] * μ sᶜ = μ t :=
  cond_add_cond_compl_eq hs μ


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

/-- Wenn A und B unabhängig sind, gilt μ[A|B] = μ A
    (bedingte Wahrscheinlichkeit = unbedingte Wahrscheinlichkeit). -/
theorem unabh_implies_cond_eq
    (A B : Set Ω) (hB : MeasurableSet B)
    (hB_pos : μ B ≠ 0) (hB_fin : μ B ≠ ⊤)
    (h : StochUnabhaengig μ A B) :
    μ[A|B] = μ A := by
  rw [cond_apply hB, Set.inter_comm]
  unfold StochUnabhaengig at h
  rw [h]
  rw [show (μ B)⁻¹ * (μ A * μ B) = μ A * ((μ B)⁻¹ * μ B) from by ring]
  rw [ENNReal.inv_mul_cancel hB_pos hB_fin, mul_one]

/-- Die Mathlib-Definition von Unabhängigkeit (`IndepSets`) stimmt
    mit unserer elementaren Definition überein. -/
example (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : IndepSets {A} {B} μ) :
    μ (A ∩ B) = μ A * μ B := by
  rw [IndepSets_iff] at h
  exact h A B rfl rfl


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

/-- Bedingte Wortwahrscheinlichkeiten: P(Wort_i | Klasse) als rationale Zahlen. -/
structure SpamFilterParams (n : ℕ) where
  /-- P(A_i | Spam) für jedes Wort i -/
  pWortGivenSpam : Fin n → ℚ
  /-- P(A_i | Ham) für jedes Wort i -/
  pWortGivenHam  : Fin n → ℚ

/-- Naive Bayes Spam-Wahrscheinlichkeit:
    P(S | A₁ ∩...∩ Aₙ) = pS / (pH + pS)
    wobei pS = ∏ P(Aᵢ|S) und pH = ∏ P(Aᵢ|H)
    über die vorhandenen Wörter. -/
def naiveBayesSpamProb {n : ℕ} (params : SpamFilterParams n)
    (woerterVorhanden : Fin n → Bool) : ℚ :=
  let indices := Finset.univ.filter (fun i => woerterVorhanden i)
  let pS := ∏ i ∈ indices, params.pWortGivenSpam i
  let pH := ∏ i ∈ indices, params.pWortGivenHam i
  pS / (pH + pS)

/-- Bemerkung: P(H | ...) = 1 - P(S | ...) -/
def naiveBayesHamProb {n : ℕ} (params : SpamFilterParams n)
    (woerterVorhanden : Fin n → Bool) : ℚ :=
  1 - naiveBayesSpamProb params woerterVorhanden

/-- Beispiel: 3 Wörter ("reich", "casino", "Vergrösserung")
    mit fiktiven Wahrscheinlichkeiten.
    P(reich|Spam)=4/5, P(casino|Spam)=7/10, P(vergr|Spam)=3/5
    P(reich|Ham)=1/10, P(casino|Ham)=1/20, P(vergr|Ham)=1/100 -/
def beispielParams : SpamFilterParams 3 where
  pWortGivenSpam := ![4/5, 7/10, 3/5]
  pWortGivenHam  := ![1/10, 1/20, 1/100]

-- Alle drei Wörter kommen vor → hohe Spam-Wahrscheinlichkeit
#eval naiveBayesSpamProb beispielParams (fun _ => true)

-- Kein Wort kommt vor → leeres Produkt (= 1), also P(S) = 1/2
#eval naiveBayesSpamProb beispielParams (fun _ => false)

-- Nur "reich" kommt vor
#eval naiveBayesSpamProb beispielParams (![true, false, false])

/-- Die Spam-Formel ist korrekt im Sinne: P(S|W) + P(H|W) = 1,
    vorausgesetzt der Nenner ist nicht 0. -/
theorem spam_ham_sum_one {n : ℕ} (params : SpamFilterParams n)
    (w : Fin n → Bool)
    (hNenner : (∏ i ∈ Finset.univ.filter (fun i => w i), params.pWortGivenHam i) +
               (∏ i ∈ Finset.univ.filter (fun i => w i), params.pWortGivenSpam i) ≠ 0) :
    naiveBayesSpamProb params w + naiveBayesHamProb params w = 1 := by
  unfold naiveBayesHamProb
  ring

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
