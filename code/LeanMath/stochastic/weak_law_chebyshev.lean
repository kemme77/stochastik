import Mathlib

open MeasureTheory ProbabilityTheory BigOperators
open Filter
open scoped ENNReal Topology BigOperators

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/--
`partialSum X n` ist die Zufallsvariable

`X 0 + ... + X (n-1)`.

Wir summieren also die ersten `n` Glieder der Folge `X`, wobei die Auswertung punktweise in
`ω : Ω` erfolgt.
-/
def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => Finset.sum (Finset.range n) (fun i => X i ω)

/--
`avg X n` ist das empirische Mittel der ersten `n` Zufallsvariablen:

`(X 0 + ... + X (n-1)) / n`.

Dieses Objekt ist die zentrale Größe im schwachen Gesetz der großen Zahlen.
-/
def avg (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.sum (Finset.range n) (fun i => X i ω) : ℝ) / n

section Helpers

variable {μ}

/--
Schreibt das empirische Mittel als konstantes Vielfaches der Partialsumme um.

Inhaltlich ist das nur die Identität

`avg X n = (1 / n) * partialSum X n`.

Diese Form ist für Integrale und Varianzen bequemer als die Schreibweise mit Division.
-/
lemma avg_eq_const_mul_partialSum (X : ℕ → Ω → ℝ) (n : ℕ) :
    avg X n = fun ω => (1 / n : ℝ) * partialSum X n ω := by
  ext ω
  simp [avg, partialSum, div_eq_mul_inv, mul_comm]

/--
Das Integral einer endlichen Summe ist die Summe der Integrale.

Hier wird die übliche Linearität des Erwartungswerts für die Partialsumme `partialSum X n`
formuliert.
-/
lemma integral_partialSum
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ) :
  ∀ n, ∫ ω, partialSum X n ω ∂μ = Finset.sum (Finset.range n) (fun i => ∫ ω, X i ω ∂μ) := by
  intro n
  simpa [partialSum] using
    (integral_finset_sum (μ := μ) (s := Finset.range n) (f := fun i => X i)
      (fun i _ => (hL2 i).integrable one_le_two))

lemma integral_eq_of_identDistrib
    (X : ℕ → Ω → ℝ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ) :
    ∀ n, ∫ ω, X n ω ∂μ = ∫ ω, X 0 ω ∂μ := by
  intro n
  simpa using (h_ident n).integral_eq

/--
Alle empirischen Mittelwerte haben denselben Erwartungswert wie `X 0`.

Anschaulich: Wenn alle `X n` gleich verteilt sind, dann haben sie denselben Mittelwert. Also hat
auch ihr Durchschnitt wieder genau diesen Mittelwert.

Der Beweis zerlegt `avg X n` in eine Konstante mal Partialsumme, zieht die Konstante vor das
Integral und ersetzt dann mithilfe der identischen Verteilung jeden Summanden durch den gemeinsamen
Erwartungswert.
-/
lemma integral_avg
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, avg X n ω ∂μ = ∫ ω, X 0 ω ∂μ := by
  have hsum :
      ∫ ω, partialSum X n ω ∂μ = Finset.sum (Finset.range n) (fun i => ∫ ω, X i ω ∂μ) :=
    integral_partialSum (μ := μ) X hL2 n
  have hpartial_int : Integrable (partialSum X n) μ := by
    simpa [partialSum] using
      (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞)) (s := Finset.range n)
        (f := fun i => X i) (fun i _ => hL2 i)).integrable one_le_two
  have hsame := integral_eq_of_identDistrib (μ := μ) X h_ident
  -- Wir schreiben den Durchschnitt als skalierten Summenausdruck und werten die Summe gliedweise aus.
  calc
    ∫ ω, avg X n ω ∂μ
        = ∫ ω, ((1 / n : ℝ) * partialSum X n ω) ∂μ := by
            simp [avg_eq_const_mul_partialSum]
    _ = (1 / n : ℝ) * ∫ ω, partialSum X n ω ∂μ := by
          rw [integral_const_mul]
    _ = (1 / n : ℝ) * Finset.sum (Finset.range n) (fun i => ∫ ω, X i ω ∂μ) := by
          rw [hsum]
    _ = (1 / n : ℝ) * Finset.sum (Finset.range n) (fun _ => ∫ ω, X 0 ω ∂μ) := by
          congr with i
          exact hsame i
    _ = ∫ ω, X 0 ω ∂μ := by
          simp [hn]

/--
Die Varianz der Partialsumme ist `n` mal die gemeinsame Varianz.

Das ist genau die bekannte Formel

`Var(X₁ + ... + Xₙ) = Var(X₁) + ... + Var(Xₙ)`

für paarweise unabhängige Zufallsvariablen. Weil alle `X i` dieselbe Verteilung haben, besitzen sie
auch dieselbe Varianz, also vereinfacht sich die Summe zu `n * Var(X 0)`.
-/
lemma variance_partialSum
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (h_pair : Pairwise fun i j => IndepFun (X i) (X j) μ) :
    ∀ n, variance (partialSum X n) μ = n * variance (X 0) μ := by
  intro n
  have hsum :
      variance (Finset.sum (Finset.range n) X) μ
        = Finset.sum (Finset.range n) (fun i => variance (X i) μ) := by
    simpa using
      (ProbabilityTheory.IndepFun.variance_sum
        (μ := μ) (s := Finset.range n) (X := X)
        (hs := fun i hi => hL2 i)
        (h := by
          intro i hi j hj hij
          exact h_pair hij))
  -- Zuerst identifizieren wir `partialSum` mit einer expliziten endlichen Summe.
  -- Danach ersetzen wir alle Einzelvarianzen durch die gemeinsame Varianz von `X 0`.
  calc
    variance (partialSum X n) μ
        = variance (Finset.sum (Finset.range n) X) μ := by
            congr 1
            ext ω
            simp [partialSum]
    _ = Finset.sum (Finset.range n) (fun i => variance (X i) μ) := hsum
    _ = Finset.sum (Finset.range n) (fun _ => variance (X 0) μ) := by
          congr with i
          simpa using (h_ident i).variance_eq
    _ = n * variance (X 0) μ := by
          simp

/--
Eine endliche Summe von `L²`-Zufallsvariablen liegt wieder in `L²`.

Diese Aussage wird später benötigt, damit Erwartungswert- und Varianzformeln auf die Partialsumme
angewendet werden dürfen.
-/
lemma memLp_partialSum
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ) :
    ∀ n, MeasureTheory.MemLp (partialSum X n) 2 μ := by
  intro n
  simpa [partialSum] using
    (memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞)) (s := Finset.range n)
      (f := fun i => X i) (fun i _ => hL2 i))

/--
Auch das empirische Mittel liegt in `L²`.

Denn `avg X n` ist nur ein konstantes Vielfaches der bereits behandelten Partialsumme.
-/
lemma memLp_avg
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ) :
    ∀ n, MeasureTheory.MemLp (avg X n) 2 μ := by
  intro n
  simpa [avg_eq_const_mul_partialSum, smul_eq_mul] using
    (memLp_partialSum (μ := μ) X hL2 n).const_mul (1 / n : ℝ)

/--
Die Varianz des empirischen Mittels fällt wie `1 / n`.

Das ist die zentrale quantitative Beobachtung hinter dem Chebyshev-Beweis des schwachen Gesetzes:
Mittelwerte werden mit wachsendem `n` immer weniger streuend.

Formal kombiniert der Beweis die Skalierungsregel für Varianzen mit der zuvor bestimmten Varianz der
Partialsumme.
-/
lemma variance_avg
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (h_pair : Pairwise fun i j => IndepFun (X i) (X j) μ)
    {n : ℕ} (hn : n ≠ 0) :
    variance (avg X n) μ = variance (X 0) μ / n := by
  have hsumVar : variance (partialSum X n) μ = n * variance (X 0) μ :=
    variance_partialSum (μ := μ) X hL2 h_ident h_pair n
  -- Wir ziehen den Faktor `(1 / n)` aus der Varianz heraus und setzen dann die Summenformel ein.
  calc
    variance (avg X n) μ
        = variance (fun ω => (1 / n : ℝ) * partialSum X n ω) μ := by
            simp [avg_eq_const_mul_partialSum]
    _ = (1 / n : ℝ) ^ 2 * variance (partialSum X n) μ := by
          rw [ProbabilityTheory.variance_const_mul]
    _ = (1 / n : ℝ) ^ 2 * (n * variance (X 0) μ) := by
          rw [hsumVar]
    _ = variance (X 0) μ / n := by
          field_simp [hn]

/--
Chebyshev-Ungleichung für das empirische Mittel.

In Worten: Die Wahrscheinlichkeit einer Abweichung vom gemeinsamen Erwartungswert wird durch

`Var(avg X n) / ε^2`

kontrolliert. Zusammen mit `Var(avg X n) = Var(X 0) / n` ergibt das genau die gewünschte Schranke.
-/
lemma chebyshev_avg
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (h_pair : Pairwise fun i j => IndepFun (X i) (X j) μ)
    {n : ℕ} (hn : n ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |avg X n ω - ∫ x, X 0 x ∂μ|}
      ≤ ENNReal.ofReal (variance (X 0) μ / (n * ε ^ 2)) := by
  have hmean : ∫ ω, avg X n ω ∂μ = ∫ ω, X 0 ω ∂μ :=
    integral_avg (μ := μ) X hL2 h_ident hn
  have hvar : variance (avg X n) μ = variance (X 0) μ / n :=
    variance_avg (μ := μ) X hL2 h_ident h_pair hn
  have hmem : MeasureTheory.MemLp (avg X n) 2 μ := memLp_avg (μ := μ) X hL2 n
  -- Zunächst zentrieren wir um den tatsächlichen Erwartungswert von `avg X n`.
  -- Danach wenden wir die Standardform der Chebyshev-Ungleichung an.
  calc
    μ {ω | ε ≤ |avg X n ω - ∫ x, X 0 x ∂μ|}
        = μ {ω | ε ≤ |avg X n ω - ∫ x, avg X n x ∂μ|} := by
            congr 1
            ext ω
            rw [hmean]
    _ ≤ ENNReal.ofReal (variance (avg X n) μ / ε ^ 2) := by
          simpa using
            (ProbabilityTheory.meas_ge_le_variance_div_sq
              (μ := μ) (X := avg X n) hmem hε)
    _ = ENNReal.ofReal (variance (X 0) μ / (n * ε ^ 2)) := by
          rw [hvar]
          congr 1
          field_simp [hn]

/--
Ein fester Realwert geteilt durch `n + 1` konvergiert gegen `0`.

Dieses elementare Grenzwertlemma wird später auf die Chebyshev-Schranke angewendet.
-/
lemma tendsto_inverse_nat_mul_const (a : ℝ) :
    Tendsto (fun n : ℕ => a / ((n.succ : ℝ))) atTop (𝓝 0) := by
  convert (tendsto_const_div_atTop_nhds_zero_nat a).comp (tendsto_add_atTop_nat 1) using 1

/--
Die explizite obere Chebyshev-Schranke geht für `n → ∞` gegen `0`.

Genau dieses Verschwinden des deterministischen Fehlerterms erlaubt am Ende den Sandwich-Schritt im
schwachen Gesetz der großen Zahlen.
-/
lemma tendsto_variance_bound (σ2 ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => σ2 / ((n.succ : ℝ) * ε ^ 2)) atTop (𝓝 0) := by
  have hε2 : ε ^ 2 ≠ 0 := by positivity
  have hmul :
      (fun n : ℕ => σ2 / ((n.succ : ℝ) * ε ^ 2))
        = fun n : ℕ => (σ2 / (ε ^ 2)) / (n.succ : ℝ) := by
          ext n
          field_simp [hε2]
  rw [hmul]
  exact tendsto_inverse_nat_mul_const (σ2 / (ε ^ 2))

end Helpers

/--
Eine einfache Chebyshev-Version des schwachen Gesetzes der großen Zahlen.

Für paarweise unabhängige, identisch verteilte reellwertige Zufallsvariablen mit endlichem zweitem
Moment konvergieren die empirischen Mittel in Wahrscheinlichkeit gegen den gemeinsamen
Erwartungswert.

Die Beweisidee ist klassisch:
1. Erwartungswert des Mittels bestimmen.
2. Varianz des Mittels als `Var(X 0) / n` berechnen.
3. Chebyshev anwenden.
4. Die entstehende obere Schranke gegen `0` laufen lassen.
-/
theorem weak_law_of_large_numbers_chebyshev
    (X : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MeasureTheory.MemLp (X n) 2 μ)
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (h_pair : Pairwise fun i j => IndepFun (X i) (X j) μ) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ => μ {ω | ε ≤ |avg X n.succ ω - ∫ x, X 0 x ∂μ|})
        atTop (𝓝 0) := by
  intro ε hε
  -- Chebyshev liefert für jedes `n + 1` eine explizite obere Schranke.
  have hbound :
      ∀ n : ℕ,
        μ {ω | ε ≤ |avg X n.succ ω - ∫ x, X 0 x ∂μ|}
          ≤ ENNReal.ofReal (variance (X 0) μ / ((n.succ : ℝ) * ε ^ 2)) := by
    intro n
    simpa using
      (chebyshev_avg (μ := μ) X hL2 h_ident h_pair (hn := Nat.succ_ne_zero n) (hε := hε))
  have hlim_real :
      Tendsto (fun n : ℕ => variance (X 0) μ / ((n.succ : ℝ) * ε ^ 2)) atTop (𝓝 0) :=
    tendsto_variance_bound (σ2 := variance (X 0) μ) (ε := ε) hε
  have hlim :
      Tendsto (fun n : ℕ => ENNReal.ofReal (variance (X 0) μ / ((n.succ : ℝ) * ε ^ 2)))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hlim_real
  -- Die gesuchten Wahrscheinlichkeiten liegen zwischen `0` und einer deterministischen Schranke,
  -- die gegen `0` konvergiert. Damit folgt die Konvergenz ebenfalls per Sandwich-Argument.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim ?_ ?_
  · intro n
    exact zero_le _
  · intro n
    exact hbound n
