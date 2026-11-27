import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_medcore_model_floor

/-!
# Wide remainder inner floor

Route wide-arc-signed-remainder, lemma L-goldbach-wide-remainder-inner-floor.

This file develops the set-theoretic and measure-theoretic skeleton of the
registered statement: the widened arc sets, their measurability, the exclusion
of the low-modulus mask inside the remainder, and the additivity of signed
integrals over disjoint pieces.

The analytic step (the signed floor for the near-rational part of the widened
remainder) is still open in this file.
-/

namespace Conjectures.Goldbach

noncomputable section

open scoped BigOperators

/-- The log-weighted prime weight used by the registered statement. -/
def wrfW : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0

/-- The exponential kernel. -/
def wrfE : ℝ → ℂ := fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The weighted exponential sum. -/
def wrfS : ℕ → (ℕ → ℝ) → ℝ → ℂ :=
  fun n u t => Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * wrfE ((k : ℝ) * t))

/-- The cutoff. -/
def wrfQ : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2

/-- The medium-modulus cutoff. -/
def wrfQ1 : ℕ → ℕ := fun n => ⌊(n : ℝ)^(1 / 3 : ℝ)⌋₊

/-- The widened arc radius. -/
def wrfH : ℕ → ℕ := fun n => 256 * wrfQ1 n * wrfQ n

/-- The arc family with moduli up to X and half width rho/(q n). -/
def wrfArcs (X : ℕ) (ρ n : ℝ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ X ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ ρ / ((q : ℝ) * n)}

/-- The original major arcs. -/
def wrfArcsMain (n : ℕ) : Set ℝ := wrfArcs (wrfQ n) (wrfQ n : ℝ) n

/-- The widened arcs. -/
def wrfArcsWide (n : ℕ) : Set ℝ := wrfArcs (wrfQ1 n) (wrfH n : ℝ) n

/-- The widened arcs carrying the original moduli. -/
def wrfArcsLowWide (n : ℕ) : Set ℝ := wrfArcs (wrfQ n) (wrfH n : ℝ) n

/-- The part of the widened arcs carrying the original moduli. -/
def wrfLowPart (n : ℕ) : Set ℝ := wrfArcsLowWide n \ wrfArcsMain n

/-- The remainder of the widened arcs outside the original arcs. -/
def wrfRemainder (n : ℕ) : Set ℝ := (wrfArcsWide n \ wrfArcsMain n) \ wrfLowPart n

/-- The near-rational part: a short window around every reduced fraction of
denominator at most the medium cutoff. -/
def wrfInner (n : ℕ) : Set ℝ :=
  wrfArcs (wrfQ1 n) ((wrfQ n : ℝ) * (n : ℝ)^(1 / 6 : ℝ)) n

/-- The integrand of the registered statement. -/
def wrfF : ℕ → ℝ → ℂ := fun n t => (wrfS n wrfW t) ^ 2 * wrfE (-(n : ℝ) * t)

/-- The signed integral of the integrand over a set. -/
def wrfJ (n : ℕ) (A : Set ℝ) : ℝ :=
  (intervalIntegral (fun t => A.indicator (wrfF n) t) (0 : ℝ) 1 MeasureTheory.volume).re

/-- Measurability of the arc families. -/
private theorem wrf_measurable_arcs (X : ℕ) (ρ n : ℝ) :
    MeasurableSet (wrfArcs X ρ n) := by
  have h : wrfArcs X ρ n
      = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1 ≤ q ∧ q ≤ X ∧ a ≤ q ∧ Nat.Coprime a q} ∩
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ ρ / ((q : ℝ) * n)}) := by
    ext t
    simp only [wrfArcs, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [h]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

theorem wrfArcsMain_measurable (n : ℕ) : MeasurableSet (wrfArcsMain n) :=
  wrf_measurable_arcs (wrfQ n) (wrfQ n : ℝ) n

theorem wrfArcsWide_measurable (n : ℕ) : MeasurableSet (wrfArcsWide n) :=
  wrf_measurable_arcs (wrfQ1 n) (wrfH n : ℝ) n

theorem wrfArcsLowWide_measurable (n : ℕ) : MeasurableSet (wrfArcsLowWide n) :=
  wrf_measurable_arcs (wrfQ n) (wrfH n : ℝ) n

theorem wrfInner_measurable (n : ℕ) : MeasurableSet (wrfInner n) :=
  wrf_measurable_arcs (wrfQ1 n) ((wrfQ n : ℝ) * (n : ℝ)^(1 / 6 : ℝ)) n

theorem wrfLowPart_measurable (n : ℕ) : MeasurableSet (wrfLowPart n) :=
  (wrfArcsLowWide_measurable n).diff (wrfArcsMain_measurable n)

theorem wrfRemainder_measurable (n : ℕ) : MeasurableSet (wrfRemainder n) :=
  ((wrfArcsWide_measurable n).diff (wrfArcsMain_measurable n)).diff (wrfLowPart_measurable n)

/-- The remainder never meets the low-modulus widened arcs. -/
theorem wrfRemainder_disjoint_lowWide (n : ℕ) : Disjoint (wrfRemainder n) (wrfArcsLowWide n) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  exact ht.2 ht'.2

/-- The remainder meets the original arcs in nothing. -/
theorem wrfRemainder_disjoint_main (n : ℕ) : Disjoint (wrfRemainder n) (wrfArcsMain n) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  exact ht.1 ht'

end
end Conjectures.Goldbach
