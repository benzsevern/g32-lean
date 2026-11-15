import HodgeLean.Foundations.Program.SchoenCycleSliceDivisors
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Basic

/-! # Effective divisors as unordered tuples
The positive multiplicities of an integer divisor give an actual multiset.
For effective divisors this encoding retains every coefficient.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

/-- The multiset with the positive multiplicities of the integer divisor.
Source: Forster, Lectures on Riemann Surfaces, GTM 81, §13; Schoen (1988), Lemma 2.3. -/
def s2e_divisorMultiset {C : Type*} (D : C →₀ ℤ) : Multiset C :=
  (D.mapRange Int.toNat rfl).toMultiset

example {C : Type*} [DecidableEq C] (D : C →₀ ℤ) (p : C) :
    (s2e_divisorMultiset D).count p = (D p).toNat := by
  classical
  simp only [s2e_divisorMultiset, Finsupp.count_toMultiset, Finsupp.mapRange_apply]

/-- Every coefficient of an effective divisor is recovered from its
multiset encoding. -/
theorem s2e_divisorMultiset_recover
    {C : Type*} [DecidableEq C] (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) :
    (s2e_divisorMultiset D).toFinsupp.mapRange (fun n : ℕ => (n : ℤ)) rfl = D := by
  ext p
  simp only [s2e_divisorMultiset, Finsupp.toMultiset_toFinsupp, Finsupp.mapRange_apply]
  exact Int.toNat_of_nonneg (hD p)

/-- Cardinality of the actual multiset equals degree of the effective divisor. -/
theorem s2e_divisorMultiset_card
    {C : Type} (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) :
    ((s2e_divisorMultiset D).card : ℤ) = b4c_deg D := by
  classical
  rw [s2e_divisorMultiset, Finsupp.card_toMultiset,
    Finsupp.sum_mapRange_index (fun _ => rfl)]
  simp only [b4c_deg, Finsupp.sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact Int.toNat_of_nonneg (hD p)

/-- An effective divisor of degree n gives an actual unordered n-tuple.
Source: Forster, Lectures on Riemann Surfaces, GTM 81, §13; Schoen (1988), Lemma 2.3. -/
def s2e_divisorSym {C : Type} {n : ℕ} (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p)
    (hd : b4c_deg D = (n : ℤ)) : Sym C n :=
  ⟨s2e_divisorMultiset D, by
    have h := (s2e_divisorMultiset_card D hD).trans hd
    omega⟩

example {C : Type} {n : ℕ} (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p)
    (hd : b4c_deg D = (n : ℤ)) : (s2e_divisorSym D hD hd : Multiset C) = s2e_divisorMultiset D := rfl

/-- The unordered tuple retains the original integer divisor exactly. -/
theorem s2e_divisorSym_recover
    {C : Type} [DecidableEq C] {n : ℕ}
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = (n : ℤ)) :
    (s2e_divisorSym D hD hd : Multiset C).toFinsupp.mapRange (fun m : ℕ => (m : ℤ)) rfl = D :=
  s2e_divisorMultiset_recover D hD

/-- A point occurs in the unordered effective divisor exactly when its coefficient is positive. -/
theorem s2e_divisorSym_mem_iff
    {C : Type} {n : ℕ} (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p)
    (hd : b4c_deg D = (n : ℤ)) (p : C) :
    p ∈ s2e_divisorSym D hD hd ↔ 0 < D p := by
  classical
  change p ∈ s2e_divisorMultiset D ↔ 0 < D p
  rw [← Multiset.count_pos]
  simp only [s2e_divisorMultiset, Finsupp.count_toMultiset, Finsupp.mapRange_apply,
    ← Int.pos_iff_toNat_pos]

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The actual unordered zeros assigned to a projective differential parameter.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
def s2e_projectiveDifferentialSymmetricPower
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) : Sym C (2 * k) :=
  s2e_divisorSym (n := 2 * k) (s2e_projectiveDifferentialDivisor hE w y z)
    (s2e_projectiveDifferentialDivisor_effective hE w x hres y hy horder hout z)
    (s2e_projectiveDifferentialDivisor_degree hE w x hres y hgenus z)

example [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) :
    (s2e_projectiveDifferentialSymmetricPower hE w x hres y hy horder hout hgenus z : Multiset C) =
      s2e_divisorMultiset (s2e_projectiveDifferentialDivisor hE w y z) := rfl

/-- The symmetric-power function retains the original projective divisor,
including every integer coefficient. -/
theorem s2e_projectiveDifferentialSymmetricPower_recover
    [DecidableEq C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) :
    (s2e_projectiveDifferentialSymmetricPower hE w x hres y hy horder hout hgenus z :
      Multiset C).toFinsupp.mapRange (fun m : ℕ => (m : ℤ)) rfl =
        s2e_projectiveDifferentialDivisor hE w y z :=
  s2e_divisorSym_recover (s2e_projectiveDifferentialDivisor hE w y z)
    (s2e_projectiveDifferentialDivisor_effective hE w x hres y hy horder hout z)
    (s2e_projectiveDifferentialDivisor_degree hE w x hres y hgenus z)

end HodgeLean.Foundations.Program
