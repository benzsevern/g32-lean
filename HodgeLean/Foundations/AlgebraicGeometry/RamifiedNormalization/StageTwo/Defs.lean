import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.Defs
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Original-field overlap rings and invariant coefficients

All subrings retain their inclusion in the supplied field.
HC no distance; AV milestone no distance. -/

noncomputable section
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageTwo

/-- The image ring with the inverse of one specified element adjoined.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3.
HC no distance; AV milestone no distance. -/
def awayImage {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (s : A) : Subring K :=
  Subring.closure (Set.range f ∪ {(f s)⁻¹})

/-- The actual quotient-chart image with its inverse ratio adjoined.
Source: Hartshorne, Algebraic Geometry, II.7, the intersection of blowup charts.
HC no distance; AV milestone no distance. -/
def overlap {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (u v : R) (hv : f v ≠ 0) : Subring K :=
  awayImage (chartMap f u v hv) (RegularPairChart.ratio u v)

/-- The fixed coefficient ring of the specified field action.
Source: Esnault–Viehweg, Lectures on Vanishing Theorems, §3.
HC no distance; AV milestone no distance. -/
def fixedCoefficients {K : Type*} [Field K] (σ : K ≃+* K) : Subring K where
  carrier := {x | σ x = x}
  zero_mem' := σ.map_zero
  one_mem' := σ.map_one
  add_mem' hx hy := by
    change σ _ = _ at hx hy ⊢
    rw [map_add, hx, hy]
  mul_mem' hx hy := by
    change σ _ = _ at hx hy ⊢
    rw [map_mul, hx, hy]
  neg_mem' hx := by
    change σ _ = _ at hx ⊢
    rw [map_neg, hx]

example : (3 : ℚ) ∈ awayImage (RingHom.id ℚ) (2 : ℚ) :=
  Subring.subset_closure (Or.inl ⟨3, rfl⟩)

example : (3 : ℚ) ∈ fixedCoefficients (RingEquiv.refl ℚ) := rfl

example : (3 : ℚ) ∈ overlap (RingHom.id ℚ) 6 2 (by norm_num) := by
  apply Subring.subset_closure
  left
  exact ⟨RegularPairChart.ratio 6 2, by norm_num [chartMap, RegularPairChart.ratio]⟩

/-- Reciprocal sphere coordinate, interchanging zero and infinity.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.4–2.5.
HC no distance; AV milestone no distance. -/
def reciprocal : OnePoint ℂ → OnePoint ℂ
  | none => ((0 : ℂ) : OnePoint ℂ)
  | some z => if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ)

example : reciprocal ((2 : ℂ) : OnePoint ℂ) = ((1 / 2 : ℂ) : OnePoint ℂ) := by
  norm_num [reciprocal]

/-- Coefficients as integral elements in the original covering field.
Source: Atiyah–Macdonald, Chapter 5, integral elements.
HC no distance; AV milestone no distance. -/
def integralCoeff {A K : Type*} [CommRing A] [Field K] (f : A →+* K) :
    A →+* normalizedChart f := by
  letI := f.toAlgebra
  exact (algebraMap A (integralClosure A K))

example : (integralCoeff (Int.castRingHom ℚ) 3 : ℚ) = 3 := rfl

end AlgebraicGeometry.RamifiedNormalization.StageTwo
