import HodgeLean.Foundations.Curves.CurveDivisorsDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Degrees of divisors on complex curves

On a smooth curve over `ℂ`, every coheight-one point is a closed point with residue field `ℂ`.
Hence the degree of a divisor is the plain sum of its coefficients.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

variable {X : Over (Spec ↧ℂ)}

/-- A coheight-one point of a smooth complex curve is closed.
Source: Hartshorne, *Algebraic Geometry*, II.6; HodgeConjecture
`SmoothOfRelativeDimension.height_le_sub_of_coheight_eq`. -/
theorem isClosed_of_coheight_eq_one [SmoothOfRelativeDimension 1 X.hom] {x : X.left}
    (hx : Order.coheight x = 1) : IsClosed ({x} : Set X.left) := by
  have hh : Order.height x ≤ (1 : ℕ) - (1 : ℕ) :=
    SmoothOfRelativeDimension.height_le_sub_of_coheight_eq (f := X.hom) x (p := 1)
      (by exact_mod_cast hx)
  have hmin : IsMin x := Order.height_eq_zero.mp (by simpa using hh)
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hyx : y ⤳ x := Scheme.le_iff_specializes.mp (hmin (Scheme.le_iff_specializes.mpr hxy))
  exact (hxy.antisymm hyx).eq.symm

/-- The residue degree over `ℂ` of a closed point of a complex scheme of finite type is one.
Source: Hilbert's Nullstellensatz; Mathlib `AlgebraicGeometry.residueFieldIsoBase`. -/
theorem residueDegree_eq_one [LocallyOfFiniteType X.hom] {x : X.left}
    (hx : IsClosed ({x} : Set X.left)) : X.hom.residueDegree x = 1 := by
  let ρ := residueFieldIsoBase X.hom x hx
  have hρ : Spec.map ρ.inv = X.left.fromSpecResidueField x ≫ X.hom :=
    SpecMap_residueFieldIsoBase_inv X.hom x hx
  let y := X.hom x
  have := y.isPrime
  let φ : CommRingCat.of ℂ ⟶ (Spec ↧ℂ).residueField y :=
    (Ideal.algEquivResidueFieldOfField y.asIdeal).toRingEquiv.toCommRingCatIso.hom ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of ℂ) y).inv
  have hφ : IsIso φ := by dsimp only [φ]; infer_instance
  have hfrom : (Spec ↧ℂ).fromSpecResidueField y = Spec.map φ := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    congr 1
  have hcomp : φ ≫ X.hom.residueFieldMap x = ρ.inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hfrom, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, hρ]
  have hiso : IsIso (X.hom.residueFieldMap x) := by
    have : X.hom.residueFieldMap x = inv φ ≫ ρ.inv := by rw [← hcomp]; simp
    rw [this]
    infer_instance
  have hbij : Function.Bijective (X.hom.residueFieldMap x).hom :=
    ConcreteCategory.bijective_of_isIso _
  let := (X.hom.residueFieldMap x).hom.toAlgebra
  change Module.finrank _ _ = 1
  let e := AlgEquiv.ofBijective (Algebra.ofId ((Spec ↧ℂ).residueField y) (X.left.residueField x))
    hbij
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- On a smooth complex curve, the degree of the principal divisor of `f` is the plain sum of the
orders of `f`.
Source: Hartshorne, *Algebraic Geometry*, II.6 and IV.1. -/
theorem divisorDegree_principalDivisor_eq_finsum [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsLocallyNoetherian X.left] [CompactSpace X.left]
    (f : X.left.functionField) (hfin : (Function.support (ordAt X.left f)).Finite) :
    divisorDegree X (principalDivisor X.left f) = ∑ᶠ P : X.left, X.left.ord f P := by
  have happ : ∀ P, (principalDivisor X.left f).1 P = X.left.ord f P := by
    intro P
    rw [principalDivisor, dite_eq_left hfin]
    rfl
  rw [divisorDegree, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, AlgebraicCycle.degree_apply]
  refine finsum_congr fun P ↦ ?_
  rw [happ]
  by_cases h0 : X.left.ord f P = 0
  · rw [h0, smul_zero]
  · have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
    have hP : Order.coheight P = 1 := by
      by_contra hne
      exact h0 (Scheme.ord_eq_zero_of_coheight_neq_one hne f)
    rw [residueDegree_eq_one (isClosed_of_coheight_eq_one hP), one_smul]

end HodgeLean.Foundations.Curves
