import HodgeLean.Adapters.CycleClassPullbackSpan
import HodgeLean.Adapters.IntersectionProductMoving

/-! # Linear properties of inverse-image cycles for Bloch translation

The scheme-theoretic inverse-image cycle used in the translation family is linear in the
input cycle.  This file records the scalar part of that fact over rational coefficients.

Source: Fulton, *Intersection Theory*, second edition, section 1.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Adapters

/-- Scheme-theoretic inverse-image cycles commute with addition. -/
theorem IntersectionProductTrans_flatPullback_add {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (c c' : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (c + c') =
      ccm3_flatPullback f.left c + ccm3_flatPullback f.left c' :=
  ccm3_flatPullback_add f c c'

/-- Scheme-theoretic inverse-image cycles commute with rational scaling. -/
theorem IntersectionProductTrans_flatPullback_smul {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (r : ℚ) (c : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (a3m_smul r c) =
      a3m_smul r (ccm3_flatPullback f.left c) :=
  ccm6_flatPullback_smul f r c

/-- Scheme-theoretic inverse-image cycles carry the zero cycle to zero. -/
theorem IntersectionProductTrans_flatPullback_zero {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z) :
    ccm3_flatPullback f.left (0 : AlgebraicCycle Z.left ℚ) = 0 := by
  have hzero : a3m_smul 0 (0 : AlgebraicCycle Z.left ℚ) = 0 := by ext x; simp
  rw [← hzero, IntersectionProductTrans_flatPullback_smul]
  ext x
  simp

/-- Scheme-theoretic inverse-image cycles commute with negation. -/
theorem IntersectionProductTrans_flatPullback_neg {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (c : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (-c) = -ccm3_flatPullback f.left c := by
  have hneg : a3m_smul (-1) c = -c := by ext x; simp
  rw [← hneg, IntersectionProductTrans_flatPullback_smul]
  ext x
  simp

/-- Scheme-theoretic inverse-image cycles commute with subtraction. -/
theorem IntersectionProductTrans_flatPullback_sub {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (c c' : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (c - c') =
      ccm3_flatPullback f.left c - ccm3_flatPullback f.left c' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, IntersectionProductTrans_flatPullback_add,
    IntersectionProductTrans_flatPullback_neg]

/-- Scheme-theoretic inverse image as an additive map on rational cycles. -/
def IntersectionProductTrans_flatPullbackHom {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z) :
    AlgebraicCycle Z.left ℚ →+ AlgebraicCycle X.left ℚ where
  toFun := ccm3_flatPullback f.left
  map_zero' := IntersectionProductTrans_flatPullback_zero f
  map_add' := IntersectionProductTrans_flatPullback_add f

@[simp] theorem IntersectionProductTrans_flatPullbackHom_apply {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (c : AlgebraicCycle Z.left ℚ) :
    IntersectionProductTrans_flatPullbackHom f c = ccm3_flatPullback f.left c := rfl

/-- The additive inverse-image map commutes with the rational scaling used for cycles. -/
theorem IntersectionProductTrans_flatPullbackHom_smul {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (r : ℚ) (c : AlgebraicCycle Z.left ℚ) :
    IntersectionProductTrans_flatPullbackHom f (a3m_smul r c) =
      a3m_smul r (IntersectionProductTrans_flatPullbackHom f c) :=
  IntersectionProductTrans_flatPullback_smul f r c

/-- Inverse-image cycles commute with the finite sums used to assemble translation chains. -/
theorem IntersectionProductTrans_flatPullback_sum {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    {ι : Type*} (s : Finset ι) (c : ι → AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (∑ i ∈ s, c i) =
      ∑ i ∈ s, ccm3_flatPullback f.left (c i) := by
  simpa only [IntersectionProductTrans_flatPullbackHom_apply] using
    map_sum (IntersectionProductTrans_flatPullbackHom f) c s

end HodgeLean.Adapters
