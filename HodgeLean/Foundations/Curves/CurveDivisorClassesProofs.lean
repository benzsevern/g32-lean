import HodgeLean.Foundations.Curves.CubicClassMap

/-! # Proofs for the frozen curve divisor-class spec

The degree statements follow from the product formula `degree_principalDivisor`. Closed points of
a smooth complex curve have coheight one (`coheight_eq_one_of_isClosed`), and points of Mathlib's
Weierstrass group are `ℂ`-points of `E`, hence closed. For the Abel map, `CubicClassMap` builds a
homomorphism from `Cl(E)` to the class group of the Dedekind domain `W.CoordinateRing` that sends
the Abel class of a point to `Point.toClass` and is injective on degree-zero classes. The bridge,
additivity and nonvanishing statements then come from Mathlib's `Point.toClass` being an injective
group homomorphism.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

open CubicClassMap

/-- Principal divisors on a smooth projective curve have degree zero. -/
theorem principalDivisors_le_ker_degree_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [IsLocallyNoetherian X.left] [CompactSpace X.left] :
    principalDivisors X.left ≤ (divisorDegree X).ker := by
  rw [principalDivisors, AddSubgroup.closure_le]
  rintro _ ⟨f, hf, rfl⟩
  exact degree_principalDivisor f hf

/-- A divisor has degree-zero class exactly when it has degree zero. -/
theorem mk_mem_divisorClassZero_iff_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [IsLocallyNoetherian X.left] [CompactSpace X.left] (D : Divisor X.left) :
    DivisorClass.mk X.left D ∈ DivisorClassZero X ↔ divisorDegree X D = 0 := by
  constructor
  · rintro ⟨D', hD', h⟩
    have hmem : -D' + D ∈ principalDivisors X.left :=
      (QuotientAddGroup.eq (s := principalDivisors X.left)).mp h
    have h0 := principalDivisors_le_ker_degree_aux X hmem
    rw [AddMonoidHom.mem_ker, map_add, map_neg, AddMonoidHom.mem_ker.mp hD', neg_zero,
      zero_add] at h0
    exact h0
  · intro h
    exact ⟨D, h, rfl⟩

/-- At a closed point of a curve, the prime divisor is the unit point cycle. -/
theorem pointDivisor_of_isClosed_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (P : X.left) (hP : IsClosed ({P} : Set X.left)) :
    (pointDivisor X.left P : AlgebraicCycle X.left ℤ) = pointCycle X.left P 1 :=
  pointDivisor_eq_pointCycle X P hP

/-- The image of a point of Mathlib's Weierstrass group is a closed point of `E`. -/
theorem cubicPointOf_isClosed_aux (P : W.toAffine.Point) :
    IsClosed ({cubicPointOf P} : Set E.left) :=
  cubicPointOf_isClosed' P

/-- The origin of the affine chart is the second named point of `E`. -/
theorem cubicPointOf_origin_aux :
    cubicPointOf (.some 0 0 W_nonsingular_origin) = finitePoint.base default :=
  cubicPointOf_origin'

/-- The Abel map takes closed points to degree-zero classes. -/
theorem cubicAbelMap_mem_divisorClassZero_aux (P : E.left) (hP : IsClosed ({P} : Set E.left)) :
    cubicAbelMap P ∈ DivisorClassZero E := by
  refine ⟨_, ?_, rfl⟩
  change _ ∈ (divisorDegree E).ker
  rw [AddMonoidHom.mem_ker, map_sub, divisorDegree_pointDivisor P hP,
    divisorDegree_pointDivisor _ cubicInfinity_isClosed, sub_self]

/-- The class map sends the Abel class of a Mathlib point to `Point.toClass`. -/
theorem classMapQ_cubicAbelMap (P : W.toAffine.Point) :
    classMapQ (cubicAbelMap (cubicPointOf P)) = WeierstrassCurve.Affine.Point.toClass P :=
  classMap_abel P

/-- On points of Mathlib's group, the Abel map identifies points exactly when `Point.toClass`
does. -/
theorem cubicAbelMap_eq_iff_toClass_eq_aux (P Q : W.toAffine.Point) :
    cubicAbelMap (cubicPointOf P) = cubicAbelMap (cubicPointOf Q) ↔
      WeierstrassCurve.Affine.Point.toClass P = WeierstrassCurve.Affine.Point.toClass Q := by
  constructor
  · intro h
    rw [← classMapQ_cubicAbelMap, ← classMapQ_cubicAbelMap, h]
  · intro h
    rw [WeierstrassCurve.Affine.Point.toClass_injective h]

/-- The Abel map is additive for Mathlib's group law. -/
theorem cubicAbelMap_add_aux (P Q : W.toAffine.Point) :
    cubicAbelMap (cubicPointOf (P + Q)) =
      cubicAbelMap (cubicPointOf P) + cubicAbelMap (cubicPointOf Q) := by
  rw [← sub_eq_zero, cubicAbelMap, cubicAbelMap, cubicAbelMap, ← map_add, ← map_sub]
  apply mk_eq_zero_of_classMap_eq_zero
  · rw [map_sub, map_add, classMap_abel, classMap_abel, classMap_abel, map_add, sub_self]
  · rw [map_sub, map_add, map_sub, map_sub, map_sub,
      divisorDegree_pointDivisor _ (cubicPointOf_isClosed' _),
      divisorDegree_pointDivisor _ (cubicPointOf_isClosed' _),
      divisorDegree_pointDivisor _ (cubicPointOf_isClosed' _),
      divisorDegree_pointDivisor _ cubicInfinity_isClosed]
    norm_num

/-- The class `[(0,0)] - [∞]` is nonzero. -/
theorem cubicAbelMap_finitePoint_ne_zero_aux :
    cubicAbelMap (finitePoint.base default) ≠ 0 := by
  intro h
  have h0 : cubicAbelMap (cubicPointOf 0) = 0 := by
    change DivisorClass.mk E.left (pointDivisor E.left cubicInfinity -
      pointDivisor E.left cubicInfinity) = 0
    rw [sub_self, map_zero]
  rw [← cubicPointOf_origin', ← h0, cubicAbelMap_eq_iff_toClass_eq_aux] at h
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ (WeierstrassCurve.Affine.Point.toClass_injective h)

/-- The class `[(0,0)] - [∞]` has order dividing two. -/
theorem two_smul_cubicAbelMap_finitePoint_aux :
    2 • cubicAbelMap (finitePoint.base default) = 0 := by
  have h : 2 • (pointDivisor E.left (finitePoint.base default) -
      pointDivisor E.left cubicInfinity) = principalDivisor E.left cubicX := by
    apply Subtype.ext
    rw [cubicX_principalDivisor]
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_sub,
      pointDivisor_eq_pointCycle E _ finitePoint_isClosed,
      pointDivisor_eq_pointCycle E _ cubicInfinity_isClosed, smul_sub]
    rfl
  rw [cubicAbelMap, ← map_nsmul, h]
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (AddSubgroup.subset_closure ⟨cubicX, CubicDivisor.cubicX_ne_zero, rfl⟩)

end HodgeLean.Foundations.Curves
