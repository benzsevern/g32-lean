import HodgeLean.Foundations.Curves.SymmetricCharts.Proofs

/-! # Global symmetric-power chart interfaces

These interfaces retain M3 ordered powers and the existing invariant-spectrum gluing.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.Picard.Families
namespace HodgeLean.Foundations.Curves.SymmetricCharts
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom]
  [IsProjective C.hom] (n : ℕ)

/-- Affine curve opens give actual invariant affine product charts, also in degree zero.
Source: Milne, Jacobian Varieties, §3; Mumford, Abelian Varieties, §II. -/
theorem product_affine_index (U : C.left.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set C.left).Nonempty) :
    ∃ W : Index C n, W.val = productOpen C n U :=
  product_affine_index_aux C n U hU hne

/-- Identify the actual affine invariant spectrum with its saturated global chart, retaining the projection.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1. -/
theorem chart_comparison (W : Index C n) :
    ∃ (V : (symmetricPower C n).left.Opens) (e : affineChart C n W ≅ V.toScheme),
      e.hom ≫ V.ι = chartInclusion C n W ∧
      affineProjection C n W ≫ e.hom ≫ V.ι = W.val.ι ≫ (projection C n).left ∧
      (projection C n).left ⁻¹ᵁ V = W.val :=
  chart_comparison_aux C n W

/-- Affine inclusions and both intersection maps descend with their actual projection squares.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1. -/
theorem overlap_descent (U V : Index C n) :
    (∀ h : U ≤ V, chartMap C n U V h ≫ chartInclusion C n V = chartInclusion C n U ∧
    affineProjection C n U ≫ chartMap C n U V h =
      (g3_power C n).left.homOfLE h ≫ affineProjection C n V) ∧
    chartMap C n (intersection C n U V) U (by change U.val ⊓ V.val ≤ U.val; exact inf_le_left) ≫ chartInclusion C n U =
      chartMap C n (intersection C n U V) V (by change U.val ⊓ V.val ≤ V.val; exact inf_le_right) ≫ chartInclusion C n V ∧
    IsPullback
      (chartMap C n (intersection C n U V) U (by change U.val ⊓ V.val ≤ U.val; exact inf_le_left))
      (chartMap C n (intersection C n U V) V (by change U.val ⊓ V.val ≤ V.val; exact inf_le_right))
      (chartInclusion C n U) (chartInclusion C n V) :=
  overlap_descent_aux C n U V

/-- The retained ordered power has its finite integral projective categorical permutation quotient.
Source: Milne, Jacobian Varieties, §3; Mumford, Abelian Varieties, §II. -/
theorem projective_quotient :
    IsIntegral (symmetricPower C n).left ∧ IsProjective (symmetricPower C n).hom ∧
    IsFinite (projection C n).left ∧ Function.Surjective (projection C n).left ∧
    (∀ σ : Equiv.Perm (Fin n), orderedPermutation C n σ ≫ orderedProjection C n =
      orderedProjection C n) ∧
    (∀ (T : Over (Spec ↧ℂ)) (f : OrderedPower C n ⟶ T),
      (∀ σ : Equiv.Perm (Fin n), orderedPermutation C n σ ≫ f = f) →
      ∃! d : symmetricPower C n ⟶ T, orderedProjection C n ≫ d = f) :=
  projective_quotient_aux C n

/-- The actual quotient has Krull dimension n, including n = 0.
Source: Milne, Jacobian Varieties, §3; Stacks Project, Lemma 29.45.9 (Tag 0ECG), dimension under integral surjective morphisms. -/
theorem krull_dimension [SmoothOfRelativeDimension 1 C.hom] :
    topologicalKrullDim (symmetricPower C n).left = n :=
  krull_dimension_aux C n

end HodgeLean.Foundations.Curves.SymmetricCharts
