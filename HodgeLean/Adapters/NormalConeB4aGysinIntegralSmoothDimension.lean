import HodgeLean.Adapters.NormalConeB4aGysinIntegralAffineDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The dimension of an integral finite type complex scheme is bounded by the
dimension of any nonempty smooth affine region of it. -/
theorem a3b4a_gysin_integral_dimension_bound_of_smooth_affine
    (X : Over (Spec (CommRingCat.of ℂ))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (d : ℕ) [SmoothOfRelativeDimension d (U.ι ≫ X.hom)] :
    topologicalKrullDim X.left ≤ (d : ℕ) := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨z, hzU, hz⟩ := nonempty_inter_closedPoints
    (Z := (U : Set X.left)) (by simpa using ‹Nonempty U›) U.isOpen.isLocallyClosed
  let zu : U.toScheme := ⟨z, hzU⟩
  have hzu : IsClosed ({zu} : Set U.toScheme) := by
    have he : U.ι ⁻¹' ({z} : Set X.left) = {zu} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hz.preimage U.ι.continuous
  have hcoU := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    (f := U.ι ≫ X.hom) (d := d) zu hzu
  have hco : Order.coheight z = d :=
    (coheight_eq_of_isOpenImmersion (x := zu) U.ι).trans hcoU
  apply a3b4a_gysin_integral_dimension_bound_of_affine X U hU d
  have hring : ringKrullDim Γ(X.left, U) = (d : ℕ) := by
    rw [a3b4a_gysin_integral_affine_closed_point_dimension X U hU z hzU hz, hco]
    rfl
  exact hring.le

/-- Any nonempty smooth open region bounds the dimension of an integral finite
type complex scheme; the region need not be affine. -/
theorem a3b4a_gysin_integral_dimension_bound_of_smooth_open
    (X : Over (Spec (CommRingCat.of ℂ))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) [Nonempty U]
    (d : ℕ) [SmoothOfRelativeDimension d (U.ι ≫ X.hom)] :
    topologicalKrullDim X.left ≤ (d : ℕ) := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨z, hzU, hz⟩ := nonempty_inter_closedPoints
    (Z := (U : Set X.left)) (by simpa using ‹Nonempty U›) U.isOpen.isLocallyClosed
  let zu : U.toScheme := ⟨z, hzU⟩
  have hzu : IsClosed ({zu} : Set U.toScheme) := by
    have he : U.ι ⁻¹' ({z} : Set X.left) = {zu} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hz.preimage U.ι.continuous
  have hcoU := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    (f := U.ι ≫ X.hom) (d := d) zu hzu
  have hco : Order.coheight z = d :=
    (coheight_eq_of_isOpenImmersion (x := zu) U.ι).trans hcoU
  obtain ⟨V, hV, hzV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (U := ⊤) (x := z) (by simp)
  letI : Nonempty V := ⟨⟨z, hzV⟩⟩
  apply a3b4a_gysin_integral_dimension_bound_of_affine X V hV d
  have hring : ringKrullDim Γ(X.left, V) = (d : ℕ) := by
    rw [a3b4a_gysin_integral_affine_closed_point_dimension X V hV z hzV hz, hco]
    rfl
  exact hring.le

end HodgeLean.Adapters
