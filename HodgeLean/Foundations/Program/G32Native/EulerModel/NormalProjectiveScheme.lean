import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalGlobalPointClass
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # The normal model and the actual projective scheme points -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified leading coordinate and tail as actual ordered homogeneous coordinates. -/
def normalHomogeneousCoordinates (k : ℕ) :
    (ℂ × (Fin k → ℂ)) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun v := Fin.cons v.1 v.2
  invFun v := (v 0, fun j => v j.succ)
  left_inv v := rfl
  right_inv v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  map_add' v w := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  map_smul' a v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

#print axioms normalHomogeneousCoordinates
/-- Linear projective coordinate transport is continuous for the actual quotient topologies. -/
theorem continuous_normalProjectiveCoordinates (k : ℕ) :
    Continuous (s2e_projectiveLinearEquiv (normalHomogeneousCoordinates k)) := by
  apply continuous_coinduced_dom.mpr
  exact isQuotientMap_quotient_mk'.continuous.comp
    (((normalHomogeneousCoordinates k).toLinearMap.continuous_of_finiteDimensional.comp
      continuous_subtype_val).subtype_mk (fun v =>
        (normalHomogeneousCoordinates k).map_ne_zero_iff.mpr v.2))

#print axioms continuous_normalProjectiveCoordinates
/-- The inverse ordered homogeneous coordinate transport is continuous in the quotient topology. -/
theorem continuous_normalProjectiveCoordinates_symm (k : ℕ) :
    Continuous (s2e_projectiveLinearEquiv (normalHomogeneousCoordinates k)).symm := by
  apply continuous_coinduced_dom.mpr
  exact isQuotientMap_quotient_mk'.continuous.comp
    (((normalHomogeneousCoordinates k).symm.toLinearMap.continuous_of_finiteDimensional.comp
      continuous_subtype_val).subtype_mk (fun v =>
        (normalHomogeneousCoordinates k).symm.map_ne_zero_iff.mpr v.2))

#print axioms continuous_normalProjectiveCoordinates_symm
/-- The specified normal projective base and the ordered homogeneous-coordinate projective space. -/
def normalProjectiveCoordinatesHomeomorph (k : ℕ) :
    Projectivization ℂ (ℂ × (Fin k → ℂ)) ≃ₜ Projectivization ℂ (CoordinateSpace k) where
  toEquiv := s2e_projectiveLinearEquiv (normalHomogeneousCoordinates k)
  continuous_toFun := continuous_normalProjectiveCoordinates k
  continuous_invFun := continuous_normalProjectiveCoordinates_symm k

/-- The normal model base identified with the complex points of the actual projective scheme. -/
def normalProjectiveSchemeHomeomorph (k : ℕ) :
    Projectivization ℂ (ℂ × (Fin k → ℂ)) ≃ₜ
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :=
  (normalProjectiveCoordinatesHomeomorph k).trans (s2e_projectivePointHomeomorph k)

#print axioms normalProjectiveCoordinatesHomeomorph
#print axioms normalProjectiveSchemeHomeomorph
/-- The scheme-point comparison retains the actual ordered homogeneous vector. -/
theorem normalProjectiveSchemeHomeomorph_mk (k : ℕ)
    (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    normalProjectiveSchemeHomeomorph k (Projectivization.mk ℂ v hv) =
      vectorToComplexPoint (normalHomogeneousCoordinates k v)
        ((normalHomogeneousCoordinates k).map_ne_zero_iff.mpr hv) := by
  rfl

#print axioms normalProjectiveSchemeHomeomorph_mk
end HodgeLean.Foundations.Program.G32Native.EulerModel
