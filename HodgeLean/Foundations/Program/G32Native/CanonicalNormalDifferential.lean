import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientFibre
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Restricting a specified differential to the actual normal complement

The map D is retained in the resulting equivalence. Its kernel and evaluation
identities are explicit inputs; this module does not construct the Abel differential.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A differential whose kernel lies in the immersion tangent space is injective
on the normal complement selected by the immersion derivative projection. -/
theorem g32n_normal_differential_injective
    (X Q : Over (Spec ↧ℂ)) (ι : Q ⟶ X) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) X.hom] [IsClosedImmersion ι.left]
    (x : ComplexPoint Q)
    (D : (Fin (k + k) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (k + 1) → ℂ))
    (hker : LinearMap.ker D ≤ LinearMap.range
      (fderiv ℂ (inclusionInComplexCharts X Q ι k (k + k) x)
        (localChart Q k x x)).toLinearMap) :
    Function.Injective (D.comp
      (closedImmersionDerivativeProjection X Q ι k (k + k) x).ker.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hvD : D v.val = 0 := hv
  obtain ⟨u, hu⟩ := hker hvD
  change (fderiv ℂ (inclusionInComplexCharts X Q ι k (k + k) x)
    (localChart Q k x x)) u = v.val at hu
  have hleft := closedImmersionDerivativeProjection_leftInverse X Q ι k (k + k) x
  have hPu := DFunLike.congr_fun hleft u
  change (closedImmersionDerivativeProjection X Q ι k (k + k) x)
    ((fderiv ℂ (inclusionInComplexCharts X Q ι k (k + k) x)
      (localChart Q k x x)) u) = u at hPu
  rw [hu] at hPu
  have hvP : (closedImmersionDerivativeProjection X Q ι k (k + k) x) v.val = 0 := v.property
  rw [hvP] at hPu
  have hu0 : u = 0 := hPu.symm
  have hv0 : v.val = 0 := by rw [← hu, hu0, map_zero]
  exact Subtype.ext hv0

/-- The specified differential, restricted to the actual normal complement and
with codomain the retained homogeneous coefficient kernel. -/
def g32n_normalCoefficientMap
    (X Q : Over (Spec ↧ℂ)) (ι : Q ⟶ X) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) X.hom] [IsClosedImmersion ι.left]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (x : ComplexPoint Q)
    (D : (Fin (k + k) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (k + 1) → ℂ))
    (heval : ∀ v, D v (g32n_homogeneousLine k eQ x).rep = 0) :
    (closedImmersionDerivativeProjection X Q ι k (k + k) x).ker →ₗ[ℂ]
      (g32n_homogeneousLine k eQ x).submodule.dualAnnihilator :=
  (D.comp (closedImmersionDerivativeProjection X Q ι k (k + k) x).ker.subtype).codRestrict
    _ (fun v => by
      rw [← g32n_selected_coefficient_kernel]
      exact heval v.val)

/-- Kernel exactness and the homogeneous evaluation equation turn the retained
normal differential into a linear equivalence, without selecting bases. -/
def g32n_normalCoefficientEquiv
    (X Q : Over (Spec ↧ℂ)) (ι : Q ⟶ X) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) X.hom] [IsClosedImmersion ι.left]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (x : ComplexPoint Q)
    (D : (Fin (k + k) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (k + 1) → ℂ))
    (hker : LinearMap.ker D ≤ LinearMap.range
      (fderiv ℂ (inclusionInComplexCharts X Q ι k (k + k) x)
        (localChart Q k x x)).toLinearMap)
    (heval : ∀ v, D v (g32n_homogeneousLine k eQ x).rep = 0) :
    (closedImmersionDerivativeProjection X Q ι k (k + k) x).ker ≃ₗ[ℂ]
      (g32n_homogeneousLine k eQ x).submodule.dualAnnihilator :=
  LinearEquiv.ofInjectiveOfFinrankEq
    (g32n_normalCoefficientMap X Q ι k eQ x D heval)
    (fun _ _ h => g32n_normal_differential_injective X Q ι k x D hker
      (congrArg Subtype.val h))
    ((g32n_normal_rank X Q ι k x).trans (g32n_selected_coefficient_rank k eQ x).symm)

/-- The equivalence sends each actual normal vector to the value of the specified D. -/
theorem g32n_normalCoefficientEquiv_apply
    (X Q : Over (Spec ↧ℂ)) (ι : Q ⟶ X) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) X.hom] [IsClosedImmersion ι.left]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (x : ComplexPoint Q)
    (D : (Fin (k + k) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (k + 1) → ℂ))
    (hker : LinearMap.ker D ≤ LinearMap.range
      (fderiv ℂ (inclusionInComplexCharts X Q ι k (k + k) x)
        (localChart Q k x x)).toLinearMap)
    (heval : ∀ v, D v (g32n_homogeneousLine k eQ x).rep = 0)
    (v : (closedImmersionDerivativeProjection X Q ι k (k + k) x).ker) :
    (g32n_normalCoefficientEquiv X Q ι k eQ x D hker heval v).val = D v.val := by
  change ((g32n_normalCoefficientEquiv X Q ι k eQ x D hker heval).toLinearMap v).val = _
  simp only [g32n_normalCoefficientEquiv, LinearEquiv.coe_ofInjectiveOfFinrankEq]
  rfl

#print axioms g32n_normal_differential_injective
#print axioms g32n_normalCoefficientMap
#print axioms g32n_normalCoefficientEquiv
#print axioms g32n_normalCoefficientEquiv_apply
end HodgeLean.Foundations.Program
