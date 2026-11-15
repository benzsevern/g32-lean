import HodgeLean.Foundations.BundleResolution.ModuleTopology
import HodgeLean.Foundations.Program.G32Native.FunctionRelatedFamilies

/-! # Covector-map comparison on an actual point fibre -/
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleResolution

/-- Apply a covector map while retaining its actual module-fibre interface.
Source: linear-map evaluation on `i1_moduleFibre`. -/
def moduleFibreCovectorValue
    (Q : Over (Spec ↧ℂ)) (M : Q.left.Modules) (x : ComplexPoint Q) (d : ℕ)
    (F : i1_moduleFibre M x →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ))
    (a : i1_moduleFibre M x) : (Fin d → ℂ) →L[ℂ] ℂ := F a

theorem moduleFibreCovectorValue_eq
    (Q : Over (Spec ↧ℂ)) (M : Q.left.Modules) (x : ComplexPoint Q) (d : ℕ)
    (F : i1_moduleFibre M x →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ))
    (a : i1_moduleFibre M x) : moduleFibreCovectorValue Q M x d F a = F a := rfl

theorem moduleFibreCovectorValue_of_equation
    (Q : Over (Spec ↧ℂ)) (M : Q.left.Modules) (x : ComplexPoint Q) (d : ℕ)
    (F G : i1_moduleFibre M x →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ))
    (a b : i1_moduleFibre M x) (h : F a = G b) :
    moduleFibreCovectorValue Q M x d F a = moduleFibreCovectorValue Q M x d G b := h

theorem moduleFibreCovectorValue_congr_input
    (Q : Over (Spec ↧ℂ)) (M : Q.left.Modules) (x : ComplexPoint Q) (d : ℕ)
    (F : i1_moduleFibre M x →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ))
    (a b : i1_moduleFibre M x) (h : a = b) :
    moduleFibreCovectorValue Q M x d F a = moduleFibreCovectorValue Q M x d F b :=
  congrArg (moduleFibreCovectorValue Q M x d F) h

theorem moduleFibreCovector_ext_value
    (Q : Over (Spec ↧ℂ)) (M : Q.left.Modules) (x : ComplexPoint Q) (d : ℕ)
    (F G : i1_moduleFibre M x →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ))
    (h : ∀ a, moduleFibreCovectorValue Q M x d F a = moduleFibreCovectorValue Q M x d G a) :
    F = G := LinearMap.ext h

/-- Compare covector maps on the actual fibre of a module sheaf using
related surjective families, retaining the fibre's scalar structure.
Source: function extensionality and `Function.Surjective.forall`. -/
theorem moduleFibreCovector_ext_related
    (Q : Over (Spec ↧ℂ)) (M : Q.left.Modules) (x : ComplexPoint Q) (d : ℕ)
    {I : Type*}
    (F G : i1_moduleFibre M x →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ))
    (s t : I → i1_moduleFibre M x) (hs : Function.Surjective s)
    (hst : ∀ i, s i = t i) (h : ∀ i, F (s i) = G (t i)) : F = G := by
  exact LinearMap.ext (hs.forall.mpr (fun i => (h i).trans (congrArg G (hst i).symm)))

#print axioms moduleFibreCovectorValue_eq
#print axioms moduleFibreCovectorValue_of_equation
#print axioms moduleFibreCovectorValue_congr_input
#print axioms moduleFibreCovector_ext_value
#print axioms moduleFibreCovector_ext_related
end HodgeLean.Foundations.TubularEuler
