import HodgeLean.Adapters.DegreeOneLattice

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Adapters

/-- Complex-linear functionals are precisely the holomorphic real-linear functionals.
Source: Birkenhake–Lange, Complex Abelian Varieties, Theorem 1.4.1. -/
def holomorphicTangentDual (g : ℕ) :
    Module.Dual ℂ (Fin g → ℂ) ≃ₗ[ℂ] degreeOneLatticeHolomorphic g where
  toFun φ := ⟨φ.restrictScalars ℝ, fun v => by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    { toFun := f
      map_add' := f.1.map_add
      map_smul' := fun c v => by
        change (f : DegreeOneLatticeDual g) (c • v) = c * (f : DegreeOneLatticeDual g) v
        have hc : c • v = c.re • v + c.im • (Complex.I • v) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [hc, map_add, LinearMap.map_smul, LinearMap.map_smul, f.2 v,
          Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Precomposition uses the same complex scalar on forms and on the tangent space.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.2. -/
theorem holomorphicTangentDual_comp (g : ℕ) (f : Module.End ℂ (Fin g → ℂ))
    (φ : Module.Dual ℂ (Fin g → ℂ)) :
    (holomorphicTangentDual g (f.dualMap φ)).val =
      (holomorphicTangentDual g φ).val.comp (f.restrictScalars ℝ) := rfl

/-- Transpose preserves every eigenvalue multiplicity, without conjugating the scalar.
Source: Bourbaki, Algebra, II §5, rank of a transpose. -/
theorem tangentDual_eigenrank {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) (z : K) :
    Module.finrank K (Module.End.eigenspace f.dualMap z) =
      Module.finrank K (Module.End.eigenspace f z) := by
  have he : f.dualMap - z • (1 : Module.End K (Module.Dual K V)) =
      (f - z • (1 : Module.End K V)).dualMap := by
    ext φ v
    simp [LinearMap.dualMap_apply]
  rw [Module.End.eigenspace_def, Module.End.eigenspace_def, he]
  have h₁ := LinearMap.finrank_range_add_finrank_ker (f - z • (1 : Module.End K V))
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (f - z • (1 : Module.End K V)).dualMap
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h₂
  omega

#print axioms tangentDual_eigenrank
#print axioms holomorphicTangentDual
end HodgeLean.Foundations.Program.G32Native
