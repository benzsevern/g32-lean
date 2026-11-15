import HodgeLean.Foundations.Program.G32Native.TypeIIIHermitianDeterminant
import HodgeLean.Foundations.Program.G32Native.TypeIIIDiscriminantScale

noncomputable section
open Module HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program.G32Native

/-- The displayed trace matrix determines the determinant class in any basis.
All matrix and quotient factors are retained; the remaining geometric task is
to construct the basis identifying the actual form with this matrix. -/
theorem typeIII_detClass_of_trace_matrix
    {V : Type*} [AddCommGroup V] [Module (QuadraticAlgebra ℚ (-3) 0) V]
    [FiniteDimensional (QuadraticAlgebra ℚ (-3) 0) V]
    (h : V →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] V →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (hh : h.IsSymm) (hn : h.Nondegenerate)
    (e : Basis (Fin 2 × Fin 3) (QuadraticAlgebra ℚ (-3) 0) V)
    (b d : ℚˣ) (l1 l2 l3 : Fin 3 → ℚ)
    (hd : (d : ℚ) = ∏ i, (-3 * l1 i ^ 2 + (b : ℚ) * l2 i ^ 2 +
      3 * (b : ℚ) * l3 i ^ 2))
    (hm : LinearMap.toMatrix₂ e e h = typeIIIHermitianMatrix (b : ℚ) l1 l2 l3) :
    detClass h hh hn = ((-b * d : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  have hg : gramDetℚ h e = -1728 * (b : ℚ) ^ 3 * (d : ℚ) := by
    unfold gramDetℚ gramDet
    rw [hm, typeIIIHermitianMatrix_det, ← hd]
    simp [QuadraticAlgebra.re_ofNat]
  rw [detClass_eq hh hn e]
  have hu : Units.mk0 (gramDetℚ h e) (gramDetℚ_ne_zero hh hn e) =
      Units.mk0 (-1728 : ℚ) (by norm_num) * b ^ 3 * d := by
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hg]
  rw [hu]
  exact typeIII_discriminant_scale_class b d

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_detClass_of_trace_matrix
