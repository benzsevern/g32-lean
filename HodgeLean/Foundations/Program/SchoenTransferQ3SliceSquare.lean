import HodgeLean.Foundations.Program.SchoenTransferQ3SlicePairMap

/-! Coefficients transported through the actual supported normal-slice square. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- An actual commuting slice square transports the target coefficient and
the slice degree to their product on the ambient normal coclass. -/
theorem s4_q3_slice_square_normal_coefficient
    {A B C D P : TopPair} (n : ℕ)
    (q : B ⟶ A) (jX : C ⟶ B) (f : C ⟶ D) (jZ : D ⟶ A) (t : D ⟶ P)
    (hsquare : jX ≫ q = f ≫ jZ)
    (hinj : Function.Injective (relativeCohomologyMap ℚ n jX))
    (α : RelativeCohomology ℚ A n) (ω : RelativeCohomology ℚ P n)
    (ν : RelativeCohomology ℚ B n) (η : RelativeCohomology ℚ C n)
    (a m : ℚ)
    (htarget : relativeCohomologyMap ℚ n jZ α =
      a • relativeCohomologyMap ℚ n t ω)
    (hdegree : relativeCohomologyMap ℚ n (f ≫ t) ω = m • η)
    (hnormal : relativeCohomologyMap ℚ n jX ν = η) :
    relativeCohomologyMap ℚ n q α = (a * m) • ν := by
  apply hinj
  rw [map_smul, hnormal]
  calc
    _ = relativeCohomologyMap ℚ n (jX ≫ q) α := by
      rw [relativeCohomologyMap_comp, LinearMap.comp_apply]
    _ = relativeCohomologyMap ℚ n f (relativeCohomologyMap ℚ n jZ α) := by
      rw [hsquare, relativeCohomologyMap_comp, LinearMap.comp_apply]
    _ = a • relativeCohomologyMap ℚ n (f ≫ t) ω := by
      rw [htarget, map_smul, relativeCohomologyMap_comp, LinearMap.comp_apply]
    _ = (a * m) • η := by rw [hdegree, smul_smul]

end HodgeLean.Foundations.Program
