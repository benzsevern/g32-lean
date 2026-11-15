import HodgeLean.Foundations.Program.PrymVariationLatticeDefs

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b63l_mem_saturation_of_smul_mem {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M] (L : Submodule R M)
    (n : R) (hn : n ≠ 0) (x : M) (hx : n • x ∈ b63l_saturation L) :
    x ∈ b63l_saturation L := by
  rcases hx with ⟨m, hm, hmx⟩
  refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
  simpa only [mul_smul] using hmx

theorem b63l_subtype_baseChange_rat_injective {M : Type*} [AddCommGroup M] [Module ℤ M]
    (L : Submodule ℤ M) :
    letI : Module ℤ L := L.module
    Function.Injective (L.subtype.baseChange ℚ) := by
  letI : Module ℤ L := L.module
  change Function.Injective (L.subtype.lTensor ℚ)
  exact Module.Flat.lTensor_preserves_injective_linearMap L.subtype L.subtype_injective

end HodgeLean.Foundations.Program
