import HodgeLean.Foundations.Program.SchoenTransferR2Coefficients
import HodgeLean.Foundations.CyclicAction
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # Descent of primitive restriction vanishing to rational coefficients

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

local instance (X : TopCat.{0}) (n : ℕ) : Module ℚ (Cohomology ℂ X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)
local instance (X : TopCat.{0}) (n : ℕ) : IsScalarTower ℚ ℂ (Cohomology ℂ X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Restriction vanishing on all primitive complex eigenvectors implies vanishing
on the actual rational cyclotomic kernel. No finite-dimensionality premise is needed.
Source: Hatcher, Algebraic Topology, §3.1; rational coefficient naturality;
`HodgeLean.Foundations.baseChange_isotypic`.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_rational_primitive_restriction_zero
    {X Y : TopCat.{0}} (n m : ℕ) (hm : 0 < m) (f : X ⟶ Y) (d : Y ⟶ Y)
    (hvanish : ∀ (ζ : ℂ), IsPrimitiveRoot ζ m →
      ∀ a : Cohomology ℂ Y n, cohomologyMap ℂ n d a = ζ • a → cohomologyMap ℂ n f a = 0)
    (u : Cohomology ℚ Y n)
    (hu : Polynomial.aeval (cohomologyMap ℚ n d) (Polynomial.cyclotomic m ℚ) u = 0) :
    cohomologyMap ℚ n f u = 0 := by
  let T := cohomologyMap ℚ n d
  let Tℂ := cohomologyMap ℂ n d
  let J := (s4_assembly_coefficientMap Y n).liftBaseChange ℂ
  have hJ : J.comp (T.baseChange ℂ) = Tℂ.comp J := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      J, LinearMap.liftBaseChange_tmul, map_smul, T, Tℂ]
    rw [s4_assembly_coefficientMap_naturality]
  have hzero : (isotypic T m).baseChange ℂ ≤
      LinearMap.ker ((cohomologyMap ℂ n f).comp J) := by
    rw [baseChange_isotypic T hm]
    refine iSup_le fun ζ => iSup_le fun hζ => ?_
    intro z hz
    change cohomologyMap ℂ n f (J z) = 0
    have he := LinearMap.congr_fun hJ z
    change J ((T.baseChange ℂ) z) = Tℂ (J z) at he
    rw [Module.End.mem_eigenspace_iff.mp hz, map_smul] at he
    exact hvanish ζ ((mem_primitiveRoots hm).mp hζ) (J z) he.symm
  have hu' : u ∈ isotypic T m := hu
  have hz := hzero (Submodule.tmul_mem_baseChange_of_mem (1 : ℂ) hu')
  change cohomologyMap ℂ n f (J (1 ⊗ₜ[ℚ] u)) = 0 at hz
  apply s4_assembly_coefficientMap_injective X n
  rw [map_zero, s4_assembly_coefficientMap_naturality]
  simpa only [J, LinearMap.liftBaseChange_one_tmul] using hz

#print axioms s4_assembly_rational_primitive_restriction_zero
end HodgeLean.Foundations.Program
