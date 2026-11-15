import HodgeLean.Foundations.Program.SchoenSelectedGeometryHomologyNaturality
import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Rational to complex singular cohomology for the primitive restriction

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

local instance (X : TopCat.{0}) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)
local instance (X : TopCat.{0}) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _
local instance (X : TopCat.{0}) (n : ℕ) : Module ℚ (Cohomology ℂ X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)
local instance (X : TopCat.{0}) (n : ℕ) : IsScalarTower ℚ ℂ (Cohomology ℂ X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- The coefficient map is the dual of the actual rational-to-complex homology
base change, transported through the universal coefficient identifications.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficients over fields.
HC no distance; AV milestone no distance. -/
def s4_assembly_coefficientMap (X : TopCat.{0}) (n : ℕ) :
    Cohomology ℚ X n →ₗ[ℚ] Cohomology ℂ X n :=
  (cohomologyEquivDualHomology ℂ X n).symm.toLinearMap.restrictScalars ℚ ∘ₗ
    (Module.Dual.congr (qToCHomology_isBaseChange X n).equiv).toLinearMap.restrictScalars ℚ ∘ₗ
    Module.Dual.baseChange ℂ ∘ₗ (cohomologyEquivDualHomology ℚ X n).toLinearMap

/-- Coefficient extension has the literal expected value on every rational homology class.
Source: Hatcher, Algebraic Topology, §3.1, evaluation of extended coefficients.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_coefficientMap_eval (X : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ X n) (z : Homology ℚ X n) :
    cohomologyEquivDualHomology ℂ X n (s4_assembly_coefficientMap X n a)
      (qToCHomology X n z) = (cohomologyEquivDualHomology ℚ X n a z : ℂ) := by
  simp only [s4_assembly_coefficientMap, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change (Module.Dual.baseChange ℂ (cohomologyEquivDualHomology ℚ X n a))
    ((qToCHomology_isBaseChange X n).equiv.symm (qToCHomology X n z)) = _
  have he : (qToCHomology_isBaseChange X n).equiv (1 ⊗ₜ[ℚ] z) =
      qToCHomology X n z := by
    simpa only [one_smul] using IsBaseChange.equiv_tmul (qToCHomology_isBaseChange X n) 1 z
  rw [← he, LinearEquiv.symm_apply_apply, Module.Dual.baseChange_apply_tmul]
  simpa only [Algebra.smul_def, mul_one, Rat.cast_id] using
    (map_ratCast (algebraMap ℚ ℂ) (cohomologyEquivDualHomology ℚ X n a z))

/-- The actual coefficient extension detects every rational class.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficient evaluation.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_coefficientMap_injective (X : TopCat.{0}) (n : ℕ) :
    Function.Injective (s4_assembly_coefficientMap X n) := by
  intro a b hab
  apply (cohomologyEquivDualHomology ℚ X n).injective
  ext z
  have hz := congrArg (fun c : Cohomology ℂ X n =>
    cohomologyEquivDualHomology ℂ X n c (qToCHomology X n z)) hab
  rw [s4_assembly_coefficientMap_eval, s4_assembly_coefficientMap_eval] at hz
  exact_mod_cast hz

/-- The coefficient map commutes with pullback along the specified continuous map.
Source: Hatcher, Algebraic Topology, §3.1, naturality of universal coefficients.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_coefficientMap_naturality {X Y : TopCat.{0}} (n : ℕ) (f : X ⟶ Y)
    (a : Cohomology ℚ Y n) :
    s4_assembly_coefficientMap X n (cohomologyMap ℚ n f a) =
      cohomologyMap ℂ n f (s4_assembly_coefficientMap Y n a) := by
  apply (cohomologyEquivDualHomology ℂ X n).injective
  apply (qToCHomology_isBaseChange X n).algHom_ext
  intro z
  calc
    _ = (cohomologyEquivDualHomology ℚ X n (cohomologyMap ℚ n f a) z : ℂ) :=
      s4_assembly_coefficientMap_eval X n _ z
    _ = (cohomologyEquivDualHomology ℚ Y n a (homologyMap ℚ n f z) : ℂ) := by
      rw [cohomologyEquivDualHomology_cohomologyMap]
    _ = cohomologyEquivDualHomology ℂ Y n (s4_assembly_coefficientMap Y n a)
        (qToCHomology Y n (homologyMap ℚ n f z)) :=
      (s4_assembly_coefficientMap_eval Y n a _).symm
    _ = cohomologyEquivDualHomology ℂ Y n (s4_assembly_coefficientMap Y n a)
        (homologyMap ℂ n f (qToCHomology X n z)) := by
      rw [s0_qToCHomology_naturality]
    _ = _ := (cohomologyEquivDualHomology_cohomologyMap ℂ n f
      (s4_assembly_coefficientMap Y n a) (qToCHomology X n z)).symm

#print axioms s4_assembly_coefficientMap_naturality
#print axioms s4_assembly_coefficientMap_injective
#print axioms s4_assembly_coefficientMap_eval
end HodgeLean.Foundations.Program
