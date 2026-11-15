import HodgeLean.Foundations.Program.G32Native.PairedC3HyperplaneUnitExact
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Transport of the actual hyperplane relation kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The kernel of the actual quotient restriction, after any supplied
quotient identification, is the pullback of the original hyperplane ideal. -/
def pairedC3HyperplaneKernelTransport (k : ℕ) (j : Fin (k + 1))
    (Q : (pairedC3Proj k).Modules) (eQ : Q ≅ pairedC3HyperplaneQuotient k j) :
    kernel (pairedC3HyperplaneUnit k j ≫ eQ.inv) ≅
      (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).obj
        (Conormal.idealModule (s2e_s2b_residueIdeal k j).subschemeι) := by
  let e := s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))
  let F := Scheme.Modules.pullback e.hom
  letI : F.IsEquivalence := conormal_pullback_isEquivalence e
  let i := (s2e_s2b_residueIdeal k j).subschemeι
  let q := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  let eu := Scheme.Modules.pullbackUnitIso e.hom
  exact kernelCompMono (pairedC3HyperplaneUnit k j) eQ.inv ≪≫
    kernelIsIsoComp eu.inv (F.map (pairedC3SubschemeUnit i)) ≪≫
    kernelIsoOfEq (congrArg F.map (paired_c3_subscheme_unit_eq i)) ≪≫
    (PreservesKernel.iso F q).symm

#print axioms pairedC3HyperplaneKernelTransport
end HodgeLean.Foundations.Program.G32Native
