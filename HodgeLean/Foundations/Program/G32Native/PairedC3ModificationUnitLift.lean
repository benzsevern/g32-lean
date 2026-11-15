import HodgeLean.Foundations.Program.G32Native.PairedC3MixedBundleCoherence
import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitLift

/-! # Lifting the actual hyperplane quotient unit in Route N -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Restriction of structure functions to a subscheme, as a module arrow. -/
def pairedC3SubschemeUnit {X Y : Scheme.{0}} (i : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _
    (Scheme.Modules.pullbackUnitIso i).hom

/-- The distinguished unit belongs to the actual untwisted hyperplane quotient. -/
def pairedC3HyperplaneUnit (k : ℕ) (j : Fin (k + 1)) :
    SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶
      pairedC3HyperplaneQuotient k j := by
  let e := HodgeLean.Foundations.Program.s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))
  exact (Scheme.Modules.pullbackUnitIso e.hom).inv ≫
    (Scheme.Modules.pullback e.hom).map
      (pairedC3SubschemeUnit
        (HodgeLean.Foundations.Program.s2e_s2b_residueIdeal k j).subschemeι)

/-- The first step of the projective modification argument lifts its
specified quotient unit through the original arrow, with no extra premise.
Source: Hartshorne, Algebraic Geometry, III.5.1 and the cohomology sequence. -/
theorem paired_c3_modification_unit_lift
    (k a b : ℕ) (hk : 0 < k)
    (j : Fin (k + 1)) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact) (hqc : E.X₂.IsQuasicoherent)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a b)
    (e₃ : E.X₃ ≅ pairedC3HyperplaneQuotient k j) :
    ∃ l : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₂,
      l ≫ E.g = pairedC3HyperplaneUnit k j ≫ e₃.inv := by
  letI := hqc
  exact conormal_unit_lift_of_top_surjective E.g
    (paired_c3_mixed_kernel_global_lift k a b hk E hE e₁) _

#print axioms pairedC3SubschemeUnit
#print axioms pairedC3HyperplaneUnit
#print axioms paired_c3_modification_unit_lift
end HodgeLean.Foundations.Program.G32Native
