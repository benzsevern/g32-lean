import HodgeLean.Foundations.Program.SchoenCycleProjectiveReducedIdeals
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual subscheme factors from a component generic point

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A component whose generic point lies on a centre factors through the actual
centre subscheme, with its literal projection equation.
Source: Hartshorne, Algebraic Geometry, II.3, generic points and reduced schematic images.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_generic_subscheme_factor
    {Q X : Scheme.{0}} [IsIntegral Q] (f : Q ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (h : f (genericPoint Q) ∈ I.support) :
    ∃ g : Q ⟶ I.subscheme, g ≫ I.subschemeι = f := by
  have hr : Set.range f ⊆ (I.support : Set X) := by
    have hclosed : IsClosed (f ⁻¹' (I.support : Set X)) := I.support.isClosed.preimage f.continuous
    have hall : closure ({genericPoint Q} : Set Q) ⊆ f ⁻¹' (I.support : Set X) :=
      hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
    rw [genericPoint_closure] at hall
    rintro y ⟨x, rfl⟩
    exact hall (Set.mem_univ x)
  have hs : f.ker.support ≤ I.support := by
    change (f.ker.support : Set X) ⊆ I.support
    rw [Scheme.Hom.support_ker]
    exact closure_minimal hr I.support.isClosed
  have hi : I ≤ f.ker := by
    have hh := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hs
    rwa [Scheme.IdealSheafData.vanishingIdeal_support, s2e_kernel_radical_of_reduced f] at hh
  have hi' : I.subschemeι.ker ≤ f.ker := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨IsClosedImmersion.lift I.subschemeι f hi', IsClosedImmersion.lift_fac _ _ _⟩

#print axioms s4_assembly_generic_subscheme_factor
end HodgeLean.Foundations.Program
