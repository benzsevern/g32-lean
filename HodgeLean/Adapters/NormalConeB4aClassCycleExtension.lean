import HodgeLean.Adapters.NormalConeB4aClassExtension
import HodgeLean.Adapters.NormalConeB4aClassCyclePurity

/-! # Extension of cycle-support classes across algebraic boundaries

Route: higher algebraic codimension gives the two boundary vanishing degrees.
The nested-support extension theorem and the universal-neighborhood comparison
then apply to the frozen cycle-support pair.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Removing an algebraic boundary of codimension at least `c+1` preserves
all degree-`2*c` classes supported on the cycle. -/
theorem a3b4a_classCycle_restriction_bijective_of_boundary_codimension
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (B : Closeds Z) (hBS : B ≤ a3b4a_classAlgebraicSupport q γ)
    (hcB : ∀ z ∈ B, ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight z) :
    Function.Bijective (relativeCohomologyMap ℚ (2 * c)
      (a3b4_neighborhoodPairMap
        (Point.underlying ⁻¹' (B : Set Z))ᶜ (a3b4_cycleSupport q γ))) := by
  letI : LocallyOfFiniteType (Over.mk q).hom := inferInstanceAs (LocallyOfFiniteType q)
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI (V : Opens (ComplexPoint (Over.mk q))) : ParacompactSpace V :=
    a3b4a_class_openParacompact q V
  let S : Closeds (a3b4_an q) := ⟨a3b4_cycleSupport q γ, a3b4a_classSupport_isClosed q γ⟩
  let B' : Closeds (a3b4_an q) := B.preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))
  have hB'S : B' ≤ S := fun x hx => hBS hx
  have hz (j : ℕ) (hj : j ∈ ({2 * c, 2 * c + 1} : Finset ℕ)) :
      IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (Set.univ : Set (a3b4_an q)) B') j) :=
    a3b4a_classRelative_purity_vanishing q B (c + 1) hcB ⊤ j (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        omega)
  have hres := a3b4a_classRelative_restriction_bijective_of_boundary_vanishing
    (a3b4_an q) S B' hB'S (2 * c) hz
  have h := hres.comp (a3b4a_classLocal_restrict_univ_bijective (S : Set (a3b4_an q)) (2 * c))
  have he : (relativeCohomologyMap ℚ (2 * c)
      (neighborhoodSupportInclusionPairMap
        (show (B'.compl : Set (a3b4_an q)) ⊆ Set.univ from Set.subset_univ _) (S : Set (a3b4_an q)))) ∘
      (relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap (M := a3b4_an q) Set.univ (S : Set (a3b4_an q)))) =
      relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap (M := a3b4_an q) (B'.compl : Set (a3b4_an q)) (S : Set (a3b4_an q))) := by
    funext β
    exact a3b4a_classLocal_restriction_comp (S : Set (a3b4_an q)) (Set.subset_univ _) (2 * c) β
  rw [he] at h
  exact h

end HodgeLean.Adapters
