import HodgeLean.Foundations.Program.G32Native.ProjectiveTwistedGenerators
import HodgeLean.Foundations.Program.G32Native.IdealModuleGenerators

/-! Common twisted generators of an ideal on polynomial projective space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.ProjSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard projective open as an affine open. -/
def g32l4_standardProjectiveAffine (R : Type) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).affineOpens :=
  ⟨standardOpen R n i, Proj.isAffineOpen_basicOpen _ _ (X_mem_one R n i) one_pos⟩

/-- A finite list of global twisted ideal sections generates the ideal on every standard chart. -/
theorem g32l4_projective_ideal_twisted_generators (R : Type) [CommRing R] (n : ℕ)
    [IsLocallyNoetherian (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))]
    (I : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).IdealSheafData) :
    ∃ d m : ℕ,
      ∃ t : Fin (m + 1) → Γ(I.toModules ⊗ (twistingSheaf R n).tensorPow d, ⊤),
      ∃ g : ∀ i : Fin (n + 1), Fin (m + 1) → I.ideal (g32l4_standardProjectiveAffine R n i),
        (∀ i, Ideal.span (Set.range (fun k => (g i k).val)) =
          I.ideal (g32l4_standardProjectiveAffine R n i)) ∧
        ∀ i k, (I.toModules ⊗ (twistingSheaf R n).tensorPow d).presheaf.map
            (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (t k) =
          tensorSections ((I.toModulesSectionsEquiv (g32l4_standardProjectiveAffine R n i)).symm
            (g i k)) (((twistingSheaf R n).tensorPow d).presheaf.map
            (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
              (tensorPowSection (twistingCoordinateSection R n i) d)) := by
  have := I.isFinitePresentation_toModules
  obtain ⟨d, m, t, g, hg, ht⟩ := g32l4_projective_twisted_generators R n I.toModules
  refine ⟨d, m, t, fun i k => I.toModulesSectionsEquiv
    (g32l4_standardProjectiveAffine R n i) (g i k), ?_, ?_⟩
  · intro i
    exact g32l4_ideal_module_generators I (g32l4_standardProjectiveAffine R n i) (g i) (hg i)
  · intro i k
    rw [LinearEquiv.symm_apply_apply]
    exact ht i k

end HodgeLean.Foundations.Program
