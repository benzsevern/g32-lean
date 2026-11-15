import HodgeLean.Foundations.Program.G32Native.ProjectiveIdealGenerators
import HodgeLean.Foundations.Program.G32Native.TwistedCoefficientTransition

/-! Compatible finite generators of centre ideals on projective charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.ProjSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The same finite ideal generators on standard charts differ by one powered coordinate ratio. -/
theorem g32l4_projective_ideal_compatible_generators (R : Type) [CommRing R] (n : ℕ)
    [IsLocallyNoetherian (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))]
    (I : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).IdealSheafData) :
    ∃ d m : ℕ,
      ∃ g : ∀ i : Fin (n + 1), Fin (m + 1) → I.ideal (g32l4_standardProjectiveAffine R n i),
        (∀ i, Ideal.span (Set.range (fun k => (g i k).val)) =
          I.ideal (g32l4_standardProjectiveAffine R n i)) ∧
        ∀ i j k,
          (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
              (homOfLE (inf_le_left : standardOpen R n i ⊓ standardOpen R n j ≤
                standardOpen R n i)).op (g i k).val =
            (GlueOfCocycle.rO inf_le_left (coordinateRatioSection R n i j)) ^ d *
              (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).presheaf.map
                (homOfLE inf_le_right).op (g j k).val := by
  obtain ⟨d, m, t, g, hg, ht⟩ := g32l4_projective_ideal_twisted_generators R n I
  refine ⟨d, m, g, hg, fun i j k => ?_⟩
  have h := g32l4_twisted_coefficient_transition R n d I.toModules (t k) i j
    (standardOpen R n i ⊓ standardOpen R n j) inf_le_left inf_le_right
    ((I.toModulesSectionsEquiv (g32l4_standardProjectiveAffine R n i)).symm (g i k))
    ((I.toModulesSectionsEquiv (g32l4_standardProjectiveAffine R n j)).symm (g j k))
    (ht i k) (ht j k)
  exact congrArg (fun s : Γ(I.toModules, standardOpen R n i ⊓ standardOpen R n j) =>
    (s : I.toSubmodule.obj (Opposite.op (standardOpen R n i ⊓ standardOpen R n j))).val) h

end HodgeLean.Foundations.Program
