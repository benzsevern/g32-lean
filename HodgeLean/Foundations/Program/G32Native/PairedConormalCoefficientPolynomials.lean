import HodgeLean.Foundations.Program.G32Native.PairedConormalCoefficientGluing
import HodgeLean.Foundations.Program.G32Native.PairedConormalLinearSectionPolynomials

/-! # Linear forms from compatible actual projective chart coefficients -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] (k : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) K
local notation "P" => Proj 𝒜
local notation "U" => ProjSpace.standardOpen K k

/-- The original twisting transition forces each regular coefficient family to be a homogeneous linear form. -/
theorem conormal_twisting_coefficients_linear_polynomial (hk : 1 ≤ k)
    (c : ∀ i : Fin (k + 1), Γ(P, U i))
    (hc : ∀ i j : Fin (k + 1),
      (P).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (c i) =
        (P).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
            (ProjSpace.coordinateRatioSection K k i j) *
          (P).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (c j)) :
    ∃ p : 𝒜 1, ∀ i : Fin (k + 1),
      c i = ProjSpace.homogeneousRatioSection K k 1 p i := by
  obtain ⟨s, hs⟩ := conormal_twisting_coefficients_glue K k c hc
  obtain ⟨p, hp⟩ := conormal_polynomial_linear_sections_surjective K k hk s
  refine ⟨p, fun i => ?_⟩
  have he : c i • ((ProjSpace.twistingSheaf K k).tensorPow 1).presheaf.map
        (homOfLE (le_top : U i ≤ ⊤)).op
        (tensorPowSection (ProjSpace.twistingCoordinateSection K k i) 1) =
      ProjSpace.homogeneousRatioSection K k 1 p i •
        ((ProjSpace.twistingSheaf K k).tensorPow 1).presheaf.map
          (homOfLE (le_top : U i ≤ ⊤)).op
          (tensorPowSection (ProjSpace.twistingCoordinateSection K k i) 1) := by
    rw [← hs i, ← hp, ProjSpace.polynomialTwistingSection_restrict]
    rfl
  exact (((ProjSpace.isFrameOn_twistingCoordinateSection K k i).tensorPowSection_monoidalV2 1)
    le_top le_rfl).1 he

end HodgeLean.Foundations.Program.G32Native
