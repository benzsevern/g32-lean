import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialScalars

/-! # The actual linear polynomial-to-global-section map -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type) [CommRing R] (k : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R
local notation "P" => Proj 𝒜
local notation "sP" => (𝟙 P) ≫ ProjSpace.π R k

/-- The concrete polynomial section uses the original structural base-ring scalar. -/
theorem conormal_polynomialTwistingSection_smul (d : ℕ) (p : 𝒜 d) (r : R) :
    (show (ProjSpace.twistingSectionPresheaf R k d).obj ⊤ from
      ProjSpace.polynomialTwistingSection R k d (r • p)) =
    r • (show (ProjSpace.twistingSectionPresheaf R k d).obj ⊤ from
      ProjSpace.polynomialTwistingSection R k d p) := by
  let M := (ProjSpace.twistingSheaf R k).tensorPow d
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (ProjSpace.twistingCover R k) ⊤ (fun _ => le_top) (ProjSpace.iSup_twistingCover R k).ge).1
  intro i
  change M.presheaf.map (homOfLE (le_top : ProjSpace.standardOpen R k i.down ≤ ⊤)).op
      (ProjSpace.polynomialTwistingSection R k d (r • p)) =
    M.presheaf.map (homOfLE (le_top : ProjSpace.standardOpen R k i.down ≤ ⊤)).op
      (((sP).constToPresheaf.app (op ⊤)).hom r • ProjSpace.polynomialTwistingSection R k d p)
  have hcoef : (P).presheaf.map
      (homOfLE (le_top : ProjSpace.standardOpen R k i.down ≤ ⊤)).op
      (((sP).constToPresheaf.app (op ⊤)).hom r) =
      ((sP).constToPresheaf.app (op (ProjSpace.standardOpen R k i.down))).hom r :=
    (congrArg (fun q : CommRingCat.of R ⟶ Γ(P, ProjSpace.standardOpen R k i.down) => q r)
      ((sP).constToPresheaf.naturality
        (homOfLE (le_top : ProjSpace.standardOpen R k i.down ≤ ⊤)).op)).symm
  rw [M.map_smul, hcoef, ProjSpace.polynomialTwistingSection_restrict,
    ProjSpace.polynomialTwistingSection_restrict]
  unfold ProjSpace.homogeneousTwistingLocalSection
  rw [conormal_homogeneousRatioSection_smul, mul_smul]

/-- Homogeneous polynomials map linearly to their actual native global sections. -/
def conormalPolynomialSectionMap (d : ℕ) :
    𝒜 d →ₗ[R] (ProjSpace.twistingSectionPresheaf R k d).obj ⊤ where
  toFun := ProjSpace.polynomialTwistingSection R k d
  map_add' := ProjSpace.polynomialTwistingSection_add R k d
  map_smul' := fun r p => conormal_polynomialTwistingSection_smul R k d p r

end HodgeLean.Foundations.Program.G32Native
