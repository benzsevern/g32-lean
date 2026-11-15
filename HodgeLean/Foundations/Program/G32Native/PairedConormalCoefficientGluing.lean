import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialSectionMap

/-! # Gluing actual regular coefficients with the projective twisting transition -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev res {X : Scheme} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    Γ(M, U) →+ Γ(M, V) := (M.presheaf.map (homOfLE h).op).hom

private theorem res_res {X : Scheme} (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(M, U)) :
    res M hWV (res M hVU s) = res M (hWV.trans hVU) s := by
  change (M.presheaf.map (homOfLE hVU).op ≫ M.presheaf.map (homOfLE hWV).op) s = _
  rw [← Functor.map_comp]
  rfl

variable (R : Type) [CommRing R] (k : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R
local notation "P" => Proj 𝒜
local notation "L" => ProjSpace.twistingSheaf R k
local notation "U" => ProjSpace.standardOpen R k

/-- The original twisting transition glues a compatible family of regular coefficients to an actual section. -/
theorem conormal_twisting_coefficients_glue
    (c : ∀ i : Fin (k + 1), Γ(P, U i))
    (hc : ∀ i j : Fin (k + 1),
      (P).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (c i) =
        (P).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
            (ProjSpace.coordinateRatioSection R k i j) *
          (P).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (c j)) :
    ∃ s : (ProjSpace.twistingSectionPresheaf R k 1).obj ⊤,
      ∀ i : Fin (k + 1), ((L).tensorPow 1).presheaf.map
          (homOfLE (le_top : U i ≤ ⊤)).op s =
        c i • ((L).tensorPow 1).presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op
          (tensorPowSection (ProjSpace.twistingCoordinateSection R k i) 1) := by
  let M := (L).tensorPow 1
  let v (i : Fin (k + 1)) : Γ(M, U i) :=
    c i • res M le_top (tensorPowSection (ProjSpace.twistingCoordinateSection R k i) 1)
  have hcompatible (i j : Fin (k + 1)) : res M inf_le_left (v i) = res M inf_le_right (v j) := by
    have hframe := congrArg (res M (inf_le_left : U i ⊓ U j ≤ U i))
      (ProjSpace.coordinateRatioSection_pow_smul_twistingCoordinateSection R k 1 i j)
    change res M inf_le_left
      (ProjSpace.coordinateRatioSection R k i j ^ 1 • res M le_top
        (tensorPowSection (ProjSpace.twistingCoordinateSection R k i) 1)) =
      res M inf_le_left (res M le_top
        (tensorPowSection (ProjSpace.twistingCoordinateSection R k j) 1)) at hframe
    rw [M.map_smul, map_pow, res_res, res_res, pow_one] at hframe
    change res M inf_le_left (c i • res M le_top _) =
      res M inf_le_right (c j • res M le_top _)
    rw [M.map_smul, M.map_smul, res_res, res_res, hc i j,
      mul_comm _ ((P).presheaf.map (homOfLE inf_le_right).op (c j)), mul_smul, hframe]
  obtain ⟨s, hs⟩ := (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (ProjSpace.twistingCover R k) ⊤ (fun _ => le_top) (ProjSpace.iSup_twistingCover R k).ge).2
      (fun i => v i.down) (fun i j => hcompatible i.down j.down)
  exact ⟨s, fun i => hs (ULift.up i)⟩

end HodgeLean.Foundations.Program.G32Native
