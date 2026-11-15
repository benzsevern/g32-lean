import HodgeLean.Foundations.Program.G32Native.PairedC3BiproductCechVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso

/-! # Native Cech vanishing for binary sums -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
namespace HodgeLean.Foundations.Program.G32Native
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsSeparated f] (M N : X.Modules) (K : X.OrderedAffineCover)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Native positive Cech vanishing is preserved by the binary sum. -/
theorem paired_c3_binary_vanishing (q : ℕ)
    [Subsingleton ((toOModulePresheaf f M).HSucc K q)]
    [Subsingleton ((toOModulePresheaf f N).HSucc K q)] :
    Subsingleton ((toOModulePresheaf f (M ⊞ N)).HSucc K q) := by
  let L : ULift.{u} Bool → X.Modules := fun j => if j.down then N else M
  let e : (⨁ L) ≅ M ⊞ N :=
    { hom := biproduct.desc (fun j => by rcases j with ⟨j⟩; cases j; exact biprod.inl; exact biprod.inr)
      inv := biprod.desc (biproduct.ι L ⟨false⟩) (biproduct.ι L ⟨true⟩)
      hom_inv_id := by
        apply biproduct.hom_ext'
        intro ⟨j⟩
        cases j <;> simp [L]
      inv_hom_id := by
        apply biprod.hom_ext' <;> simp [L] }
  haveI : ∀ j, Subsingleton ((toOModulePresheaf f (L j)).HSucc K q) := by
    intro j
    rcases j with ⟨j⟩
    cases j <;> dsimp [L] <;> infer_instance
  letI := paired_c3_biproduct_vanishing f (ULift.{u} Bool) L K q
  exact subsingleton_HSucc_of_iso f K e q

#print axioms paired_c3_binary_vanishing
end HodgeLean.Foundations.Program.G32Native
