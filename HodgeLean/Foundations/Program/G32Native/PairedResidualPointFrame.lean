import HodgeLean.Foundations.Program.SchoenCycleS3ConormalFreeTransport

/-! # Global frames on a scheme with a single point -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A local frame on a one-point scheme is a global frame on that same scheme. -/
def residual_global_frame_of_subsingleton {X : Scheme.{0}} [Nonempty X] [Subsingleton X]
    (M : X.Modules) (k : ℕ)
    (hframes : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict M U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    M ≅ (SheafOfModules.free (R := X.ringCatSheaf) (Fin k) : X.Modules) := by
  classical
  let U := Classical.choose (hframes (Classical.arbitrary X))
  have hx := (Classical.choose_spec (hframes (Classical.arbitrary X))).1
  let b := Classical.choice (Classical.choose_spec (hframes (Classical.arbitrary X))).2
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    simpa only [Subsingleton.elim y (Classical.arbitrary X)] using hx
  letI : IsIso U.ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι
      (by rw [Scheme.Opens.opensRange_ι, hU])
  exact s2e_freeOfPullbackIso (asIso U.ι) M (Fin k)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ b)

#print axioms residual_global_frame_of_subsingleton

end HodgeLean.Foundations.Program.G32Native
