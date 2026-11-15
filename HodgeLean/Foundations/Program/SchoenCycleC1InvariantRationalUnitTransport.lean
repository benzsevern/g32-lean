import HodgeLean.Foundations.Program.SchoenCycleC1AutomorphismLocalSquare

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual invariant rational stalk units transport along every specified
scheme automorphism, retaining the moving point's original stalk map. -/
theorem s2e_c1_invariant_rational_unit_transport
    (X : Scheme) [IsIntegral X] (a : X ⟶ X) [IsIso a]
    (t : X.functionField) (ht : s2e_step1_fieldPullback X a t = t)
    (p : X) (u : (X.presheaf.stalk (a p))ˣ)
    (hu : algebraMap (X.presheaf.stalk (a p)) X.functionField (u : _) = t) :
    ∃ v : (X.presheaf.stalk p)ˣ,
      algebraMap (X.presheaf.stalk p) X.functionField (v : _) = t := by
  refine ⟨Units.map (a.stalkMap p).hom.toMonoidHom u, ?_⟩
  change algebraMap (X.presheaf.stalk p) X.functionField ((a.stalkMap p).hom (u : _)) = t
  rw [← s2e_c1_automorphism_rational_local_square X a p (u : _), hu, ht]

end HodgeLean.Foundations.Program
