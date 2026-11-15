import HodgeLean.Foundations.Program.SchoenCycleIdealJetLifting
import HodgeLean.Foundations.Program.SchoenCycleAffineStalkJets

/-! # Actual affine finite jets with a prescribed ideal membership -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every finite jet belonging to an actual affine ideal stalk has a representative inside that same affine ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_affine_ideal_stalk_jet_representative
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (p : X) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X))
    (J : Ideal Γ(X, U)) (N : ℕ) (r : X.presheaf.stalk p)
    (hr : r ∈ J.map (X.presheaf.germ U p hp).hom) :
    ∃ s ∈ J, r - (X.presheaf.germ U p hp).hom s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N := by
  apply s2e_ideal_jet_lift_of_quotient_surjective (X.presheaf.germ U p hp).hom J
    (IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N) ?_ r hr
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨s, hs⟩ := s2e_affine_stalk_power_jet_representative X U hU p hp hclosed N a
  refine ⟨s, ?_⟩
  apply Ideal.Quotient.eq.mpr
  simpa only [neg_sub] using (IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N).neg_mem hs

end HodgeLean.Foundations.Program
