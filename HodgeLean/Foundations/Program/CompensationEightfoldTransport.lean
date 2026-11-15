import HodgeLean.Foundations.Program.CompensationEightfoldSurface

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {X : Over (Spec ↧ℂ)} [GrpObj X] [IsCommMonObj X]
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

theorem cq8_homPullback_cast (f : X ⟶ X) {i j : ℕ} (h : i = j) (v : HQ X i) :
    homPullback f j (HQ.castEquiv X h v) =
      HQ.castEquiv X h (homPullback f i v) := by
  subst j
  rfl

theorem cq8_cupWedge_naturality (f : X ⟶ X) (k : ℕ) :
    homPullback f (2 * k) ∘ₗ
      ((HQ.castEquiv X (two_mul k).symm).toLinearMap ∘ₗ
        (cupProductOf X).cupWedgeMap (k + k)) =
      ((HQ.castEquiv X (two_mul k).symm).toLinearMap ∘ₗ
        (cupProductOf X).cupWedgeMap (k + k)) ∘ₗ
          exteriorPower.map (k + k) (homPullback f 1) := by
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cq8_homPullback_cast]
  congr 1
  exact LinearMap.congr_fun (spec_homPullback_cupWedgeMap f (k + k)) w

theorem cq8_weilClassOf_invariant (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology (cupProductOf X)) {d : ℚ}
    (W : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; W.IsWeilType) (f : X ⟶ X)
    (hs : ∀ x ∈ W.Vs, (homPullback f 1).baseChange ℂ x ∈ W.Vs)
    (hb : ∀ x ∈ W.Vsbar, (homPullback f 1).baseChange ℂ x ∈ W.Vsbar) :
    letI := hT.finite
    (weilClassOf hF hB hD hT W hW).map (homPullback f _) ≤
      weilClassOf hF hB hD hT W hW := by
  let := hT.finite
  unfold weilClassOf
  rw [← Submodule.map_comp, cq8_cupWedge_naturality, Submodule.map_comp]
  exact Submodule.map_mono (cq8_weilClasses_invariant W _ hW (homPullback f 1) hs hb)

end HodgeLean.Foundations.Program
