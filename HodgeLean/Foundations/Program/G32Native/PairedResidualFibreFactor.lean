import HodgeLean.Foundations.Program.G32Native.PairedResidualConstantMap

/-! # Actual factorization into a specified scheme fibre -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A literal constant-composite equation gives a map into the specified scheme fibre. -/
theorem residual_factor_through_specified_fibre
    (X B Y : Over (Spec ↧ℂ)) (f : X ⟶ B) (a : B ⟶ Y) (y : ComplexPoint Y)
    (h : f ≫ a = residualConstantMap X Y y) :
    ∃ l : X.left ⟶ pullback a.left y.left,
      l ≫ pullback.fst a.left y.left = f.left ∧
      l ≫ pullback.snd a.left y.left = X.hom := by
  have hc := congrArg Over.Hom.left h
  change f.left ≫ a.left = X.hom ≫ y.left at hc
  exact ⟨pullback.lift f.left X.hom hc, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

#print axioms residual_factor_through_specified_fibre
/-- A specified closed immersion remains a closed immersion in its actual fibre factorization. -/
theorem residual_closedImmersion_into_specified_fibre
    (X B Y : Over (Spec ↧ℂ)) (f : X ⟶ B) [IsClosedImmersion f.left]
    (a : B ⟶ Y) (y : ComplexPoint Y) [IsClosedImmersion y.left]
    (h : f ≫ a = residualConstantMap X Y y) :
    ∃ l : X.left ⟶ pullback a.left y.left, IsClosedImmersion l ∧
      l ≫ pullback.fst a.left y.left = f.left ∧
      l ≫ pullback.snd a.left y.left = X.hom := by
  obtain ⟨l, hl, hp⟩ := residual_factor_through_specified_fibre X B Y f a y h
  haveI : IsClosedImmersion (l ≫ pullback.fst a.left y.left) := hl.symm ▸ inferInstance
  exact ⟨l, IsClosedImmersion.of_comp l (pullback.fst a.left y.left), hl, hp⟩

#print axioms residual_closedImmersion_into_specified_fibre
end HodgeLean.Foundations.Program.G32Native
