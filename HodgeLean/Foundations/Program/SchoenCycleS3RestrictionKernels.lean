import HodgeLean.Foundations.Program.SchoenCycleS3AffineIdealCotangent

/-! # Kernel preservation under open restriction -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restriction along an open immersion preserves module kernels. -/
theorem s2e_restrictFunctor_preservesKernel {X Y : Scheme} (j : Y ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0) (Scheme.Modules.restrictFunctor j) := by
  let α : Y.presheaf ⟶ j.opensFunctor.op ⋙ X.presheaf :=
    { app V := (j.appIso V.unop).inv }
  let ψ : Y.ringCatSheaf ⟶
      (j.opensFunctor.sheafPushforwardContinuous RingCat _ _).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  change PreservesLimit (parallelPair g 0) (SheafOfModules.pushforward ψ)
  let : (SheafOfModules.pushforward ψ).IsRightAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction ψ).isRightAdjoint
  infer_instance

end HodgeLean.Foundations.Program
