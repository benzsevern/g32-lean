import HodgeLean.Foundations.BundleThom.AnalyticNormalFramesHelpers
/-! # Actual complex fibres of specified finite module frames -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- Specialize the supplied module frame to the actual complex point, using
its canonical open factorization and pullback comparisons. -/
def paired_module_pointFrameIso {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) (k : ℕ) (U : Q.left.Opens)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (Scheme.Modules.pullback x.left).obj M ≅
      SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k) := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  exact ((Scheme.Modules.pullbackComp a U.ι ≪≫
    Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).symm.app M) ≪≫
    (Scheme.Modules.pullback a).mapIso e.symm ≪≫
    SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)

/-- The actual complex-point fibre has coordinates induced by the supplied frame. -/
def paired_module_fibreCoordinates_of_frame {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) (k : ℕ) (U : Q.left.Opens)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj M) ≃ₗ[ℂ] (Fin k → ℂ) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    (paired_module_pointFrameIso M k U e x hx)).toLinearEquiv.trans
      (i1_freePointCoordinates k)

/-- Fixed finite frames imply both finite complex fibres and their exact rank. -/
theorem paired_module_fibre_rank_of_fixedFrames {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) (k : ℕ)
    (hM : ∀ y : Q.left, ∃ U : Q.left.Opens, y ∈ U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) ≅
        (Scheme.Modules.pullback U.ι).obj M)) (x : ComplexPoint Q) :
    Module.Finite ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj M)) ∧
    Module.finrank ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj M)) = k := by
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x.underlying
  let c := paired_module_fibreCoordinates_of_frame M k U e x hx
  refine ⟨c.symm.finiteDimensional, ?_⟩
  simpa only [Module.finrank_pi, Fintype.card_fin, Module.finrank_self, mul_one] using
    c.finrank_eq

end HodgeLean.Foundations.Program.G32Native
