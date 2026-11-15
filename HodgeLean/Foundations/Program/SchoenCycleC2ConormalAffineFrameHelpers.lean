import HodgeLean.Foundations.Program.SchoenCycleC2ConormalExtensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalSmoothRankHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2TildeBasisHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual affine conormal sheaf has rank-`k` frames after localization
near each prime of a standard smooth quotient of codimension `k`. -/
theorem s2e_standardSmooth_affine_conormal_localization_frame
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Nontrivial S]
    (P : Algebra.Extension.{0} R S) [IsNoetherianRing P.Ring]
    (n k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension (n + k) R P.Ring]
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] (p : PrimeSpectrum S) :
    ∃ f : S, f ∉ p.asIdeal ∧ Nonempty
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap S (Localization.Away f))))).obj
          (s2c_conormal (Spec.map (CommRingCat.ofHom (algebraMap P.Ring S)))) ≅
        (SheafOfModules.free
          (R := (Spec (CommRingCat.of (Localization.Away f))).ringCatSheaf) (Fin k) :
            (Spec (CommRingCat.of (Localization.Away f))).Modules)) := by
  obtain ⟨f, hf, ⟨b⟩⟩ := s2e_standardSmooth_conormal_principal_basis P n k p
  let T := Localization.Away f
  let j := Spec.map (CommRingCat.ofHom (algebraMap S T))
  let M := ModuleCat.of S P.Cotangent
  let eL : (ModuleCat.extendScalars (algebraMap S T)).obj M ≅
      ModuleCat.of T (LocalizedModule.Away f P.Cotangent) :=
    s2e_extendScalars_algebraMap_iso M ≪≫
      (LocalizedModule.equivTensorProduct (.powers f) P.Cotangent).symm.toModuleIso
  refine ⟨f, hf, ⟨?_⟩⟩
  exact (Scheme.Modules.pullback j).mapIso (s2e_affine_extension_conormal_iso P) ≪≫
    (s2e_affine_pullback_tilde_iso (CommRingCat.of S) (CommRingCat.of T)
      (CommRingCat.ofHom (algebraMap S T))).app M ≪≫
    (tilde.functor (CommRingCat.of T)).mapIso eL ≪≫
    s2e_tilde_basis_iso (CommRingCat.of T)
      (ModuleCat.of T (LocalizedModule.Away f P.Cotangent)) (Fin k) b

end HodgeLean.Foundations.Program
