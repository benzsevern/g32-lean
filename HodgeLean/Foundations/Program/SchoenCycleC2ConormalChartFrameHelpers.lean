import HodgeLean.Foundations.Program.SchoenCycleC2ImmersionChartExtensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalAffineFrameHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Simultaneous standard smooth charts give principal-localization
frames for the actual spectrum of the immersion's section map. -/
theorem s2e_immersion_chart_localization_frame
    (Q W : Over (Spec ↧ℂ)) (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (V : W.left.Opens) (hV : IsAffineOpen V) [Nonempty (ι.left ⁻¹ᵁ V)]
    (n k : ℕ)
    (hW : (W.hom.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension (n + k))
    (hQ : (Q.hom.appLE ⊤ (ι.left ⁻¹ᵁ V) (by simp)).hom.IsStandardSmoothOfRelativeDimension n)
    (p : PrimeSpectrum Γ(Q.left, ι.left ⁻¹ᵁ V)) :
    ∃ f : Γ(Q.left, ι.left ⁻¹ᵁ V), f ∉ p.asIdeal ∧ Nonempty
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Q.left, ι.left ⁻¹ᵁ V) (Localization.Away f))))).obj
          (s2c_conormal (Spec.map (ι.left.app V))) ≅
        (SheafOfModules.free
          (R := (Spec (CommRingCat.of (Localization.Away f))).ringCatSheaf) (Fin k) :
            (Spec (CommRingCat.of (Localization.Away f))).Modules)) := by
  letI := overSpecAlgebra W V
  letI := overSpecAlgebra Q (ι.left ⁻¹ᵁ V)
  let P := s2e_closedImmersion_affine_extension Q W ι V hV
  letI : Algebra.IsStandardSmoothOfRelativeDimension (n + k) ℂ Γ(W.left, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n + k)).mp
      (algebraMap_isStandardSmoothOfRelativeDimension W hW)
  letI : Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(Q.left, ι.left ⁻¹ᵁ V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mp
      (algebraMap_isStandardSmoothOfRelativeDimension Q hQ)
  letI : Algebra.IsStandardSmooth ℂ Γ(W.left, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n + k)
  letI : IsNoetherianRing Γ(W.left, V) := Algebra.FiniteType.isNoetherianRing ℂ _
  letI : IsNoetherianRing P.Ring := by
    change IsNoetherianRing Γ(W.left, V)
    infer_instance
  letI : Algebra.IsStandardSmoothOfRelativeDimension (n + k) ℂ P.Ring := by
    change Algebra.IsStandardSmoothOfRelativeDimension (n + k) ℂ Γ(W.left, V)
    infer_instance
  exact s2e_standardSmooth_affine_conormal_localization_frame P n k p

end HodgeLean.Foundations.Program
