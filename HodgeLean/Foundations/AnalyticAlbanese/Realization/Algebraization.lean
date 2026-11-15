import HodgeLean.Foundations.AnalyticAlbanese.Proofs
import HodgeLean.Adapters.UniformizationBiholomorphic
import HodgeLean.Adapters.GagaMaps

/-! # Algebraization through the actual exponential coverings
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open scoped Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.AnalyticAlbanese.Realization

variable (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y]
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem exponential_algebraization
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim Y.left) → ℂ))
    (hA : ∀ l : abelianPeriodLattice X, A l ∈ abelianPeriodLattice Y) :
    ∃! f : X ⟶ Y, IsMonHom f ∧ ∀ v,
      Point.map f (Additive.toMul (complexExponential X (dim X.left) v)) =
        Additive.toMul (complexExponential Y (dim Y.left) (A v)) := by
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  letI : IsCommMonObj Y := isCommMonObj_of_complexSelfProductIntegral Y
    (complexSelfProductIntegral_of_isIntegral Y)
  have hAc : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ)
      𝓘(ℂ, Fin (dim Y.left) → ℂ) ω A :=
    (LinearMap.toContinuousLinearMap A).contMDiff
  obtain ⟨F, ⟨hF, hFe⟩, _⟩ :=
    spec_existsUnique_contMDiff_descent_manifold X (dim X.left)
      𝓘(ℂ, Fin (dim Y.left) → ℂ)
      (fun v ↦ Additive.toMul (complexExponential Y (dim Y.left) (A v)))
      ((spec_contMDiff_complexExponential Y (dim Y.left)).comp hAc)
      (by
        intro l hl v
        have h0 : complexExponential Y (dim Y.left) (A l) = 0 := hA ⟨l, hl⟩
        change Additive.toMul (complexExponentialHom Y (dim Y.left) (A (v + l))) =
          Additive.toMul (complexExponentialHom Y (dim Y.left) (A v))
        rw [map_add, map_add]
        change Additive.toMul (_ + complexExponential Y (dim Y.left) (A l)) = _
        rw [h0, add_zero])
  obtain ⟨f, hf⟩ := gagam_algebraize X Y F hF
  have he (v) : Point.map f (Additive.toMul (complexExponential X (dim X.left) v)) =
      Additive.toMul (complexExponential Y (dim Y.left) (A v)) := by rw [hf]; exact hFe v
  have hexpX (v w) : Additive.toMul (complexExponential X (dim X.left) (v + w)) =
      Additive.toMul (complexExponential X (dim X.left) v) *
        Additive.toMul (complexExponential X (dim X.left) w) :=
    congrArg Additive.toMul ((complexExponentialHom X (dim X.left)).map_add v w)
  have hexpY (v w) : Additive.toMul (complexExponential Y (dim Y.left) (v + w)) =
      Additive.toMul (complexExponential Y (dim Y.left) v) *
        Additive.toMul (complexExponential Y (dim Y.left) w) :=
    congrArg Additive.toMul ((complexExponentialHom Y (dim Y.left)).map_add v w)
  have hs (x : ComplexPoint X) : ∃ v,
      Additive.toMul (complexExponential X (dim X.left) v) = x := by
    obtain ⟨v, hv⟩ := surjective_complexExponential X (dim X.left) (Additive.ofMul x)
    exact ⟨v, congrArg Additive.toMul hv⟩
  refine ⟨f, ⟨?_, he⟩, ?_⟩
  · apply (faithful_group_reflection_aux X Y).2
    · have h := he 0
      rwa [map_zero, complexExponential_zero, complexExponential_zero, toMul_zero] at h
    · intro x y
      obtain ⟨v, rfl⟩ := hs x
      obtain ⟨w, rfl⟩ := hs y
      rw [← hexpX, he, he, he, map_add, hexpY]
  · intro g hg
    apply (faithful_group_reflection_aux X Y).1
    funext x
    obtain ⟨v, rfl⟩ := hs x
    exact (hg.2 v).trans (he v).symm

end HodgeLean.Foundations.AnalyticAlbanese.Realization
