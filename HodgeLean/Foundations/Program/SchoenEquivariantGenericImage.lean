import HodgeLean.Foundations.Program.SchoenProjAction
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- The generic image of an integral equivariant source is fixed by the ambient actual Proj action. -/
theorem s2_equivariantProj_genericImage_fixed {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (X : Scheme.{0}) [IsIntegral X] (ρ : G →* Aut X) (f : X ⟶ Proj 𝒜)
    (he : ∀ g : G, (ρ g).asIso.hom ≫ f = f ≫ (s2_projAction 𝒜 hgrade g).asIso.hom) :
    ∀ g : G, (s2_projAction 𝒜 hgrade g).asIso.hom (f (genericPoint X)) = f (genericPoint X) := by
  intro g
  have h := congrArg (fun m : X ⟶ Proj 𝒜 => m (genericPoint X)) (he g)
  change f ((ρ g).asIso.hom (genericPoint X)) =
    (s2_projAction 𝒜 hgrade g).asIso.hom (f (genericPoint X)) at h
  rw [genericPoint_eq_of_isOpenImmersion] at h
  exact h.symm

/-- A fixed actual Proj point defines a homogeneous prime preserved by the original ring action. -/
theorem s2_fixedProjPoint_ideal_invariant {A G : Type} [CommRing A]
    [Group G] [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (p : ProjectiveSpectrum 𝒜)
    (hfix : ∀ g : G, (s2_projAction 𝒜 hgrade g).asIso.hom p = p) :
    ∀ g : G, ∀ a ∈ p.asHomogeneousIdeal.toIdeal, g • a ∈ p.asHomogeneousIdeal.toIdeal := by
  intro g a ha
  have hp := hfix g⁻¹
  change s2_projActionMap 𝒜 hgrade (g⁻¹)⁻¹ p = p at hp
  rw [inv_inv] at hp
  have hi := congrArg (fun q : Proj 𝒜 => q.asHomogeneousIdeal.toIdeal) hp
  change p.asHomogeneousIdeal.toIdeal.comap (s2_gradedActionHom 𝒜 hgrade g).toRingHom =
    p.asHomogeneousIdeal.toIdeal at hi
  have ha' : a ∈ p.asHomogeneousIdeal.toIdeal.comap (s2_gradedActionHom 𝒜 hgrade g).toRingHom := by
    rwa [hi]
  exact ha'

end HodgeLean.Foundations.Program
