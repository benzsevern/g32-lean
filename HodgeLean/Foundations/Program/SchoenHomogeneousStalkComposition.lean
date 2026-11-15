import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- Homogeneous localization at prime ideals respects composition of actual graded maps. -/
theorem s2_homogeneousLocalRingHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) (𝒞 : ℕ → AddSubgroup C)
    [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (I : Ideal A) (J : Ideal B) (P : Ideal C) [I.IsPrime] [J.IsPrime] [P.IsPrime]
    (hIJ : I = J.comap f) (hJP : J = P.comap g) (hIP : I = P.comap (g.comp f)) :
    localRingHom (g.comp f) I P hIP =
      (localRingHom g J P hJP).comp (localRingHom f I J hIJ) := by
  exact HomogeneousLocalization.map_comp _ _

end HodgeLean.Foundations.Program
