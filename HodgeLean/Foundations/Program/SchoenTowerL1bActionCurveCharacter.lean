import HodgeLean.Foundations.Program.SchoenTowerL1bActionCharacter

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two normalized scalar-preserving expansions of the actual smooth curve
stalk assign the same scalar to a fixed-point pullback. -/
theorem s2v_l1b_action_curve_character_independent
    (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (f : Y ⟶ Y) (p : ComplexPoint Y) (hp : f.left p.underlying = p.underlying)
    (ι κ : Y.left.presheaf.stalk p.underlying →+* PowerSeries ℂ)
    (hι : Function.Injective ι)
    (hXι : ∃ u, ι u = PowerSeries.X) (hXκ : ∃ v, κ v = PowerSeries.X)
    (hCι : ∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p.underlying c) =
      PowerSeries.C c)
    (hCκ : ∀ c : ℂ, κ (HodgeLean.Foundations.Curves.stalkC p.underlying c) =
      PowerSeries.C c)
    (ζ η : ℂ)
    (hactι : ∀ r, ι (s2e_fixed_point_stalkPullback Y.left f.left p.underlying hp r) =
      PowerSeries.rescale ζ (ι r))
    (hactκ : ∀ r, κ (s2e_fixed_point_stalkPullback Y.left f.left p.underlying hp r) =
      PowerSeries.rescale η (κ r)) : ζ = η := by
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    simpa only [hdimY] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Y.left) Y.hom)
  let R := Y.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  letI : IsDiscreteValuationRing R := s2e_smooth_curve_point_stalk_dvr Y p
  let φ : R →ₐ[ℂ] PowerSeries ℂ := { toRingHom := ι, commutes' := hCι }
  let ψ : R →ₐ[ℂ] PowerSeries ℂ := { toRingHom := κ, commutes' := hCκ }
  obtain ⟨u, hu⟩ := hXι
  obtain ⟨v, hv⟩ := hXκ
  exact s2v_l1b_action_character_independent φ ψ hι u v hu hv
    (s2e_fixed_point_stalkPullback Y.left f.left p.underlying hp) ζ η hactι hactκ

end HodgeLean.Foundations.Program
