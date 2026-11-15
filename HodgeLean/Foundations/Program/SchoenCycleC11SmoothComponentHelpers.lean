import HodgeLean.Foundations.Program.SchoenCycleC11IntegralHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11ComponentHelpers
import HodgeLean.Foundations.Mathlib.ZmtIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Smooth complex schemes have integral affine neighbourhoods at every scheme point.
Source: AlgebraicGeometry.zmtiso_normal_of_smooth and noetherian localization kernels. -/
theorem s2e_c11_smooth_integral_affine_neighbourhood
    (X : Over (Spec ↧ℂ)) [Smooth X.hom] (x : X.left) :
    ∃ U : X.left.Opens, x ∈ U ∧ IsAffineOpen U ∧ IsIntegral U.toScheme := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let R := Γ(X.left, U)
  let S := X.left.presheaf.stalk x
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let p := hU.primeIdealOf ⟨x, hx⟩
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : Algebra R S := TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨x, hx⟩
  letI : IsLocalization.AtPrime S p.asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  letI : IsDomain S := (zmtiso_normal_of_smooth X.left X.hom x).1
  obtain ⟨f, hf, hdom⟩ := s2e_c11_domain_principal_neighbourhood (S := S) p.asIdeal
  let V := X.left.basicOpen f
  have hV : IsAffineOpen V := hU.basicOpen f
  have hxV : x ∈ V := by
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.left.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hf
    change hU.fromSpec p ∈ X.left.basicOpen f at hp
    have he : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
    rw [he] at hp
    exact hp
  letI := hdom
  letI := hU.isLocalization_basicOpen f
  let e : Γ(X.left, V) ≃ₐ[R] Localization.Away f :=
    IsLocalization.algEquiv (Submonoid.powers f) _ _
  letI : IsDomain Γ(X.left, V) := e.toRingEquiv.toMulEquiv.isDomain
  refine ⟨V, hxV, hV, ?_⟩
  exact IsIntegral.of_isIso hV.isoSpec.inv

/-- Analytic clopen subsets of smooth complex schemes are algebraic clopen subsets.
Source: Smooth integral affine neighbourhoods and ComplexPoint.connectedSpace. -/
theorem s2e_c11_smooth_clopen_preimage
    (X : Over (Spec ↧ℂ)) [Smooth X.hom] (A : Set (Point ℂ X)) (hA : IsClopen A) :
    ∃ U : X.left.Opens, IsClosed (U : Set X.left) ∧
      Point.underlying ⁻¹' (U : Set X.left) = A := by
  choose U hmem hAffine hIntegral using fun x : X.left =>
    s2e_c11_smooth_integral_affine_neighbourhood X x
  exact s2e_c11_smooth_clopen_of_integral_affine_cover X U
    (fun p => ⟨p.underlying, hmem p.underlying⟩) hIntegral hAffine A hA

end HodgeLean.Foundations.Program
