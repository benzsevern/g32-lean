import HodgeLean.Foundations.Program.SchoenTowerI2bChartIdeals
import Mathlib.AlgebraicGeometry.AffineScheme
import HodgeLean.Foundations.Program.SchoenCycleCartierCharts

/-! Coefficient opens on actual affine Cartier neighborhoods.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting a global section to its actual basic-open subscheme makes it invertible.
Source: the ringed-space basic-open unit criterion and the open restriction section isomorphism. -/
theorem s2v_i2b_basicOpen_inclusion_unit
    (X : Scheme) (a : Γ(X, ⊤)) :
    IsUnit ((X.basicOpen a).ι.appTop.hom a) := by
  let U := X.basicOpen a
  have hm : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ U.topIso.inv = U.ι.appTop := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, ← Functor.map_comp]
    congr 1
  have h := (X.toRingedSpace.isUnit_res_basicOpen a).map U.topIso.inv.hom
  change IsUnit ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ U.topIso.inv).hom a) at h
  rw [hm] at h
  exact h

/-- At each actual point, one of the two coefficients of a free selected ideal gives a basic-open chart.
Source: generation by the two coefficients and pullback of principal opens along the affine adjunction. -/
theorem s2v_i2b_invertible_ideal_coefficient_point_cover
    (X : Scheme) (I : Ideal Γ(X, ⊤)) (u v : Γ(X, ⊤))
    (hu : u ∈ I) (hv : v ∈ I) (hI : I = Ideal.span {u, v})
    (e : I ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen (e ⟨u, hu⟩) ∨ x ∈ X.basicOpen (e ⟨v, hv⟩) := by
  have hcover := s2v_l1b_invertible_ideal_basicOpen_cover I u v hu hv hI e
  have hmem : X.toSpecΓ x ∈
      PrimeSpectrum.basicOpen (e ⟨u, hu⟩) ⊔ PrimeSpectrum.basicOpen (e ⟨v, hv⟩) := by
    rw [hcover]
    trivial
  change x ∈ X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (e ⟨u, hu⟩) ∨
    x ∈ X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (e ⟨v, hv⟩) at hmem
  simpa only [Scheme.toSpecΓ_preimage_basicOpen] using hmem

/-- The rank-one test on an affine scheme persists on each actual basic-open subscheme.
Source: localization of a free Cartier ideal and transport to the open subscheme. -/
theorem s2v_i2b_cartier_free_on_basicOpen_source
    (X : Scheme) [IsAffine X] (I : X.IdealSheafData)
    (hfree : Nonempty ((I.ideal ⟨⊤, isAffineOpen_top X⟩) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)))
    (a : Γ(X, ⊤)) :
    Nonempty (((I.comap (X.basicOpen a).ι).ideal
      ⟨⊤, isAffineOpen_top (X.basicOpen a).toScheme⟩)
      ≃ₗ[Γ((X.basicOpen a).toScheme, ⊤)] Γ((X.basicOpen a).toScheme, ⊤)) := by
  apply s2e_cartier_free_on_open_subscheme I (X.basicOpen a)
  exact s2e_cartier_free_on_basicOpen I ⟨⊤, isAffineOpen_top X⟩ hfree a

end HodgeLean.Foundations.Program
