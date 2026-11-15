import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Equations vanishing off actual affine opens

Implication from the actual affine vanishing ideal to principal neighborhoods
inside a prescribed scheme open. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Membership in the vanishing ideal of the complement of an actual affine
open is exactly containment of the corresponding principal open.
Source: Hartshorne, Algebraic Geometry, II.2, affine vanishing ideals and principal opens. -/
theorem s2v_l1a_affine_open_vanishing_equation
    (X : Scheme) [IsAffine X] (W : X.Opens) (r : Γ(X, ⊤)) :
    r ∈ (Scheme.IdealSheafData.vanishingIdeal
      ⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩).ideal ⟨⊤, isAffineOpen_top X⟩ ↔
        X.basicOpen r ≤ W := by
  let hA := isAffineOpen_top X
  change r ∈ PrimeSpectrum.vanishingIdeal
    (hA.fromSpec ⁻¹' (W : Set X)ᶜ) ↔ X.basicOpen r ≤ W
  constructor
  · intro hr x hx
    by_contra hnot
    let y := hA.primeIdealOf ⟨x, trivial⟩
    have hfrom : hA.fromSpec y = x := hA.fromSpec_primeIdealOf ⟨x, trivial⟩
    have H := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr y
      (show hA.fromSpec y ∈ (W : Set X)ᶜ by rw [hfrom]; exact hnot)
    have hy : y ∈ PrimeSpectrum.basicOpen r := by
      rw [← hA.fromSpec_preimage_basicOpen]
      change hA.fromSpec y ∈ X.basicOpen r
      rw [hfrom]
      exact hx
    exact hy H
  · intro hsub
    rw [PrimeSpectrum.mem_vanishingIdeal]
    intro y hy
    by_contra hny
    have hyr : hA.fromSpec y ∈ X.basicOpen r := by
      change y ∈ hA.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hA.fromSpec_preimage_basicOpen]
      exact hny
    exact hy (hsub hyr)

end HodgeLean.Foundations.Program
