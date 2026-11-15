import HodgeLean.Adapters.NormalConeB4aClassComponentDimension

/-! # Component dimensions from a single ambient affine chart

Route: compute the component quotient ring inside a standard-smooth affine
neighborhood of the specified point. No constant ambient dimension is needed
outside that neighborhood.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
attribute [local instance] AlgebraicGeometry.overSpecAlgebra

/-- A standard-smooth affine neighborhood determines the intrinsic coheight
of a closed point of the reduced component. -/
theorem a3b4a_classComponent_closedPoint_coheight_local
    (X : Over (Spec (CommRingCat.of ℂ))) {d p : ℕ} [Smooth X.hom]
    (x : X.left) (z : cycleComponent X.left x)
    (hx : Order.coheight x = p) (hz : IsClosed {z})
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hyU : cycleComponentι X.left x z ∈ U)
    (hstandard : (X.hom.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension d) :
    Order.coheight z = d - p := by
  let c : cycleComponent X.left x ⟶ X.left := cycleComponentι X.left x
  let y : X.left := c z
  have hyx : y ≤ x := (cycleComponentOrderIsoIic X.left x z).2
  have hxU : x ∈ U := by
    rw [Scheme.le_iff_specializes] at hyx
    exact hyx.mem_open U.isOpen hyU
  let W : (cycleComponent X.left x).Opens := c ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage c
  have hzW : z ∈ W := hyU
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  let xu : U.toScheme := ⟨x, hxU⟩
  let zw : W.toScheme := ⟨z, hzW⟩
  let q : Γ(X.left, U) →+* Γ(cycleComponent X.left x, W) :=
    (c.app U).hom
  have hqsurj : Function.Surjective q := c.app_surjective U hU
  let P : Ideal Γ(X.left, U) :=
    (hU.primeIdealOf xu).asIdeal
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X.left) ⟨closure {x}, isClosed_closure⟩
  have hsingleton : hU.fromSpec ⁻¹' ({x} : Set X.left) =
      ({hU.primeIdealOf xu} : Set (Spec Γ(X.left, U))) := by
    ext Q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hQ ↦ hU.fromSpec.isOpenEmbedding.injective
      (hQ.trans (hU.fromSpec_primeIdealOf xu).symm), ?_⟩
    rintro rfl
    exact hU.fromSpec_primeIdealOf xu
  have hpreimage : hU.fromSpec ⁻¹' closure {x} =
      closure {hU.primeIdealOf xu} := by
    have hclosure := congrArg
      (fun T : Set (Spec Γ(X.left, U)) ↦ closure T) hsingleton
    exact (hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous ({x} : Set X.left)).trans hclosure
  have hideal : I.ideal ⟨U, hU⟩ = P := by
    change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure {x}) = P
    erw [hpreimage, PrimeSpectrum.vanishingIdeal_closure,
      PrimeSpectrum.vanishingIdeal_singleton]
  have hqker : RingHom.ker q = P := by
    change RingHom.ker (c.app U).hom = P
    rw [← Scheme.Hom.ker_apply c ⟨U, hU⟩]
    calc
      c.ker.ideal ⟨U, hU⟩ = I.ideal ⟨U, hU⟩ := by
        rw [show c = I.subschemeι from rfl]
        exact congrArg (fun J : X.left.IdealSheafData ↦ J.ideal ⟨U, hU⟩)
          I.ker_subschemeι
      _ = P := hideal
  have hPheight : P.height = p := by
    calc
      P.height = Order.coheight xu := by
        change (hU.primeIdealOf xu).asIdeal.height = Order.coheight xu
        exact hU.primeIdealOf_height_eq_coheight _
      _ = Order.coheight x := by
        have h := coheight_eq_of_isOpenImmersion
          (x := xu) U.ι
        simpa [xu] using h.symm
      _ = p := hx
  have hquotient : ringKrullDim (Γ(X.left, U) ⧸ P) = d - p :=
    (algebraMap_isStandardSmoothOfRelativeDimension
      (d := d) X hstandard).ringKrullDim_quotient_eq_sub_complex
        P hPheight
  have hringW : ringKrullDim Γ(cycleComponent X.left x, W) = d - p := by
    calc
      ringKrullDim Γ(cycleComponent X.left x, W) =
          ringKrullDim (Γ(X.left, U) ⧸ RingHom.ker q) :=
        (ringKrullDim_eq_of_ringEquiv
          (RingHom.quotientKerEquivOfSurjective hqsurj)).symm
      _ = ringKrullDim (Γ(X.left, U) ⧸ P) := by rw [hqker]
      _ = d - p := hquotient
  let s : cycleComponent X.left x ⟶ Spec ↧ℂ := c ≫ X.hom
  let : Algebra ℂ Γ(cycleComponent X.left x, W) :=
    overSpecAlgebra (Over.mk s) W
  let : Algebra.FiniteType ℂ Γ(cycleComponent X.left x, W) := by
    rw [← RingHom.finiteType_algebraMap]
    change (algebraMap ℂ Γ(cycleComponent X.left x, W)).FiniteType
    apply (s.finiteType_appLE (isAffineOpen_top (Spec ↧ℂ)) hW (by simp)).comp
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv.surjective
  let Q : Ideal Γ(cycleComponent X.left x, W) :=
    (hW.primeIdealOf zw).asIdeal
  have hQmax : Q.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed
    zw hz
  have hQheight : (↑Q.height : WithBot ℕ∞) = d - p := by
    rw [Algebra.FiniteType.height_eq_ringKrullDim_of_isMaximal
      (k := ℂ) Q, hringW]
  have hQcoheight : Q.height = Order.coheight z := by
    calc
      Q.height = Order.coheight zw := by
        change (hW.primeIdealOf zw).asIdeal.height = Order.coheight zw
        exact hW.primeIdealOf_height_eq_coheight _
      _ = Order.coheight z := by
        have h := coheight_eq_of_isOpenImmersion
          (x := zw) W.ι
        simpa [zw] using h.symm
  apply WithBot.coe_injective
  rw [← hQcoheight]
  exact hQheight

end HodgeLean.Adapters
