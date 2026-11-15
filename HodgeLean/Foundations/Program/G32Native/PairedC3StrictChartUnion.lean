import HodgeLean.Foundations.Program.G32Native.PairedC3ChartClosure
import HodgeLean.Foundations.Program.SchoenTowerL1bStrictTransformChart
import HodgeLean.Foundations.Program.SchoenCycleC1AffineComapSections

/-! # The actual reduced strict component and total transform on a Rees chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The reduced strict component in a supplied Rees chart has the
translated-ratio ideal in the original affine section ring.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_strict_rees_sections
    {X Y : Scheme} (σ : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ σ ⁻¹ᵁ U.1)
    (u v a : Γ(Y, U)) (t : Γ(X, V))
    [(D.ideal U).IsPrime]
    (hs : Function.Surjective (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t))
    (hk : RingHom.ker (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t) =
      Ideal.span {C v - Polynomial.X * C u})
    (ha : v - a * u ∈ D.ideal U) (hu : u ∉ D.ideal U)
    (hK : (K.comap σ).ideal V = Ideal.span {(σ.appLE U.1 V.1 hVU).hom u}) :
    (s2c_strictTransform σ D K).ideal V =
      (D.comap σ).ideal V ⊔ Ideal.span {t - (σ.appLE U.1 V.1 hVU).hom a} := by
  rw [s2v_l1b_strictTransform_affine_formula, hK, PrimeSpectrum.zeroLocus_span,
    s2e_c1_affine_comap_appLE σ D U V hVU]
  exact paired_c3_rees_strict_ideal _ u v a t (D.ideal U) hs hk ha hu

#print axioms paired_c3_strict_rees_sections
/-- On each supplied Rees chart the actual total-transform ideal is the
intersection of the reduced strict component and the residual component.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_strict_rees_union
    {X Y : Scheme} (σ : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ σ ⁻¹ᵁ U.1)
    (u v a : Γ(Y, U)) (t : Γ(X, V))
    [(D.ideal U).IsPrime]
    (hs : Function.Surjective (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t))
    (hk : RingHom.ker (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t) =
      Ideal.span {C v - Polynomial.X * C u})
    (ha : v - a * u ∈ D.ideal U) (hu : u ∉ D.ideal U)
    (hK : (K.comap σ).ideal V = Ideal.span {(σ.appLE U.1 V.1 hVU).hom u}) :
    (D.comap σ).ideal V = (s2c_strictTransform σ D K).ideal V ⊓
      ((K.comap σ).ideal V ⊔ (D.comap σ).ideal V) := by
  rw [paired_c3_strict_rees_sections σ D K U V hVU u v a t hs hk ha hu hK,
    hK, s2e_c1_affine_comap_appLE σ D U V hVU]
  apply paired_c3_direct_chart_union _ u v a t (D.ideal U) hs hk ha
  intro x hx
  exact (Ideal.IsPrime.mem_or_mem inferInstance hx).resolve_left hu

#print axioms paired_c3_strict_rees_union
end HodgeLean.Foundations.Program.G32Native
