import HodgeLean.Foundations.Program.G32Native.PairedC3StrictChartUnion
import HodgeLean.Foundations.Program.G32Native.PairedC3IntegralSliceIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3ChartCentre

/-! # The direct chart union for an integral retained slice -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- Equal proper branch restrictions on an integral slice suffice for the
actual total-transform union on a supplied Rees chart. No adapted slice
generators enter the calculation.
Source: Hartshorne, Algebraic Geometry, II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_integral_chart_union
    {Q X Y : Scheme} [IsIntegral Q] (i : Q ⟶ Y) [IsClosedImmersion i]
    (σ : X ⟶ Y) (D E : Y.IdealSheafData)
    (heq : D.comap i = E.comap i) (hproper : (D.comap i).support ≠ ⊤)
    (U : Y.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (V : X.affineOpens) (hVU : V.1 ≤ σ ⁻¹ᵁ U.1)
    (u v : Γ(Y, U)) (t : Γ(X, V))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v})
    (hrel : (σ.appLE U.1 V.1 hVU).hom v = t * (σ.appLE U.1 V.1 hVU).hom u)
    (hs : Function.Surjective (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t))
    (hk : RingHom.ker (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t) =
      Ideal.span {C v - Polynomial.X * C u}) :
    (i.ker.comap σ).ideal V =
      (HodgeLean.Foundations.Program.s2c_strictTransform σ i.ker (D ⊔ E)).ideal V ⊓
        (((D ⊔ E).comap σ).ideal V ⊔ (i.ker.comap σ).ideal V) := by
  letI := paired_c3_integral_slice_prime i U
  obtain ⟨a, ha⟩ := paired_c3_affine_slice_coefficient i E D heq.symm U v u hv hu
  have haI : v - a * u ∈ i.ker.ideal U := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    exact ha
  have hcancel := paired_c3_integral_slice_cancel i D hproper U u hu
  have hnon : u ∉ i.ker.ideal U := by
    intro h
    have hone : (1 : Γ(Y, U)) ∈ i.ker.ideal U := hcancel 1 (by rwa [mul_one])
    exact (paired_c3_integral_slice_prime i U).ne_top ((i.ker.ideal U).eq_top_iff_one.mpr hone)
  exact paired_c3_strict_rees_union σ i.ker (D ⊔ E) U V hVU u v a t hs hk haI hnon
    (paired_c3_chart_centre σ D E U V hVU u v t hu hv hrel)

#print axioms paired_c3_integral_chart_union
end HodgeLean.Foundations.Program.G32Native
