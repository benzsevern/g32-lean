import HodgeLean.Foundations.Program.G32Native.PairedC3StrictChartUnion
import HodgeLean.Foundations.Program.G32Native.PairedC3IntegralSliceIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3ChartCentre
import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedResidualEquations

/-! # The actual strict slice ideal in supplied residual coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The marked intersection in the actual residual quotient has equation
`t - α`. The strict component is calculated from its reduced closure;
its equation is not an input. -/
theorem pairedC3_supplied_strict_marked_ideal
    {Q X Y : Scheme} [IsIntegral Q] (i : Q ⟶ Y) [IsClosedImmersion i]
    (σ : X ⟶ Y) (D E : Y.IdealSheafData)
    (hproper : (D.comap i).support ≠ ⊤)
    (U : Y.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (V : X.affineOpens) (hVU : V.1 ≤ σ ⁻¹ᵁ U.1)
    (u v α : Γ(Y, U)) (t : Γ(X, V))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v})
    (hrel : (σ.appLE U.1 V.1 hVU).hom v = t * (σ.appLE U.1 V.1 hVU).hom u)
    (hs : Function.Surjective (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t))
    (hk : RingHom.ker (eval₂RingHom (σ.appLE U.1 V.1 hVU).hom t) =
      Ideal.span {C v - Polynomial.X * C u})
    (hα : (i.app U.1).hom (v - α * u) = 0) :
    let M := ((D ⊔ E) ⊔ i.ker).comap σ
    let q := Ideal.Quotient.mk (M.ideal V)
    Ideal.map q ((s2c_strictTransform σ i.ker (D ⊔ E)).ideal V) =
      Ideal.span {q t - q ((σ.appLE U.1 V.1 hVU).hom α)} := by
  dsimp only
  let M := ((D ⊔ E) ⊔ i.ker).comap σ
  let q := Ideal.Quotient.mk (M.ideal V)
  letI := paired_c3_integral_slice_prime i U
  have hαI : v - α * u ∈ i.ker.ideal U := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    exact hα
  have hcancel := paired_c3_integral_slice_cancel i D hproper U u hu
  have hnon : u ∉ i.ker.ideal U := by
    intro h
    have h1 : (1 : Γ(Y, U)) ∈ i.ker.ideal U := hcancel 1 (by rwa [mul_one])
    exact (paired_c3_integral_slice_prime i U).ne_top
      ((i.ker.ideal U).eq_top_iff_one.mpr h1)
  have hstrict := paired_c3_strict_rees_sections σ i.ker (D ⊔ E) U V hVU
    u v α t hs hk hαI hnon (paired_c3_chart_centre σ D E U V hVU u v t hu hv hrel)
  have hzero : Ideal.map q ((i.ker.comap σ).ideal V) = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker q).mpr
    rw [Ideal.mk_ker]
    exact (Scheme.IdealSheafData.comap_mono σ le_sup_right) V
  change Ideal.map q _ = _
  rw [hstrict, Ideal.map_sup, hzero, bot_sup_eq, Ideal.map_span, Set.image_singleton,
    map_sub]

#print axioms pairedC3_supplied_strict_marked_ideal
end HodgeLean.Foundations.Program.G32Native
