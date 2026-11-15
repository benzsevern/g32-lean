import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNAffineReesMap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNChartComparisonTransport
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison

/-! # Restricting the original natural ideal map to a supplied Rees neighborhood -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- A binomial presentation on actual ambient affine opens makes the
restriction of the original ideal comparison invertible. The affine
diagram is obtained by restricting the supplied global cartesian square.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_conormal_open_rees_ideal_map_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f)
    (U : W.affineOpens) (V : W'.affineOpens) (hle : V.1 ≤ f ⁻¹ᵁ U.1)
    (u v a : Γ(U.1.toScheme, ⊤)) (t : Γ(V.1.toScheme, ⊤))
    (hs : Function.Surjective (eval₂RingHom (f.resLE U.1 V.1 hle).appTop.hom t))
    (hk : RingHom.ker (eval₂RingHom (f.resLE U.1 V.1 hle).appTop.hom t) =
      Ideal.span {C u - X * C v})
    (ha : u - a * v ∈ RingHom.ker (i ∣_ U.1).appTop.hom)
    (hv : IsSMulRegular (Γ(U.1.toScheme, ⊤) ⧸ RingHom.ker (i ∣_ U.1).appTop.hom) v) :
    IsIso ((Scheme.Modules.pullback V.1.ι).map (idealPullbackMap i i' f g sq.w)) := by
  have hpre : i' ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ (i ⁻¹ᵁ U.1) := by
    intro x hx
    change i (g x) ∈ U.1
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hle hx
  let gU := g.resLE (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ V.1) hpre
  let fU := f.resLE U.1 V.1 hle
  have sqU : IsPullback gU (i' ∣_ V.1) (i ∣_ U.1) fU := by
    have H := Scheme.Hom.isPullback_resLE sq hle (le_refl (i ⁻¹ᵁ U.1))
      (show i' ⁻¹ᵁ V.1 = g ⁻¹ᵁ (i ⁻¹ᵁ U.1) ⊓ i' ⁻¹ᵁ V.1 from
        (inf_eq_right.mpr hpre).symm)
    simpa only [gU, fU, Scheme.Hom.resLE_eq_morphismRestrict] using H
  letI : IsAffine U.1.toScheme := U.2
  letI : IsAffine V.1.toScheme := V.2
  haveI : IsIso (idealPullbackMap (i ∣_ U.1) (i' ∣_ V.1) fU gU sqU.w) :=
    paired_conormal_affine_rees_ideal_map_isIso (i ∣_ U.1) (i' ∣_ V.1)
      fU gU sqU u v a t hs hk ha hv
  haveI := idealPullbackMap_open_isIso i U.1
  haveI := idealPullbackMap_open_isIso i' V.1
  exact paired_conormal_chart_ideal_map_isIso i i' (i ∣_ U.1) (i' ∣_ V.1)
    f g sq.w fU gU sqU.w U.1.ι V.1.ι (i ⁻¹ᵁ U.1).ι (i' ⁻¹ᵁ V.1).ι
    (morphismRestrict_ι i U.1).symm (morphismRestrict_ι i' V.1).symm
    (f.resLE_comp_ι hle)

#print axioms paired_conormal_open_rees_ideal_map_isIso
end HodgeLean.Foundations.Program.G32Native
