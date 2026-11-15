import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNAffineIdealMap
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNChartComparisonTransport
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison

/-! # Native ideal comparison using the original open-section rings -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Natural ideal tensors over the original open-section rings determine
the restriction of the original global ideal comparison. The coefficient
map remains `appLE`, without replacing it by an unrelated algebra map.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem paired_conormal_original_open_ideal_map_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f)
    (U : W.affineOpens) (V : W'.affineOpens) (hle : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(W, U) Γ(W', V) := (f.appLE U.1 V.1 hle).hom.toAlgebra
    ∀ eI : (Γ(W', V) ⊗[Γ(W, U)] RingHom.ker (i.app U.1).hom) ≃ₗ[Γ(W', V)]
        RingHom.ker (i'.app V.1).hom,
      (∀ x : RingHom.ker (i.app U.1).hom,
        (eI (1 ⊗ₜ[Γ(W, U)] x)).val = (f.appLE U.1 V.1 hle).hom x.val) →
      IsIso ((Scheme.Modules.pullback V.1.ι).map (idealPullbackMap i i' f g sq.w)) := by
  letI : Algebra Γ(W, U) Γ(W', V) := (f.appLE U.1 V.1 hle).hom.toAlgebra
  intro eI hvalue
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
  let iΓ := Spec.map (i.app U.1)
  let iΓ' := Spec.map (i'.app V.1)
  let fΓ := Spec.map (f.appLE U.1 V.1 hle)
  let gΓ := Spec.map (g.appLE (i ⁻¹ᵁ U.1) (i' ⁻¹ᵁ V.1) hpre)
  have h₀ : (i ⁻¹ᵁ U.1).toSpecΓ ≫ iΓ = (i ∣_ U.1) ≫ U.1.toSpecΓ :=
    Scheme.Opens.toSpecΓ_naturality i U.1
  have h₁ : (i' ⁻¹ᵁ V.1).toSpecΓ ≫ iΓ' = (i' ∣_ V.1) ≫ V.1.toSpecΓ :=
    Scheme.Opens.toSpecΓ_naturality i' V.1
  have hf : V.1.toSpecΓ ≫ fΓ = fU ≫ U.1.toSpecΓ :=
    Scheme.Opens.toSpecΓ_SpecMap_appLE f U.1 V.1 hle
  have hg : (i' ⁻¹ᵁ V.1).toSpecΓ ≫ gΓ = gU ≫ (i ⁻¹ᵁ U.1).toSpecΓ :=
    Scheme.Opens.toSpecΓ_SpecMap_appLE g _ _ hpre
  have sqΓ : IsPullback gΓ iΓ' iΓ fΓ := by
    exact sqU.of_iso (V.2.preimage i').isoSpec (U.2.preimage i).isoSpec
      V.2.isoSpec U.2.isoSpec hg.symm h₁.symm h₀.symm hf.symm
  haveI : IsIso U.1.toSpecΓ := by change IsIso U.2.isoSpec.hom; infer_instance
  haveI : IsIso V.1.toSpecΓ := by change IsIso V.2.isoSpec.hom; infer_instance
  haveI : IsIso (i ⁻¹ᵁ U.1).toSpecΓ := by
    change IsIso (U.2.preimage i).isoSpec.hom; infer_instance
  haveI : IsIso (i' ⁻¹ᵁ V.1).toSpecΓ := by
    change IsIso (V.2.preimage i').isoSpec.hom; infer_instance
  haveI : IsIso (idealPullbackMap iΓ iΓ' fΓ gΓ sqΓ.w) :=
    paired_conormal_affine_ideal_map_isIso Γ(Q, i ⁻¹ᵁ U.1) Γ(Q', i' ⁻¹ᵁ V.1)
      (i.app U.1) (i'.app V.1) (g.appLE _ _ hpre) sqΓ.w eI hvalue
  haveI : IsIso (idealPullbackMap iΓ (i ∣_ U.1) U.1.toSpecΓ (i ⁻¹ᵁ U.1).toSpecΓ h₀) :=
    idealPullbackMap_isIso_of_isIso _ _ _ _ h₀
  haveI : IsIso (idealPullbackMap iΓ' (i' ∣_ V.1) V.1.toSpecΓ (i' ⁻¹ᵁ V.1).toSpecΓ h₁) :=
    idealPullbackMap_isIso_of_isIso _ _ _ _ h₁
  have hOld : (gU ≫ (i ⁻¹ᵁ U.1).toSpecΓ) ≫ iΓ = (i' ∣_ V.1) ≫ (fU ≫ U.1.toSpecΓ) := by
    rw [Category.assoc, h₀, ← Category.assoc, sqU.w, Category.assoc]
  have hNew : ((i' ⁻¹ᵁ V.1).toSpecΓ ≫ gΓ) ≫ iΓ =
      (i' ∣_ V.1) ≫ (V.1.toSpecΓ ≫ fΓ) := by
    rw [Category.assoc, sqΓ.w, ← Category.assoc, h₁, Category.assoc]
  have hn := idealPullbackMap_comp_isIso iΓ iΓ' (i' ∣_ V.1) fΓ V.1.toSpecΓ gΓ
    (i' ⁻¹ᵁ V.1).toSpecΓ sqΓ.w h₁ hNew
  haveI : IsIso (idealPullbackMap iΓ (i' ∣_ V.1) (fU ≫ U.1.toSpecΓ)
      (gU ≫ (i ⁻¹ᵁ U.1).toSpecΓ) hOld) :=
    (idealPullbackMap_isIso_congr _ _ _ _ hf.symm _ _ hOld hNew).mpr hn
  haveI : IsIso (idealPullbackMap (i ∣_ U.1) (i' ∣_ V.1) fU gU sqU.w) :=
    idealPullbackMap_isIso_of_comp iΓ (i ∣_ U.1) (i' ∣_ V.1)
      U.1.toSpecΓ fU (i ⁻¹ᵁ U.1).toSpecΓ gU h₀ sqU.w hOld
  haveI := idealPullbackMap_open_isIso i U.1
  haveI := idealPullbackMap_open_isIso i' V.1
  exact paired_conormal_chart_ideal_map_isIso i i' (i ∣_ U.1) (i' ∣_ V.1)
    f g sq.w fU gU sqU.w U.1.ι V.1.ι (i ⁻¹ᵁ U.1).ι (i' ⁻¹ᵁ V.1).ι
    (morphismRestrict_ι i U.1).symm (morphismRestrict_ι i' V.1).symm
    (f.resLE_comp_ι hle)

#print axioms paired_conormal_original_open_ideal_map_isIso
end HodgeLean.Foundations.Program.G32Native
