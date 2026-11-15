import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineSchemeFirstArrow
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineFirstIdealArrow
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineLastObject
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineKernelInf
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineIntersectionKernel
import HodgeLean.Foundations.Program.G32Native.UnionConormalRingExact
import HodgeLean.Foundations.Program.G32Native.UnionConormalRingNoetherian
import HodgeLean.Foundations.Program.G32Native.UnionConormalTildeFirstArrowExact

/-! # Recognizing affine union conormal exactness from the first arrow -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Affine first-arrow coordinates and the actual last object determine exactness. -/
lemma unionConormal_affine_exact_recognition
    {V T T₁ T₂ Z : Scheme.{0}}
    [IsAffine V] [IsAffine T] [IsAffine T₁] [IsAffine T₂] [IsAffine Z]
    [IsNoetherianRing Γ(V, ⊤)]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    (a : T₁ ⟶ T) (s₁ : Z ⟶ T₁) (s₂ : Z ⟶ T₂)
    [IsClosedImmersion t] [IsClosedImmersion t₁] [IsClosedImmersion t₂]
    [IsClosedImmersion s₂]
    (ha : a ≫ t = t₁) (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hunion : t.ker = t₁.ker ⊓ t₂.ker)
    (hinter : (s₁ ≫ t₁).ker = t₁.ker ⊔ t₂.ker)
    (S : ShortComplex (Spec Γ(T₁, ⊤)).Modules) [Epi S.g]
    (ef : Arrow.mk S.f ≅ Arrow.mk ((Scheme.Modules.pullback T₁.isoSpec.inv).map
      (unionConormalFirst t t₁ a ha)))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pullback T₁.isoSpec.inv).obj
      ((Scheme.Modules.pushforward s₁).obj (s2c_conormal s₂))) : S.Exact := by
  have hq := t₁.app_surjective ⊤ (isAffineOpen_top V)
  have hr := t₂.app_surjective ⊤ (isAffineOpen_top V)
  have hss := s₂.app_surjective ⊤ (isAffineOpen_top T₂)
  have hc : s₂.appTop.hom.comp t₂.appTop.hom = s₁.appTop.hom.comp t₁.appTop.hom := by
    change (t₂.appTop ≫ s₂.appTop).hom = (t₁.appTop ≫ s₁.appTop).hom
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hs]
  have hsup : RingHom.ker (s₂.appTop.hom.comp t₂.appTop.hom) =
      RingHom.ker t₁.appTop.hom ⊔ RingHom.ker t₂.appTop.hom := by
    change RingHom.ker (t₂.appTop ≫ s₂.appTop).hom = _
    rw [← Scheme.Hom.comp_appTop, ← hs]
    exact unionConormal_affine_kernel_sup (s₁ ≫ t₁) t₁ t₂ hinter
  have hK := unionConormal_intersection_kernel_map t₁.appTop.hom t₂.appTop.hom
    s₂.appTop.hom hr hsup
  haveI := unionConormalRingLast_isNoetherian t₁.appTop.hom t₂.appTop.hom
    s₂.appTop.hom s₁.appTop.hom hc hK hq hr hss
  let efirst := ef ≪≫ unionConormalAffineSchemeFirstArrowIso t t₁ a ha ≪≫
    unionConormalAffineFirstIdealArrowIso Γ(V, ⊤) Γ(T, ⊤) Γ(T₁, ⊤)
      t.appTop t₁.appTop a.appTop
      (by rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop, ha])
      (RingHom.ker t₂.appTop.hom) (unionConormal_affine_kernel_inf t t₁ t₂ hunion)
  exact unionConormal_tilde_exact_of_firstArrow Γ(T₁, ⊤) _ _ _ _
    (unionConormalRingLast t₁.appTop.hom t₂.appTop.hom s₂.appTop.hom s₁.appTop.hom hc hK)
    (unionConormalRingLast_exact t₁.appTop.hom t₂.appTop.hom
      s₂.appTop.hom s₁.appTop.hom hc hK hq hr hss)
    (unionConormalRingLast_surjective t₁.appTop.hom t₂.appTop.hom
      s₂.appTop.hom s₁.appTop.hom hc hK hr hss)
    S efirst (e₃ ≪≫ unionConormalAffineLastObjectIso s₁ s₂)

end HodgeLean.Foundations.Program.G32Native
