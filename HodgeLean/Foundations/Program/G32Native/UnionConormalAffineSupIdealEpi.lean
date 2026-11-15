import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineIdealEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineIntersectionKernel
import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealEpiTransport
import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineSchemeComparison

/-! # Epic ideal comparison from the affine intersection equation -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- The kernel supremum identity makes ideal comparison epic on affine schemes. -/
lemma unionConormal_idealMap_epi_of_affine_sup
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffine W] [IsAffine W']
    (f : W' ⟶ W) [IsClosedImmersion f] (g : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (hsup : (i' ≫ f).ker = i.ker ⊔ f.ker) :
    Epi (idealPullbackMap i i' f g h) := by
  have : IsAffine Q := isAffine_of_isAffineHom i
  have : IsAffine Q' := isAffine_of_isAffineHom i'
  let iΓ := Spec.map i.appTop
  let iΓ' := Spec.map i'.appTop
  let fΓ := Spec.map f.appTop
  let gΓ := Spec.map g.appTop
  have hΓsq : gΓ ≫ iΓ = iΓ' ≫ fΓ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, h]
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := f.appTop.hom.toAlgebra
  have hr : Function.Surjective f.appTop.hom := f.app_surjective ⊤ (isAffineOpen_top W)
  have hk : RingHom.ker (i'.appTop.hom.comp f.appTop.hom) =
      RingHom.ker i.appTop.hom ⊔ RingHom.ker f.appTop.hom := by
    have he := unionConormal_affine_kernel_sup (i' ≫ f) i f hsup
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using he
  have hker := unionConormal_intersection_kernel_map i.appTop.hom f.appTop.hom
    i'.appTop.hom hr hk
  have hΓ : Epi (idealPullbackMap iΓ iΓ' fΓ gΓ hΓsq) :=
    unionConormal_affineIdeal_epi_of_kernel_eq Γ(Q, ⊤) Γ(Q', ⊤)
      i.appTop i'.appTop g.appTop hΓsq hker
  have h₀ : Q.toSpecΓ ≫ iΓ = i ≫ W.toSpecΓ := (Scheme.toSpecΓ_naturality i).symm
  have h₁ : Q'.toSpecΓ ≫ iΓ' = i' ≫ W'.toSpecΓ := (Scheme.toSpecΓ_naturality i').symm
  have hOld : (g ≫ Q.toSpecΓ) ≫ iΓ = i' ≫ (f ≫ W.toSpecΓ) := by
    rw [Category.assoc, h₀, ← Category.assoc, h, Category.assoc]
  have hNew : (Q'.toSpecΓ ≫ gΓ) ≫ iΓ = i' ≫ (W'.toSpecΓ ≫ fΓ) := by
    rw [Category.assoc, hΓsq, ← Category.assoc, h₁, Category.assoc]
  have : IsIso (idealPullbackMap iΓ i W.toSpecΓ Q.toSpecΓ h₀) :=
    idealPullbackMap_isIso_of_isIso iΓ i W.toSpecΓ Q.toSpecΓ h₀
  have : IsIso (idealPullbackMap iΓ' i' W'.toSpecΓ Q'.toSpecΓ h₁) :=
    idealPullbackMap_isIso_of_isIso iΓ' i' W'.toSpecΓ Q'.toSpecΓ h₁
  have hn : Epi (idealPullbackMap iΓ i' (W'.toSpecΓ ≫ fΓ) (Q'.toSpecΓ ≫ gΓ) hNew) :=
    unionConormal_idealMap_comp_epi iΓ iΓ' i' fΓ W'.toSpecΓ gΓ Q'.toSpecΓ hΓsq h₁ hNew
  have : Epi (idealPullbackMap iΓ i' (f ≫ W.toSpecΓ) (g ≫ Q.toSpecΓ) hOld) :=
    unionConormal_idealMap_epi_congr iΓ i' (W'.toSpecΓ ≫ fΓ) (f ≫ W.toSpecΓ)
      (Scheme.toSpecΓ_naturality f).symm (Q'.toSpecΓ ≫ gΓ) (g ≫ Q.toSpecΓ) hNew hOld
  exact unionConormal_idealMap_epi_of_comp iΓ i i' W.toSpecΓ f Q.toSpecΓ g h₀ h hOld

end HodgeLean.Foundations.Program.G32Native
