import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineCartesianIdealEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealEpiTransport
import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineSchemeComparison

/-! # Epic ideal comparison on affine schemes -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Cartesian squares of immersions with affine ambient schemes have epic
natural ideal comparison maps. -/
lemma unionConormal_idealMap_epi_of_isAffine
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffine W] [IsAffine W']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    Epi (idealPullbackMap i i' f g sq.w) := by
  have : IsAffine Q := isAffine_of_isAffineHom i
  have : IsAffine Q' := isAffine_of_isAffineHom i'
  let iΓ := Spec.map i.appTop
  let iΓ' := Spec.map i'.appTop
  let fΓ := Spec.map f.appTop
  let gΓ := Spec.map g.appTop
  have sqΓ : IsPullback gΓ iΓ' iΓ fΓ :=
    sq.of_iso Q'.isoSpec Q.isoSpec W'.isoSpec W.isoSpec
      (Scheme.isoSpec_hom_naturality g).symm
      (Scheme.isoSpec_hom_naturality i').symm
      (Scheme.isoSpec_hom_naturality i).symm
      (Scheme.isoSpec_hom_naturality f).symm
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := f.appTop.hom.toAlgebra
  have hΓ : Epi (idealPullbackMap iΓ iΓ' fΓ gΓ sqΓ.w) :=
    unionConormal_affineCartesianIdeal_epi Γ(Q, ⊤) Γ(Q', ⊤)
      i.appTop i'.appTop g.appTop sqΓ
      (i.app_surjective ⊤ (isAffineOpen_top W))
  have h₀ : Q.toSpecΓ ≫ iΓ = i ≫ W.toSpecΓ := (Scheme.toSpecΓ_naturality i).symm
  have h₁ : Q'.toSpecΓ ≫ iΓ' = i' ≫ W'.toSpecΓ := (Scheme.toSpecΓ_naturality i').symm
  have hOld : (g ≫ Q.toSpecΓ) ≫ iΓ = i' ≫ (f ≫ W.toSpecΓ) := by
    rw [Category.assoc, h₀, ← Category.assoc, sq.w, Category.assoc]
  have hNew : (Q'.toSpecΓ ≫ gΓ) ≫ iΓ = i' ≫ (W'.toSpecΓ ≫ fΓ) := by
    rw [Category.assoc, sqΓ.w, ← Category.assoc, h₁, Category.assoc]
  have : IsIso (idealPullbackMap iΓ i W.toSpecΓ Q.toSpecΓ h₀) :=
    idealPullbackMap_isIso_of_isIso iΓ i W.toSpecΓ Q.toSpecΓ h₀
  have : IsIso (idealPullbackMap iΓ' i' W'.toSpecΓ Q'.toSpecΓ h₁) :=
    idealPullbackMap_isIso_of_isIso iΓ' i' W'.toSpecΓ Q'.toSpecΓ h₁
  have hn : Epi (idealPullbackMap iΓ i' (W'.toSpecΓ ≫ fΓ) (Q'.toSpecΓ ≫ gΓ) hNew) :=
    unionConormal_idealMap_comp_epi iΓ iΓ' i' fΓ W'.toSpecΓ gΓ Q'.toSpecΓ sqΓ.w h₁ hNew
  have : Epi (idealPullbackMap iΓ i' (f ≫ W.toSpecΓ) (g ≫ Q.toSpecΓ) hOld) :=
    unionConormal_idealMap_epi_congr iΓ i' (W'.toSpecΓ ≫ fΓ) (f ≫ W.toSpecΓ)
      (Scheme.toSpecΓ_naturality f).symm (Q'.toSpecΓ ≫ gΓ) (g ≫ Q.toSpecΓ) hNew hOld
  exact unionConormal_idealMap_epi_of_comp iΓ i i' W.toSpecΓ f Q.toSpecΓ g h₀ sq.w hOld

end HodgeLean.Foundations.Program.G32Native
