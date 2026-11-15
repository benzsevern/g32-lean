import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNAffineIdealMap
import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineSchemeComparison
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonCompositionIso

/-! # The natural flat ideal comparison over affine schemes
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- A supplied isomorphism of original affine ideal tensors with its natural
coefficient identity makes the native ideal comparison invertible on the
actual affine schemes. Ambient flatness is unnecessary.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem paired_conormal_affine_scheme_ideal_map_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffine W] [IsAffine W']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := f.appTop.hom.toAlgebra
    ∀ eI : (Γ(W', ⊤) ⊗[Γ(W, ⊤)] RingHom.ker i.appTop.hom) ≃ₗ[Γ(W', ⊤)]
        RingHom.ker i'.appTop.hom,
      (∀ x : RingHom.ker i.appTop.hom,
        (eI (1 ⊗ₜ[Γ(W, ⊤)] x)).val = f.appTop.hom x.val) →
      IsIso (idealPullbackMap i i' f g sq.w) := by
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := f.appTop.hom.toAlgebra
  intro eI hvalue
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
  have hΓ : IsIso (idealPullbackMap iΓ iΓ' fΓ gΓ sqΓ.w) :=
    paired_conormal_affine_ideal_map_isIso Γ(Q, ⊤) Γ(Q', ⊤)
      i.appTop i'.appTop g.appTop sqΓ.w eI hvalue
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
  have hn : IsIso (idealPullbackMap iΓ i' (W'.toSpecΓ ≫ fΓ) (Q'.toSpecΓ ≫ gΓ) hNew) :=
    idealPullbackMap_comp_isIso iΓ iΓ' i' fΓ W'.toSpecΓ gΓ Q'.toSpecΓ sqΓ.w h₁ hNew
  have : IsIso (idealPullbackMap iΓ i' (f ≫ W.toSpecΓ) (g ≫ Q.toSpecΓ) hOld) :=
    (idealPullbackMap_isIso_congr iΓ i' (f ≫ W.toSpecΓ) (W'.toSpecΓ ≫ fΓ)
      (Scheme.toSpecΓ_naturality f) (g ≫ Q.toSpecΓ) (Q'.toSpecΓ ≫ gΓ) hOld hNew).mpr hn
  exact idealPullbackMap_isIso_of_comp iΓ i i' W.toSpecΓ f Q.toSpecΓ g h₀ sq.w hOld

end HodgeLean.Foundations.Program.G32Native
