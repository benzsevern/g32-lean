import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineComparisonIso
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonCompositionIso

/-! # The natural flat ideal comparison over affine schemes
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- A flat cartesian square with affine ambient schemes has invertible natural ideal comparison. -/
lemma idealPullbackMap_isIso_of_isAffine
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffine W] [IsAffine W']
    (f : W' ⟶ W) [Flat f] (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    IsIso (idealPullbackMap i i' f g sq.w) := by
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
  have hfΓ : Flat fΓ := by
    have he : fΓ = W'.isoSpec.inv ≫ f ≫ W.isoSpec.hom := by
      calc
        _ = W'.isoSpec.inv ≫ W'.isoSpec.hom ≫ fΓ := by rw [Iso.inv_hom_id_assoc]
        _ = _ := by rw [Scheme.isoSpec_hom_naturality f]
    rw [he]
    infer_instance
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := f.appTop.hom.toAlgebra
  have : Module.Flat Γ(W, ⊤) Γ(W', ⊤) :=
    RingHom.flat_algebraMap_iff.mp
      ((Flat.SpecMap_iff (f := f.appTop)).mp hfΓ)
  have hΓ : IsIso (idealPullbackMap iΓ iΓ' fΓ gΓ sqΓ.w) :=
    affineIdealPullbackMap_isIso Γ(Q, ⊤) Γ(Q', ⊤) i.appTop i'.appTop g.appTop sqΓ
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
  have hn : IsIso (idealPullbackMap iΓ i' (W'.toSpecΓ ≫ fΓ) (Q'.toSpecΓ ≫ gΓ) hNew) :=
    idealPullbackMap_comp_isIso iΓ iΓ' i' fΓ W'.toSpecΓ gΓ Q'.toSpecΓ sqΓ.w h₁ hNew
  have : IsIso (idealPullbackMap iΓ i' (f ≫ W.toSpecΓ) (g ≫ Q.toSpecΓ) hOld) :=
    (idealPullbackMap_isIso_congr iΓ i' (f ≫ W.toSpecΓ) (W'.toSpecΓ ≫ fΓ)
      (Scheme.toSpecΓ_naturality f) (g ≫ Q.toSpecΓ) (Q'.toSpecΓ ≫ gΓ) hOld hNew).mpr hn
  exact idealPullbackMap_isIso_of_comp iΓ i i' W.toSpecΓ f Q.toSpecΓ g h₀ sq.w hOld

end AlgebraicGeometry.Conormal
