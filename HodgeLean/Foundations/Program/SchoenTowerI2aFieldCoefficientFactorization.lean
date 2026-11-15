import HodgeLean.Foundations.Program.SchoenTowerI2aFiniteFieldPoints
import Mathlib.RingTheory.Localization.Integral

/-! # Compatible coefficient fields of actual factorizations
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
universe u

/-- A factorization of actual field points retains the affine coefficient embeddings.
Source: Mathlib, Scheme.Hom.comp_appTop and Scheme.ΓSpecIso_naturality. -/
theorem s2v_i2a_field_point_coefficients_factor
    {K L : Type u} [Field K] [Field L] {U : Scheme}
    (κ : L →+* K) (η : Spec (CommRingCat.of K) ⟶ U)
    (θ : Spec (CommRingCat.of L) ⟶ U)
    (h : Spec.map (CommRingCat.ofHom κ) ≫ θ = η) :
    κ.comp (θ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom =
      (η.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
  have H : θ.appTop ≫ (Spec.map (CommRingCat.ofHom κ)).appTop = η.appTop := by
    rw [← Scheme.Hom.comp_appTop, h]
  change (θ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom ≫
    CommRingCat.ofHom κ).hom = _
  rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc, H]

/-- Every actual intermediate field-point factor is algebraic over the retained affine coefficients.
Source: Mathlib, IsFractionRing.comap_isAlgebraic_iff and Algebra.IsAlgebraic.of_injective. -/
theorem s2v_i2a_intermediate_field_point_algebraic
    {K L : Type u} [Field K] [Field L] {U : Scheme}
    [IsAffine U] [IsReduced U]
    (κ : L →+* K) (η : Spec (CommRingCat.of K) ⟶ U)
    [IsDominant η] [LocallyQuasiFinite η]
    (θ : Spec (CommRingCat.of L) ⟶ U)
    (h : Spec.map (CommRingCat.ofHom κ) ≫ θ = η) :
    let φL : Γ(U, ⊤) →+* L := (θ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom
    letI := φL.toAlgebra
    Algebra.IsAlgebraic Γ(U, ⊤) L := by
  intro φL
  letI : Algebra Γ(U, ⊤) L := φL.toAlgebra
  let φK : Γ(U, ⊤) →+* K := (η.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
  letI : Algebra Γ(U, ⊤) K := φK.toAlgebra
  have hinj := s2v_i2a_field_point_coefficient_injective η
  haveI : FaithfulSMul Γ(U, ⊤) K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsDomain Γ(U, ⊤) := IsDomain.of_faithfulSMul _ K
  letI : Algebra (FractionRing Γ(U, ⊤)) K := FractionRing.liftAlgebra _ _
  letI : IsScalarTower Γ(U, ⊤) (FractionRing Γ(U, ⊤)) K :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Module.Finite (FractionRing Γ(U, ⊤)) K :=
    s2v_i2a_affine_field_point_finite η (FractionRing Γ(U, ⊤))
  haveI : Algebra.IsAlgebraic Γ(U, ⊤) K := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic (FractionRing Γ(U, ⊤)) K)
  have hcoeff := s2v_i2a_field_point_coefficients_factor κ η θ h
  let κA : L →ₐ[Γ(U, ⊤)] K :=
    { κ with commutes' r := congrArg (fun f : Γ(U, ⊤) →+* K => f r) hcoeff }
  exact Algebra.IsAlgebraic.of_injective κA κ.injective

/-- Actual field-point factorizations retain coefficient embeddings on every common open neighborhood.
Source: Mathlib, Scheme.Hom.appLE_comp_appLE and Scheme.ΓSpecIso_naturality. -/
theorem s2v_i2a_field_point_open_coefficients_factor
    {K L : Type u} [Field K] [Field L] {B : Scheme}
    (κ : L →+* K) (η : Spec (CommRingCat.of K) ⟶ B)
    (θ : Spec (CommRingCat.of L) ⟶ B)
    (h : Spec.map (CommRingCat.ofHom κ) ≫ θ = η)
    (U : B.Opens) (hθ : ⊤ ≤ θ ⁻¹ᵁ U) (hη : ⊤ ≤ η ⁻¹ᵁ U) :
    κ.comp (θ.appLE U ⊤ hθ ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom =
      (η.appLE U ⊤ hη ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
  have H : θ.appLE U ⊤ hθ ≫ (Spec.map (CommRingCat.ofHom κ)).appTop =
      η.appLE U ⊤ hη := by
    change θ.appLE U ⊤ hθ ≫ (Spec.map (CommRingCat.ofHom κ)).app ⊤ = _
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    subst η
    rfl
  change (θ.appLE U ⊤ hθ ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom ≫
    CommRingCat.ofHom κ).hom = _
  rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc, H]

/-- A dominant locally quasi-finite field point is algebraic over every retained affine-open coefficient ring.
Source: Mathlib, locally quasi-finite affine section maps and IsFractionRing.comap_isAlgebraic_iff. -/
theorem s2v_i2a_open_field_point_algebraic
    {K : Type u} [Field K] {B : Scheme} [IsReduced B]
    (η : Spec (CommRingCat.of K) ⟶ B) [IsDominant η] [LocallyQuasiFinite η]
    [QuasiCompact η] (U : B.Opens) (hU : IsAffineOpen U) (hη : ⊤ ≤ η ⁻¹ᵁ U) :
    let φ : Γ(B, U) →+* K := (η.appLE U ⊤ hη ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    letI := φ.toAlgebra
    Algebra.IsAlgebraic Γ(B, U) K := by
  intro φ
  letI : Algebra Γ(B, U) K := φ.toAlgebra
  haveI : IsSchemeTheoreticallyDominant η := .of_isDominant η
  let r := (Spec (CommRingCat.of K)).presheaf.map (homOfLE hη).op
  haveI : IsIso (homOfLE hη) :=
    ⟨⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  haveI : IsIso r := by dsimp only [r]; infer_instance
  have hinj : Function.Injective φ :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective.comp
      ((ConcreteCategory.bijective_of_isIso r).injective.comp (η.app_injective U))
  have hηQF : (η.appLE U ⊤ hη).hom.QuasiFinite :=
    LocallyQuasiFinite.quasiFinite_appLE hU (isAffineOpen_top _) hη
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.Finite :=
    RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.surjective
  haveI : Algebra.QuasiFinite Γ(B, U) K := (RingHom.QuasiFinite.of_finite he).comp hηQF
  haveI : FaithfulSMul Γ(B, U) K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsDomain Γ(B, U) := IsDomain.of_faithfulSMul _ K
  letI : Algebra (FractionRing Γ(B, U)) K := FractionRing.liftAlgebra _ _
  letI : IsScalarTower Γ(B, U) (FractionRing Γ(B, U)) K :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.QuasiFinite (FractionRing Γ(B, U)) K :=
    .of_restrictScalars Γ(B, U) _ _
  haveI : Module.Finite (FractionRing Γ(B, U)) K := Module.Finite.of_quasiFinite
  exact IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic (FractionRing Γ(B, U)) K)

/-- A dominant actual field point embeds the coefficient ring of every open containing its image.
Source: Mathlib, Scheme.Hom.app_injective and the restriction isomorphism to the full field spectrum. -/
theorem s2v_i2a_open_field_point_coefficient_injective
    {K : Type u} [Field K] {B : Scheme} [IsReduced B]
    (η : Spec (CommRingCat.of K) ⟶ B) [IsDominant η] [QuasiCompact η]
    (U : B.Opens) (hη : ⊤ ≤ η ⁻¹ᵁ U) :
    Function.Injective
      (η.appLE U ⊤ hη ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
  haveI : IsSchemeTheoreticallyDominant η := .of_isDominant η
  let r := (Spec (CommRingCat.of K)).presheaf.map (homOfLE hη).op
  haveI : IsIso (homOfLE hη) :=
    ⟨⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  haveI : IsIso r := by dsimp only [r]; infer_instance
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective.comp
    ((ConcreteCategory.bijective_of_isIso r).injective.comp (η.app_injective U))

end HodgeLean.Foundations.Program
