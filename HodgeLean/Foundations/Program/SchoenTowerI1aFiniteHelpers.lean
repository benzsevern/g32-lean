import HodgeLean.Foundations.Program.SchoenTowerI1aPreDefs
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_chart_pullback_id (X : Scheme) (U : X.Opens)
    (h : U ≤ (𝟙 X) ⁻¹ᵁ U) : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact X.presheaf.map_id _

abbrev s2v_i1ahi_chartAction
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hinvU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    MulSemiringAction G Γ(X.left, U) where
  smul g r := ((a g⁻¹).left.appLE U U (hinvU g⁻¹)).hom r
  one_smul r := by
    have h : (a 1).left = 𝟙 X.left := congrArg Over.Hom.left ha1
    change ((a (1 : G)⁻¹).left.appLE U U _).hom r = r
    simp only [inv_one, h, s2v_i1ahi_chart_pullback_id, CommRingCat.hom_id, RingHom.id_apply]
  mul_smul g h r := by
    have he := Scheme.Hom.appLE_comp_appLE (a g⁻¹).left (a h⁻¹).left U U U
      (hinvU h⁻¹) (hinvU g⁻¹)
    have hm : (a (h⁻¹ * g⁻¹)).left = (a g⁻¹).left ≫ (a h⁻¹).left :=
      congrArg Over.Hom.left (hamul h⁻¹ g⁻¹)
    change ((a (g * h)⁻¹).left.appLE U U _).hom r =
      ((a g⁻¹).left.appLE U U _).hom (((a h⁻¹).left.appLE U U _).hom r)
    simp only [mul_inv_rev, hm]
    rw [← he]
    rfl
  smul_zero g := map_zero _
  smul_one g := map_one _
  smul_add g := map_add _
  smul_mul g := map_mul _

lemma s2v_i1ahi_chart_isInvariant
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
    letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
    Algebra.IsInvariant (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U) G := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
  constructor
  intro r hr
  refine ⟨⟨r, fun g => ?_⟩, rfl⟩
  simpa only [show g⁻¹ • r = ((a (g⁻¹)⁻¹).left.appLE U U _).hom r from rfl,
    inv_inv] using hr g⁻¹

lemma s2v_i1ahi_finite_invariant_inclusion
    {R A : Type*} [CommRing R] [CommRing A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A]
    (B : Subring A) [Algebra.IsInvariant B A G]
    (f : R →+* B) (hf : (B.subtype.comp f).FiniteType) :
    B.subtype.Finite := by
  letI : Algebra.IsIntegral B A := Algebra.IsInvariant.isIntegral B A G
  exact RingHom.IsIntegral.to_finite (show B.subtype.IsIntegral from
    Algebra.IsIntegral.isIntegral) (RingHom.FiniteType.of_comp_finiteType hf)

lemma s2v_i1ahi_chart_finite_transport
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hf : (s2v_i1a_chartInvariants X G a U hiU).subtype.Finite)
    (hint : (s2v_i1a_chartInvariants X G a U hiU).subtype.IsIntegral) :
    IsFinite (s2v_i1a_affineQuotientMap X G a U hiU) ∧
      Surjective (s2v_i1a_affineQuotientMap X G a U hiU) := by
  let j := CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype
  haveI : IsFinite (Spec.map j) := (IsFinite.SpecMap_iff j).mpr hf
  haveI : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  haveI : Surjective (Spec.map j) :=
    ⟨hint.comap_surjective (s2v_i1a_chartInvariants X G a U hiU).subtype_injective⟩
  exact ⟨inferInstanceAs (IsFinite (U.toSpecΓ ≫ Spec.map j)),
    inferInstanceAs (Surjective (U.toSpecΓ ≫ Spec.map j))⟩

lemma s2v_i1ahi_chart_evaluations_equal
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (Q : Scheme) (q : X.left ⟶ Q)
    (V : Q.Opens)
    (e : Spec ↧(s2v_i1a_chartInvariants X G a U hiU) ≅ V.toScheme)
    (hsq : U.ι ≫ q = s2v_i1a_affineQuotientMap X G a U hiU ≫ e.hom ≫ V.ι)
    (x y : Spec ↧ℂ ⟶ X.left)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (heq : x ≫ q = y ≫ q)
    (r : s2v_i1a_chartInvariants X G a U hiU) :
    (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom r.val =
      (y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom r.val := by
  let j := CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype
  have he (z : Spec ↧ℂ ⟶ X.left) (hz : ⊤ ≤ z ⁻¹ᵁ U) :
      Spec.map (z.appLE U ⊤ hz) ≫ Spec.map j ≫ e.hom ≫ V.ι =
        (isAffineOpen_top (Spec ↧ℂ)).fromSpec ≫ z ≫ q := by
    rw [← Category.assoc (isAffineOpen_top (Spec ↧ℂ)).fromSpec z q,
      ← hU.SpecMap_appLE_fromSpec z (isAffineOpen_top _) hz]
    simp only [IsAffineOpen.fromSpec, Category.assoc]
    rw [hsq]
    dsimp [s2v_i1a_affineQuotientMap]
    simp only [Category.assoc, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]
    rfl
  have hmap : Spec.map (j ≫ x.appLE U ⊤ hx) = Spec.map (j ≫ y.appLE U ⊤ hy) := by
    apply (cancel_mono e.hom).mp
    apply (cancel_mono V.ι).mp
    simp only [Spec.map_comp, Category.assoc]
    rw [he x hx, he y hy, heq]
  have h := Spec.map_injective hmap
  exact congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (k.hom r)) h

end HodgeLean.Foundations.Program
