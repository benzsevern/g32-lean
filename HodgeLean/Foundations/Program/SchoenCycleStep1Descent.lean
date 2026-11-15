import HodgeLean.Foundations.Program.SchoenCycleStep1FixedNormalization

/-! # Integral-closure sections of the invariant normalization -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- When the normalization map is an isomorphism, its integral elements come from the base. -/
theorem s2e_step1_normalization_algebraMap_surjective
    (R Y : Scheme) (η : R ⟶ Y) [QuasiCompact η] [QuasiSeparated η]
    [IsIso η.fromNormalization] (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := (η.app U).hom.toAlgebra
    Function.Surjective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(R, η ⁻¹ᵁ U))) := by
  letI := (η.app U).hom.toAlgebra
  let φ : Γ(Y, U) ⟶ CommRingCat.of (integralClosure Γ(Y, U) Γ(R, η ⁻¹ᵁ U)) :=
    CommRingCat.ofHom (algebraMap _ _)
  haveI : IsIso (η.fromNormalization.app U) :=
    Scheme.Hom.isIso_app _ _ (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  haveI : IsIso (φ ≫ (η.normalizationObjIso hU).inv) := by
    rw [show φ ≫ (η.normalizationObjIso hU).inv = η.fromNormalization.app U from
      (η.fromNormalization_app hU).symm]
    infer_instance
  haveI : IsIso φ := IsIso.of_isIso_comp_right φ (η.normalizationObjIso hU).inv
  exact ((ConcreteCategory.isIso_iff_bijective φ).mp inferInstance).2

/-- A regular rational function in an intermediate field descends when its normalization is the base. -/
theorem s2e_step1_descend_of_mem_subfield
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (q : X ⟶ Y) [IsFinite q.left]
    (K : Subfield X.left.functionField)
    (η : Spec (CommRingCat.of K) ⟶ Y.left) [IsAffineHom η]
    [IsIso η.fromNormalization]
    (hη : Spec.map (CommRingCat.ofHom K.subtype) ≫ η =
      X.left.fromSpecStalk (genericPoint X.left) ≫ q.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty (q.left ⁻¹ᵁ U)]
    (b : Γ(X.left, q.left ⁻¹ᵁ U))
    (hb : X.left.germToFunctionField (q.left ⁻¹ᵁ U) b ∈ K) :
    ∃ c : Γ(Y.left, U), (q.left.app U).hom c = b := by
  let F := X.left.functionField
  let κ : CommRingCat.of K ⟶ F := CommRingCat.ofHom K.subtype
  have hx : genericPoint X.left ∈ q.left ⁻¹ᵁ U :=
    ((genericPoint_spec X.left).mem_open_set_iff (q.left ⁻¹ᵁ U).isOpen).mpr
      (by simpa using ‹Nonempty (q.left ⁻¹ᵁ U)›)
  have ht : ⊤ ≤ (X.left.fromSpecStalk (genericPoint X.left)) ⁻¹ᵁ (q.left ⁻¹ᵁ U) := by
    change ∀ z : PrimeSpectrum X.left.functionField, _
    intro z _
    have hz : z = IsLocalRing.closedPoint X.left.functionField := Subsingleton.elim _ _
    change q.left (X.left.fromSpecStalk (genericPoint X.left) z) ∈ U
    rw [hz]
    change q.left (X.left.fromSpecStalk (genericPoint X.left)
      (IsLocalRing.closedPoint (X.left.presheaf.stalk (genericPoint X.left)))) ∈ U
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hx
  have htop : ⊤ ≤ η ⁻¹ᵁ U := by
    haveI : Subsingleton (Spec (CommRingCat.of K)) := by
      change Subsingleton (PrimeSpectrum K)
      infer_instance
    intro z _
    let zF : Spec F := IsLocalRing.closedPoint X.left.functionField
    have hz : z = (Spec.map κ) zF := Subsingleton.elim _ _
    rw [hz]
    change (Spec.map κ ≫ η) zF ∈ U
    rw [hη, Scheme.Hom.comp_apply]
    change q.left (X.left.fromSpecStalk (genericPoint X.left)
      (IsLocalRing.closedPoint (X.left.presheaf.stalk (genericPoint X.left)))) ∈ U
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hx
  have hv : ⊤ ≤ Spec.map κ ⁻¹ᵁ (η ⁻¹ᵁ U) := by
    intro z _
    exact htop trivial
  let r := (Spec (CommRingCat.of K)).presheaf.map (homOfLE htop).op
  haveI : IsIso r := by
    haveI : IsIso (homOfLE htop) :=
      ⟨⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    dsimp only [r]
    infer_instance
  let e := asIso r ≪≫ Scheme.ΓSpecIso (CommRingCat.of K)
  let k : Γ(Spec (CommRingCat.of K), η ⁻¹ᵁ U) →+* F := (e.hom ≫ κ).hom
  have hk : e.hom ≫ κ = (Spec.map κ).appLE (η ⁻¹ᵁ U) ⊤ hv ≫
      (Scheme.ΓSpecIso F).hom := by
    change r ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ κ = _
    rw [← Scheme.ΓSpecIso_naturality κ, ← Category.assoc]
    change ((Spec (CommRingCat.of K)).presheaf.map (homOfLE htop).op ≫
      (Spec.map κ).appLE ⊤ ⊤ le_top) ≫ _ = _
    rw [Scheme.Hom.map_appLE]
  have hbase : η.app U ≫ e.hom ≫ κ =
      q.left.app U ≫ X.left.germToFunctionField (q.left ⁻¹ᵁ U) := by
    rw [hk, Scheme.Hom.app_eq_appLE, ← Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
    have hc : (Spec.map κ ≫ η).appLE U ⊤ (by exact hv) =
        (X.left.fromSpecStalk (genericPoint X.left) ≫ q.left).appLE U ⊤ ht := by
      congr 1
    rw [hc, ← Scheme.Hom.appLE_comp_appLE (X.left.fromSpecStalk (genericPoint X.left))
      q.left U (q.left ⁻¹ᵁ U) ⊤ le_rfl ht,
      Category.assoc, s2e_step1_generic_appLE, ← Scheme.Hom.app_eq_appLE]
  letI : Algebra Γ(Y.left, U) Γ(Spec (CommRingCat.of K), η ⁻¹ᵁ U) := (η.app U).hom.toAlgebra
  letI : Algebra Γ(Y.left, U) F :=
    ((X.left.germToFunctionField (q.left ⁻¹ᵁ U)).hom.comp (q.left.app U).hom).toAlgebra
  let kAlg : Γ(Spec (CommRingCat.of K), η ⁻¹ᵁ U) →ₐ[Γ(Y.left, U)] F :=
    ⟨k, fun c => congrArg (fun t : Γ(Y.left, U) ⟶ F => t.hom c) hbase⟩
  have hki : Function.Injective kAlg := by
    intro c d hcd
    apply ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance).1
    exact Subtype.ext hcd
  let bK : K := ⟨X.left.germToFunctionField (q.left ⁻¹ᵁ U) b, hb⟩
  let bA := e.inv.hom bK
  have hbA : kAlg bA = X.left.germToFunctionField (q.left ⁻¹ᵁ U) b := by
    change κ.hom (e.hom.hom (e.inv.hom bK)) = _
    have he := congrArg (fun m : CommRingCat.of K ⟶ CommRingCat.of K => m.hom bK)
      e.inv_hom_id
    change e.hom.hom (e.inv.hom bK) = bK at he
    rw [he]
    rfl
  have hi : _root_.IsIntegral Γ(Y.left, U) bA := by
    apply (isIntegral_algHom_iff kAlg hki).mp
    rw [hbA]
    exact (s2e_finite_smooth_integral_rational_iff_regular X Y q U hU _).mpr ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := s2e_step1_normalization_algebraMap_surjective
    (Spec (CommRingCat.of K)) Y.left η U hU ⟨bA, hi⟩
  refine ⟨c, ?_⟩
  apply X.left.germToFunctionField_injective (q.left ⁻¹ᵁ U)
  have hval := congrArg (fun t : integralClosure Γ(Y.left, U)
    Γ(Spec (CommRingCat.of K), η ⁻¹ᵁ U) => kAlg t.val) hc
  exact (congrArg (fun t : Γ(Y.left, U) ⟶ F => t.hom c) hbase).symm.trans
    (hval.trans hbA)

end HodgeLean.Foundations.Program
