import HodgeLean.Foundations.Program.SchoenCycleStep1FixedField

/-! # Normalization in the fixed field of a categorical quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The normalization in the fixed rational field recovers the categorical quotient. -/
theorem s2e_step1_fixedField_normalization
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (I : Type) (a : I → (X ⟶ X)) [∀ i, IsIso (a i)]
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ i, a i ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ i, a i ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty (q.left ⁻¹ᵁ U)] :
    let K := s2e_step1_fixedField X.left I (fun i => (a i).left)
    ∃ (η : Spec (CommRingCat.of K) ⟶ Y.left) (hηaff : IsAffineHom η),
      letI := hηaff
      Spec.map (CommRingCat.ofHom K.subtype) ≫ η =
          X.left.fromSpecStalk (genericPoint X.left) ≫ q.left ∧
        IsIso η.fromNormalization := by
  let K := s2e_step1_fixedField X.left I (fun i => (a i).left)
  let κ : CommRingCat.of K ⟶ X.left.functionField := CommRingCat.ofHom K.subtype
  obtain ⟨η, hηaff, hη⟩ := s2e_step1_fixedField_genericMap X.left Y.left I
    (fun i => (a i).left) q.left (fun i => congrArg Over.Hom.left (hinv i)) U hU
  letI := hηaff
  obtain ⟨g, hfac, hgen⟩ := s2e_step1_integralTarget_lift X Y q
    η.normalization η.fromNormalization (Spec.map κ ≫ η.toNormalization)
    (by rw [Category.assoc, η.toNormalization_fromNormalization, hη])
  haveI : IsFinite (g ≫ η.fromNormalization) := by rw [hfac]; infer_instance
  haveI : IsFinite g := IsFinite.of_comp g η.fromNormalization
  haveI : Surjective (Spec.map κ) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap κ.hom)
    intro x
    exact ⟨default, Subsingleton.elim _ _⟩
  haveI : IsDominant (X.left.fromSpecStalk (genericPoint X.left) ≫ g) := by
    rw [hgen]
    infer_instance
  haveI : IsDominant g := IsDominant.of_comp
    (X.left.fromSpecStalk (genericPoint X.left)) g
  have hsurj : Surjective g :=
    surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have hginv : ∀ i, (a i).left ≫ g = g := by
    intro i
    let δ := CommRingCat.ofHom (s2e_step1_fieldPullback X.left (a i).left)
    have he : κ ≫ δ = κ := by
      ext x
      exact (s2e_step1_mem_fixedField X.left I (fun i => (a i).left) x.val).mp x.property i
    have hκ : Spec.map δ ≫ Spec.map κ = Spec.map κ := by
      rw [← Spec.map_comp, he]
    haveI := s2e_step1_generic_dominant X.left
    refine ext_of_isDominant_of_isSeparated η.fromNormalization ?_
      (X.left.fromSpecStalk (genericPoint X.left)) ?_
    · rw [Category.assoc, hfac]
      exact congrArg Over.Hom.left (hinv i)
    · rw [← Category.assoc, ← s2e_step1_fieldPullback_generic X.left (a i).left,
        Category.assoc, hgen, ← Category.assoc, hκ]
  let T : Over (Spec ↧ℂ) := Over.mk (η.fromNormalization ≫ Y.hom)
  let p : T ⟶ Y := Over.homMk η.fromNormalization
  let v : X ⟶ T := Over.homMk g (by
    change g ≫ (η.fromNormalization ≫ Y.hom) = X.hom
    rw [← Category.assoc, hfac]
    exact Over.w q)
  haveI : Surjective v.left := hsurj
  haveI : IsReduced T.left := by
    change IsReduced η.normalization
    haveI : IsReduced (Spec (CommRingCat.of K)) := inferInstance
    infer_instance
  haveI : IsSeparated p.left := by
    change IsSeparated η.fromNormalization
    infer_instance
  have hp : IsIso p.left := by
    apply s2e_step1_quotient_reduced_factor_isIso X Y T I a q hinv hquot v p
    · intro i
      ext1
      exact hginv i
    · ext1
      exact hfac
  exact ⟨η, hηaff, hη, hp⟩

end HodgeLean.Foundations.Program
