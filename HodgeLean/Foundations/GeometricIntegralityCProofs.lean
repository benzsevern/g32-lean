import HodgeLean.Adapters.AbelianPower
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HodgeLean.Foundations.GeometricIntegralitySchemes

/-! # Geometric integrality over `ℂ`, stage G3 part 2a: proof obligations

One `_aux` theorem per statement of `GeometricIntegralityC.lean`, all open. HC no distance; AV
milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

namespace HodgeLean.Foundations

open HodgeLean.Adapters

/-! ### Commutative algebra over an algebraically closed field -/

theorem spec_g3b_eq_zero_of_forall_algHom_aux {k A : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A] (a : A)
    (h : ∀ φ : A →ₐ[k] k, φ a = 0) : a = 0 := by
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  suffices ha : a ∈ nilradical A by
    simpa [nilradical_eq_zero A] using ha
  rw [nilradical, Ideal.radical_eq_jacobson, Ideal.jacobson, Ideal.mem_sInf]
  intro m hm
  letI : (m : Ideal A).IsMaximal := hm.2
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  letI : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k (A ⧸ m)
  let e : k ≃ₐ[k] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ : A →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)
  have ha := h φ
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply e.symm.injective
  simpa [φ] using ha

theorem spec_g3b_tensor_eq_zero_of_forall_algHom_aux {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A] [CommRing B] [Algebra k B]
    (f : A ⊗[k] B) (h : ∀ φ : A →ₐ[k] k, Algebra.TensorProduct.map φ (AlgHom.id k B) f = 0) :
    f = 0 := by
  classical
  let β := Module.Free.chooseBasis k B
  apply (TensorProduct.equivFinsuppOfBasisRight β).injective
  ext i
  apply spec_g3b_eq_zero_of_forall_algHom_aux (k := k)
  intro φ
  have hcoord : (TensorProduct.equivFinsuppOfBasisRight β
      (Algebra.TensorProduct.map φ (AlgHom.id k B) f)) i =
      φ ((TensorProduct.equivFinsuppOfBasisRight β f) i) := by
    clear h
    induction f <;> simp_all
  have hi : (TensorProduct.equivFinsuppOfBasisRight β
      (Algebra.TensorProduct.map φ (AlgHom.id k B) f)) i = 0 := by
    simpa using congrArg (fun x => (TensorProduct.equivFinsuppOfBasisRight β) x i) (h φ)
  rw [hcoord] at hi
  exact hi

theorem spec_g3b_isDomain_tensorProduct_aux {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain A] [CommRing B] [Algebra k B]
    [IsDomain B] : IsDomain (A ⊗[k] B) := by
  letI : Nontrivial (A ⊗[k] B) := Function.Injective.nontrivial
    (Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := A) (B := B)
      (RingHom.injective (algebraMap k B)))
  letI : NoZeroDivisors (A ⊗[k] B) := ⟨by
    intro f g hfg
    classical
    by_cases hf : f = 0
    · exact Or.inl hf
    right
    let β := Module.Free.chooseBasis k B
    let F := TensorProduct.equivFinsuppOfBasisRight β f
    let G := TensorProduct.equivFinsuppOfBasisRight β g
    have hF : F ≠ 0 := by
      intro hF
      apply hf
      apply (TensorProduct.equivFinsuppOfBasisRight β).injective
      simpa [F] using hF
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hF
    apply (TensorProduct.equivFinsuppOfBasisRight β).injective
    ext j
    apply (mul_eq_zero.mp (show F i * G j = 0 by
      apply spec_g3b_eq_zero_of_forall_algHom_aux (k := k)
      intro φ
      have hcoord (x : A ⊗[k] B) :
          (TensorProduct.equivFinsuppOfBasisRight β
            (Algebra.TensorProduct.map φ (AlgHom.id k B) x)) =
          (TensorProduct.equivFinsuppOfBasisRight β x).mapRange φ (map_zero φ) := by
        ext l
        induction x <;> simp_all
      have hp : Algebra.TensorProduct.map φ (AlgHom.id k B) f *
          Algebra.TensorProduct.map φ (AlgHom.id k B) g = 0 := by
        rw [← map_mul, hfg, map_zero]
      have hp' : Algebra.TensorProduct.lid k B
            (Algebra.TensorProduct.map φ (AlgHom.id k B) f) *
          Algebra.TensorProduct.lid k B
            (Algebra.TensorProduct.map φ (AlgHom.id k B) g) = 0 := by
        rw [← map_mul, hp, map_zero]
      rcases mul_eq_zero.mp hp' with hf' | hg'
      · have hf'' : Algebra.TensorProduct.map φ (AlgHom.id k B) f = 0 :=
          (Algebra.TensorProduct.lid k B).injective (by simpa using hf')
        have hc := hcoord f
        rw [hf'', LinearEquiv.map_zero] at hc
        have hc_i := DFunLike.congr_fun hc i
        have hz : φ (F i) = 0 := by
          simpa only [Finsupp.zero_apply, Finsupp.mapRange_apply, F] using hc_i.symm
        rw [map_mul, hz, zero_mul]
      · have hg'' : Algebra.TensorProduct.map φ (AlgHom.id k B) g = 0 :=
          (Algebra.TensorProduct.lid k B).injective (by simpa using hg')
        have hc := hcoord g
        rw [hg'', LinearEquiv.map_zero] at hc
        have hc_j := DFunLike.congr_fun hc j
        have hz : φ (G j) = 0 := by
          simpa only [Finsupp.zero_apply, Finsupp.mapRange_apply, G] using hc_j.symm
        rw [map_mul, hz, mul_zero])).resolve_left hi⟩
  exact NoZeroDivisors.to_isDomain _

/-! ### Base change of an integral complex scheme to a field -/

theorem spec_g3b_isIntegral_pullback_spec_aux (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [IsDomain A] (K : Type) [Field K] [Algebra ℂ K] :
    IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) := by
  letI : IsDomain (A ⊗[ℂ] K) := isDomain_tensorProduct_of_isAlgClosed ℂ A K
  exact IsIntegral.of_isIso (pullbackSpecIso ℂ A K).inv

private theorem g3b_geometricallyIntegral_affine
    (X : Scheme) (f : X ⟶ Spec (.of ℂ)) [IsAffine X] [IsIntegral X]
    [LocallyOfFiniteType f] : GeometricallyIntegral f := by
  let A := Γ(X, ⊤)
  let a := Spec.preimage (X.isoSpec.inv ≫ f)
  letI : Algebra ℂ A := a.hom.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = X.isoSpec.inv ≫ f :=
    Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) := by
    rw [ha]
    infer_instance
  letI : Algebra.FiniteType ℂ A := HasRingHomProperty.Spec_iff.mp hft
  have hspec : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) := by
    constructor
    rw [geometrically_iff_of_commRing]
    intro K _ _ Z fst snd h
    letI : IsDomain (A ⊗[ℂ] K) := isDomain_tensorProduct_of_isAlgClosed ℂ A K
    exact IsIntegral.of_isIso
      (h.isoPullback ≪≫ pullbackSpecIso ℂ A K).inv
  rw [ha] at hspec
  constructor
  intro K _ y Z p q hpq
  exact hspec.geometrically_isIntegral y (p ≫ X.isoSpec.hom) q
    (hpq.of_iso (.refl _) X.isoSpec (.refl _) (.refl _)
      (by simp) (by simp) (by simp) (by simp))

private def g3bPointedAffineCover (X : Scheme) : X.OpenCover where
  I₀ := X
  X x := X.affineCover.X (X.affineCover.idx x)
  f x := X.affineCover.f (X.affineCover.idx x)
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x ↦ ⟨x, X.affineCover.covers x⟩, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
private theorem g3b_isIntegral_baseChange (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (K : Type) [Field K] [Algebra ℂ K] :
    IsIntegral (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) := by
  let C := g3bPointedAffineCover X.left
  let g := Spec.map (CommRingCat.ofHom (algebraMap ℂ K))
  let D := Scheme.Pullback.openCoverOfLeft C X.hom g
  have (i : C.I₀) : Nonempty (C.X i) := by
    let ⟨y, _⟩ := X.left.affineCover.covers i
    exact ⟨y⟩
  have (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C, g3bPointedAffineCover]
    infer_instance
  have (i : C.I₀) : IsIntegral (C.X i) := by
    exact isIntegral_of_isOpenImmersion (C.f i)
  have (i : C.I₀) : IsOpenImmersion (C.f i) := C.map_prop i
  have (i : D.I₀) : IsOpenImmersion (D.f i) := D.map_prop i
  have (i : C.I₀) : GeometricallyIntegral (C.f i ≫ X.hom) :=
    g3b_geometricallyIntegral_affine (C.X i) (C.f i ≫ X.hom)
  have (i : C.I₀) : IsIntegral (D.X i) := by
    change IsIntegral (pullback (C.f i ≫ X.hom) g)
    letI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := inferInstance
    letI : Flat (C.f i ≫ X.hom) := inferInstance
    letI : UniversallyOpen (C.f i ≫ X.hom) := inferInstance
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd _ _)
  letI : IsReduced (pullback X.hom g) := IsReduced.of_openCover _ D
  have hr (i : C.I₀) : Set.range (D.f i) =
      (pullback.fst X.hom g) ⁻¹' Set.range (C.f i) := by
    convert! (Scheme.Pullback.range_map (f := C.f i ≫ X.hom) (g := g)
      X.hom g (C.f i) (𝟙 _) (𝟙 _) (by simp) (by simp)) using 1
    simp
  have hn : Pairwise (fun i j : D.I₀ ↦
      ¬ Disjoint ((D.f i).opensRange) ((D.f j).opensRange)) := by
    intro i j _
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.not_disjoint_iff]
    obtain ⟨x, hi, hj⟩ := nonempty_preirreducible_inter
      (C.f i).isOpenEmbedding.isOpen_range (C.f j).isOpenEmbedding.isOpen_range
      (Set.range_nonempty _) (Set.range_nonempty _)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := g)
      x (Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of K))))
      (Subsingleton.elim _ _)
    exact ⟨z, by change z ∈ Set.range (D.f i); rw [hr]; simpa [hz] using hi,
      by change z ∈ Set.range (D.f j); rw [hr]; simpa [hz] using hj⟩
  letI : PreirreducibleSpace ↥(pullback X.hom g) :=
    PreirreducibleSpace.of_isOpenCover hn D.isOpenCover_opensRange fun i ↦
      Subtype.preirreducibleSpace (by
        change IsPreirreducible (Set.range (D.f i))
        simpa only [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ (D.X i)).isPreirreducible.image
            (D.f i) (D.f i).continuous.continuousOn)
  letI : IrreducibleSpace ↥(pullback X.hom g) := ⟨inferInstance⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem spec_g3b_isReduced_baseChange_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (K : Type) [Field K] [Algebra ℂ K] :
    IsReduced (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) := by
  have : IsIntegral
      (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
    g3b_isIntegral_baseChange X K
  infer_instance

theorem spec_g3b_irreducibleSpace_baseChange_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (K : Type) [Field K] [Algebra ℂ K] :
    IrreducibleSpace ↥(pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) := by
  have : IsIntegral
      (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
    g3b_isIntegral_baseChange X K
  infer_instance

theorem spec_g3b_geometricallyIntegral_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] : GeometricallyIntegral X.hom := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  let : IsReduced (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
    spec_g3b_isReduced_baseChange_aux X K
  let : IrreducibleSpace ↥(pullback X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
    spec_g3b_irreducibleSpace_baseChange_aux X K
  let : IsIntegral (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  exact IsIntegral.of_isIso h.isoPullback.inv

theorem spec_g3b_isIntegral_power_aux (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom]
    (r : ℕ) : IsIntegral (g3_power A r).left := by
  let := spec_g3b_geometricallyIntegral_aux A
  exact spec_g3_isIntegral_power A r

/-! ### Falsification checks -/

theorem spec_g3b_not_isDomain_complex_tensor_aux : ¬ IsDomain (ℂ ⊗[ℝ] ℂ) := by
  intro hD
  let x : ℂ ⊗[ℝ] ℂ := 1 ⊗ₜ Complex.I - Complex.I ⊗ₜ 1
  let y : ℂ ⊗[ℝ] ℂ := 1 ⊗ₜ Complex.I + Complex.I ⊗ₜ 1
  have hxy : x * y = 0 := by
    simp [x, y, mul_add, sub_mul, Complex.I_mul_I]
    apply sub_eq_zero.mpr
    calc
      1 ⊗ₜ[ℝ] (-1 : ℂ) = (-1 : ℝ) • (1 ⊗ₜ[ℝ] 1) := by
        rw [show (-1 : ℂ) = (-1 : ℝ) • 1 by norm_num, TensorProduct.tmul_smul]
      _ = (-1 : ℂ) ⊗ₜ[ℝ] 1 := by
        rw [show (-1 : ℂ) = (-1 : ℝ) • 1 by norm_num, TensorProduct.smul_tmul']
  have hx : x ≠ 0 := by
    intro hx
    have := congrArg
      (Algebra.TensorProduct.lift Complex.conjAe.toAlgHom (AlgHom.id ℝ ℂ)
        (fun _ _ ↦ .all _ _)) hx
    norm_num [x] at this
  have hy : y ≠ 0 := by
    intro hy
    have := congrArg
      (Algebra.TensorProduct.lift (AlgHom.id ℝ ℂ) (AlgHom.id ℝ ℂ)
        (fun _ _ ↦ .all _ _)) hy
    norm_num [y] at this
  exact hx (mul_eq_zero.mp hxy |>.resolve_right hy)

theorem spec_g3b_not_geometricallyIntegral_real_aux :
    IsIntegral (Spec (CommRingCat.of ℂ)) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) ∧
      ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) := by
  have hft : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) :=
    HasRingHomProperty.Spec_iff.mpr
      (show Algebra.FiniteType ℝ ℂ from inferInstance)
  refine ⟨inferInstance, hft, ?_⟩
  intro h
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing] at h
  have hp : IsIntegral (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))) :=
    h (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)
  have hs : IsIntegral (Spec (CommRingCat.of (ℂ ⊗[ℝ] ℂ))) :=
    IsIntegral.of_isIso (pullbackSpecIso ℝ ℂ ℂ).hom
  have hd : IsDomain (ℂ ⊗[ℝ] ℂ) := (affine_isIntegral_iff _).mp hs
  exact spec_g3b_not_isDomain_complex_tensor_aux hd

theorem spec_g3b_not_geometricallyIntegral_prod_aux :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (ℂ × ℂ)))) ∧
      ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℂ (ℂ × ℂ)))) := by
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change (algebraMap ℂ (ℂ × ℂ)).FiniteType
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  · intro h
    have hi : IsIntegral (Spec (CommRingCat.of (ℂ × ℂ))) :=
      self_of_isIntegral_of_geometrically h.geometrically_isIntegral
    have hd : IsDomain (ℂ × ℂ) :=
      (affine_isIntegral_iff (CommRingCat.of (ℂ × ℂ))).mp hi
    exact false_of_nontrivial_of_product_domain ℂ ℂ

theorem spec_g3b_not_geometricallyIntegral_dualNumber_aux :
    IrreducibleSpace (Spec (CommRingCat.of (DualNumber ℂ))) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) ∧
      ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) := by
  have hirr : IrreducibleSpace (Spec (CommRingCat.of (DualNumber ℂ))) := by
    rw [show IrreducibleSpace (Spec (CommRingCat.of (DualNumber ℂ))) ↔
      IrreducibleSpace (PrimeSpectrum (DualNumber ℂ)) by rfl]
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    rw [show nilradical (DualNumber ℂ) = Ideal.span {DualNumber.eps} by
      ext x
      rw [mem_nilradical, DualNumber.isNilpotent_iff_eps_dvd]
      simp only [Ideal.mem_span_singleton', dvd_def]
      constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, mul_comm _ _⟩]
    exact (DualNumber.isMaximal_span_singleton_eps).isPrime
  refine ⟨hirr, ?_, ?_⟩
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change (algebraMap ℂ (DualNumber ℂ)).FiniteType
    apply RingHom.Finite.to_finiteType
    rw [RingHom.finite_algebraMap]
    change Module.Finite ℂ (ℂ × ℂ)
    infer_instance
  · intro h
    have hi : IsIntegral (Spec (CommRingCat.of (DualNumber ℂ))) :=
      self_of_isIntegral_of_geometrically h.geometrically_isIntegral
    have hd : IsDomain (DualNumber ℂ) :=
      (affine_isIntegral_iff (CommRingCat.of (DualNumber ℂ))).mp hi
    have heps : (DualNumber.eps : DualNumber ℂ) = 0 :=
      (DualNumber.isNilpotent_eps : IsNilpotent (DualNumber.eps : DualNumber ℂ)).eq_zero
    exact one_ne_zero (congrArg TrivSqZeroExt.snd heps)

theorem spec_g3b_isEmpty_algHom_ratFunc_aux : IsEmpty (RatFunc ℂ →ₐ[ℂ] ℂ) := by
  constructor
  intro φ
  let z : RatFunc ℂ := RatFunc.X - algebraMap ℂ (RatFunc ℂ) (φ RatFunc.X)
  have hz : z ≠ 0 := by
    dsimp [z]
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      (RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero (φ RatFunc.X)))
  have hu : IsUnit z := hz.isUnit
  have hm : φ z = 0 := by
    dsimp [z]
    rw [map_sub, ← RatFunc.algebraMap_eq_C, φ.commutes]
    exact sub_self _
  exact not_isUnit_zero (hm ▸ hu.map φ)

end HodgeLean.Foundations
