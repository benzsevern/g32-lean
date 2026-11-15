import HodgeLean.Foundations.Program.PrymFamilyAssemblyDefs

/-! # B6-3g, part 1: proof obligations

One auxiliary statement for each public statement of `PrymFamilyAssembly.lean`, with the helper
lemmas its body uses.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic TopologicalSpace
open HodgeLean.Foundations.AppellHumbert
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-- Complexification is functorial. -/
theorem b63g_cplxMap_comp {Λ Λ' Λ'' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
    [AddCommGroup Λ''] (g : Λ' →+ Λ) (h : Λ'' →+ Λ') :
    b2_cplxMap (g.comp h) = (b2_cplxMap g).comp (b2_cplxMap h) := by
  unfold b2_cplxMap
  rw [← LinearMap.baseChange_comp]
  rfl

/-- Complexification commutes with conjugation. -/
theorem b63g_conj_cplxMap {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ'] (g : Λ' →+ Λ)
    (x : ℂ ⊗[ℤ] Λ') : b2_conj Λ (b2_cplxMap g x) = b2_cplxMap g (b2_conj Λ' x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c y => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The complexified pullback form is the complexified form on complexified arguments. -/
theorem b63g_baseChange_compl {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
    (Q : LinearMap.BilinForm ℤ Λ) (g : Λ' →+ Λ) (x y : ℂ ⊗[ℤ] Λ') :
    LinearMap.BilinForm.baseChange ℂ (Q.compl₁₂ g.toIntLinearMap g.toIntLinearMap) x y =
      Q.baseChange ℂ (b2_cplxMap g x) (b2_cplxMap g y) := by
  induction x using TensorProduct.inductionOn with
  | tmul c u =>
    induction y using TensorProduct.inductionOn with
    | tmul d v => simp [b2_cplxMap]
    | add a b ha hb => simp only [map_add, ha, hb]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- The complexified periods of `J_ℂ ξ` are those of `ξ` on `φ`-images. -/
theorem b63g_complexPeriod_dual (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (ξ : ℂ ⊗[ℚ] HQ X 1) (l : b2_abelianLattice X) :
    complexAbelianPeriod X ((b63g_dualOperator X φ).baseChange ℂ ξ) l =
      complexAbelianPeriod X ξ (φ l) := by
  induction ξ using TensorProduct.inductionOn with
  | tmul c x =>
    have h (y : HQ X 1) (m : b2_abelianLattice X) :
        abelianPeriodEquiv X y m = abelianPeriod X y m :=
      Classical.choose_spec (spec_abelianPeriod_equiv X) y m
    have hc (y : HQ X 1) (m : b2_abelianLattice X) :
        complexAbelianPeriod X (c ⊗ₜ y) m = c * (abelianPeriod X y m : ℂ) := by
      simp [complexAbelianPeriod]
    rw [LinearMap.baseChange_tmul, hc, hc, ← h, ← h]
    simp [b63g_dualOperator, b63g_precomp]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/-- The period pairing transposes the dual operator into `φ_ℂ`. -/
theorem b63g_pairing_dual (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (ξ : ℂ ⊗[ℚ] HQ X 1) (v : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b2_abelianPairing X ((b63g_dualOperator X φ).baseChange ℂ ξ) v =
      b2_abelianPairing X ξ (b2_cplxMap φ v) := by
  induction v using TensorProduct.inductionOn with
  | tmul d l =>
    rw [b2a_pairing_tmul, b63g_complexPeriod_dual]
    exact (b2a_pairing_tmul X ξ d (φ l)).symm
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The period pairing is injective. -/
theorem b63g_pairing_injective (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] : Function.Injective (b2_abelianPairing X) := by
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ complexAbelianPeriod_injective X ?_
  funext l
  have := b2a_pairing_tmul X ξ 1 l
  rw [hξ, one_mul] at this
  simpa using this.symm

theorem b63g_dualOperator_sq_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (n : ℤ)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X) (hφ : ∀ l, φ (φ l) = (-n) • l) :
    (b63g_dualOperator X φ).comp (b63g_dualOperator X φ) = (-(n : ℚ)) • LinearMap.id := by
  refine LinearMap.ext fun x ↦ (abelianPeriodEquiv X).injective ?_
  ext l
  simp [b63g_dualOperator, b63g_precomp, hφ]

theorem b63g_dualOperator_hodge_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ)) :
    letI := (torusCohomology_cupProductOf X).finite
    ∀ pq : ℤ × ℤ,
      ((abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H pq).map
          ((b63g_dualOperator X φ).baseChange ℂ) ≤
        (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H pq := by
  letI := (torusCohomology_cupProductOf X).finite
  intro pq
  change (cohomologyHodgePiece X 1 pq).map _ ≤ cohomologyHodgePiece X 1 pq
  set J := b63g_dualOperator X φ
  -- the `(1, 0)` piece
  have h10 : (cohomologyHodgePiece X 1 (1, 0)).map (J.baseChange ℂ) ≤
      cohomologyHodgePiece X 1 (1, 0) := by
    letI := (finiteBetti_abelian X).finite 1
    have hann : (cohomologyHodgePiece X 1 (1, 0)).map (b2_abelianPairing X) =
        (b2_abelianF X).dualAnnihilator := by
      rw [← b2_abelianHodgeF_eq X, b2_abelianHodgeF,
        Subspace.dualCoannihilator_dualAnnihilator_eq]
      rfl
    rintro _ ⟨ξ, hξ, rfl⟩
    have hmem : b2_abelianPairing X (J.baseChange ℂ ξ) ∈ (b2_abelianF X).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      rw [b63g_pairing_dual]
      have hp : b2_abelianPairing X ξ ∈ (b2_abelianF X).dualAnnihilator :=
        hann ▸ Submodule.mem_map_of_mem hξ
      exact (Submodule.mem_dualAnnihilator _).1 hp _ (hφ hv)
    rw [← hann] at hmem
    obtain ⟨ξ', hξ', he⟩ := hmem
    rwa [← b63g_pairing_injective X he]
  by_cases hpq : pq = (1, 0)
  · subst hpq; exact h10
  by_cases hpq' : pq = (0, 1)
  · subst hpq'
    rw [← cohomologyHodgePiece_map_sigmaQ X 1 1 0]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨J.baseChange ℂ y, h10 ⟨y, hy, rfl⟩, ?_⟩
    exact (baseChange_sigmaQ_comm X J y).symm
  · rw [spec_g4_cohomologyHodgePiece_one_eq X]
    simp [latticeHodgePieces, hpq, hpq']

/-- The column `y ↦ (E y x - E x y)/2` of the alternation of an integral form, a rational
character of the lattice. -/
def b63g_column {Λ : Type*} [AddCommGroup Λ] (E : Λ →+ Λ →+ ℤ) : Λ →+ (Λ →+ ℚ) where
  toFun x :=
    { toFun := fun y ↦ ((E y x - E x y : ℤ) : ℚ) / 2
      map_zero' := by simp
      map_add' := fun y z ↦ by simp only [map_add, AddMonoidHom.add_apply]; push_cast; ring }
  map_zero' := by ext; simp
  map_add' x z := by ext y; simp only [map_add, AddMonoidHom.add_apply, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]; push_cast; ring

/-- Contraction with the lattice class of any integral form evaluates on the column of its
alternation. -/
theorem b63g_contract_latticeClass {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] (E : Λ →+ Λ →+ ℤ) (ψ : Module.Dual ℚ (Λ →+ ℚ)) (x : Λ) :
    contract (latticeClass E) ψ x = ψ (b63g_column E x) := by
  let b := Module.Free.chooseBasis ℤ Λ
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  rw [contract_latticeClass_apply]
  conv_rhs => rw [← (latticeDualBasisQ (Λ := Λ)).sum_repr (b63g_column E (b k))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul, mul_comm, latticeDualBasisQ_apply]
  congr 1

/-- Contraction of a pushed-forward 2-vector: `contract (⋀² g ω) = g ∘ contract ω ∘ gᵀ`. -/
theorem b63g_contract_map {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (g : W →ₗ[K] V) (ω : ⋀[K]^2 W) (ψ : Module.Dual K V) :
    contract (exteriorPower.map 2 g ω) ψ = g (contract ω (g.dualMap ψ)) := by
  have : contract ∘ₗ exteriorPower.map 2 g =
      (LinearMap.llcomp K (Module.Dual K V) W V g ∘ₗ
        (LinearMap.llcomp K (Module.Dual K V) (Module.Dual K W) W).flip g.dualMap) ∘ₗ
          contract := by
    ext v φ
    simp [LinearMap.dualMap_apply]
  exact LinearMap.congr_fun (LinearMap.congr_fun this ω) ψ

/-- Skewness of `φ` for an integral form makes its columns anti-commute with `φ`. -/
theorem b63g_column_skew {Λ : Type*} [AddCommGroup Λ] (Q : LinearMap.BilinForm ℤ Λ)
    (φ : Λ →+ Λ) (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) (x : Λ) :
    (b63g_column (b2_bilinToAddHom Q) x).comp φ = -b63g_column (b2_bilinToAddHom Q) (φ x) := by
  ext y
  simp only [b63g_column, AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Function.comp_apply, AddMonoidHom.neg_apply, b2_bilinToAddHom]
  simp only [AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, hskew]
  rw [show Q x (φ y) = -Q (φ x) y by rw [hskew, neg_neg]]
  push_cast
  ring

theorem b63g_dualOperator_rosati_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := (torusCohomology_cupProductOf X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q))) (b63g_dualOperator X φ) := by
  letI := (torusCohomology_cupProductOf X).finite
  have hsymm : polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q)) =
      exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap
        (latticeClass (b2_bilinToAddHom Q)) :=
    ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm_apply_apply _
  rw [hsymm, IsRosatiSkew]
  ext ψ : 1
  refine (abelianPeriodEquiv X).injective ?_
  ext x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, b63g_contract_map, map_neg,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, AddMonoidHom.neg_apply]
  have hJ (w : b2_abelianLattice X →+ ℚ) : b63g_dualOperator X φ
      ((abelianPeriodEquiv X).symm w) = (abelianPeriodEquiv X).symm (w.comp φ) := by
    simp [b63g_dualOperator, b63g_precomp]
  have hJ' (y : HQ X 1) (l : b2_abelianLattice X) :
      abelianPeriodEquiv X (b63g_dualOperator X φ y) l = abelianPeriodEquiv X y (φ l) := by
    simp [b63g_dualOperator, b63g_precomp]
  rw [hJ', LinearEquiv.apply_symm_apply, b63g_contract_latticeClass]
  simp only [LinearMap.dualMap_apply, LinearEquiv.coe_coe]
  rw [hJ, b63g_column_skew Q φ hskew, map_neg, map_neg, b63g_contract_latticeClass]
  rfl

theorem b63g_model_finrank_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    Module.finrank ℤ Λ = 2 * dim (b5_model Λ F hF Q).left := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  rw [(b5_periodEquiv Λ F hF Q hQ).toIntLinearEquiv.finrank_eq,
    ← b2_two_mul_finrank (b2_abelianF _) (b2_abelianF_isWeightOne _), b2_abelian_finrank]

theorem b63g_modelMap_sq_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (φ : Λ →+ Λ)
    (hφ : ∀ l, φ (φ l) = (-n) • l) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l, b63g_modelMap Λ F hF Q hQ φ (b63g_modelMap Λ F hF Q hQ φ l) = (-n) • l := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  intro l
  simp [b63g_modelMap, hφ]

theorem b63g_modelMap_filtration_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_abelianF (b5_model Λ F hF Q) ≤
      (b2_abelianF (b5_model Λ F hF Q)).comap (b2_cplxMap (b63g_modelMap Λ F hF Q hQ φ)) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  rw [← b5_period_filtration Λ F hF Q hQ]
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨b2_cplxMap φ w, hφ hw, ?_⟩
  have h1 : (b63g_modelMap Λ F hF Q hQ φ).comp (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom =
      (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom.comp φ := by
    ext l
    simp [b63g_modelMap]
  change b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom (b2_cplxMap φ w) =
    b2_cplxMap (b63g_modelMap Λ F hF Q hQ φ)
      (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom w)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← b63g_cplxMap_comp, ← b63g_cplxMap_comp,
    h1]

theorem b63g_modelForm_riemann_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_IsRiemannForm (b2_abelianLattice (b5_model Λ F hF Q)) (b2_abelianF (b5_model Λ F hF Q))
      (b63g_modelForm Λ F hF Q hQ) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  set e := b5_periodEquiv Λ F hF Q hQ
  have hid : (e.symm.toAddMonoidHom).comp e.toAddMonoidHom = AddMonoidHom.id Λ := by
    ext l; simp
  have hback (w : ℂ ⊗[ℤ] Λ) :
      b2_cplxMap e.symm.toAddMonoidHom (b2_cplxMap e.toAddMonoidHom w) = w := by
    rw [← LinearMap.comp_apply, ← b63g_cplxMap_comp, hid, b2_cplxMap_id, LinearMap.id_apply]
  have hbc (a b : ℂ ⊗[ℤ] Λ) : LinearMap.BilinForm.baseChange ℂ (b63g_modelForm Λ F hF Q hQ)
      (b2_cplxMap e.toAddMonoidHom a) (b2_cplxMap e.toAddMonoidHom b) =
      Q.baseChange ℂ a b := by
    change LinearMap.BilinForm.baseChange ℂ
      (Q.compl₁₂ e.symm.toAddMonoidHom.toIntLinearMap e.symm.toAddMonoidHom.toIntLinearMap) _ _ = _
    rw [b63g_baseChange_compl, hback, hback]
  rw [← b5_period_filtration Λ F hF Q hQ]
  refine ⟨fun x ↦ hQ.alt _, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hbc]
    exact hQ.isotropic a ha b hb
  · rintro _ ⟨a, ha, rfl⟩ h0
    have ha0 : a ≠ 0 := by rintro rfl; exact h0 (map_zero _)
    rw [b63g_conj_cplxMap, hbc]
    exact hQ.positive a ha ha0

theorem b63g_modelForm_skew_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hskew : ∀ l m, Q (φ l) m = -Q l (φ m)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m, b63g_modelForm Λ F hF Q hQ (b63g_modelMap Λ F hF Q hQ φ l) m =
      -b63g_modelForm Λ F hF Q hQ l (b63g_modelMap Λ F hF Q hQ φ m) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  intro l m
  simp [b63g_modelForm, b63g_modelMap, hskew]

theorem b63g_modelForm_original_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m, b63g_modelForm Λ F hF Q hQ l m = b5_originalChernPairing Λ F hF Q hQ l m := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  intro l m
  have h := b5_polarization_normalized Λ F hF Q hQ ((b5_periodEquiv Λ F hF Q hQ).symm l)
    ((b5_periodEquiv Λ F hF Q hQ).symm m)
  simp only [AddEquiv.apply_symm_apply] at h
  rw [h]
  rfl

end HodgeLean.Foundations.Program
