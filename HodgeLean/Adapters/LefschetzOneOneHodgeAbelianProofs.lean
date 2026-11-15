import HodgeLean.Adapters.LefschetzOneOneHodgeAbelianDefs
import HodgeLean.Adapters.RiemannFormHermitian
import HodgeLean.Adapters.AbelianHodgeDischarge
import HodgeLean.Adapters.PolarizedHodgeAbelianProofs
import HodgeLean.Adapters.AbelianCMData

/-! # Proof obligations for the abelian Hodge half of Lefschetz (1,1) -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

open scoped TensorProduct
open Module HodgeBlocks Symplectic

private def bh1_eval (v : Fin (dim X.left) → ℂ) : Dual ℂ (ℂ ⊗[ℚ] HQ X 1) where
  toFun z := abelianPeriodComplexEquiv X z v
  map_add' x y := by simp only [map_add, LinearMap.add_apply]
  map_smul' c x := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply]

private theorem bh1_eval_lattice (l : abelianPeriodLattice X) (x : HQ X 1) :
    bh1_eval X l (1 ⊗ₜ[ℚ] x) = (abelianPeriodEquiv X x l : ℂ) := by
  have h := congrFun (latticeRestriction_abelianPeriodComplexEquiv X (1 ⊗ₜ[ℚ] x)) l
  change abelianPeriodComplexEquiv X (1 ⊗ₜ[ℚ] x) l = _ at h
  change abelianPeriodComplexEquiv X (1 ⊗ₜ[ℚ] x) l = _
  rw [h, abelianPeriodEquiv, Classical.choose_spec (spec_abelianPeriod_equiv X) x l]
  simp [complexAbelianPeriod]

private theorem bh1_contract_map {K V W : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (ω : ⋀[K]^2 V) (φ : Dual K W) :
    contract (exteriorPower.map 2 f ω) φ = f (contract ω (φ.comp f)) := by
  have h : (LinearMap.applyₗ φ).comp (contract.comp (exteriorPower.map 2 f)) =
      f.comp ((LinearMap.applyₗ (φ.comp f)).comp contract) := by
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
      exteriorPower.map_apply_ιMulti, contract_ιMulti, Function.comp_apply,
      map_sub, map_smul]
  exact LinearMap.congr_fun h ω

/-- Period evaluation turns the weight-one grading operator into multiplication by `i`
on the tangent space. -/
private theorem bh1_grading_eval
    (hH : DirectSum.IsInternal (cohomologyHodgePiece X 1))
    (z : ℂ ⊗[ℚ] HQ X 1) (v : Fin (dim X.left) → ℂ) :
    bh1_eval X v (gradingOperator (cohomologyHodgePiece X 1) hH z) =
      bh1_eval X (Complex.I • v) z := by
  have h10 : cohomologyHodgePiece X 1 (1, 0) = complexHolomorphicH1 X := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]; simp only [latticeHodgePieces, ite_true]
  have h01 : cohomologyHodgePiece X 1 (0, 1) = complexAntiholomorphicH1 X := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]; norm_num [latticeHodgePieces]
  have hz : z ∈ complexHolomorphicH1 X ⊔ complexAntiholomorphicH1 X := by
    rw [(spec_complexH1_split X).1]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  have hga : gradingOperator (cohomologyHodgePiece X 1) hH a = Complex.I • a := by
    rw [gradingOperator_apply_of_mem _ hH (h10.symm ▸ ha)]; norm_num
  have hgb : gradingOperator (cohomologyHodgePiece X 1) hH b = -Complex.I • b := by
    rw [gradingOperator_apply_of_mem _ hH (h01.symm ▸ hb)]; norm_num
  rw [complexHolomorphicH1_eq] at ha
  rw [complexAntiholomorphicH1_eq] at hb
  have ha' := ha v
  have hb' := hb v
  simp only [map_add, hga, hgb, map_smul, smul_eq_mul]
  exact congrArg₂ (· + ·) ha'.symm hb'.symm

private def bh1_latticeEval {Λ : Type*} [AddCommGroup Λ] (l : Λ) :
    Dual ℚ (Λ →+ ℚ) where
  toFun f := f l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem bh1_lattice_pair {Λ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : Λ →+ Λ →+ ℤ)
    (hE : ∀ l, E l l = 0) (l m : Λ) :
    contract (latticeClass E) (bh1_latticeEval l) m = (E l m : ℚ) := by
  classical
  have hk (k : Free.ChooseBasisIndex ℤ Λ) :
      contract (latticeClass E) (bh1_latticeEval l) (Free.chooseBasis ℤ Λ k) =
        (E l (Free.chooseBasis ℤ Λ k) : ℚ) := by
    rw [contract_latticeClass_apply_of_alt E hE]
    change (∑ i, (latticeDualBasis i l) * _) = _
    conv_rhs => rw [← (Free.chooseBasis ℤ Λ).sum_repr l]
    simp only [map_sum, AddMonoidHom.finsetSum_apply, map_zsmul,
      AddMonoidHom.zsmul_apply, zsmul_eq_mul, Int.cast_sum, Int.cast_mul]
    rfl
  conv_lhs => rw [← (Free.chooseBasis ℤ Λ).sum_repr m]
  conv_rhs => rw [← (Free.chooseBasis ℤ Λ).sum_repr m]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_sum, Int.cast_mul, hk, Int.cast_id]

private theorem bh1_eval_baseChange (l : abelianPeriodLattice X) :
    bh1_eval X l = Module.Dual.baseChange ℂ
      ((bh1_latticeEval l).comp (abelianPeriodEquiv X).toLinearMap) := by
  ext x
  change bh1_eval X l (1 ⊗ₜ[ℚ] x) = Module.Dual.baseChange ℂ
    ((bh1_latticeEval l).comp (abelianPeriodEquiv X).toLinearMap) (1 ⊗ₜ[ℚ] x)
  rw [bh1_eval_lattice, Module.Dual.baseChange_apply_tmul]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, bh1_latticeEval, LinearMap.coe_mk,
    AddHom.coe_mk, Rat.smul_def, mul_one]

private def bh1_omega (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    ⋀[ℚ]^2 (HQ X 1) :=
  exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap (latticeClass E)

private theorem bh1_pair_lattice
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l, E l l = 0) (l m : abelianPeriodLattice X) :
    bh1_eval X m (contract (complexifyWedge 2 (bh1_omega X E))
      (bh1_eval X l)) = (E l m : ℂ) := by
  rw [bh1_eval_baseChange X l, pol1_contract_complexify, bh1_eval_lattice]
  unfold bh1_omega
  rw [bh1_contract_map]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have he : ((bh1_latticeEval l).comp (abelianPeriodEquiv X).toLinearMap).comp
      (abelianPeriodEquiv X).symm.toLinearMap = bh1_latticeEval l := by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [he, bh1_lattice_pair E hE]
  exact_mod_cast (rfl : E l m = E l m)

private def bh1_evalR : (Fin (dim X.left) → ℂ) →ₗ[ℝ] Dual ℂ (ℂ ⊗[ℚ] HQ X 1) where
  toFun := bh1_eval X
  map_add' v w := by apply LinearMap.ext; intro z; exact (abelianPeriodComplexEquiv X z).map_add v w
  map_smul' r v := by apply LinearMap.ext; intro z; exact (abelianPeriodComplexEquiv X z).map_smul r v

private def bh1_pair (ω : ⋀[ℂ]^2 (ℂ ⊗[ℚ] HQ X 1)) :
    (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun v w => bh1_eval X w (contract ω (bh1_eval X v)))
    (by intros; change bh1_eval X _ (contract ω (bh1_evalR X (_ + _))) = _
        rw [map_add, map_add, map_add]; rfl)
    (by intros; change bh1_eval X _ (contract ω (bh1_evalR X (_ • _))) = _
        rw [map_smul, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]; rfl)
    (by intros; exact (abelianPeriodComplexEquiv X _).map_add _ _)
    (by intros; exact (abelianPeriodComplexEquiv X _).map_smul _ _)

/-- The complexified bivector recovers the real extension of the integral lattice form. -/
private theorem bh1_pair_eq
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hBext : ∀ l m : abelianPeriodLattice X, B l m = E l m) (v w) :
    bh1_pair X (complexifyWedge 2 (bh1_omega X E)) v w = (B v w : ℂ) := by
  have h : bh1_pair X (complexifyWedge 2 (bh1_omega X E)) =
      (B.compr₂ Complex.ofRealLI.toLinearMap) := by
    apply LinearMap.ext_basis (abelianRealBasis X) (abelianRealBasis X)
    intro i j
    change bh1_eval X _ (contract _ (bh1_eval X _)) = (B _ _ : ℂ)
    rw [abelianRealBasis_apply, abelianRealBasis_apply, bh1_pair_lattice X E hE, hBext]
    norm_cast
  exact LinearMap.congr_fun₂ h v w

private theorem bh1_eval_basis (i : Fin (2 * dim X.left)) :
    bh1_eval X (abelianRealBasis X i) = ((abelianH1Basis X).baseChange ℂ).dualBasis i := by
  apply ((abelianH1Basis X).baseChange ℂ).ext
  intro j
  simp [bh1_eval, abelianPeriodComplexEquiv]

/-- Evaluations on real tangent vectors detect a bivector, including degenerate ones. -/
private theorem bh1_pair_zero (ω : ⋀[ℂ]^2 (ℂ ⊗[ℚ] HQ X 1))
    (h : ∀ v w, bh1_pair X ω v w = 0) : ω = 0 := by
  let := finiteDimensional_HQ_one X
  apply contract_injective
  rw [map_zero]
  apply ((abelianH1Basis X).baseChange ℂ).dualBasis.ext
  intro i
  rw [← bh1_eval_basis]
  apply (abelianPeriodComplexEquiv X).injective
  apply LinearMap.ext
  intro v
  simpa only [bh1_pair, LinearMap.mk₂_apply, bh1_eval, LinearMap.coe_mk, AddHom.coe_mk,
    map_zero, LinearMap.zero_apply] using h (abelianRealBasis X i) v

theorem spec_latticeClassHQ_mem_hdg_of_riemann_aux
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hBext : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (hE : ∀ l : abelianPeriodLattice X, E l l = 0)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    (latticeClassHQ X E : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) := by
  let hT := torusCohomology_cupProductOf X
  let := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
  let M := (abelianVarietyCohomologyOf hF hB hD hT).weight1
  have hω : polarizationVec hT (latticeClassHQ X E) = bh1_omega X E := by
    change (hT.cupWedgeEquiv 2).symm ((hT.cupWedgeEquiv 2) (bh1_omega X E)) = _
    exact LinearEquiv.symm_apply_apply _ _
  apply (pol1_hodge_iff_polarizationVec_type X hF hB _).mpr
  rw [show polarizationVec (torusCohomology_cupProductOf X) (latticeClassHQ X E) =
    bh1_omega X E from hω]
  apply (pol1_exterior_type_iff_grading_zero M _).mpr
  rw [WeilAction.exteriorPowerBaseChangeEquiv_tmul]
  apply bh1_pair_zero X
  intro v w
  change bh1_eval X w (contract (InvariantsExterior.exteriorDer 2
    (gradingOperator M.H M.isInternal) (complexifyWedge 2 (bh1_omega X E)))
      (bh1_eval X v)) = 0
  rw [pol1_contract_exteriorDer]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
  have hg (z) (u) : bh1_eval X u (gradingOperator M.H M.isInternal z) =
      bh1_eval X (Complex.I • u) z := bh1_grading_eval X M.isInternal z u
  have hd : (gradingOperator M.H M.isInternal).dualMap (bh1_eval X v) =
      bh1_eval X (Complex.I • v) := by
    apply LinearMap.ext
    intro z
    exact hg z v
  rw [hg, hd]
  change bh1_pair X (complexifyWedge 2 (bh1_omega X E)) v (Complex.I • w) +
    bh1_pair X (complexifyWedge 2 (bh1_omega X E)) (Complex.I • v) w = 0
  rw [bh1_pair_eq X E hE B hBext, bh1_pair_eq X E hE B hBext]
  have hs := h11 v (Complex.I • w)
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at hs
  have hz : B v (Complex.I • w) + B (Complex.I • v) w = 0 := by linarith
  exact_mod_cast hz

#print axioms spec_latticeClassHQ_mem_hdg_of_riemann_aux

theorem spec_lefschetzOneOneFor_of_global_aux (h11 : LefschetzOneOneHyp) :
    LefschetzOneOneFor X := by
  exact h11.holds X

theorem spec_lefschetzOneOneFor_dim_zero_aux (hg : dim X.left = 0) :
    LefschetzOneOneFor X := by
  intro x _
  have hx : x = 0 :=
    ((vanishingAboveTop_abelian X).subsingleton (2 * 1) (by omega)).elim x 0
  rw [hx]
  exact Submodule.zero_mem _

theorem spec_abelian_hdg_le_span_g1_of_for_aux
    (hH : CycleClassIsHodge X)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_g1_of_degree_one (torusCohomology_cupProductOf X) h11 hg

end HodgeLean.Adapters
