import HodgeLean.Adapters.LefschetzOneOneHodgeAbelian

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

open scoped TensorProduct
open Module HodgeBlocks Symplectic

private def bh2_eval (v : Fin (dim X.left) → ℂ) : Dual ℂ (ℂ ⊗[ℚ] HQ X 1) where
  toFun z := abelianPeriodComplexEquiv X z v
  map_add' x y := by simp only [map_add, LinearMap.add_apply]
  map_smul' c x := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply]

private theorem bh2_eval_lattice (l : abelianPeriodLattice X) (x : HQ X 1) :
    bh2_eval X l (1 ⊗ₜ[ℚ] x) = (abelianPeriodEquiv X x l : ℂ) := by
  have h := congrFun (latticeRestriction_abelianPeriodComplexEquiv X (1 ⊗ₜ[ℚ] x)) l
  change abelianPeriodComplexEquiv X (1 ⊗ₜ[ℚ] x) l = _ at h
  change abelianPeriodComplexEquiv X (1 ⊗ₜ[ℚ] x) l = _
  rw [h, abelianPeriodEquiv, Classical.choose_spec (spec_abelianPeriod_equiv X) x l]
  simp [complexAbelianPeriod]

private theorem bh2_contract_map {K V W : Type*} [Field K] [CharZero K]
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
private theorem bh2_grading_eval
    (hH : DirectSum.IsInternal (cohomologyHodgePiece X 1))
    (z : ℂ ⊗[ℚ] HQ X 1) (v : Fin (dim X.left) → ℂ) :
    bh2_eval X v (gradingOperator (cohomologyHodgePiece X 1) hH z) =
      bh2_eval X (Complex.I • v) z := by
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

private def bh2_latticeEval {Λ : Type*} [AddCommGroup Λ] (l : Λ) :
    Dual ℚ (Λ →+ ℚ) where
  toFun f := f l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem bh2_lattice_pair {Λ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : Λ →+ Λ →+ ℤ)
    (hE : ∀ l, E l l = 0) (l m : Λ) :
    contract (latticeClass E) (bh2_latticeEval l) m = (E l m : ℚ) := by
  classical
  have hk (k : Free.ChooseBasisIndex ℤ Λ) :
      contract (latticeClass E) (bh2_latticeEval l) (Free.chooseBasis ℤ Λ k) =
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

private theorem bh2_eval_baseChange (l : abelianPeriodLattice X) :
    bh2_eval X l = Module.Dual.baseChange ℂ
      ((bh2_latticeEval l).comp (abelianPeriodEquiv X).toLinearMap) := by
  ext x
  change bh2_eval X l (1 ⊗ₜ[ℚ] x) = Module.Dual.baseChange ℂ
    ((bh2_latticeEval l).comp (abelianPeriodEquiv X).toLinearMap) (1 ⊗ₜ[ℚ] x)
  rw [bh2_eval_lattice, Module.Dual.baseChange_apply_tmul]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, bh2_latticeEval, LinearMap.coe_mk,
    AddHom.coe_mk, Rat.smul_def, mul_one]

private def bh2_omega (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    ⋀[ℚ]^2 (HQ X 1) :=
  exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap (latticeClass E)

private theorem bh2_pair_lattice
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l, E l l = 0) (l m : abelianPeriodLattice X) :
    bh2_eval X m (contract (complexifyWedge 2 (bh2_omega X E))
      (bh2_eval X l)) = (E l m : ℂ) := by
  rw [bh2_eval_baseChange X l, pol1_contract_complexify, bh2_eval_lattice]
  unfold bh2_omega
  rw [bh2_contract_map]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have he : ((bh2_latticeEval l).comp (abelianPeriodEquiv X).toLinearMap).comp
      (abelianPeriodEquiv X).symm.toLinearMap = bh2_latticeEval l := by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [he, bh2_lattice_pair E hE]
  exact_mod_cast (rfl : E l m = E l m)

private def bh2_evalR : (Fin (dim X.left) → ℂ) →ₗ[ℝ] Dual ℂ (ℂ ⊗[ℚ] HQ X 1) where
  toFun := bh2_eval X
  map_add' v w := by apply LinearMap.ext; intro z; exact (abelianPeriodComplexEquiv X z).map_add v w
  map_smul' r v := by apply LinearMap.ext; intro z; exact (abelianPeriodComplexEquiv X z).map_smul r v

private def bh2_pair (ω : ⋀[ℂ]^2 (ℂ ⊗[ℚ] HQ X 1)) :
    (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun v w => bh2_eval X w (contract ω (bh2_eval X v)))
    (by intros; change bh2_eval X _ (contract ω (bh2_evalR X (_ + _))) = _
        rw [map_add, map_add, map_add]; rfl)
    (by intros; change bh2_eval X _ (contract ω (bh2_evalR X (_ • _))) = _
        rw [map_smul, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]; rfl)
    (by intros; exact (abelianPeriodComplexEquiv X _).map_add _ _)
    (by intros; exact (abelianPeriodComplexEquiv X _).map_smul _ _)

/-- The complexified bivector recovers the real extension of the integral lattice form. -/
private theorem bh2_pair_eq
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hBext : ∀ l m : abelianPeriodLattice X, B l m = E l m) (v w) :
    bh2_pair X (complexifyWedge 2 (bh2_omega X E)) v w = (B v w : ℂ) := by
  have h : bh2_pair X (complexifyWedge 2 (bh2_omega X E)) =
      (B.compr₂ Complex.ofRealLI.toLinearMap) := by
    apply LinearMap.ext_basis (abelianRealBasis X) (abelianRealBasis X)
    intro i j
    change bh2_eval X _ (contract _ (bh2_eval X _)) = (B _ _ : ℂ)
    rw [abelianRealBasis_apply, abelianRealBasis_apply, bh2_pair_lattice X E hE, hBext]
    norm_cast
  exact LinearMap.congr_fun₂ h v w

private theorem bh2_clear_finite {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ z : ℤ, (z : ℚ) = (N : ℚ) * f i := by
  classical
  let N := ∏ i, (f i).den
  refine ⟨N, Finset.prod_pos (fun i _ ↦ Rat.den_pos _), fun i ↦ ?_⟩
  have hd : (f i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := hd
  refine ⟨(f i).num * (k : ℤ), ?_⟩
  rw [hk]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

private theorem bh2_integral_pair {Λ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Λ →+ Λ →+ ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ E : Λ →+ Λ →+ ℤ,
      ∀ l m, (E l m : ℚ) = (N : ℚ) * F l m := by
  classical
  let b := Free.chooseBasis ℤ Λ
  obtain ⟨N, hN, hz⟩ := bh2_clear_finite
    (fun ij : Free.ChooseBasisIndex ℤ Λ × Free.ChooseBasisIndex ℤ Λ ↦ F (b ij.1) (b ij.2))
  choose z hz using hz
  let E : Λ →+ Λ →+ ℤ :=
    (b.constr ℤ (fun i ↦ (b.constr ℤ (fun j ↦ z (i, j))).toAddMonoidHom)).toAddMonoidHom
  have hb (i j) : (E (b i) (b j) : ℚ) = (N : ℚ) * F (b i) (b j) := by
    simp only [E, LinearMap.toAddMonoidHom_coe, Basis.constr_basis]
    exact hz (i, j)
  refine ⟨N, hN, E, fun l m ↦ ?_⟩
  conv_lhs => rw [← b.sum_repr l, ← b.sum_repr m]
  conv_rhs => rw [← b.sum_repr l, ← b.sum_repr m]
  simp only [map_sum, AddMonoidHom.finsetSum_apply, map_zsmul,
    AddMonoidHom.zsmul_apply, Int.cast_sum, zsmul_eq_mul, Int.cast_mul, Int.cast_id,
    Finset.mul_sum, hb]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private def bh2_rationalPair {Λ : Type*} [AddCommGroup Λ]
    (ω : ⋀[ℚ]^2 (Λ →+ ℚ)) : Λ →+ Λ →+ ℚ where
  toFun l := contract ω (bh2_latticeEval l)
  map_zero' := by
    have h : bh2_latticeEval (0 : Λ) = 0 := by ext f; exact f.map_zero
    rw [h, map_zero]
  map_add' l m := by
    have h : bh2_latticeEval (l + m) = bh2_latticeEval l + bh2_latticeEval m := by
      ext f; exact f.map_add l m
    rw [h, map_add]

private theorem bh2_lattice_reconstruction {Λ : Type*} [AddCommGroup Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (ω : ⋀[ℚ]^2 (Λ →+ ℚ)) :
    ∃ N : ℕ, 0 < N ∧ ∃ E : Λ →+ Λ →+ ℤ,
      (∀ l, E l l = 0) ∧ latticeClass E = (N : ℚ) • ω := by
  classical
  obtain ⟨N, hN, E, hE⟩ := bh2_integral_pair (bh2_rationalPair ω)
  have halt (l) : E l l = 0 := by
    have h := hE l l
    change (E l l : ℚ) = (N : ℚ) * bh2_latticeEval l (contract ω (bh2_latticeEval l)) at h
    rw [apply_contract_self, mul_zero] at h
    exact_mod_cast h
  refine ⟨N, hN, E, halt, ?_⟩
  let : Module.Finite ℚ (Λ →+ ℚ) := Module.Finite.of_basis (latticeDualBasisQ (Λ := Λ))
  apply contract_injective
  apply (latticeDualBasisQ (Λ := Λ)).dualBasis.ext
  intro i
  have he : (latticeDualBasisQ (Λ := Λ)).dualBasis i =
      bh2_latticeEval (Free.chooseBasis ℤ Λ i) := by
    apply (latticeDualBasisQ (Λ := Λ)).ext
    intro j
    rw [Basis.dualBasis_apply]
    change (latticeDualBasisQ (Λ := Λ)).repr (latticeDualBasisQ j) i =
      (latticeDualBasisQ j) (Free.chooseBasis ℤ Λ i)
    rw [Basis.repr_self, latticeDualBasisQ_apply, latticeDualBasis_apply_basis]
    simp only [Finsupp.single_apply, eq_comm]
  rw [he]
  ext m
  rw [bh2_lattice_pair E halt, hE]
  simp only [map_smul, LinearMap.smul_apply, AddMonoidHom.smul_apply,
    smul_eq_mul]
  rfl

private theorem bh2_riemann_of_hodge
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l, E l l = 0)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hBext : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (hx : (latticeClassHQ X E : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ)) :
    IsTypeOneOne (fun v w ↦ B v w) := by
  let hT := torusCohomology_cupProductOf X
  let := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
  let M := (abelianVarietyCohomologyOf hF hB hD hT).weight1
  have hω : polarizationVec hT (latticeClassHQ X E) = bh2_omega X E := by
    change (hT.cupWedgeEquiv 2).symm ((hT.cupWedgeEquiv 2) (bh2_omega X E)) = _
    exact LinearEquiv.symm_apply_apply _ _
  have ht := (pol1_hodge_iff_polarizationVec_type X hF hB _).mp hx
  rw [hω] at ht
  have hz := (pol1_exterior_type_iff_grading_zero M _).mp ht
  rw [WeilAction.exteriorPowerBaseChangeEquiv_tmul] at hz
  have hp (v w) : B v (Complex.I • w) + B (Complex.I • v) w = 0 := by
    have he := congrArg (fun ω ↦ bh2_eval X w (contract ω (bh2_eval X v))) hz
    rw [pol1_contract_exteriorDer] at he
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, map_zero,
      LinearMap.zero_apply] at he
    have hg (z) (u) : bh2_eval X u (gradingOperator M.H M.isInternal z) =
        bh2_eval X (Complex.I • u) z := bh2_grading_eval X M.isInternal z u
    have hd : (gradingOperator M.H M.isInternal).dualMap (bh2_eval X v) =
        bh2_eval X (Complex.I • v) := by
      apply LinearMap.ext
      intro z
      exact hg z v
    rw [hg, hd] at he
    change bh2_pair X (complexifyWedge 2 (bh2_omega X E)) v (Complex.I • w) +
      bh2_pair X (complexifyWedge 2 (bh2_omega X E)) (Complex.I • v) w = 0 at he
    rw [bh2_pair_eq X E hE B hBext, bh2_pair_eq X E hE B hBext] at he
    exact_mod_cast he
  intro v w
  have h := hp v (Complex.I • w)
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  linarith

theorem spec_hdg_one_exists_riemann_latticeClassHQ_aux
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :
    ∃ (N : ℕ) (hN : 0 < N)
      (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
        (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      (∀ l : abelianPeriodLattice X, E l l = 0) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧
      x = (N : ℚ)⁻¹ • latticeClassHQ X E := by
  let hT := torusCohomology_cupProductOf X
  let ω := (hT.cupWedgeEquiv 2).symm x
  let f := exteriorPower.map 2 (abelianPeriodEquiv X).toLinearMap
  let g := exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap
  have hgf (w : ⋀[ℚ]^2 (HQ X 1)) : g (f w) = w := by
    change (exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap)
      (exteriorPower.map 2 (abelianPeriodEquiv X).toLinearMap w) = w
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    simp only [LinearEquiv.symm_comp, exteriorPower.map_id, LinearMap.id_apply]
  obtain ⟨N, hN, E, hE, hω⟩ := bh2_lattice_reconstruction (f ω)
  have hclass : latticeClassHQ X E = (N : ℚ) • x := by
    change (hT.cupWedgeEquiv 2) (g (latticeClass E)) = _
    rw [hω, map_smul, hgf, map_smul]
    exact congrArg ((N : ℚ) • ·) ((hT.cupWedgeEquiv 2).apply_symm_apply x)
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  let := isZLattice_complexExponentialLattice X (dim X.left)
  obtain ⟨B, hB, -⟩ := spec_exists_unique_realExtension (abelianPeriodLattice X) E
  refine ⟨N, hN, E, B, hB, hE, ?_, ?_⟩
  · apply bh2_riemann_of_hodge X hF hBdR E hE B hB
    rw [hclass]
    exact Submodule.smul_mem _ _ hx
  · rw [hclass]
    exact (inv_smul_smul₀ (Nat.cast_ne_zero.mpr hN.ne') (x : HQ X 2)).symm


#print axioms spec_hdg_one_exists_riemann_latticeClassHQ_aux

theorem spec_hdg_one_clear_denominators_aux
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :
    ∃ (N : ℕ) (hN : 0 < N)
      (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
        (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      (∀ l : abelianPeriodLattice X, E l l = 0) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧
      N • x = latticeClassHQ X E := by
  obtain ⟨N, hN, E, B, hB, hE, h11, hxE⟩ :=
    spec_hdg_one_exists_riemann_latticeClassHQ_aux X hF hBdR x hx
  refine ⟨N, hN, E, B, hB, hE, h11, ?_⟩
  let z : H^(2 * 1)(X; ℚ) := latticeClassHQ X E
  change x = (N : ℚ)⁻¹ • z at hxE
  change N • x = z
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [hxE, ← Nat.cast_smul_eq_nsmul ℚ]
  exact smul_inv_smul₀ hNq z

theorem spec_hdg_one_eq_span_riemann_latticeClassHQ_aux
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :
    Hdg^1(X; ℚ) = Submodule.span ℚ
      {x : H^(2 * 1)(X; ℚ) | ∃
        (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
        (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
          (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
        (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
        (∀ l : abelianPeriodLattice X, E l l = 0) ∧
        IsTypeOneOne (fun v w ↦ B v w) ∧ x = latticeClassHQ X E} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨N, hN, E, B, hB, hE, h11, rfl⟩ :=
      spec_hdg_one_exists_riemann_latticeClassHQ_aux X hF hBdR x hx
    exact (Submodule.span ℚ _).smul_mem ((N : ℚ)⁻¹)
      (Submodule.subset_span ⟨E, B, hB, hE, h11, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨E, B, hB, hE, h11, rfl⟩
    exact spec_latticeClassHQ_mem_hdg_of_riemann X hF hBdR E B hB hE h11

theorem spec_lefschetzOneOneFor_iff_riemann_latticeClassHQ_aux
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :
    LefschetzOneOneFor X ↔
      ∀ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
        (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
          (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
        (∀ l m : abelianPeriodLattice X, B l m = E l m) →
        (∀ l : abelianPeriodLattice X, E l l = 0) →
        IsTypeOneOne (fun v w ↦ B v w) →
        latticeClassHQ X E ∈ algebraicCycleClassSpan X 1 := by
  constructor
  · intro h11 E B hB hE hType
    exact h11 (spec_latticeClassHQ_mem_hdg_of_riemann X hF hBdR E B hB hE hType)
  · intro hRiemann
    rw [LefschetzOneOneFor,
      spec_hdg_one_eq_span_riemann_latticeClassHQ_aux X hF hBdR]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨E, B, hB, hE, hType, rfl⟩
    exact hRiemann E B hB hE hType

theorem bh2_lefschetzOneOne_of_for {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) (h11 : LefschetzOneOneFor X) :
    letI := hT.finite
    HodgeBlocks.LefschetzOneOne (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} ↦ isAlgebraicOf μ (m := m)) := by
  letI := hT.finite
  refine ⟨fun v hv ↦ ?_⟩
  exact (isAlgebraicOf_iff 1 v).mpr
    (h11 ((isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT 1 v).mp hv))

theorem spec_abelian_hdg_le_span_g2_of_for_aux {μ : CupProduct X}
    (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let hF := finbetti_finiteBetti X
  let hB := spec_bettiDeRhamIso_abelian X
  let hD := hodgeDecomposition_of_abelian_aux X
  letI := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g2 _ _ hg
      (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (bh2_lefschetzOneOne_of_for X hF hB hD hT h11)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

theorem spec_abelian_hdg_le_span_g3_of_for_aux {μ : CupProduct X}
    (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hC : CupFiltered X μ)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let hF := finbetti_finiteBetti X
  let hB := spec_bettiDeRhamIso_abelian X
  let hD := hodgeDecomposition_of_abelian_aux X
  letI := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g3 _ _ hg
      (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (bh2_lefschetzOneOne_of_for X hF hB hD hT h11)
      (hardLefschetzFromDegreeTwoOf hF hB hD hT hH hA hL hC hg)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

theorem spec_harvestBetti_hdg_le_span_abelian_g2_of_for_aux {μ : CupProduct X}
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hM : CycleClassMultiplicative μ) (hH : CycleClassIsHodge X) {η : HQ X 2}
    (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let hF := finbetti_finiteBetti X
  letI := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g2 _ _ hg
      (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (bh2_lefschetzOneOne_of_for X hF hB hD hT h11)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

theorem spec_harvestBetti_hdg_le_span_abelian_g3_of_for_aux {μ : CupProduct X}
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hM : CycleClassMultiplicative μ) (hH : CycleClassIsHodge X) {η : HQ X 2}
    (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (hC : CupFiltered X μ) (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let hF := finbetti_finiteBetti X
  letI := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g3 _ _ hg
      (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (bh2_lefschetzOneOne_of_for X hF hB hD hT h11)
      (hardLefschetzFromDegreeTwoOf hF hB hD hT hH hA hL hC hg)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

theorem spec_abelian_hdg_le_span_g2_cupProductOf_of_for_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact spec_abelian_hdg_le_span_g2_of_for_aux X (torusCohomology_cupProductOf X)
    hM hH hA (hardLefschetz_abelian X hη) h11 hg

theorem spec_abelian_hdg_le_span_g3_cupProductOf_of_for_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact spec_abelian_hdg_le_span_g3_of_for_aux X (torusCohomology_cupProductOf X)
    hM hH hA (hardLefschetz_abelian X hη)
      (cupFiltered_cupProductOf_of_abelian_aux X) h11 hg

theorem spec_abelian_hdg_le_span_g2_of_cupPow_of_for_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 2 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  have hη' : cupPow X (cupProductOf X) η (dim X.left) ≠ 0 := by
    rwa [hg]
  exact spec_abelian_hdg_le_span_g2_of_for_aux X (torusCohomology_cupProductOf X)
    hM hH hA (hardLefschetz_abelian_of_cupPow X hη') h11 hg

theorem spec_abelian_hdg_le_span_g3_of_cupPow_of_for_aux
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 3 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  have hη' : cupPow X (cupProductOf X) η (dim X.left) ≠ 0 := by
    rwa [hg]
  exact spec_abelian_hdg_le_span_g3_of_for_aux X (torusCohomology_cupProductOf X)
    hM hH hA (hardLefschetz_abelian_of_cupPow X hη')
      (cupFiltered_cupProductOf_of_abelian_aux X) h11 hg

theorem spec_hdg_one_dim_one_aux (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (hg : dim X.left = 1) (x : H^(2 * 1)(X; ℚ)) : x ∈ Hdg^1(X; ℚ) := by
  have htop : Hdg^1(X; ℚ) = ⊤ :=
    spec_hodgeClasses_eq_top_of_hodgeFiltration X 1 (by
      have hf := spec_hodgeFiltration_dim_eq_top_of_hodgeDecomposition X
        (hodgeDecomposition_of_abelian_aux X)
      rw [hg] at hf
      exact hf)
  rw [htop]
  exact Submodule.mem_top

theorem spec_non_hodge_not_riemann_latticeClassHQ_aux
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∉ Hdg^1(X; ℚ)) :
    ¬ ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
        (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      (∀ l : abelianPeriodLattice X, E l l = 0) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ x = latticeClassHQ X E := by
  rintro ⟨E, B, hB, hE, hType, rfl⟩
  exact hx (spec_latticeClassHQ_mem_hdg_of_riemann X hF hBdR E B hB hE hType)

end HodgeLean.Adapters
