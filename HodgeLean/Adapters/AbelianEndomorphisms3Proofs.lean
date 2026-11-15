import HodgeLean.Adapters.AbelianEndomorphisms3Defs

/-! # Proof obligations for stage 3 of the geometric commutant

One obligation per statement of `HodgeLean.Adapters.AbelianEndomorphisms3`, in the same order.
All twelve are proved, by three parallel provers. -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped Manifold ContDiff CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A rational character of the period lattice is determined by its values on the S12 basis. -/
private theorem addMonoidHom_apply_eq_sum_basis (χ : abelianPeriodLattice X →+ ℚ)
    (l : abelianPeriodLattice X) :
    χ l = ∑ i, ((abelianLatticeBasis X).repr l i : ℚ) * χ (abelianLatticeBasis X i) := by
  conv_lhs => rw [← (abelianLatticeBasis X).sum_repr l]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul]

theorem spec_abelianPeriod_transpose_aux (T : Module.End ℚ (HQ X 1)) :
    ∃ N : ℕ, 0 < N ∧ ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X ((N : ℚ) • T x) l = abelianPeriod X x (φ l) := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  set b := abelianLatticeBasis X
  let δ : Fin (2 * dim X.left) → (abelianPeriodLattice X →+ ℚ) := fun i =>
    (Int.castAddHom ℚ).comp (b.coord i).toAddMonoidHom
  have hδ : ∀ χ : abelianPeriodLattice X →+ ℚ, χ = ∑ i, χ (b i) • δ i := by
    intro χ
    ext l
    rw [addMonoidHom_apply_eq_sum_basis X χ l, AddMonoidHom.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [δ, b, mul_comm]
  let M : Fin (2 * dim X.left) → Fin (2 * dim X.left) → ℚ := fun i j =>
    e (T (e.symm (δ i))) (b j)
  let N : ℕ := ∏ i, ∏ j, (M i j).den
  have hN : 0 < N := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (M i j).den_pos
  have hK : ∀ i j, ∃ k : ℤ, (k : ℚ) = N * M i j := by
    intro i j
    obtain ⟨c, hc⟩ : (M i j).den ∣ N :=
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (M i j).den) (Finset.mem_univ i))
    refine ⟨(M i j).num * c, ?_⟩
    rw [hc]
    push_cast
    rw [← Rat.mul_den_eq_num (M i j)]
    ring
  choose K hK using hK
  let φ : abelianPeriodLattice X →+ abelianPeriodLattice X :=
    (b.constr ℤ fun j => ∑ i, K i j • b i).toAddMonoidHom
  refine ⟨N, hN, φ, fun x l => ?_⟩
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← he, ← he]
  have h1 : e (T x) l = ∑ i, e x (b i) * ∑ j, (b.repr l j : ℚ) * M i j := by
    conv_lhs => rw [← e.symm_apply_apply x, hδ (e x)]
    simp only [map_sum, map_smul, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [addMonoidHom_apply_eq_sum_basis X _ l]
  have h2 : e x (φ l) = ∑ j, (b.repr l j : ℚ) * ∑ i, (K i j : ℚ) * e x (b i) := by
    simp only [φ, LinearMap.toAddMonoidHom_coe, Module.Basis.constr_apply_fintype,
      Module.Basis.equivFun_apply, map_sum, map_zsmul, zsmul_eq_mul]
  rw [h1, h2]
  simp only [hK, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Two points of the period lattice with the same rational periods are equal. -/
private theorem abelianPeriodLattice_eq_of_period₃ {a b : abelianPeriodLattice X}
    (h : ∀ x, abelianPeriod X x a = abelianPeriod X x b) : a = b := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  refine (abelianLatticeBasis X).ext_elem fun i => ?_
  let χ : abelianPeriodLattice X →+ ℚ :=
    (Int.castAddHom ℚ).comp ((abelianLatticeBasis X).coord i).toAddMonoidHom
  have hχ := h (e.symm χ)
  rw [← he, ← he, LinearEquiv.apply_symm_apply] at hχ
  have h2 : ((abelianLatticeBasis X).repr a i : ℚ) = (abelianLatticeBasis X).repr b i := hχ
  exact_mod_cast h2

theorem spec_not_exists_latticeTranspose_half_aux (hg : 0 < dim X.left) :
    ¬ ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X ((1 / 2 : ℚ) • x) l = abelianPeriod X x (φ l) := by
  rintro ⟨φ, hφ⟩
  have h2 : ∀ l, φ l + φ l = l := by
    intro l
    refine abelianPeriodLattice_eq_of_period₃ X fun x => ?_
    rw [spec_abelianPeriod_add, ← hφ, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  let i : Fin (2 * dim X.left) := ⟨0, by omega⟩
  have := congrArg (fun l => (abelianLatticeBasis X).repr l i) (h2 (abelianLatticeBasis X i))
  simp only [map_add, Finsupp.add_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
  omega

/-- Complexified periods of `T_ℂ w` are the periods of `w` along a dual lattice map. -/
private theorem complexAbelianPeriod_baseChange_of_dual (T : Module.End ℚ (HQ X 1))
    (φ : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (T x) l = abelianPeriod X x (φ l))
    (w : ℂ ⊗[ℚ] HQ X 1) (l : abelianPeriodLattice X) :
    complexAbelianPeriod X (T.baseChange ℂ w) l = complexAbelianPeriod X w (φ l) := by
  induction w using TensorProduct.inductionOn with
  | tmul c x => simp [complexAbelianPeriod, hφ]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem spec_hodge_iff_complexLinear_aux (T : Module.End ℚ (HQ X 1))
    (φ : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (T x) l = abelianPeriod X x (φ l)) :
    (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X ↔
      ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ l,
        ((φ l : abelianPeriodLattice X) : Fin (dim X.left) → ℂ) = A l := by
  have hper := complexAbelianPeriod_baseChange_of_dual X T φ hφ
  constructor
  · intro hT
    obtain ⟨Φ, hΦ⟩ := spec_complexAbelianPeriod_restriction X
    let b := abelianLatticeBasis X
    let R := abelianRealBasis X
    let B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) :=
      R.constr ℝ fun i => ((φ (b i) : abelianPeriodLattice X) : Fin (dim X.left) → ℂ)
    have hBb : ∀ i, B (b i) = φ (b i) := by
      intro i
      rw [← abelianRealBasis_apply, Module.Basis.constr_basis]
    have hB : ∀ l : abelianPeriodLattice X, B l = φ l := by
      intro l
      conv_lhs => rw [← b.sum_repr l]
      conv_rhs => rw [← b.sum_repr l]
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, hBb]
    have hcomm : ∀ v k, B (Complex.I • v) k = Complex.I * B v k := by
      intro v k
      let F : DegreeOneLatticeDual (dim X.left) :=
        (LinearMap.proj k : (Fin (dim X.left) → ℂ) →ₗ[ℂ] ℂ).restrictScalars ℝ
      have hF : Φ.symm F ∈ complexHolomorphicH1 X :=
        ⟨F, fun v => by simp [F], by rw [← hΦ, Φ.apply_symm_apply]⟩
      obtain ⟨F', hF', hF'eq⟩ := hT ⟨_, hF, rfl⟩
      have hext : F' = F ∘ₗ B := by
        refine R.ext fun i => ?_
        have h := congrFun hF'eq (b i)
        rw [hper, ← hΦ, Φ.apply_symm_apply] at h
        rw [LinearMap.comp_apply, abelianRealBasis_apply]
        change F' (b i) = F (B (b i))
        rw [hBb]
        exact h
      have h1 : F' (Complex.I • v) = Complex.I * F' v := hF' v
      rw [hext] at h1
      exact h1
    refine ⟨{ toFun := B, map_add' := B.map_add, map_smul' := ?_ }, fun l => (hB l).symm⟩
    intro c v
    have hc : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_comm, mul_smul, Complex.coe_smul, Complex.coe_smul, smul_comm]
    simp only [RingHom.id_apply]
    rw [hc, map_add, map_smul, map_smul]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, hcomm, Complex.real_smul, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  · rintro ⟨A, hA⟩
    rw [Submodule.map_le_iff_le_comap]
    rintro w ⟨F, hF, hFw⟩
    refine ⟨F ∘ₗ A.restrictScalars ℝ, fun v => ?_, ?_⟩
    · simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, map_smul]
      exact hF (A v)
    · funext l
      change F (A l) = _
      rw [hper, ← hA, ← hFw]
      rfl

theorem spec_exists_lattice_of_hodge_aux (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    ∃ N : ℕ, 0 < N ∧ ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X,
      ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ),
        (∀ x l, abelianPeriod X ((N : ℚ) • T x) l = abelianPeriod X x (φ l)) ∧
          ∀ l, ((φ l : abelianPeriodLattice X) : Fin (dim X.left) → ℂ) = A l := by
  obtain ⟨N, hN, φ, hφ⟩ := spec_abelianPeriod_transpose_aux X T
  have hNT : (complexHolomorphicH1 X).map (((N : ℚ) • T).baseChange ℂ) ≤
      complexHolomorphicH1 X := by
    rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.baseChange_smul, LinearMap.smul_apply]
    exact Submodule.smul_of_tower_mem _ _ (hT ⟨w, hw, rfl⟩)
  obtain ⟨A, hA⟩ := (spec_hodge_iff_complexLinear_aux X ((N : ℚ) • T) φ hφ).1 hNT
  exact ⟨N, hN, φ, A, hφ, hA⟩

omit [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The complexification of a rational endomorphism commutes with rational conjugation. -/
theorem baseChange_sigmaQ_comm (T : Module.End ℚ (HQ X 1)) (w : ℂ ⊗[ℚ] HQ X 1) :
    T.baseChange ℂ (HodgeBlocks.sigmaQ (HQ X 1) w) =
      HodgeBlocks.sigmaQ (HQ X 1) (T.baseChange ℂ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    change T.baseChange ℂ (HodgeBlocks.sigmaQR (HQ X 1) (c ⊗ₜ v)) =
      HodgeBlocks.sigmaQR (HQ X 1) (T.baseChange ℂ (c ⊗ₜ v))
    rw [HodgeBlocks.sigmaQ_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      HodgeBlocks.sigmaQ_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem spec_map_antiholomorphic_le_of_holomorphic_aux (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    (complexAntiholomorphicH1 X).map (T.baseChange ℂ) ≤ complexAntiholomorphicH1 X := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← spec_complexH1_conjugation_exchanges X] at ha ⊢
  obtain ⟨h, hh, rfl⟩ := ha
  rw [baseChange_sigmaQ_comm]
  exact Submodule.mem_map_of_mem (hT (Submodule.mem_map_of_mem hh))

omit [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The complexification of the rational elementary map `b k ↦ b j` (in a rational basis `b`) is
the complex elementary map in the base-changed basis. -/
theorem baseChange_coord_smulRight {I : Type*} (b : Module.Basis I ℚ (HQ X 1)) (j k : I) :
    ((b.coord k).smulRight (b j)).baseChange ℂ =
      ((Algebra.TensorProduct.basis ℂ b).coord k).smulRight (Algebra.TensorProduct.basis ℂ b j) := by
  refine (Algebra.TensorProduct.basis ℂ b).ext fun i => ?_
  simp only [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
    LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rw [TensorProduct.tmul_smul, algebraMap_smul]

theorem spec_exists_not_hodge_aux (hg : 0 < dim X.left) :
    ∃ T : Module.End ℚ (HQ X 1),
      ¬ (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X := by
  by_contra hall
  push Not at hall
  obtain ⟨hdimH, hdimA⟩ := spec_complexH1_dimension X
  have hne : complexHolomorphicH1 X ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdimH
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let b := Module.Basis.ofVectorSpace ℚ (HQ X 1)
  let B := Algebra.TensorProduct.basis ℂ b
  obtain ⟨k, hk⟩ : ∃ k, B.repr w k ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (B.repr.injective (by ext k; simp [h k]))
  have hB : ∀ j, B j ∈ complexHolomorphicH1 X := by
    intro j
    have hmem := hall ((b.coord k).smulRight (b j)) (Submodule.mem_map_of_mem hw)
    rw [baseChange_coord_smulRight, LinearMap.smulRight_apply, Module.Basis.coord_apply] at hmem
    exact (Submodule.smul_mem_iff _ hk).mp hmem
  have htop : complexHolomorphicH1 X = ⊤ := by
    rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hB j
  have hbot : complexAntiholomorphicH1 X = ⊥ :=
    (spec_complexH1_split X).2.symm.eq_bot_of_le (htop ▸ le_top)
  rw [hbot, finrank_bot] at hdimA
  omega

theorem spec_exists_abelianEnd_of_hodge_aux [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : AbelianEnd X, abelianEndAction X f = (N : ℚ) • T := by
  obtain ⟨N, hN, φ, A, hφ, hA⟩ := spec_exists_lattice_of_hodge_aux X T hT
  obtain ⟨f, hf⟩ := spec_exists_abelianEnd_of_lattice X hAlg A fun l hl => by
    have h := (φ ⟨l, hl⟩).2
    rwa [hA] at h
  obtain ⟨φf, hφf⟩ := spec_abelianEndAction_period X f
  have heq : φf = φ := AddMonoidHom.ext fun l =>
    Subtype.ext ((spec_latticeRepresentation_eq_analytic X f A hf φf hφf l).trans (hA l).symm)
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  refine ⟨N, hN, f, LinearMap.ext fun x => e.injective (AddMonoidHom.ext fun l => ?_)⟩
  rw [he, he, LinearMap.smul_apply, hφf, heq, hφ]

theorem spec_abelianEnd0Action_range_aux [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F) :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧ Function.Injective ρ ∧
        ρ.range = (hodgeEndH1 X).op := by
  obtain ⟨ρ, hρ, hinj⟩ := spec_abelianEnd0Action X
  have htmul : ∀ (q : ℚ) (f : AbelianEnd X),
      (q ⊗ₜ[ℤ] f : AbelianEnd0 X) = q • ((1 : ℚ) ⊗ₜ[ℤ] f) := by
    intro q f
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨ρ, hρ, hinj, le_antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range ρ).mp hy
    clear hy
    rw [Subalgebra.mem_op]
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, MulOpposite.unop_zero]; exact zero_mem _
    | tmul q f =>
      rw [htmul, map_smul, hρ, MulOpposite.unop_smul, MulOpposite.unop_op]
      exact Subalgebra.smul_mem _ (spec_abelianEndAction_hodge X f) q
    | add x y hx hy => rw [map_add, MulOpposite.unop_add]; exact add_mem hx hy
  · intro T hT
    rw [Subalgebra.mem_op] at hT
    obtain ⟨N, hN, f, hf⟩ := spec_exists_abelianEnd_of_hodge_aux X hAlg T.unop hT.1
    refine (AlgHom.mem_range ρ).mpr ⟨((N : ℚ)⁻¹) ⊗ₜ f, ?_⟩
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    rw [htmul, map_smul, hρ, hf, MulOpposite.op_smul, smul_smul, inv_mul_cancel₀ hN', one_smul,
      MulOpposite.op_unop]

theorem finiteDimensional_HQ_one : FiniteDimensional ℚ (HQ X 1) := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  let b := abelianLatticeBasis X
  let F : HQ X 1 →ₗ[ℚ] (Fin (2 * dim X.left) → ℚ) :=
    LinearMap.pi fun i => (LinearMap.proj (b i)).comp (abelianPeriod X)
  refine Module.Finite.of_injective F fun x y hxy => e.injective ?_
  have hb : ((e x).toIntLinearMap : abelianPeriodLattice X →ₗ[ℤ] ℚ) = (e y).toIntLinearMap :=
    b.ext fun i => by
      have := congrFun hxy i
      simp only [F, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_proj, Function.eval] at this
      simp only [AddMonoidHom.coe_toIntLinearMap, he, this]
  ext l
  exact LinearMap.congr_fun hb l

theorem latticeHodgePieces_iSup_ne_le (i : ℤ × ℤ) (S : Submodule ℂ (ℂ ⊗[ℚ] HQ X 1))
    (hS : ∀ j, j ≠ i → latticeHodgePieces X j ≤ S) :
    (⨆ j, ⨆ (_ : j ≠ i), latticeHodgePieces X j) ≤ S :=
  iSup₂_le hS

theorem spec_latticeHodgePieces_isInternal_aux :
    DirectSum.IsInternal (latticeHodgePieces X) := by
  have h10 : latticeHodgePieces X (1, 0) = complexHolomorphicH1 X := by
    simp [latticeHodgePieces]
  have h01 : latticeHodgePieces X (0, 1) = complexAntiholomorphicH1 X := by
    simp [latticeHodgePieces]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hi : i = (1, 0)
    · subst hi
      rw [h10]
      refine (spec_complexH1_split X).2.mono_right
        (latticeHodgePieces_iSup_ne_le X _ _ fun j hj => ?_)
      unfold latticeHodgePieces
      split_ifs <;> first | contradiction | exact le_rfl | exact bot_le
    · by_cases hi' : i = (0, 1)
      · subst hi'
        rw [h01]
        refine (spec_complexH1_split X).2.symm.mono_right
          (latticeHodgePieces_iSup_ne_le X _ _ fun j hj => ?_)
        unfold latticeHodgePieces
        split_ifs <;> first | contradiction | exact le_rfl | exact bot_le
      · have : latticeHodgePieces X i = ⊥ := by simp [latticeHodgePieces, hi, hi']
        rw [this]
        exact disjoint_bot_left
  · rw [eq_top_iff, ← (spec_complexH1_split X).1, ← h10, ← h01]
    exact sup_le (le_iSup _ _) (le_iSup _ _)

theorem spec_mem_centralizer_hodgeLieAlgebra_iff_aux
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) (T : Module.End ℚ (HQ X 1)) :
    T ∈ Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) ↔
      T ∈ hodgeEndH1 X := by
  have := finiteDimensional_HQ_one X
  have h10 : latticeHodgePieces X (1, 0) = complexHolomorphicH1 X := by
    simp [latticeHodgePieces]
  have h01 : latticeHodgePieces X (0, 1) = complexAntiholomorphicH1 X := by
    simp [latticeHodgePieces]
  set C := gradingOperator (latticeHodgePieces X) hH with hC
  have hCh : ∀ x ∈ complexHolomorphicH1 X, C x = Complex.I • x := by
    intro x hx
    rw [hC, gradingOperator_apply_of_mem (p := 1) (q := 0) _ hH (h10 ▸ hx)]
    simp
  have hCa : ∀ x ∈ complexAntiholomorphicH1 X, C x = (-Complex.I) • x := by
    intro x hx
    rw [hC, gradingOperator_apply_of_mem (p := 0) (q := 1) _ hH (h01 ▸ hx)]
    simp
  -- Decompose `x = h + a` and compute `C x`.
  have hdec : ∀ x : ℂ ⊗[ℚ] HQ X 1, ∃ h ∈ complexHolomorphicH1 X,
      ∃ a ∈ complexAntiholomorphicH1 X, h + a = x ∧
        C x = Complex.I • h + (-Complex.I) • a := by
    intro x
    have hx : x ∈ complexHolomorphicH1 X ⊔ complexAntiholomorphicH1 X := by
      rw [(spec_complexH1_split X).1]; trivial
    obtain ⟨h, hh, a, ha, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨h, hh, a, ha, rfl, by rw [map_add, hCh h hh, hCa a ha]⟩
  have two_ne : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hHol : ∀ x, C x = Complex.I • x → x ∈ complexHolomorphicH1 X := by
    intro x hx
    obtain ⟨h, hh, a, ha, rfl, hCx⟩ := hdec x
    have ha0 : a = 0 := by
      have h2 : (2 * Complex.I) • a = 0 := by
        rw [hx, smul_add] at hCx
        have := congrArg (fun y => y - Complex.I • h + Complex.I • a) hCx
        simp only [add_sub_cancel_left, neg_smul] at this
        rw [two_mul, add_smul]
        linear_combination (norm := module) this
      exact (smul_eq_zero.1 h2).resolve_left two_ne
    rw [ha0, add_zero]; exact hh
  have hAnti : ∀ x, C x = (-Complex.I) • x → x ∈ complexAntiholomorphicH1 X := by
    intro x hx
    obtain ⟨h, hh, a, ha, rfl, hCx⟩ := hdec x
    have hh0 : h = 0 := by
      have h2 : (2 * Complex.I) • h = 0 := by
        rw [hx, smul_add] at hCx
        rw [two_mul, add_smul]
        linear_combination (norm := module) -hCx
      exact (smul_eq_zero.1 h2).resolve_left two_ne
    rw [hh0, zero_add]; exact ha
  rw [spec_eqw_mem_centralizer_hodgeLieAlgebra_iff, ← hC]
  constructor
  · intro hcomm
    have key : ∀ x, C (T.baseChange ℂ x) = T.baseChange ℂ (C x) := fun x => by
      rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hHol _ (by rw [key, hCh x hx, map_smul])
    · rintro _ ⟨x, hx, rfl⟩
      exact hAnti _ (by rw [key, hCa x hx, map_smul])
  · rintro ⟨hTh, hTa⟩
    refine linearMap_ext_of_isInternal hH fun i x hx => ?_
    simp only [Module.End.mul_apply]
    unfold latticeHodgePieces at hx
    split_ifs at hx with hi hi'
    · rw [hCh x hx, map_smul, hCh _ (hTh ⟨x, hx, rfl⟩)]
    · rw [hCa x hx, map_smul, hCa _ (hTa ⟨x, hx, rfl⟩)]
    · rw [(Submodule.mem_bot ℂ).1 hx, map_zero, map_zero, map_zero]

theorem spec_centralizer_hodgeLieAlgebra_eq_aux [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧
        Subalgebra.centralizer ℚ
            (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) =
          ρ.range.unop := by
  obtain ⟨ρ, hρ, -, hr⟩ := spec_abelianEnd0Action_range_aux X hAlg
  refine ⟨ρ, hρ, ?_⟩
  rw [hr, Subalgebra.unop_op]
  ext T
  exact spec_mem_centralizer_hodgeLieAlgebra_iff_aux X hH T

theorem spec_centralizer_eq_adjoin_of_adjoin_eq_top_aux [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) (j : AbelianEnd X)
    (hK : Algebra.adjoin ℚ {(1 : ℚ) ⊗ₜ[ℤ] j} = (⊤ : Subalgebra ℚ (AbelianEnd0 X))) :
    Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) =
      Algebra.adjoin ℚ {abelianEndAction X j} := by
  refine le_antisymm (fun T hT => ?_) ?_
  · have hT' := (spec_mem_centralizer_hodgeLieAlgebra_iff_aux X hH T).1 hT
    obtain ⟨N, hN, f, hf⟩ := spec_exists_abelianEnd_of_hodge_aux X hAlg T hT'.1
    obtain ⟨ρ, hρ, -⟩ := spec_abelianEnd0Action X
    have h1 : (1 : ℚ) ⊗ₜ[ℤ] f ∈ Algebra.adjoin ℚ {(1 : ℚ) ⊗ₜ[ℤ] j} := hK ▸ Algebra.mem_top
    have h2 : MulOpposite.op (abelianEndAction X f) ∈
        Algebra.adjoin ℚ {MulOpposite.op (abelianEndAction X j)} := by
      have : ρ (1 ⊗ₜ f) ∈ (Algebra.adjoin ℚ {(1 : ℚ) ⊗ₜ[ℤ] j}).map ρ :=
        Subalgebra.mem_map.2 ⟨_, h1, rfl⟩
      rwa [AlgHom.map_adjoin, Set.image_singleton, hρ, hρ] at this
    have h3 : abelianEndAction X f ∈ Algebra.adjoin ℚ {abelianEndAction X j} := by
      have hpre : MulOpposite.op ⁻¹' {MulOpposite.op (abelianEndAction X j)} =
          {abelianEndAction X j} := by
        ext; simp
      have : abelianEndAction X f ∈
          (Algebra.adjoin ℚ {MulOpposite.op (abelianEndAction X j)}).unop := h2
      rwa [Subalgebra.unop_adjoin, hpre] at this
    have hTf : T = (N : ℚ)⁻¹ • abelianEndAction X f := by
      rw [hf, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rw [hTf]
    exact Subalgebra.smul_mem _ h3 _
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact (spec_mem_centralizer_hodgeLieAlgebra_iff_aux X hH _).2 (spec_abelianEndAction_hodge X j)

end HodgeLean.Adapters
