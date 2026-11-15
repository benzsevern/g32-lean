import HodgeLean.Adapters.DegreeOneLatticeLoops
import HodgeLean.Adapters.DegreeOneSplit

/-! # Proofs for the degree-one period bridge

The statements are frozen; this file proves them.

* Loops (`DegreeOneLatticeLoops`): additivity in the loop goes through the 2-torus map
  `(s, t) ↦ p s + q t`, whose diagonal is `p + q` and whose axes are translates of `p` and `q`
  (homotopic to them by path-connectedness); on the 2-torus the diagonal period is the sum of the
  axis periods by the coordinate basis. The degree of `z ↦ k • z` is `k` by induction from this.
* Coordinate torus: periods are `Σⱼ xⱼ lⱼ` in `torusCoordinateBasis`; the matrix statement is
  naturality of `loopPeriod` with `torusMatrixMap M ∘ torusLoop l = torusLoop (M l)`; the
  equivalence is `Module.Basis.constr` on `ℤⁿ` followed by `addMonoidHomLequivInt`.
* S12: the uniformization carries `t ↦ exp(t • l)` to `torusLoop (b.repr l)`
  (`quotientEquivOfBasis_mk`, `complexExponential_smul`), and the inverse of
  `cohomologyHomeomorphEquiv` is pullback, so S12 periods are torus periods; additivity and the
  character equivalence follow in the transported basis `abelianH1Basis`.
* Complexified: `abelianPeriodComplexEquiv` sends the base-changed basis of `ℂ ⊗[ℚ] HQ X 1` to the
  functionals dual to the real basis `ofZLatticeBasis` of `ℂ^g`; restriction to the full lattice
  is injective, so the two summands are the preimages of the `DegreeOneSplit` summands, and the
  split, dimensions and conjugation transport along it.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Singular

namespace HodgeLean.Adapters

theorem spec_loopPeriod_add_aux {T : Type} [AddCommGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [PathConnectedSpace T] (p q : C(UnitAddCircle, T)) :
    loopPeriod (p + q) = loopPeriod p + loopPeriod q :=
  loopPeriod_add p q

theorem spec_torusPeriod_coordinate_single_aux {n : ℕ} (i j : Fin n) :
    torusPeriod n (torusCoordinateClass j) (Pi.single i 1) = if i = j then 1 else 0 := by
  rw [torusPeriod_coordinate]
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]; simp [h]

theorem spec_torusPeriod_coordinate_aux {n : ℕ} (j : Fin n) (l : Fin n → ℤ) :
    torusPeriod n (torusCoordinateClass j) l = l j :=
  torusPeriod_coordinate n j l

theorem spec_torusPeriod_matrix_aux {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ)
    (y : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin m))) 1) (l : Fin n → ℤ) :
    torusPeriod n (cohomologyMap ℚ 1 (TopCat.ofHom (torusMatrixMap M)) y) l =
      torusPeriod m y (M.mulVec l) := by
  have h : (torusMatrixMap M).comp (torusLoop l) = torusLoop (M.mulVec l) := by
    ext z i
    simp only [ContinuousMap.comp_apply, torusMatrixMap, torusLoop, ContinuousMap.coe_mk,
      Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]
  change loopPeriod (torusLoop l) _ = loopPeriod (torusLoop (M.mulVec l)) y
  rw [← h, loopPeriod_comp]

/-- Rational characters of a free abelian group with basis `bM`, matched with a rational vector
space with a basis `bV` on the same index: `x ↦ (m ↦ Σⱼ xⱼ mⱼ)`.
Source: Mathlib `Module.Basis.constr` and `addMonoidHomLequivInt`. -/
theorem exists_equiv_addMonoidHom_of_basis {κ M V : Type*} [Fintype κ] [AddCommGroup M]
    [AddCommGroup V] [Module ℚ V] (bM : Module.Basis κ ℤ M) (bV : Module.Basis κ ℚ V) :
    ∃ e : V ≃ₗ[ℚ] (M →+ ℚ), ∀ x m, e x m = ∑ j, bV.repr x j * bM.repr m j := by
  refine ⟨bV.equivFun ≪≫ₗ bM.constr ℚ ≪≫ₗ (addMonoidHomLequivInt ℚ).symm, fun x m => ?_⟩
  simp only [LinearEquiv.trans_apply]
  change (bM.constr ℚ (bV.equivFun x)) m = _
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, zsmul_eq_mul, mul_comm]

theorem spec_torusPeriod_equiv_aux (n : ℕ) :
    ∃ e : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1 ≃ₗ[ℚ] ((Fin n → ℤ) →+ ℚ),
      ∀ x l, e x l = torusPeriod n x l := by
  obtain ⟨e, he⟩ := exists_equiv_addMonoidHom_of_basis (Pi.basisFun ℤ (Fin n))
    (torusCoordinateBasis n)
  exact ⟨e, fun x l => by rw [he, torusPeriod_eq_sum]; simp⟩

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The S12 uniformization carries the loop `t ↦ exp(t • l)` to the straight torus loop of the
basis coordinates of `l`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1;
`LatticeTorus.quotientEquivOfBasis_mk`, `complexExponential_smul`. -/
theorem complexPointTorusHomeomorph_comp_abelianLatticeLoop (l : abelianPeriodLattice X) :
    (⟨complexPointTorusHomeomorph X (dim X.left),
        (complexPointTorusHomeomorph X (dim X.left)).continuous⟩ :
      C(ComplexPoint X, UnitAddTorus (Fin (2 * dim X.left)))).comp (abelianLatticeLoop X l) =
      torusLoop ((abelianLatticeBasis X).repr l) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  let := isZLattice_complexExponentialLattice X (dim X.left)
  ext z i
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
  have h1 : Additive.ofMul (abelianLatticeLoop X l (t : UnitAddCircle)) =
      complexExponentialQuotientEquiv X (dim X.left)
        (QuotientAddGroup.mk (t • (l : Fin (dim X.left) → ℂ))) := by
    change oneParameterSubgroup X (dim X.left) (l : Fin (dim X.left) → ℂ) t =
      complexExponential X (dim X.left) (t • (l : Fin (dim X.left) → ℂ))
    rw [complexExponential_smul]
  have h2 : complexPointTorusHomeomorph X (dim X.left) (abelianLatticeLoop X l (t : UnitAddCircle)) =
      LatticeTorus.quotientEquivOfBasis (abelianPeriodLattice X) (abelianLatticeBasis X)
        (QuotientAddGroup.mk (t • (l : Fin (dim X.left) → ℂ))) := by
    change complexPointUniformization X (dim X.left)
      (Additive.ofMul (abelianLatticeLoop X l (t : UnitAddCircle))) = _
    rw [h1]
    exact congrArg (LatticeTorus.quotientEquivOfBasis (abelianPeriodLattice X)
      (abelianLatticeBasis X)) ((complexExponentialQuotientEquiv X (dim X.left)).symm_apply_apply _)
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [h2, LatticeTorus.quotientEquivOfBasis_mk, map_smul, Finsupp.smul_apply]
  change _ = ((abelianLatticeBasis X).repr l i) • ((t : ℝ) : UnitAddCircle)
  rw [← QuotientAddGroup.mk_zsmul]
  congr 1
  rw [smul_eq_mul, zsmul_eq_mul, mul_comm]
  congr 1
  exact Module.Basis.ofZLatticeBasis_repr_apply ℝ (abelianPeriodLattice X) _ l i

/-- The S12 periods are torus periods at the S12 basis coordinates. -/
theorem abelianPeriod_eq_torusPeriod (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X x l =
      torusPeriod (2 * dim X.left) (abelianTorusComparison X 1 x)
        ((abelianLatticeBasis X).repr l) := by
  change _ = loopPeriod (torusLoop ((abelianLatticeBasis X).repr l))
    (cohomologyHomeomorphEquiv (complexPointTorusHomeomorph X (dim X.left)) 1
      (cupComparison X 1 x))
  rw [← complexPointTorusHomeomorph_comp_abelianLatticeLoop, loopPeriod_comp,
    ← cohomologyHomeomorphEquiv_symm, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

/-- The rational basis of `HQ X 1` transported from the coordinate basis of the model torus. -/
def abelianH1Basis : Module.Basis (Fin (2 * dim X.left)) ℚ (HQ X 1) :=
  (torusCoordinateBasis (2 * dim X.left)).map (abelianTorusComparison X 1).symm

/-- The S12 periods in coordinates: `Σⱼ xⱼ lⱼ`. -/
theorem abelianPeriod_eq_sum (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X x l =
      ∑ j, (abelianH1Basis X).repr x j * (abelianLatticeBasis X).repr l j := by
  rw [abelianPeriod_eq_torusPeriod, torusPeriod_eq_sum]
  simp [abelianH1Basis]

theorem spec_abelianPeriod_add_aux (x : HQ X 1) (l l' : abelianPeriodLattice X) :
    abelianPeriod X x (l + l') = abelianPeriod X x l + abelianPeriod X x l' := by
  simp only [abelianPeriod_eq_sum, map_add, Finsupp.add_apply, Int.cast_add, mul_add,
    Finset.sum_add_distrib]

theorem spec_abelianPeriod_torus_aux (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X x l =
      torusPeriod (2 * dim X.left) (abelianTorusComparison X 1 x)
        ((abelianLatticeBasis X).repr l) :=
  abelianPeriod_eq_torusPeriod X x l

theorem spec_abelianPeriod_equiv_aux :
    ∃ e : HQ X 1 ≃ₗ[ℚ] (abelianPeriodLattice X →+ ℚ),
      ∀ x l, e x l = abelianPeriod X x l := by
  obtain ⟨e, he⟩ := exists_equiv_addMonoidHom_of_basis (abelianLatticeBasis X) (abelianH1Basis X)
  exact ⟨e, fun x l => by rw [he, abelianPeriod_eq_sum]⟩

/-- The S12 lattice basis as a real basis of `ℂ^g` (the lattice is full).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; Mathlib
`Module.Basis.ofZLatticeBasis`. -/
def abelianRealBasis : Module.Basis (Fin (2 * dim X.left)) ℝ (Fin (dim X.left) → ℂ) :=
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  letI := isZLattice_complexExponentialLattice X (dim X.left)
  (abelianLatticeBasis X).ofZLatticeBasis ℝ (abelianPeriodLattice X)

theorem abelianRealBasis_apply (i : Fin (2 * dim X.left)) :
    abelianRealBasis X i = (abelianLatticeBasis X i : Fin (dim X.left) → ℂ) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  let := isZLattice_complexExponentialLattice X (dim X.left)
  exact Module.Basis.ofZLatticeBasis_apply ℝ (abelianPeriodLattice X) _ i

theorem abelianRealBasis_repr (l : abelianPeriodLattice X) (i : Fin (2 * dim X.left)) :
    (abelianRealBasis X).repr l i = (abelianLatticeBasis X).repr l i := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  let := isZLattice_complexExponentialLattice X (dim X.left)
  exact Module.Basis.ofZLatticeBasis_repr_apply ℝ (abelianPeriodLattice X) _ l i

/-- The complexified period isomorphism `ℂ ⊗[ℚ] HQ X 1 ≃ Hom_ℝ(ℂ^g, ℂ)`: the class with
coordinates `c` goes to the real functional taking the value `cᵢ` on the `i`-th lattice basis
vector. -/
def abelianPeriodComplexEquiv : ℂ ⊗[ℚ] HQ X 1 ≃ₗ[ℂ] DegreeOneLatticeDual (dim X.left) :=
  ((abelianH1Basis X).baseChange ℂ).equivFun ≪≫ₗ (abelianRealBasis X).constr ℂ

theorem abelianPeriodComplexEquiv_tmul (c : ℂ) (x : HQ X 1) (v : Fin (dim X.left) → ℂ) :
    abelianPeriodComplexEquiv X (c ⊗ₜ x) v =
      ∑ i, ((abelianRealBasis X).repr v i : ℂ) * ((abelianH1Basis X).repr x i : ℂ) * c := by
  simp only [abelianPeriodComplexEquiv, LinearEquiv.trans_apply]
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.real_smul, ← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul, mul_assoc]

theorem latticeRestriction_abelianPeriodComplexEquiv (ω : ℂ ⊗[ℚ] HQ X 1) :
    latticeRestriction X (abelianPeriodComplexEquiv X ω) = complexAbelianPeriod X ω := by
  induction ω with
  | add ω ω' h h' => rw [map_add, map_add, h, h', map_add]
  | tmul c x =>
    funext l
    have h : complexAbelianPeriod X (c ⊗ₜ x) l = c * (abelianPeriod X x l : ℂ) := by
      simp [complexAbelianPeriod]
    rw [h, abelianPeriod_eq_sum]
    change abelianPeriodComplexEquiv X (c ⊗ₜ x) l = _
    rw [abelianPeriodComplexEquiv_tmul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abelianRealBasis_repr]
    push_cast
    ring

theorem latticeRestriction_injective : Function.Injective (latticeRestriction X) := by
  intro f f' h
  refine (abelianRealBasis X).ext fun i => ?_
  have hi := congrFun h (abelianLatticeBasis X i)
  rw [abelianRealBasis_apply]
  exact hi

theorem complexHolomorphicH1_eq :
    complexHolomorphicH1 X = (degreeOneLatticeHolomorphic (dim X.left)).comap
      (abelianPeriodComplexEquiv X).toLinearMap := by
  ext ω
  simp only [complexHolomorphicH1, Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe,
    ← latticeRestriction_abelianPeriodComplexEquiv]
  exact ⟨fun ⟨f, hf, he⟩ => latticeRestriction_injective X he ▸ hf, fun h => ⟨_, h, rfl⟩⟩

theorem complexAntiholomorphicH1_eq :
    complexAntiholomorphicH1 X = (degreeOneLatticeAntiholomorphic (dim X.left)).comap
      (abelianPeriodComplexEquiv X).toLinearMap := by
  ext ω
  simp only [complexAntiholomorphicH1, Submodule.mem_comap, Submodule.mem_map,
    LinearEquiv.coe_coe, ← latticeRestriction_abelianPeriodComplexEquiv]
  exact ⟨fun ⟨f, hf, he⟩ => latticeRestriction_injective X he ▸ hf, fun h => ⟨_, h, rfl⟩⟩

/-- Rational conjugation corresponds to conjugating the values of the real functional. -/
theorem abelianPeriodComplexEquiv_sigmaQ (ω : ℂ ⊗[ℚ] HQ X 1) :
    abelianPeriodComplexEquiv X (HodgeBlocks.sigmaQ (HQ X 1) ω) =
      degreeOneLatticeConjugate (dim X.left) (abelianPeriodComplexEquiv X ω) := by
  induction ω with
  | add ω ω' h h' =>
    rw [map_add, map_add, h, h']
    refine LinearMap.ext fun v => ?_
    simp [degreeOneLatticeConjugate]
  | tmul c x =>
    refine LinearMap.ext fun v => ?_
    change abelianPeriodComplexEquiv X (HodgeBlocks.sigmaQR (HQ X 1) (c ⊗ₜ x)) v =
      star (abelianPeriodComplexEquiv X (c ⊗ₜ x) v)
    rw [HodgeBlocks.sigmaQ_tmul, abelianPeriodComplexEquiv_tmul, abelianPeriodComplexEquiv_tmul]
    simp

theorem spec_complexAbelianPeriod_restriction_aux :
    ∃ Φ : ℂ ⊗[ℚ] HQ X 1 ≃ₗ[ℂ] DegreeOneLatticeDual (dim X.left),
      ∀ ω, latticeRestriction X (Φ ω) = complexAbelianPeriod X ω :=
  ⟨abelianPeriodComplexEquiv X, latticeRestriction_abelianPeriodComplexEquiv X⟩

theorem spec_complexH1_split_aux :
    complexHolomorphicH1 X ⊔ complexAntiholomorphicH1 X = ⊤ ∧
      Disjoint (complexHolomorphicH1 X) (complexAntiholomorphicH1 X) := by
  rw [complexHolomorphicH1_eq, complexAntiholomorphicH1_eq,
    Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm]
  refine ⟨?_, Submodule.disjoint_map (abelianPeriodComplexEquiv X).symm.injective
    (spec_H1_lattice_disjoint _)⟩
  rw [← Submodule.map_sup, spec_H1_lattice_split, Submodule.map_top, LinearEquiv.range]

theorem spec_complexH1_dimension_aux :
    Module.finrank ℂ (complexHolomorphicH1 X) = dim X.left ∧
      Module.finrank ℂ (complexAntiholomorphicH1 X) = dim X.left := by
  rw [complexHolomorphicH1_eq, complexAntiholomorphicH1_eq,
    Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
  exact ⟨spec_H1_lattice_holomorphic_dimension _, spec_H1_lattice_antiholomorphic_dimension _⟩

theorem spec_complexH1_conjugation_exchanges_aux :
    (complexHolomorphicH1 X).map (HodgeBlocks.sigmaQ (HQ X 1)) = complexAntiholomorphicH1 X := by
  rw [complexHolomorphicH1_eq, complexAntiholomorphicH1_eq]
  ext ω
  simp only [Submodule.mem_map, Submodule.mem_comap, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨ω', hω', rfl⟩
    rw [abelianPeriodComplexEquiv_sigmaQ]
    exact (spec_H1_lattice_conjugation_exchanges _).1 _ hω'
  · intro hω
    refine ⟨HodgeBlocks.sigmaQ (HQ X 1) ω, ?_, HodgeBlocks.sigmaQ_involutive _ ω⟩
    rw [abelianPeriodComplexEquiv_sigmaQ]
    exact (spec_H1_lattice_conjugation_exchanges _).2 _ hω

end HodgeLean.Adapters
