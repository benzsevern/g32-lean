import HodgeLean.Adapters.AbelianEndomorphisms
import HodgeLean.Adapters.UniformizationBiholomorphic

/-! # Proof obligations for stage 2 of the geometric commutant

One obligation per statement of `HodgeLean.Adapters.AbelianEndomorphisms2`, in the same order.
All twelve are proved, by two parallel provers. -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped Manifold ContDiff CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem spec_analyticRepresentation_unique_aux
    (A A' : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (h : ∀ v, complexExponential X (dim X.left) (A v) =
      complexExponential X (dim X.left) (A' v)) :
    A = A' := by
  have hD : ∀ v, (A - A') v ∈ complexExponentialLattice X (dim X.left) := fun v => by
    change complexExponential X (dim X.left) ((A - A') v) = 0
    have hadd : complexExponential X (dim X.left) (A' v + (A - A') v) =
        complexExponential X (dim X.left) (A' v) +
          complexExponential X (dim X.left) ((A - A') v) :=
      (complexExponentialHom X (dim X.left)).map_add _ _
    rw [LinearMap.sub_apply, add_sub_cancel, h v] at hadd
    rw [LinearMap.sub_apply]
    exact left_eq_add.mp hadd
  let k : (Fin (dim X.left) → ℂ) → complexExponentialLattice X (dim X.left) :=
    fun v => ⟨(A - A') v, hD v⟩
  have hk : Continuous k :=
    ((A - A').continuous_of_finiteDimensional).subtype_mk _
  refine LinearMap.ext fun v => sub_eq_zero.mp ?_
  have := congrArg Subtype.val
    (PreconnectedSpace.constant (inferInstance : PreconnectedSpace (Fin (dim X.left) → ℂ)) hk
      (x := v) (y := 0))
  simpa [k] using this

omit [GrpObj X] [IsCommMonObj X] in
/-- Morphisms of `X` over `Spec ℂ` are determined by their maps of complex points. -/
private theorem over_hom_ext_of_point_map' {f g : X ⟶ X} (h : Point.map f = Point.map g) :
    f = g := by
  refine Over.OverMorphism.ext ?_
  have hf : f.left ≫ X.hom = X.hom := Over.w f
  have hg : g.left ≫ X.hom = X.hom := Over.w g
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply X.hom x hx a]
  have := congrArg (fun z => z.left)
    (congrFun h (Over.homMk (pointOfClosedPoint X.hom x hx) (by simp) :
      Over.mk (𝟙 (Spec ↧ℂ)) ⟶ X))
  change (pointOfClosedPoint X.hom x hx ≫ f.left) a = (pointOfClosedPoint X.hom x hx ≫ g.left) a
  exact congrArg (fun φ : Spec ↧ℂ ⟶ X.left => φ a) this

theorem spec_eq_of_analyticRepresentation_aux (f f' : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (hA' : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f'.hom (Additive.toMul (complexExponential X (dim X.left) v))) :
    f = f' := by
  refine AbelianEnd.ext (over_hom_ext_of_point_map' X (funext fun p => ?_))
  obtain ⟨v, hv⟩ := surjective_complexExponential X (dim X.left) (Additive.ofMul p)
  have hp : p = Additive.toMul (complexExponential X (dim X.left) v) := by rw [hv]; rfl
  rw [hp, ← hA, ← hA']

/-- Two complex-linear maps lifting the same morphism are equal. -/
private theorem analyticRepresentation_eq_of_lift (h : X ⟶ X)
    (A B : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map h (Additive.toMul (complexExponential X (dim X.left) v)))
    (hB : ∀ v, Additive.toMul (complexExponential X (dim X.left) (B v)) =
      Point.map h (Additive.toMul (complexExponential X (dim X.left) v))) :
    A = B :=
  spec_analyticRepresentation_unique_aux X A B fun v =>
    Additive.toMul.injective ((hA v).trans (hB v).symm)

/-- The sum of lifts of `f` and `g` lifts the pointwise product `f * g`. -/
private theorem analyticRepresentation_lift_add (f g : X ⟶ X)
    (A B : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential X (dim X.left) v)))
    (hB : ∀ v, Additive.toMul (complexExponential X (dim X.left) (B v)) =
      Point.map g (Additive.toMul (complexExponential X (dim X.left) v))) :
    ∀ v, Additive.toMul (complexExponential X (dim X.left) ((A + B) v)) =
      Point.map (f * g) (Additive.toMul (complexExponential X (dim X.left) v)) := fun v => by
  have hm : complexExponential X (dim X.left) ((A + B) v) =
      complexExponential X (dim X.left) (A v) + complexExponential X (dim X.left) (B v) :=
    (complexExponentialHom X (dim X.left)).map_add _ _
  rw [hm, toMul_add, hA, hB]
  exact (MonObj.comp_mul _ _ _).symm

theorem spec_analyticRepresentation_ringHom_aux :
    ∃ ρa : AbelianEnd X →+* Module.End ℂ (Fin (dim X.left) → ℂ), ∀ f v,
      Additive.toMul (complexExponential X (dim X.left) (ρa f v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) := by
  choose ρ hρ using fun f : AbelianEnd X => spec_abelianEnd_analyticRepresentation X f
  refine ⟨{ toFun := ρ
            map_one' := analyticRepresentation_eq_of_lift X _ _ _ (hρ 1) fun v => rfl
            map_mul' := fun f g => analyticRepresentation_eq_of_lift X _ _ _ (hρ (f * g))
               fun v => by
                 rw [Module.End.mul_apply, hρ f, hρ g]
                 rfl
            map_zero' := analyticRepresentation_eq_of_lift X _ _ _ (hρ 0) fun v => by
               change Additive.toMul (complexExponential X (dim X.left) 0) =
                 Additive.toMul (complexExponential X (dim X.left) v) ≫ (1 : X ⟶ X)
               rw [MonObj.comp_one, complexExponential_zero]
               rfl
            map_add' := fun f g => analyticRepresentation_eq_of_lift X _ _ _ (hρ (f + g))
               (analyticRepresentation_lift_add X f.hom g.hom _ _ (hρ f) (hρ g)) }, hρ⟩

omit [IsCommMonObj X] in
/-- Two points of the period lattice with the same rational periods are equal. -/
private theorem abelianPeriodLattice_eq_of_period' {a b : abelianPeriodLattice X}
    (h : ∀ x, abelianPeriod X x a = abelianPeriod X x b) : a = b := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X
  refine (abelianLatticeBasis X).ext_elem fun i => ?_
  let χ : abelianPeriodLattice X →+ ℚ :=
    (Int.castAddHom ℚ).comp ((abelianLatticeBasis X).coord i).toAddMonoidHom
  have hχ := h (e.symm χ)
  rw [← he, ← he, LinearEquiv.apply_symm_apply] at hχ
  have h2 : ((abelianLatticeBasis X).repr a i : ℚ) = (abelianLatticeBasis X).repr b i := hχ
  exact_mod_cast h2

theorem spec_latticeRepresentation_unique_aux (f : AbelianEnd X)
    (φ φ' : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (hφ' : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ' l)) :
    φ = φ' :=
  AddMonoidHom.ext fun l => abelianPeriodLattice_eq_of_period' X fun x => by rw [← hφ, ← hφ']

omit [IsCommMonObj X] in
/-- A complex-linear `A` intertwining the exponential with `f` maps periods to periods. -/
private theorem analyticRepresentation_mem_lattice' (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (l : abelianPeriodLattice X) : A l ∈ abelianPeriodLattice X := by
  have hl : complexExponential X (dim X.left) (l : Fin (dim X.left) → ℂ) = 0 := l.2
  change complexExponential X (dim X.left) (A l) = 0
  apply Additive.toMul.injective
  rw [hA, hl]
  change (1 : ComplexPoint X) ≫ f.hom = 1
  exact MonObj.one_comp f.hom

omit [IsCommMonObj X] in
private theorem analyticRepresentation_loop' (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (l : abelianPeriodLattice X) :
    (Point.continuousMap f.hom).comp (abelianLatticeLoop X l) =
      abelianLatticeLoop X ⟨A l, analyticRepresentation_mem_lattice' X f A hA l⟩ := by
  refine ContinuousMap.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | H t =>
    change Point.map f.hom (Additive.toMul (oneParameterSubgroup X (dim X.left)
        (l : Fin (dim X.left) → ℂ) t)) =
      Additive.toMul (oneParameterSubgroup X (dim X.left) (A l) t)
    rw [← complexExponential_smul, ← complexExponential_smul, ← hA,
      LinearMap.map_smul_of_tower]

omit [IsCommMonObj X] in
/-- The periods of `ρ f x` along `l` are the periods of `x` along `A l`. -/
private theorem abelianPeriod_analyticRepresentation' (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (x : HQ X 1) (l : abelianPeriodLattice X) :
    abelianPeriod X (abelianEndAction X f x) l =
      abelianPeriod X x ⟨A l, analyticRepresentation_mem_lattice' X f A hA l⟩ := by
  rw [abelianPeriod, LinearMap.pi_apply, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, abelianEndAction, complexPointPullback, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, ← loopPeriod_comp, analyticRepresentation_loop' X f A hA]

theorem spec_latticeRepresentation_eq_analytic_aux (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (φ : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (l : abelianPeriodLattice X) :
    ((φ l : abelianPeriodLattice X) : Fin (dim X.left) → ℂ) = A l :=
  congrArg Subtype.val (abelianPeriodLattice_eq_of_period' X
    (b := ⟨A l, analyticRepresentation_mem_lattice' X f A hA l⟩) fun x => by
      rw [← hφ, abelianPeriod_analyticRepresentation' X f A hA])

theorem spec_rationalRepresentation_ringHom_aux :
    ∃ ρr : AbelianEnd X →+* Module.End ℤ (abelianPeriodLattice X), ∀ f x l,
      abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (ρr f l) := by
  obtain ⟨ρa, hρa⟩ := spec_analyticRepresentation_ringHom_aux X
  let r : AbelianEnd X → Module.End ℤ (abelianPeriodLattice X) := fun f =>
    { toFun := fun l => ⟨ρa f l, analyticRepresentation_mem_lattice' X f _ (hρa f) l⟩
      map_add' := fun l m => Subtype.ext (map_add (ρa f) _ _)
      map_smul' := fun n l => Subtype.ext (map_zsmul (ρa f) n (l : Fin (dim X.left) → ℂ)) }
  refine ⟨{ toFun := r
            map_one' := LinearMap.ext fun l => Subtype.ext (by
               change ρa 1 l = l
               rw [map_one]
               rfl)
            map_mul' := fun f g => LinearMap.ext fun l => Subtype.ext (by
               change ρa (f * g) l = ρa f (ρa g l)
               rw [map_mul]
               rfl)
            map_zero' := LinearMap.ext fun l => Subtype.ext (by
               change ρa 0 l = 0
               rw [map_zero]
               rfl)
            map_add' := fun f g => LinearMap.ext fun l => Subtype.ext (by
               change ρa (f + g) l = ρa f l + ρa g l
               rw [map_add]
               rfl) },
    fun f x l => abelianPeriod_analyticRepresentation' X f (ρa f) (hρa f) x l⟩

theorem spec_existsUnique_holomorphic_descent_aux
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X) :
    ∃! F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F ∧
        ∀ v, F (Additive.toMul (complexExponential X (dim X.left) v)) =
          Additive.toMul (complexExponential X (dim X.left) (A v)) := by
  have hA' : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω A :=
    (LinearMap.toContinuousLinearMap A).contMDiff
  refine spec_existsUnique_contMDiff_descent_manifold X (dim X.left) 𝓘(ℂ, Fin (dim X.left) → ℂ)
    (fun v => Additive.toMul (complexExponential X (dim X.left) (A v)))
    ((spec_contMDiff_complexExponential X (dim X.left)).comp hA') fun l hl v => ?_
  have h0 : complexExponential X (dim X.left) (A l) = 0 := hA l hl
  change Additive.toMul (complexExponentialHom X (dim X.left) (A (v + l))) =
    Additive.toMul (complexExponentialHom X (dim X.left) (A v))
  rw [map_add, map_add]
  change Additive.toMul (_ + complexExponential X (dim X.left) (A l)) = _
  rw [h0, add_zero]

theorem spec_descent_map_mul_aux
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (F : ComplexPoint X → ComplexPoint X)
    (hF : ∀ v, F (Additive.toMul (complexExponential X (dim X.left) v)) =
      Additive.toMul (complexExponential X (dim X.left) (A v))) :
    F 1 = 1 ∧ ∀ x y, F (x * y) = F x * F y := by
  have hexp : ∀ v w, Additive.toMul (complexExponential X (dim X.left) (v + w)) =
      Additive.toMul (complexExponential X (dim X.left) v) *
        Additive.toMul (complexExponential X (dim X.left) w) := fun v w =>
    congrArg Additive.toMul ((complexExponentialHom X (dim X.left)).map_add v w)
  refine ⟨?_, fun x y => ?_⟩
  · have := hF 0
    rwa [map_zero, complexExponential_zero, toMul_zero] at this
  · obtain ⟨v, hv⟩ := surjective_complexExponential X (dim X.left) (Additive.ofMul x)
    obtain ⟨w, hw⟩ := surjective_complexExponential X (dim X.left) (Additive.ofMul y)
    have hx : x = Additive.toMul (complexExponential X (dim X.left) v) := by rw [hv]; rfl
    have hy : y = Additive.toMul (complexExponential X (dim X.left) w) := by rw [hw]; rfl
    rw [hx, hy, ← hexp, hF, hF, hF, map_add, hexp]

theorem spec_not_exists_descent_half_aux (hg : 0 < dim X.left) :
    ¬ ∃ F : ComplexPoint X → ComplexPoint X, ∀ v,
      F (Additive.toMul (complexExponential X (dim X.left) v)) =
        Additive.toMul (complexExponential X (dim X.left) ((1 / 2 : ℂ) • v)) := by
  rintro ⟨F, hF⟩
  have hhalf : ∀ l ∈ complexExponentialLattice X (dim X.left),
      (1 / 2 : ℂ) • l ∈ complexExponentialLattice X (dim X.left) := by
    intro l hl
    have h0 : complexExponential X (dim X.left) l = 0 := hl
    change complexExponential X (dim X.left) ((1 / 2 : ℂ) • l) = 0
    apply Additive.toMul.injective
    rw [← hF, h0, ← complexExponential_zero X (dim X.left), hF, smul_zero]
  let b := complexExponentialLatticeBasis X (dim X.left)
  let i : Fin (2 * dim X.left) := ⟨0, by omega⟩
  let m : complexExponentialLattice X (dim X.left) :=
    ⟨(1 / 2 : ℂ) • (b i : Fin (dim X.left) → ℂ), hhalf _ (b i).2⟩
  have h2 : (2 : ℤ) • m = b i := by
    apply Subtype.ext
    change (2 : ℤ) • ((1 / 2 : ℂ) • (b i : Fin (dim X.left) → ℂ)) = _
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    norm_num
  have := congrArg (fun z => b.repr z i) h2
  simp only [map_zsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul] at this
  omega

omit [GrpObj X] [IsCommMonObj X] [IsIntegral X.left] [Smooth X.hom] in
/-- Morphisms into `X` out of a reduced scheme of finite type over `ℂ` are determined by their
maps of complex points. -/
private theorem over_hom_ext_of_point_map_of_isReduced {Y : Over (Spec ↧ℂ)} [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] {f g : Y ⟶ X} (h : Point.map f = Point.map g) : f = g := by
  refine Over.OverMorphism.ext ?_
  have hf : f.left ≫ X.hom = Y.hom := Over.w f
  have hg : g.left ≫ X.hom = Y.hom := Over.w g
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply Y.hom x hx a]
  have := congrArg (fun z => z.left)
    (congrFun h (Over.homMk (pointOfClosedPoint Y.hom x hx) (by simp) :
      Over.mk (𝟙 (Spec ↧ℂ)) ⟶ Y))
  change (pointOfClosedPoint Y.hom x hx ≫ f.left) a = (pointOfClosedPoint Y.hom x hx ≫ g.left) a
  exact congrArg (fun φ : Spec ↧ℂ ⟶ X.left => φ a) this

omit [IsCommMonObj X] in
theorem spec_isMonHom_iff_pointMap_mul_aux (h : X ⟶ X) :
    IsMonHom h ↔ ∀ x y : ComplexPoint X, Point.map h (x * y) = Point.map h x * Point.map h y := by
  constructor
  · intro _ x y
    exact MonObj.mul_comp x y h
  · intro hmul
    have h1 : Point.map h 1 = 1 := by
      have := hmul 1 1
      rw [mul_one] at this
      exact left_eq_mul.mp this
    let s : MonoidalCategory.tensorUnit (Over (Spec ↧ℂ)) ⟶ Over.mk (𝟙 (Spec ↧ℂ)) :=
      Over.homMk (MonoidalCategory.tensorUnit (Over (Spec ↧ℂ))).hom (by simp)
    have hs : s ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
      CartesianMonoidalCategory.toUnit_unique _ _
    have : IsIntegral (MonoidalCategory.tensorObj X X).left :=
      complexSelfProductIntegral_of_isIntegral X
    have : LocallyOfFiniteType (MonoidalCategory.tensorObj X X).hom := by
      change LocallyOfFiniteType (Limits.pullback.fst X.hom X.hom ≫ X.hom)
      infer_instance
    refine ⟨?_, ?_⟩
    · have h1' : (CartesianMonoidalCategory.toUnit _ ≫ η[X]) ≫ h =
          CartesianMonoidalCategory.toUnit _ ≫ η[X] := h1
      calc η[X] ≫ h = s ≫ (CartesianMonoidalCategory.toUnit _ ≫ η[X]) ≫ h := by
            rw [Category.assoc, ← Category.assoc s, hs, Category.id_comp]
        _ = η[X] := by rw [h1', ← Category.assoc, hs, Category.id_comp]
    · apply over_hom_ext_of_point_map_of_isReduced X
      funext z
      change z ≫ μ ≫ h = z ≫ MonoidalCategory.tensorHom h h ≫ μ
      have hz : z = CartesianMonoidalCategory.lift (z ≫ CartesianMonoidalCategory.fst X X)
          (z ≫ CartesianMonoidalCategory.snd X X) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [hz, ← Category.assoc, ← Category.assoc, CartesianMonoidalCategory.lift_map,
        ← Hom.mul_def, ← Hom.mul_def]
      exact hmul _ _

theorem spec_exists_abelianEnd_of_lattice_aux
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X) :
    ∃ f : AbelianEnd X, ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) := by
  obtain ⟨F, ⟨hFhol, hF⟩, -⟩ := spec_existsUnique_holomorphic_descent_aux X A hA
  obtain ⟨h, rfl⟩ := hAlg F hFhol
  have hmon : IsMonHom h :=
    (spec_isMonHom_iff_pointMap_mul_aux X h).2 (spec_descent_map_mul_aux X A _ hF).2
  exact ⟨⟨h, hmon⟩, fun v => (hF v).symm⟩

theorem spec_analyticRepresentation_range_aux
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F) :
    ∃ ρa : AbelianEnd X →+* Module.End ℂ (Fin (dim X.left) → ℂ),
      (∀ f v, Additive.toMul (complexExponential X (dim X.left) (ρa f v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v))) ∧
      Function.Injective ρa ∧
      Set.range ρa = {A | ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X} := by
  obtain ⟨ρa, hρa⟩ := spec_analyticRepresentation_ringHom_aux X
  refine ⟨ρa, hρa, fun f f' hff' => ?_, Set.Subset.antisymm ?_ fun A hA => ?_⟩
  · refine spec_eq_of_analyticRepresentation_aux X f f' (ρa f) (hρa f) fun v => ?_
    rw [hff']
    exact hρa f' v
  · rintro _ ⟨f, rfl⟩ l hl
    have h0 : complexExponential X (dim X.left) l = 0 := hl
    change complexExponential X (dim X.left) (ρa f l) = 0
    apply Additive.toMul.injective
    rw [hρa, h0]
    exact MonObj.one_comp f.hom
  · obtain ⟨f, hf⟩ := spec_exists_abelianEnd_of_lattice_aux X hAlg A hA
    refine ⟨f, spec_analyticRepresentation_unique_aux X _ _ fun v => ?_⟩
    apply Additive.toMul.injective
    rw [hρa, hf]

end HodgeLean.Adapters
