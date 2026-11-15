import HodgeLean.Foundations.AbelianQuotient.Defs
import HodgeLean.Adapters.GagaMaps
import HodgeLean.Adapters.AbelianEndomorphisms2

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
namespace HodgeLean.Foundations.AbelianQuotient

theorem multiplication_nat_hom (A : Variety) (n : ℕ) :
    (multiplication A n).hom = (𝟙 A.X) ^ (n : ℤ) := by
  change ((n : ℤ) : AbelianEnd A.X).hom = _
  rw [Int.cast_natCast, zpow_natCast]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, AbelianEnd.add_hom, ih,
      AbelianEnd.one_hom, pow_succ]

/-- The period lattice of a complex abelian variety is countable. -/
private theorem abq_countable_periodLattice (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Countable (abelianPeriodLattice X) :=
  (abelianLatticeBasis X).equivFun.toEquiv.countable_iff.mpr inferInstance

/-- Two velocities with the same exponential differ by a period. -/
private theorem abq_sub_mem_periodLattice (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsCommMonObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {v w : Fin (dim X.left) → ℂ}
    (h : complexExponential X (dim X.left) v = complexExponential X (dim X.left) w) :
    v - w ∈ abelianPeriodLattice X := by
  change complexExponentialHom X (dim X.left) (v - w) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

private theorem abq_analyticRepresentation_injective (P Q : Variety)
    (f : P.X ⟶ Q.X) (hf : ccm2_IsogenyOnPoints f)
    (A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential Q.X (dim Q.X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential P.X (dim P.X.left) v))) :
    Function.Injective A := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hv0
  let T : ℂ → ComplexPoint P.X := fun t =>
    Additive.toMul (complexExponential P.X (dim P.X.left) (t • v))
  have hT : range T ⊆ {x : ComplexPoint P.X | Point.map f x = 1} := by
    rintro _ ⟨t, rfl⟩
    change Point.map f (T t) = 1
    rw [← hA, map_smul, hv, smul_zero, complexExponential_zero]
    rfl
  have : Countable (range T) := ((hf.1.subset hT).countable).to_subtype
  have := abq_countable_periodLattice P.X
  let c := Function.invFun T
  have hc : ∀ t, T (c (T t)) = T t := fun t => Function.invFun_eq ⟨t, rfl⟩
  let ψ : ℂ → range T × abelianPeriodLattice P.X := fun t =>
    (⟨T t, mem_range_self t⟩, ⟨(t - c (T t)) • v, by
      rw [sub_smul]
      exact abq_sub_mem_periodLattice P.X (congrArg Additive.ofMul (hc t)).symm⟩)
  have hψ : Function.Injective ψ := by
    intro t s hts
    have h1 : T t = T s := congrArg Subtype.val (congrArg Prod.fst hts)
    have h2 : (t - c (T t)) • v = (s - c (T s)) • v :=
      congrArg Subtype.val (congrArg Prod.snd hts)
    rw [h1] at h2
    simpa using smul_left_injective ℂ hv0 h2
  have : Countable ℂ := hψ.countable
  exact not_countable_complex Set.countable_univ

theorem abq_analyticRepresentation_surjective (P Q : Variety)
    (f : P.X ⟶ Q.X) (hs : Function.Surjective (Point.map f))
    (A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential Q.X (dim Q.X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential P.X (dim P.X.left) v))) :
    Function.Surjective A := by
  by_contra hsurj
  obtain ⟨w, hw⟩ := not_forall.mp hsurj
  have hw' : ∀ v, A v ≠ w := fun v h => hw ⟨v, h⟩
  have hlift : ∀ t : ℂ, ∃ v, t • w - A v ∈ abelianPeriodLattice Q.X := by
    intro t
    obtain ⟨x, hx⟩ := hs (Additive.toMul (complexExponential Q.X (dim Q.X.left) (t • w)))
    obtain ⟨v, hv⟩ := surjective_complexExponential P.X (dim P.X.left) (Additive.ofMul x)
    refine ⟨v, abq_sub_mem_periodLattice Q.X ?_⟩
    apply Additive.toMul.injective
    rw [hA, hv]
    exact hx.symm
  choose v hv using hlift
  have := abq_countable_periodLattice Q.X
  let ψ : ℂ → abelianPeriodLattice Q.X := fun t => ⟨t • w - A (v t), hv t⟩
  have hψ : Function.Injective ψ := by
    intro t s hts
    have h : t • w - A (v t) = s • w - A (v s) := congrArg Subtype.val hts
    by_contra hne
    have hne' : t - s ≠ 0 := sub_ne_zero.mpr hne
    apply hw' ((t - s)⁻¹ • (v t - v s))
    rw [map_smul, map_sub, inv_smul_eq_iff₀ hne', sub_smul]
    linear_combination (norm := module) -h
  have : Countable ℂ := hψ.countable
  exact not_countable_complex Set.countable_univ

/-- An injective complex-linear map sending one full lattice of rank `r` into another of rank
`r` has finite cokernel on lattices: a positive multiple of every target period is an image of
a source period. -/
private theorem abq_exists_nsmul_mem_map {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {r : ℕ} (L : Submodule ℤ V) (M : Submodule ℤ W)
    (bL : Module.Basis (Fin r) ℤ L) (bM : Module.Basis (Fin r) ℤ M)
    (A : V →ₗ[ℂ] W) (hinj : Function.Injective A) (hA : ∀ l ∈ L, A l ∈ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ m ∈ M, ∃ l ∈ L, A l = N • m := by
  let AL : Submodule ℤ W := L.map (A.restrictScalars ℤ)
  have hle : AL ≤ M := by
    rintro _ ⟨l, hl, rfl⟩
    exact hA l hl
  let K : Submodule ℤ M := AL.comap M.subtype
  have : Module.Free ℤ M := Module.Free.of_basis bM
  have : Module.Finite ℤ M := Module.Finite.of_basis bM
  have : Module.Free ℤ L := Module.Free.of_basis bL
  have : Module.Finite ℤ L := Module.Finite.of_basis bL
  have hK : Module.finrank ℤ K = Module.finrank ℤ M := by
    have e1 : K ≃ₗ[ℤ] AL := Submodule.comapSubtypeEquivOfLe hle
    have e2 : L ≃ₗ[ℤ] AL :=
      Submodule.equivMapOfInjective (A.restrictScalars ℤ) hinj L
    rw [e1.finrank_eq, ← e2.finrank_eq, Module.finrank_eq_card_basis bL,
      Module.finrank_eq_card_basis bM]
  have : Finite (M ⧸ K.toAddSubgroup) := Submodule.finiteQuotientOfFreeOfRankEq K hK
  refine ⟨K.toAddSubgroup.index, Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite, ?_⟩
  intro m hm
  have h := K.toAddSubgroup.nsmul_index_mem (⟨m, hm⟩ : M)
  obtain ⟨l, hl, hlm⟩ := h
  exact ⟨l, hl, by simpa using hlm⟩

theorem abq_analyticRepresentation_bijective_aux (P Q : Variety)
    (f : P.X ⟶ Q.X) [IsMonHom f] (hf : ccm2_IsogenyOnPoints f) :
    ∃ A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ),
      Function.Bijective A ∧ ∀ v,
        Additive.toMul (complexExponential Q.X (dim Q.X.left) (A v)) =
          Point.map f (Additive.toMul (complexExponential P.X (dim P.X.left) v)) := by
  obtain ⟨A, hA⟩ := spec_abelianHom_analyticRepresentation f
  exact ⟨A, ⟨abq_analyticRepresentation_injective P Q f hf A hA,
    abq_analyticRepresentation_surjective P Q f hf.2 A hA⟩, hA⟩

theorem abq_exists_integral_quasiInverse_lattice_aux (P Q : Variety)
    (A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hbij : Function.Bijective A)
    (hA : ∀ l ∈ abelianPeriodLattice P.X, A l ∈ abelianPeriodLattice Q.X) :
    ∃ (N : ℕ) (B : (Fin (dim Q.X.left) → ℂ) →ₗ[ℂ]
        (Fin (dim P.X.left) → ℂ)),
      0 < N ∧
      (∀ l ∈ abelianPeriodLattice Q.X, B l ∈ abelianPeriodLattice P.X) ∧
      B.comp A = (N : ℂ) • LinearMap.id ∧
      A.comp B = (N : ℂ) • LinearMap.id := by
  let e := LinearEquiv.ofBijective A hbij
  have hdim : dim P.X.left = dim Q.X.left := by
    simpa using e.finrank_eq
  have bQ := (abelianLatticeBasis Q.X).reindex (finCongr (show 2 * dim Q.X.left = 2 * dim P.X.left by rw [hdim]))
  obtain ⟨N, hN, hmem⟩ := abq_exists_nsmul_mem_map (abelianPeriodLattice P.X)
    (abelianPeriodLattice Q.X) (abelianLatticeBasis P.X) bQ A hbij.1 hA
  refine ⟨N, (N : ℂ) • (e.symm : (Fin (dim Q.X.left) → ℂ) →ₗ[ℂ] (Fin (dim P.X.left) → ℂ)),
    hN, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨l, hl, hlm⟩ := hmem m hm
    rw [LinearMap.smul_apply, LinearEquiv.coe_coe, ← map_smul, Nat.cast_smul_eq_nsmul, ← hlm,
      show A l = e l from rfl, e.symm_apply_apply]
    exact hl
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.id_apply]
    exact congrArg _ (e.symm_apply_apply v)
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul,
      LinearMap.smul_apply, LinearMap.id_apply]
    exact congrArg _ (e.apply_symm_apply v)

theorem abq_existsUnique_holomorphic_descent_between_aux (P Q : Variety)
    (B : (Fin (dim Q.X.left) → ℂ) →ₗ[ℂ] (Fin (dim P.X.left) → ℂ))
    (hB : ∀ l ∈ abelianPeriodLattice Q.X, B l ∈ abelianPeriodLattice P.X) :
    ∃! F : ComplexPoint Q.X → ComplexPoint P.X,
      ContMDiff (modelWithCornersSelf ℂ (Fin (dim Q.X.left) → ℂ))
        (modelWithCornersSelf ℂ (Fin (dim P.X.left) → ℂ)) ω F ∧
        ∀ v, F (Additive.toMul (complexExponential Q.X (dim Q.X.left) v)) =
          Additive.toMul (complexExponential P.X (dim P.X.left) (B v)) := by
  have hB' : ContMDiff 𝓘(ℂ, Fin (dim Q.X.left) → ℂ) 𝓘(ℂ, Fin (dim P.X.left) → ℂ) ω B :=
    (LinearMap.toContinuousLinearMap B).contMDiff
  refine spec_existsUnique_contMDiff_descent_manifold Q.X (dim Q.X.left)
    𝓘(ℂ, Fin (dim P.X.left) → ℂ)
    (fun v => Additive.toMul (complexExponential P.X (dim P.X.left) (B v)))
    ((spec_contMDiff_complexExponential P.X (dim P.X.left)).comp hB') fun l hl v => ?_
  have h0 : complexExponential P.X (dim P.X.left) (B l) = 0 := hB l hl
  change Additive.toMul (complexExponentialHom P.X (dim P.X.left) (B (v + l))) =
    Additive.toMul (complexExponentialHom P.X (dim P.X.left) (B v))
  rw [map_add, map_add]
  change Additive.toMul (_ + complexExponential P.X (dim P.X.left) (B l)) = _
  rw [h0, add_zero]

/-- Morphisms out of a reduced scheme of finite type over `ℂ` are determined by their maps of
complex points. -/
theorem abq_over_hom_ext_of_point_map {Y X : Over (Spec ↧ℂ)} [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] [IsProjective X.hom] {f g : Y ⟶ X}
    (h : Point.map f = Point.map g) : f = g := by
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

/-- A morphism between group objects whose map of complex points is multiplicative is a morphism
of group objects. -/
private theorem abq_isMonHom_of_point_map_mul {Y X : Over (Spec ↧ℂ)} [GrpObj Y] [GrpObj X]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective X.hom] (h : Y ⟶ X)
    (hmul : ∀ x y : ComplexPoint Y, Point.map h (x * y) = Point.map h x * Point.map h y) :
    IsMonHom h := by
  have h1 : Point.map h 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact left_eq_mul.mp this
  let s : MonoidalCategory.tensorUnit (Over (Spec ↧ℂ)) ⟶ Over.mk (𝟙 (Spec ↧ℂ)) :=
    Over.homMk (MonoidalCategory.tensorUnit (Over (Spec ↧ℂ))).hom (by simp)
  have hs : s ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
    CartesianMonoidalCategory.toUnit_unique _ _
  have : IsIntegral (MonoidalCategory.tensorObj Y Y).left :=
    complexSelfProductIntegral_of_isIntegral Y
  have : LocallyOfFiniteType (MonoidalCategory.tensorObj Y Y).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst Y.hom Y.hom ≫ Y.hom)
    infer_instance
  refine ⟨?_, ?_⟩
  · have h1' : (CartesianMonoidalCategory.toUnit _ ≫ η[Y]) ≫ h =
        CartesianMonoidalCategory.toUnit _ ≫ η[X] := h1
    calc η[Y] ≫ h = s ≫ (CartesianMonoidalCategory.toUnit _ ≫ η[Y]) ≫ h := by
          rw [Category.assoc, ← Category.assoc s, hs, Category.id_comp]
      _ = η[X] := by rw [h1', ← Category.assoc, hs, Category.id_comp]
  · apply abq_over_hom_ext_of_point_map
    funext z
    change z ≫ μ ≫ h = z ≫ MonoidalCategory.tensorHom h h ≫ μ
    have hz : z = CartesianMonoidalCategory.lift (z ≫ CartesianMonoidalCategory.fst Y Y)
        (z ≫ CartesianMonoidalCategory.snd Y Y) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hz, ← Category.assoc, ← Category.assoc, CartesianMonoidalCategory.lift_map,
      ← Hom.mul_def, ← Hom.mul_def]
    exact hmul _ _

/-- The `N`-torsion of the complex points of an abelian variety is finite. -/
theorem abq_finite_pow_kernel (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) (hn : 0 < n) :
    Set.Finite {x : ComplexPoint X | x ^ n = 1} := by
  let e := HodgeLean.Foundations.complexPointUniformization X (TopologicalSpace.dim X.left)
  have hc := AddCircle.finite_torsion (1 : ℝ) hn
  have ht : (Set.univ.pi fun _ : Fin (2 * TopologicalSpace.dim X.left) =>
      {x : UnitAddCircle | n • x = 0}).Finite := Set.Finite.pi fun _ => hc
  refine Set.Finite.of_injOn (f := fun x : ComplexPoint X => e (Additive.ofMul x))
    ?_ (e.injective.comp Additive.ofMul.injective).injOn ht
  intro x hx i _
  have h : n • e (Additive.ofMul x) = 0 := by
    rw [← map_nsmul]
    change e (Additive.ofMul (x ^ n)) = 0
    rw [hx]
    exact map_zero e
  exact congrFun h i

theorem integral_inverse (P Q : Variety) (f : P.X ⟶ Q.X)
    (hf : IsMonHom f) (hi : ccm2_IsogenyOnPoints f) :
    ∃ (N : ℕ) (g : Hom Q P), 0 < N ∧
      g.hom ≫ f = (multiplication Q N).hom ∧
      f ≫ g.hom = (multiplication P N).hom := by
  have : IsMonHom f := hf
  obtain ⟨A, hAbij, hA⟩ := abq_analyticRepresentation_bijective_aux P Q f hi
  have hAl : ∀ l ∈ abelianPeriodLattice P.X, A l ∈ abelianPeriodLattice Q.X := by
    intro l hl
    have h0 : complexExponential P.X (dim P.X.left) l = 0 := hl
    change complexExponential Q.X (dim Q.X.left) (A l) = 0
    apply Additive.toMul.injective
    rw [hA, h0]
    exact MonObj.one_comp f
  obtain ⟨N, B, hN, hBl, hBA, hAB⟩ :=
    abq_exists_integral_quasiInverse_lattice_aux P Q A hAbij hAl
  obtain ⟨F, ⟨hFhol, hF⟩, -⟩ := abq_existsUnique_holomorphic_descent_between_aux P Q B hBl
  obtain ⟨g, rfl⟩ := gagam_algebraize Q.X P.X F hFhol
  have expP_add : ∀ v w, Additive.toMul (complexExponential P.X (dim P.X.left) (v + w)) =
      Additive.toMul (complexExponential P.X (dim P.X.left) v) *
        Additive.toMul (complexExponential P.X (dim P.X.left) w) := fun v w =>
    congrArg Additive.toMul ((complexExponentialHom P.X (dim P.X.left)).map_add v w)
  have expQ_add : ∀ v w, Additive.toMul (complexExponential Q.X (dim Q.X.left) (v + w)) =
      Additive.toMul (complexExponential Q.X (dim Q.X.left) v) *
        Additive.toMul (complexExponential Q.X (dim Q.X.left) w) := fun v w =>
    congrArg Additive.toMul ((complexExponentialHom Q.X (dim Q.X.left)).map_add v w)
  have expQ_nsmul : ∀ v, Additive.toMul (complexExponential Q.X (dim Q.X.left) ((N : ℂ) • v)) =
      Additive.toMul (complexExponential Q.X (dim Q.X.left) v) ^ N := fun v => by
    rw [Nat.cast_smul_eq_nsmul]
    exact congrArg Additive.toMul ((complexExponentialHom Q.X (dim Q.X.left)).map_nsmul N v)
  have surjQ : ∀ q : ComplexPoint Q.X,
      ∃ v, Additive.toMul (complexExponential Q.X (dim Q.X.left) v) = q := fun q => by
    obtain ⟨v, hv⟩ := surjective_complexExponential Q.X (dim Q.X.left) (Additive.ofMul q)
    exact ⟨v, by rw [hv]; rfl⟩
  have surjP : ∀ p : ComplexPoint P.X,
      ∃ v, Additive.toMul (complexExponential P.X (dim P.X.left) v) = p := fun p => by
    obtain ⟨v, hv⟩ := surjective_complexExponential P.X (dim P.X.left) (Additive.ofMul p)
    exact ⟨v, by rw [hv]; rfl⟩
  have hfg : ∀ q, Point.map f (Point.map g q) = q ^ N := by
    intro q
    obtain ⟨v, rfl⟩ := surjQ q
    rw [hF, ← hA, ← LinearMap.comp_apply, hAB, LinearMap.smul_apply, LinearMap.id_apply,
      expQ_nsmul]
  have hmon : IsMonHom g := by
    apply abq_isMonHom_of_point_map_mul
    intro x y
    obtain ⟨v, rfl⟩ := surjQ x
    obtain ⟨w, rfl⟩ := surjQ y
    rw [← expQ_add, hF, hF, hF, map_add, expP_add]
  refine ⟨N, ⟨g, hmon⟩, hN, ?_, ?_⟩
  · apply abq_over_hom_ext_of_point_map
    funext q
    rw [Point.map_comp_apply, hfg]
    rw [multiplication_nat_hom]
    change q ^ N = q ≫ 𝟙 Q.X ^ (N : ℤ)
    rw [GrpObj.comp_zpow, Category.comp_id, zpow_natCast]
  · apply abq_over_hom_ext_of_point_map
    funext p
    obtain ⟨v, rfl⟩ := surjP p
    rw [Point.map_comp_apply, ← hA, hF, ← LinearMap.comp_apply, hBA,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [multiplication_nat_hom]
    change Additive.toMul (complexExponential P.X (dim P.X.left) ((N : ℂ) • v)) =
      Additive.toMul (complexExponential P.X (dim P.X.left) v) ≫ 𝟙 P.X ^ (N : ℤ)
    rw [GrpObj.comp_zpow, Category.comp_id, zpow_natCast, Nat.cast_smul_eq_nsmul]
    exact congrArg Additive.toMul ((complexExponentialHom P.X (dim P.X.left)).map_nsmul N v)

end HodgeLean.Foundations.AbelianQuotient
