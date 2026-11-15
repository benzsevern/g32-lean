import HodgeLean.Adapters.HolomorphicPeriodsCocycleDefs
import HodgeLean.Adapters.HolomorphicPeriodsOnX

/-! # Proof obligations for `HolomorphicPeriodsCocycle`

One `_aux` per statement of `HodgeLean.Adapters.HolomorphicPeriodsCocycle`. All eleven are proved, by two parallel provers.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped Simplicial TensorProduct

namespace HodgeLean.Adapters

private theorem cochain_ext_simplex {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ}
    (φ ψ : AlgebraicTopology.Simplicial.Cochain R Y n)
    (h : ∀ σ : Y _⦋n⦌, φ (AlgebraicTopology.Simplicial.chainOfSimplex R σ) =
      ψ (AlgebraicTopology.Simplicial.chainOfSimplex R σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • AlgebraicTopology.Simplicial.chainOfSimplex R σ := by
      rw [AlgebraicTopology.Simplicial.chainOfSimplex, ← map_smul]
      simp
    change φ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

theorem spec_simplexCochain_chainOfSimplex_aux (R : Type) [CommRing R] (Y : SSet.{0}) (n : ℕ)
    (f : Y _⦋n⦌ → R) (σ : Y _⦋n⦌) :
    simplexCochain R Y n f (AlgebraicTopology.Simplicial.chainOfSimplex R σ) = f σ := by
  have h := (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n).fac
    (Limits.Cofan.mk _ fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f σ))) ⟨σ⟩
  have h1 := ConcreteCategory.congr_hom h (1 : R)
  change simplexCochain R Y n f ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) = f σ
  refine h1.trans ?_
  simp

private theorem exists_lift_stdSimplex_three {E Y : Type} [TopologicalSpace E]
    [TopologicalSpace Y] {p : E → Y} (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (f : C(Convexity.StdSimplex ℝ (Fin 3), Y)) :
    ∃ F : C(Convexity.StdSimplex ℝ (Fin 3), E), ∀ z, p (F z) = f z := by
  have he := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)
  set S := Set.range (fun t ↦ ⇑t.weights : Convexity.StdSimplex ℝ (Fin 3) → Fin 3 → ℝ) with hSdef
  have hS : Convex ℝ S := by
    rw [hSdef, Convexity.StdSimplex.range_toFun_comp_weights]
    refine Convex.inter (convex_iInter fun i ↦ ?_) ?_
    · exact convex_halfSpace_ge (f := fun s : Fin 3 → ℝ ↦ s i)
        ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 0
    · exact convex_hyperplane (f := fun s : Fin 3 → ℝ ↦ ∑ i, s i)
        ⟨fun _ _ ↦ by simp [Finset.sum_add_distrib], fun _ _ ↦ by simp [Finset.mul_sum]⟩ 1
  have hne : S.Nonempty := ⟨_, ⟨Convexity.StdSimplex.single 0, rfl⟩⟩
  have := hS.contractibleSpace hne
  have := hS.locallyPathConnectedSpace
  let h := he.toHomeomorph
  obtain ⟨e₀, he₀⟩ := hs (f (h.symm (h (Convexity.StdSimplex.single 0))))
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hp.existsUnique_continuousMap_lifts (f.comp ⟨h.symm, h.symm.continuous⟩)
    (h (Convexity.StdSimplex.single 0)) e₀ he₀
  refine ⟨F.comp ⟨h, h.continuous⟩, fun z ↦ ?_⟩
  have := congrFun hF (h z)
  simpa using this

theorem spec_holomorphicPathIntegral_simplexPath_faces_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (τ : (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) _⦋1 + 1⦌) :
    holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 1 τ)) =
      holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 2 τ)) +
        holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 0 τ)) := by
  obtain ⟨T, hT⟩ := exists_lift_stdSimplex_three (spec_isCoveringMap_complexExponential X d)
    (Additive.toMul.surjective.comp (surjective_complexExponential X d))
    ((TopCat.of (ComplexPoint X)).toSSetObjEquiv _ τ)
  have key : ∀ i : Fin 3,
      expLiftDisplacement X d (simplexPath ((TopCat.toSSet.obj _).δ i τ)) =
        T (Convexity.StdSimplex.single (i.succAbove 1)) -
          T (Convexity.StdSimplex.single (i.succAbove 0)) := by
    intro i
    rw [spec_expLiftDisplacement_eq X d _ (T.comp
      ⟨fun t ↦ Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.homeomorphI.symm t),
        (Convexity.StdSimplex.continuous_map (R := ℝ) _).comp
          Convexity.StdSimplex.homeomorphI.symm.continuous⟩) fun t ↦ hT _]
    simp [Convexity.StdSimplex.map_single]
  have h10 : (1 : Fin 3).succAbove 0 = 0 := rfl
  have h11 : (1 : Fin 3).succAbove 1 = 2 := rfl
  have h20 : (2 : Fin 3).succAbove 0 = 0 := rfl
  have h21 : (2 : Fin 3).succAbove 1 = 1 := rfl
  have h00 : (0 : Fin 3).succAbove 0 = 1 := rfl
  have h01 : (0 : Fin 3).succAbove 1 = 2 := rfl
  simp only [holomorphicPathIntegral, key, h10, h11, h20, h21, h00, h01, ← map_add]
  congr 1
  abel

theorem spec_coboundary_singularIntegrationCochain_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    AlgebraicTopology.Simplicial.coboundary ℂ 1 (singularIntegrationCochain X d θ) = 0 := by
  refine cochain_ext_simplex _ _ fun τ ↦ ?_
  rw [AlgebraicTopology.Simplicial.coboundary_chainOfSimplex, LinearMap.zero_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, singularIntegrationCochain,
    spec_simplexCochain_chainOfSimplex_aux]
  have h := spec_holomorphicPathIntegral_simplexPath_faces_aux X d θ τ
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h ⊢
  rw [h]
  simp

theorem spec_simplexPath_loopSimplex_aux {T : Type} [TopologicalSpace T]
    (p : C(UnitAddCircle, T)) :
    simplexPath (loopSimplex p) = p.comp ⟨fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle),
      (AddCircle.continuous_mk' 1).comp continuous_subtype_val⟩ := by
  ext t
  simp [simplexPath, loopSimplex]

theorem spec_singularIntegrationCochain_loopSimplex_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.obj (op ⊤))
    (l : abelianPeriodLattice X) :
    singularIntegrationCochain X (dim X.left) θ
        (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex (abelianLatticeLoop X l))) =
      holomorphicPathIntegral X (dim X.left) θ (abelianLatticePath X l) := by
  rw [singularIntegrationCochain, spec_simplexCochain_chainOfSimplex_aux,
    spec_simplexPath_loopSimplex_aux]
  rfl

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
theorem cohomologyEquivDualHomology_cohomologyClass {R : Type} [Field R] (Y : TopCat.{0})
    (n : ℕ) (ψ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj Y) n)
    (x : LinearMap.ker ((AlgebraicTopology.Singular.SingularChainComplex R Y).sc n).g.hom) :
    AlgebraicTopology.Singular.cohomologyEquivDualHomology R Y n
        (Singular.cohomologyClass Y n ψ)
        (((AlgebraicTopology.Singular.SingularChainComplex R Y).sc n).moduleCatHomologyClass x) =
      ψ.1 x.1 := by
  let K := AlgebraicTopology.Singular.SingularChainComplex R Y
  let e := ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso K n)
  let a : (K.sc n).linearDual.homology :=
    (K.sc n).linearDual.moduleCatHomologyIso.inv.hom
      (Submodule.Quotient.mk ⟨ψ.1, ?_⟩)
  · have h1 : Singular.cohomologyClass Y n ψ = e.inv.hom a := rfl
    have h2 : AlgebraicTopology.Singular.cohomologyEquivDualHomology R Y n (e.inv.hom a) =
        (K.sc n).linearDualHomologyEquiv (e.hom.hom (e.inv.hom a)) := rfl
    rw [h1, h2, show e.hom.hom (e.inv.hom a) = a from ConcreteCategory.congr_hom e.inv_hom_id a]
    exact ShortComplex.linearDualHomologyEquiv_class_apply_class _ _ _
  · change ((K.sc n).f.hom.dualMap) ψ.1 = 0
    have hψ : AlgebraicTopology.Simplicial.coboundary R n ψ.1 = 0 := ψ.2
    change (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).d
      ((ComplexShape.down ℕ).prev n) n).hom.dualMap ψ.1 = 0
    rw [ChainComplex.prev]
    exact hψ

theorem loopSimplex_δ_zero {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T)) :
    (TopCat.toSSet.obj (TopCat.of T)).δ 0 (loopSimplex p) =
      (TopCat.toSSet.obj (TopCat.of T)).δ 1 (loopSimplex p) := by
  apply ((TopCat.of T).toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  have hz : z = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
  subst hz
  simp only [loopSimplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Convexity.StdSimplex.map_single]
  refine congrArg p ?_
  rw [show Fin.succAbove (0 : Fin 2) 0 = 1 from rfl, show Fin.succAbove (1 : Fin 2) 0 = 0 from rfl,
    Convexity.StdSimplex.homeomorphI_single_one, Convexity.StdSimplex.homeomorphI_single_zero]
  change (((1 : unitInterval) : ℝ) : UnitAddCircle) = (((0 : unitInterval) : ℝ) : UnitAddCircle)
  rw [Set.Icc.coe_one, Set.Icc.coe_zero, AddCircle.coe_period, QuotientAddGroup.mk_zero]

theorem d_chainOfSimplex_loopSimplex (R : Type) [CommRing R] {T : Type} [TopologicalSpace T]
    (p : C(UnitAddCircle, T)) (j : ℕ) :
    (((TopCat.toSSet.obj (TopCat.of T)).chainComplex (ModuleCat.of R R)).d 1 j).hom
      (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) = 0 := by
  by_cases hj : j = 0
  · subst hj
    change AlgebraicTopology.Simplicial.boundary R 0 _ = 0
    rw [AlgebraicTopology.Simplicial.boundary_chainOfSimplex, Fin.sum_univ_two,
      loopSimplex_δ_zero]
    simp
  · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
    rfl

/-- The singular `1`-simplex of a loop as a cycle of the degree-one short complex of singular
chains: both faces are the base point.
Source: Hatcher, *Algebraic Topology*, §2.A (a loop is a singular `1`-cycle). -/
def loopCycle (R : Type) [CommRing R] {T : Type} [TopologicalSpace T]
    (p : C(UnitAddCircle, T)) :
    LinearMap.ker
      ((AlgebraicTopology.Singular.SingularChainComplex R (TopCat.of T)).sc 1).g.hom :=
  ⟨AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p),
    d_chainOfSimplex_loopSimplex R p _⟩

example (R : Type) [CommRing R] {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T)) :
    (loopCycle R p).1 = AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem cocycle_loopSimplex_eq_of_class_eq (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T))
    (ψ ψ' : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (h : Singular.cohomologyClass (TopCat.of T) 1 ψ =
      Singular.cohomologyClass (TopCat.of T) 1 ψ') :
    ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) =
      ψ'.1 (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) := by
  let K := AlgebraicTopology.Singular.SingularChainComplex R (TopCat.of T)
  let e := ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso K 1)
  have hmem : ∀ χ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1,
      χ.1 ∈ LinearMap.ker (K.sc 1).linearDual.g.hom := by
    intro χ
    change ((K.sc 1).f.hom.dualMap) χ.1 = 0
    have hχ : AlgebraicTopology.Simplicial.coboundary R 1 χ.1 = 0 := χ.2
    change (((TopCat.toSSet.obj (TopCat.of T)).chainComplex (ModuleCat.of R R)).d
      ((ComplexShape.down ℕ).prev 1) 1).hom.dualMap χ.1 = 0
    rw [ChainComplex.prev]
    exact hχ
  have hcl : ∀ χ : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1,
      Singular.cohomologyClass (TopCat.of T) 1 χ =
        e.inv.hom ((K.sc 1).linearDual.moduleCatHomologyIso.inv.hom
          (Submodule.Quotient.mk ⟨χ.1, hmem χ⟩)) := fun χ ↦ rfl
  rw [hcl, hcl] at h
  have h' := (e.toLinearEquiv.symm.injective h)
  have h'' := (K.sc 1).linearDual.moduleCatHomologyIso.toLinearEquiv.symm.injective h'
  obtain ⟨η, hη⟩ := (Submodule.Quotient.eq _).mp h''
  have hv := congrArg (fun z ↦ (z.1 : Module.Dual R (K.sc 1).X₂)
    (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p))) hη
  let η' : Module.Dual R (K.sc 1).X₃ := η
  have h0 : (show Module.Dual R (K.sc 1).X₂ from ((K.sc 1).linearDual.moduleCatToCycles η).1)
      (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) = 0 := by
    change η' ((K.sc 1).g.hom
      (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p))) = 0
    exact (congrArg η' (d_chainOfSimplex_loopSimplex R p _)).trans (map_zero η')
  rw [h0] at hv
  change 0 = ψ.1 _ - ψ'.1 _ at hv
  exact (sub_eq_zero.mp hv.symm)

theorem spec_cocycle_loopSimplex_eq_of_cohomologyClass_eq_aux (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T))
    (ψ ψ' : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (h : Singular.cohomologyClass (TopCat.of T) 1 ψ =
      Singular.cohomologyClass (TopCat.of T) 1 ψ') :
    ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) =
      ψ'.1 (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) :=
  cocycle_loopSimplex_eq_of_class_eq R p ψ ψ' h

theorem convex_range_stdSimplex_weights (k : ℕ) :
    Convex ℝ (Set.range (fun t ↦ t.weights : Convexity.StdSimplex ℝ (Fin k) → (Fin k → ℝ))) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  refine Convex.inter (convex_iInter fun i ↦ ?_) ?_
  · exact convex_halfSpace_ge (f := fun s : Fin k → ℝ ↦ s i) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 0
  · exact convex_hyperplane (f := fun s : Fin k → ℝ ↦ ∑ i, s i)
      ⟨fun _ _ ↦ Finset.sum_add_distrib, fun c x ↦ by simp [Finset.mul_sum]⟩ 1

/-- The topological standard simplex as the convex subset of `ℝ^k` cut out by its weights.
Source: Mathlib's `Convexity.StdSimplex.isEmbedding_toFun_comp_weights` and
`Convexity.StdSimplex.range_toFun_comp_weights`. -/
def stdSimplexHomeomorphRange (k : ℕ) :
    Convexity.StdSimplex ℝ (Fin k) ≃ₜ
      Set.range (fun t ↦ t.weights : Convexity.StdSimplex ℝ (Fin k) → (Fin k → ℝ)) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin k)).toHomeomorph

example (k : ℕ) (t : Convexity.StdSimplex ℝ (Fin k)) :
    (stdSimplexHomeomorphRange k t : Fin k → ℝ) = t.weights := rfl

/-- The standard simplex is simply connected: it is homeomorphic to a nonempty convex set. -/
instance stdSimplex_simplyConnectedSpace (k : ℕ) :
    SimplyConnectedSpace (Convexity.StdSimplex ℝ (Fin (k + 1))) := by
  have : ContractibleSpace
      (Set.range (fun t ↦ t.weights : Convexity.StdSimplex ℝ (Fin (k + 1)) → (Fin (k + 1) → ℝ))) :=
    (convex_range_stdSimplex_weights (k + 1)).contractibleSpace
      ⟨_, Convexity.StdSimplex.single 0, rfl⟩
  have : ContractibleSpace (Convexity.StdSimplex ℝ (Fin (k + 1))) :=
    (stdSimplexHomeomorphRange (k + 1)).contractibleSpace
  infer_instance

/-- The standard simplex is locally path-connected: it is homeomorphic to a convex set. -/
instance stdSimplex_locallyPathConnectedSpace (k : ℕ) :
    LocallyPathConnectedSpace (Convexity.StdSimplex ℝ (Fin k)) := by
  have := Convex.locallyPathConnectedSpace _ (convex_range_stdSimplex_weights k)
  exact (stdSimplexHomeomorphRange k).isOpenEmbedding.locallyPathConnectedSpace

theorem exists_lift_unitAddCircle {A : Type} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] (f : C(A, UnitAddCircle)) :
    ∃ F : C(A, ℝ), ∀ a, ((F a : ℝ) : UnitAddCircle) = f a := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
  obtain ⟨e₀, he₀⟩ := QuotientAddGroup.mk_surjective (f a₀)
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts f a₀ e₀ he₀
  exact ⟨F, fun a ↦ congrFun hF a⟩

theorem lift_unitAddCircle_eq_add {A : Type} [TopologicalSpace A] [PreconnectedSpace A]
    (F G : C(A, ℝ)) (h : ∀ a, ((F a : ℝ) : UnitAddCircle) = ((G a : ℝ) : UnitAddCircle))
    (a₀ : A) : ∃ k : ℤ, ∀ a, G a = F a + k := by
  have h0 := h a₀
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h0
  obtain ⟨k, hk⟩ := h0
  refine ⟨k, fun a ↦ ?_⟩
  have := (AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq G.continuous
    (F.continuous.add continuous_const) (g₁ := G) (g₂ := fun a ↦ F a + k)
    (funext fun a ↦ by
      change ((G a : ℝ) : UnitAddCircle) = ((F a + k : ℝ) : UnitAddCircle)
      rw [← h a, QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
      exact ⟨k, by simp⟩) a₀ (by
        simp only [zsmul_eq_mul, mul_one] at hk
        linarith)
  exact congrFun this a

theorem simplexCochain_apply_chainOfSimplex (R : Type) [CommRing R] (Y : SSet.{0}) (n : ℕ)
    (f : Y _⦋n⦌ → R) (σ : Y _⦋n⦌) :
    simplexCochain R Y n f (AlgebraicTopology.Simplicial.chainOfSimplex R σ) = f σ := by
  have h := (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n).fac
    (Limits.Cofan.mk _ fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f σ))) ⟨σ⟩
  have h1 := ConcreteCategory.congr_hom h (1 : R)
  change simplexCochain R Y n f ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) = _
  refine h1.trans ?_
  simp

/-- A real lift of a singular `1`-simplex of the circle along the covering `ℝ → ℝ/ℤ`.
Source: Hatcher, *Algebraic Topology*, Proposition 1.33 (lifting criterion); Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`. -/
def circleSimplexLift (σ : (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) _⦋1⦌) :
    C(Convexity.StdSimplex ℝ (Fin 2), ℝ) :=
  Classical.choose (exists_lift_unitAddCircle ((TopCat.of UnitAddCircle).toSSetObjEquiv _ σ))

example (σ : (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) _⦋1⦌) :
    circleSimplexLift σ = Classical.choose
      (exists_lift_unitAddCircle ((TopCat.of UnitAddCircle).toSSetObjEquiv _ σ)) := rfl

theorem circleSimplexLift_spec (σ : (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) _⦋1⦌)
    (z : Convexity.StdSimplex ℝ (Fin 2)) :
    ((circleSimplexLift σ z : ℝ) : UnitAddCircle) =
      (TopCat.of UnitAddCircle).toSSetObjEquiv _ σ z :=
  Classical.choose_spec (exists_lift_unitAddCircle ((TopCat.of UnitAddCircle).toSSetObjEquiv _ σ)) z

/-- The winding number of a singular `1`-simplex of the circle: the difference of the integer
parts of a real lift at its two vertices.
Source: Hatcher, *Algebraic Topology*, §1.1 (lifts along `ℝ → S¹`) and §3.1. -/
def circleWinding (σ : (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) _⦋1⦌) : ℤ :=
  ⌊circleSimplexLift σ (Convexity.StdSimplex.single 1)⌋ -
    ⌊circleSimplexLift σ (Convexity.StdSimplex.single 0)⌋

example (σ : (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) _⦋1⦌) :
    circleWinding σ = ⌊circleSimplexLift σ (Convexity.StdSimplex.single 1)⌋ -
      ⌊circleSimplexLift σ (Convexity.StdSimplex.single 0)⌋ := rfl

theorem circleWinding_eq (σ : (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) _⦋1⦌)
    (F : C(Convexity.StdSimplex ℝ (Fin 2), ℝ))
    (hF : ∀ z, ((F z : ℝ) : UnitAddCircle) = (TopCat.of UnitAddCircle).toSSetObjEquiv _ σ z) :
    circleWinding σ = ⌊F (Convexity.StdSimplex.single 1)⌋ - ⌊F (Convexity.StdSimplex.single 0)⌋ := by
  obtain ⟨k, hk⟩ := lift_unitAddCircle_eq_add F (circleSimplexLift σ)
    (fun z ↦ (hF z).trans (circleSimplexLift_spec σ z).symm) (Convexity.StdSimplex.single 0)
  rw [circleWinding, hk, hk, Int.floor_add_intCast, Int.floor_add_intCast]
  ring

/-- The winding cochain of the circle: the rational singular `1`-cochain with value
`circleWinding σ` on each singular `1`-simplex `σ`.
Source: Hatcher, *Algebraic Topology*, §3.1 (a cochain is a function on singular simplices). -/
def circleWindingCochain :
    AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1 :=
  simplexCochain ℚ _ 1 fun σ ↦ (circleWinding σ : ℚ)

example : circleWindingCochain = simplexCochain ℚ _ 1 fun σ ↦ (circleWinding σ : ℚ) := rfl

theorem coboundary_circleWindingCochain :
    AlgebraicTopology.Simplicial.coboundary ℚ 1 circleWindingCochain = 0 := by
  apply cochain_ext_simplex
  intro τ
  rw [AlgebraicTopology.Simplicial.coboundary_chainOfSimplex, LinearMap.zero_apply,
    Fin.sum_univ_three]
  simp only [circleWindingCochain, simplexCochain_apply_chainOfSimplex]
  obtain ⟨T, hT⟩ := exists_lift_unitAddCircle ((TopCat.of UnitAddCircle).toSSetObjEquiv _ τ)
  have hface : ∀ i : Fin 3, circleWinding ((TopCat.toSSet.obj _).δ i τ) =
      ⌊T (Convexity.StdSimplex.single (i.succAbove 1))⌋ -
        ⌊T (Convexity.StdSimplex.single (i.succAbove 0))⌋ := by
    intro i
    refine (circleWinding_eq _ (T.comp ⟨Convexity.StdSimplex.map i.succAbove, by fun_prop⟩)
      fun z ↦ ?_).trans ?_
    · rw [TopCat.toSSetObjEquiv_δ_apply]
      exact hT _
    · simp [Convexity.StdSimplex.map_single]
  rw [hface 0, hface 1, hface 2]
  simp only [Fin.succAbove_zero, Fin.isValue]
  rw [show (1 : Fin 3).succAbove 0 = 0 from rfl, show (1 : Fin 3).succAbove 1 = 2 from rfl,
    show (2 : Fin 3).succAbove 0 = 0 from rfl, show (2 : Fin 3).succAbove 1 = 1 from rfl]
  push_cast
  norm_num

theorem circleWindingCochain_loopSimplex_id :
    circleWindingCochain (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
      (loopSimplex (ContinuousMap.id UnitAddCircle))) = 1 := by
  rw [circleWindingCochain, simplexCochain_apply_chainOfSimplex,
    circleWinding_eq _ ⟨fun z ↦ (Convexity.StdSimplex.homeomorphI z : ℝ),
      continuous_subtype_val.comp Convexity.StdSimplex.homeomorphI.continuous⟩ (fun z ↦ rfl)]
  simp

theorem eq_circleDegree_smul_circleClass (α : AlgebraicTopology.Singular.Cohomology ℚ
    (TopCat.of UnitAddCircle) 1) : α = circleDegree α • Singular.circleClass := by
  have h := circleClassBasis.sum_repr α
  rw [Fin.sum_univ_one] at h
  have h0 : circleClassBasis 0 = Singular.circleClass := by simp [circleClassBasis]
  rw [h0] at h
  conv_lhs => rw [← h]
  rfl

theorem spec_circleDegree_cohomologyClass_aux :
    ∃ s : ℚ, s ≠ 0 ∧ ∀ χ : AlgebraicTopology.Simplicial.Cocycle ℚ
        (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1,
      circleDegree (Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ) =
        s * χ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) := by
  let hl := ((AlgebraicTopology.Singular.SingularChainComplex ℚ
    (TopCat.of UnitAddCircle)).sc 1).moduleCatHomologyClass
      (loopCycle ℚ (ContinuousMap.id UnitAddCircle))
  let e : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of UnitAddCircle) 1 → ℚ :=
    fun α ↦ AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ _ 1 α hl
  have he : ∀ χ : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1,
      e (Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ) =
        χ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) :=
    fun χ ↦ cohomologyEquivDualHomology_cohomologyClass _ 1 χ _
  have hα : ∀ α, e α = circleDegree α * e Singular.circleClass := by
    intro α
    conv_lhs => rw [eq_circleDegree_smul_circleClass α]
    simp only [e, map_smul]
    rfl
  let W : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1 :=
    ⟨circleWindingCochain, coboundary_circleWindingCochain⟩
  have hc : e Singular.circleClass ≠ 0 := by
    intro h0
    have h1 := he W
    rw [hα, h0, mul_zero] at h1
    exact zero_ne_one (h1.trans circleWindingCochain_loopSimplex_id)
  refine ⟨(e Singular.circleClass)⁻¹, inv_ne_zero hc, fun χ ↦ ?_⟩
  have h := hα (Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ)
  rw [he χ] at h
  rw [h]
  field_simp

theorem coboundary_cochainMap {R : Type} [CommRing R] {Y Z : TopCat.{0}} (f : Z ⟶ Y) (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain R (TopCat.toSSet.obj Y) n) :
    AlgebraicTopology.Simplicial.coboundary R n
        (AlgebraicTopology.Simplicial.cochainMap R (TopCat.toSSet.map f) n φ) =
      AlgebraicTopology.Simplicial.cochainMap R (TopCat.toSSet.map f) (n + 1)
        (AlgebraicTopology.Simplicial.coboundary R n φ) := by
  have h := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Singular.singularCochainComplexMap R f).comm n (n + 1)) φ
  change AlgebraicTopology.Simplicial.coboundary R n
      (AlgebraicTopology.Simplicial.cochainMap R (TopCat.toSSet.map f) n φ) =
    AlgebraicTopology.Simplicial.cochainMap R (TopCat.toSSet.map f) (n + 1)
      (AlgebraicTopology.Simplicial.coboundary R n φ) at h
  exact h

theorem map_loopSimplex {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T)) :
    (TopCat.toSSet.map (TopCat.ofHom p)).app _ (loopSimplex (ContinuousMap.id UnitAddCircle)) =
      loopSimplex p := rfl

theorem spec_loopPeriod_cohomologyClass_aux :
    ∃ s : ℚ, s ≠ 0 ∧ ∀ (T : Type) [TopologicalSpace T] (p : C(UnitAddCircle, T))
        (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of T)) 1),
      loopPeriod p (Singular.cohomologyClass (TopCat.of T) 1 ψ) =
        s * ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) := by
  obtain ⟨s, hs, h⟩ := spec_circleDegree_cohomologyClass_aux
  refine ⟨s, hs, fun T _ p ψ ↦ ?_⟩
  let ψ' : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1 :=
    ⟨AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom p)) 1 ψ.1, by
      change AlgebraicTopology.Simplicial.coboundary ℚ 1 _ = 0
      rw [coboundary_cochainMap, show AlgebraicTopology.Simplicial.coboundary ℚ 1 ψ.1 = 0 from ψ.2,
        map_zero]⟩
  rw [loopPeriod, LinearMap.comp_apply,
    Singular.cohomologyMap_class (TopCat.of T) (TopCat.ofHom p) 1 ψ ψ' rfl, h ψ']
  congr 1
  change ψ.1 (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom p))
    (ModuleCat.of ℚ ℚ)).f 1).hom _) = _
  rw [AlgebraicTopology.Simplicial.chainOfSimplex_map, map_loopSimplex]

section BaseChangeHelpers
open AlgebraicTopology.Singular

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : Module ℚ (CCyclesModel X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

open AlgebraicTopology.Singular in
set_option backward.isDefEq.respectTransparency false in
theorem qToCHomology_moduleCatHomologyClass (X : TopCat.{0}) (n : ℕ)
    (zq : LinearMap.ker ((QChains X).sc n).g.hom) (zc : LinearMap.ker ((CChains X).sc n).g.hom)
    (h : qToCChainGroup X n zq.1 = zc.1) :
    qToCHomology X n (((QChains X).sc n).moduleCatHomologyClass zq) =
      ((CChains X).sc n).moduleCatHomologyClass zc := by
  let S := (QChains X).sc n
  let S' := (CChains X).sc n
  let hC := S'.homologyData.left
  let cq := S.moduleCatCyclesIso.inv.hom zq
  have hq : S.moduleCatHomologyClass zq = S.homologyπ.hom cq :=
    (ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π zq).symm
  have hc : S'.moduleCatHomologyClass zc = S'.homologyπ.hom (S'.moduleCatCyclesIso.inv.hom zc) :=
    (ConcreteCategory.congr_hom S'.moduleCatCyclesIso_inv_π zc).symm
  have h1 := ConcreteCategory.congr_hom (homologyπ_comp_qToCHomology X n) cq
  change qToCHomology X n (S.homologyπ.hom cq) = hC.π.hom (qToCCycles X n cq) at h1
  have hiso : hC.homologyIso.inv = 𝟙 _ := by
    dsimp only [ShortComplex.LeftHomologyData.homologyIso, hC]
    exact S'.leftHomologyIso.inv_hom_id
  have h2 := ConcreteCategory.congr_hom (ShortComplex.LeftHomologyData.π_comp_homologyIso_inv (h := hC))
    (qToCCycles X n cq)
  change hC.homologyIso.inv.hom (hC.π.hom (qToCCycles X n cq)) =
    S'.homologyπ.hom (hC.cyclesIso.inv.hom (qToCCycles X n cq)) at h2
  rw [hiso] at h2
  have h3 : hC.cyclesIso.inv.hom (qToCCycles X n cq) = S'.moduleCatCyclesIso.inv.hom zc := by
    apply (ModuleCat.mono_iff_injective S'.iCycles).mp inferInstance
    have e1 := ConcreteCategory.congr_hom hC.cyclesIso_inv_comp_iCycles (qToCCycles X n cq)
    have e2 := ConcreteCategory.congr_hom S'.moduleCatCyclesIso_inv_iCycles zc
    have e3 := LinearMap.congr_fun (iCycles_comp_qToCChainGroup X n) cq
    have e4 := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles zq
    change S'.iCycles.hom (hC.cyclesIso.inv.hom (qToCCycles X n cq)) = hC.i.hom _ at e1
    change S'.iCycles.hom (S'.moduleCatCyclesIso.inv.hom zc) = zc.1 at e2
    change qToCChainGroup X n (S.iCycles.hom cq) = hC.i.hom (qToCCycles X n cq) at e3
    change S.iCycles.hom cq = zq.1 at e4
    rw [e1, e2, ← e3, e4, h]
  rw [hq, hc, h1, ← h3, ← h2]
  rfl

theorem qToCChainGroup_chainOfSimplex (X : TopCat.{0}) {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    qToCChainGroup X n (AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ) =
      AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ := by
  have := qToCChainGroup_iota X n σ 1
  rw [(algebraMap ℚ ℂ).map_one] at this
  exact this

theorem complexHomologyEquivBaseChange_symm_loopCycle {T : Type} [TopologicalSpace T]
    (p : C(UnitAddCircle, T)) :
    (complexHomologyEquivBaseChange (TopCat.of T) 1).symm
        (((SingularChainComplex ℂ (TopCat.of T)).sc 1).moduleCatHomologyClass (loopCycle ℂ p)) =
      1 ⊗ₜ ((SingularChainComplex ℚ (TopCat.of T)).sc 1).moduleCatHomologyClass
        (loopCycle ℚ p) := by
  apply (complexHomologyEquivBaseChange (TopCat.of T) 1).injective
  refine (LinearEquiv.apply_symm_apply _ _).trans ?_
  refine Eq.trans ?_ (IsBaseChange.equiv_tmul (qToCHomology_isBaseChange (TopCat.of T) 1) 1 _).symm
  refine Eq.trans ?_ (one_smul ℂ _).symm
  exact (qToCHomology_moduleCatHomologyClass _ _ (loopCycle ℚ p) (loopCycle ℂ p)
    (qToCChainGroup_chainOfSimplex _ _)).symm

end BaseChangeHelpers

theorem spec_cohomologyBaseChange_tmul_loopSimplex_aux {T : Type} [TopologicalSpace T]
    (p : C(UnitAddCircle, T))
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (h : Singular.cohomologyClass (TopCat.of T) 1 Ψ =
      cohomologyBaseChange (TopCat.of T) 1 (1 ⊗ₜ Singular.cohomologyClass (TopCat.of T) 1 ψ)) :
    Ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex p)) =
      (ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) : ℂ) := by
  have hE := congrArg (fun a ↦ AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ _ 1 a
    (((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of T)).sc 1).moduleCatHomologyClass
      (loopCycle ℂ p))) h
  simp only [cohomologyEquivDualHomology_cohomologyClass, cohomologyBaseChange,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hE
  refine hE.trans ?_
  let F := LinearMap.liftBaseChange ℂ (Module.Dual.baseChange ℂ ∘ₗ
    (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ (TopCat.of T) 1).toLinearMap)
      (1 ⊗ₜ[ℚ] Singular.cohomologyClass (TopCat.of T) 1 ψ)
  have hF : ∀ v, F (1 ⊗ₜ v) = AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ
      (TopCat.of T) 1 (Singular.cohomologyClass (TopCat.of T) 1 ψ) v • (1 : ℂ) := by
    intro v
    simp only [F, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Module.Dual.baseChange_apply_tmul]
  have s1 := Module.Dual.congr_apply_apply (complexHomologyEquivBaseChange (TopCat.of T) 1) F
    (((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of T)).sc 1).moduleCatHomologyClass
      (loopCycle ℂ p))
  rw [complexHomologyEquivBaseChange_symm_loopCycle] at s1
  have s3 := cohomologyEquivDualHomology_cohomologyClass (TopCat.of T) 1 ψ (loopCycle ℚ p)
  refine s1.trans ((hF _).trans ((congrArg (· • (1 : ℂ)) s3).trans ?_))
  change (ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p))) • (1 : ℂ) = _
  rw [Rat.smul_def, mul_one]

theorem spec_cohomologyBaseChange_loopPeriod_aux :
    ∃ s : ℚ, s ≠ 0 ∧ ∀ (T : Type) [TopologicalSpace T] (p : C(UnitAddCircle, T))
        (x : ℂ ⊗[ℚ] AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of T) 1)
        (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of T)) 1),
      Singular.cohomologyClass (TopCat.of T) 1 Ψ = cohomologyBaseChange (TopCat.of T) 1 x →
        LinearMap.liftBaseChange ℂ (Algebra.linearMap ℚ ℂ ∘ₗ loopPeriod p) x =
          (s : ℂ) * Ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex p)) := by
  obtain ⟨s, hs, h8⟩ := spec_loopPeriod_cohomologyClass_aux
  refine ⟨s, hs, fun T _ p x Ψ hΨ ↦ ?_⟩
  let hC : AlgebraicTopology.Singular.Homology ℂ (TopCat.of T) 1 := ((AlgebraicTopology.Singular.SingularChainComplex ℂ (TopCat.of T)).sc 1).moduleCatHomologyClass
    (loopCycle ℂ p)
  have key : ∀ y, LinearMap.liftBaseChange ℂ (Algebra.linearMap ℚ ℂ ∘ₗ loopPeriod p) y =
      (s : ℂ) * AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ _ 1
        (cohomologyBaseChange (TopCat.of T) 1 y) hC := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a α =>
      obtain ⟨ψ, rfl⟩ := Singular.cohomologyClass_surjective (TopCat.of T) 1 α
      obtain ⟨Ψ', hΨ'⟩ := Singular.cohomologyClass_surjective (R := ℂ) (TopCat.of T) 1
        (cohomologyBaseChange (TopCat.of T) 1 (1 ⊗ₜ Singular.cohomologyClass (TopCat.of T) 1 ψ))
      have e1 := spec_cohomologyBaseChange_tmul_loopSimplex_aux p ψ Ψ' hΨ'
      have e2 : AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ _ 1
          (cohomologyBaseChange (TopCat.of T) 1
            (1 ⊗ₜ Singular.cohomologyClass (TopCat.of T) 1 ψ)) hC =
          Ψ'.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex p)) := by
        rw [← hΨ']
        exact cohomologyEquivDualHomology_cohomologyClass (TopCat.of T) 1 Ψ' (loopCycle ℂ p)
      have ha : a ⊗ₜ[ℚ] Singular.cohomologyClass (TopCat.of T) 1 ψ =
          a • (1 ⊗ₜ Singular.cohomologyClass (TopCat.of T) 1 ψ) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ha, map_smul, map_smul, map_smul, LinearMap.smul_apply]
      rw [e2, e1, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply, h8 T p ψ]
      simp only [Algebra.linearMap_apply, smul_eq_mul, Rat.cast_mul, eq_ratCast]
      ring
    | add y z hy hz => rw [map_add, hy, hz, map_add, map_add, LinearMap.add_apply, mul_add]
  rw [key x, ← hΨ]
  exact congrArg _ (cohomologyEquivDualHomology_cohomologyClass (TopCat.of T) 1 Ψ (loopCycle ℂ p))

theorem complexAbelianPeriod_eq_liftBaseChange (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (ω : ℂ ⊗[ℚ] HQ X 1)
    (l : abelianPeriodLattice X) :
    complexAbelianPeriod X ω l =
      LinearMap.liftBaseChange ℂ (Algebra.linearMap ℚ ℂ ∘ₗ loopPeriod (abelianLatticeLoop X l))
        (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) := by
  induction ω using TensorProduct.inductionOn with
  | tmul a v =>
    simp [complexAbelianPeriod, abelianPeriod, LinearMap.liftBaseChange_tmul, smul_eq_mul]
  | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add, map_add]

theorem spec_periods_of_cohomologyBaseChange_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ)
    (hsing : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ) :
    ∃ s : ℂ, s ≠ 0 ∧
      ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
        bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
          complexAbelianPeriod X ω l = (s * c) *
            holomorphicPathIntegral X (dim X.left) (cycleOneForm X z) (abelianLatticePath X l) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨s, hs, h10⟩ := spec_cohomologyBaseChange_loopPeriod_aux
  refine ⟨(s : ℂ), by exact_mod_cast hs, fun z ω hω l ↦ ?_⟩
  let Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1 :=
    ⟨singularIntegrationCochain X (dim X.left) (cycleOneForm X z),
      spec_coboundary_singularIntegrationCochain_aux X (dim X.left) (cycleOneForm X z)⟩
  have h := hsing z ω hω Ψ rfl
  rw [← map_smul] at h
  have h' := h10 (ComplexPoint X) (abelianLatticeLoop X l) _ (c • Ψ) h.symm
  rw [complexAbelianPeriod_eq_liftBaseChange, h']
  change (s : ℂ) * (c * singularIntegrationCochain X (dim X.left) (cycleOneForm X z)
    (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex (abelianLatticeLoop X l)))) = _
  refine (congrArg (fun t ↦ (s : ℂ) * (c * t))
    (spec_singularIntegrationCochain_loopSimplex_aux X (cycleOneForm X z) l)).trans ?_
  exact (mul_assoc _ _ _).symm

end HodgeLean.Adapters
