import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import Mathlib.Tactic.NormNum

/-! # Independent tests for local normalization and variance

Point classes and a two-point exchange are actual singular classes and maps.
No statement module is imported.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Convexity
namespace AlgebraicTopology.Simplicial

variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in

private lemma coboundary_cochainMap {X Y : SSet.{0}} (f : X ⟶ Y) (p : ℕ)
    (phi : Cochain R Y p) :
    coboundary R p (cochainMap R f p phi) =
      cochainMap R f (p + 1) (coboundary R p phi) := by
  ext c
  change phi (((SSet.chainComplexMap f (ModuleCat.of R R)).f p).hom
      (((X.chainComplex (ModuleCat.of R R)).d (p + 1) p).hom c)) =
    phi (((Y.chainComplex (ModuleCat.of R R)).d (p + 1) p).hom
      (((SSet.chainComplexMap f (ModuleCat.of R R)).f (p + 1)).hom c))
  exact congrArg phi (ConcreteCategory.congr_hom
    ((SSet.chainComplexMap f (ModuleCat.of R R)).comm (p + 1) p) c).symm


private def cocycleMap {X Y : SSet.{0}} (f : X ⟶ Y) (p : ℕ) :
    Cocycle R Y p →ₗ[R] Cocycle R X p :=
  (cochainMap R f p).restrict
    (fun phi hphi ↦ by
      change coboundary R p (cochainMap R f p phi) = 0
      rw [coboundary_cochainMap, show coboundary R p phi = 0 from hphi, map_zero])

@[simp]
private lemma cocycleMap_val {X Y : SSet.{0}} (f : X ⟶ Y) (p : ℕ)
    (phi : Cocycle R Y p) :
    (cocycleMap R f p phi).1 = cochainMap R f p phi.1 := rfl

set_option backward.isDefEq.respectTransparency false in

private theorem capHomologyMap_naturality {X Y : SSet.{0}} (f : X ⟶ Y) (p q : ℕ)
    (phi : Cocycle R Y p) :
    (HomologicalComplex.homologyMap (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp
        (capHomologyMap R p q (cocycleMap R f p phi).1
          (cocycleMap R f p phi).2) =
      (capHomologyMap R p q phi.1 phi.2).comp
        (HomologicalComplex.homologyMap
          (SSet.chainComplexMap f (ModuleCat.of R R)) (p + q)).hom := by
  let F := SSet.chainComplexMap f (ModuleCat.of R R)
  let Fpq := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{0} R) (ComplexShape.down ℕ) (p + q)).map F
  let Fq := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{0} R) (ComplexShape.down ℕ) q).map F
  have h :
      ShortComplex.homologyMap
        (capShortComplexHom R p q (cocycleMap R f p phi).1
          (cocycleMap R f p phi).2 ≫ Fq) =
      ShortComplex.homologyMap (Fpq ≫ capShortComplexHom R p q phi.1 phi.2) := by
    apply homologyMap_eq_of_τ₂_eq
    simp only [ShortComplex.comp_τ₂, capShortComplexHom_τ₂]
    exact ModuleCat.hom_ext (LinearMap.ext fun c => cap_naturality R f p q phi.1 c)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h
  exact congrArg ModuleCat.Hom.hom h


private def cochainCohomologyMap {X Y : SSet.{0}} (f : X ⟶ Y) (p : ℕ) :
    CochainCohomology R Y p →ₗ[R] CochainCohomology R X p :=
  (ShortComplex.homologyMap (ShortComplex.linearDualMap
    ((HomologicalComplex.shortComplexFunctor
      (ModuleCat.{0} R) (ComplexShape.down ℕ) p).map
        (SSet.chainComplexMap f (ModuleCat.of R R))))).hom

set_option backward.isDefEq.respectTransparency false in

private theorem capCohomologyLinear_naturality {X Y : SSet.{0}} (f : X ⟶ Y) (p q : ℕ)
    (alpha : CochainCohomology R Y p) :
    (HomologicalComplex.homologyMap (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp
        (capCohomologyLinear R p q (cochainCohomologyMap R f p alpha)) =
      (capCohomologyLinear R p q alpha).comp
        (HomologicalComplex.homologyMap
          (SSet.chainComplexMap f (ModuleCat.of R R)) (p + q)).hom := by
  let S := (X.chainComplex (ModuleCat.of R R)).sc p
  let T := (Y.chainComplex (ModuleCat.of R R)).sc p
  let F := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{0} R) (ComplexShape.down ℕ) p).map
      (SSet.chainComplexMap f (ModuleCat.of R R))
  obtain ⟨phi, rfl⟩ := T.linearDual.moduleCatHomologyClass_surjective alpha
  change (HomologicalComplex.homologyMap
      (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp (capCohomologyLinear R p q
      ((ShortComplex.homologyMap (ShortComplex.linearDualMap F)).hom
        (T.linearDual.moduleCatHomologyClass phi))) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  change (HomologicalComplex.homologyMap
      (SSet.chainComplexMap f (ModuleCat.of R R)) q).hom.comp (capCohomologyLinear R p q
      (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk _))) =
    (capCohomologyLinear R p q
      (T.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi))).comp _
  rw [capCohomologyLinear_on_cycle, capCohomologyLinear_on_cycle]
  exact capHomologyMap_naturality R f p q (cohomologyCycleToCocycle R p phi)

end AlgebraicTopology.Simplicial

namespace AlgebraicTopology.Singular

variable (R : Type) [CommRing R]


private def cocycleMap {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ) :
    Cocycle R Y p →ₗ[R] Cocycle R X p :=
  Simplicial.cocycleMap R (TopCat.toSSet.map f) p


private theorem capHomologyMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (phi : Cocycle R Y p) (c : Homology R X (p + q)) :
    homologyMap R q f (capHomologyMap R X p q (cocycleMap R f p phi) c) =
      capHomologyMap R Y p q phi (homologyMap R (p + q) f c) :=
  LinearMap.congr_fun
    (Simplicial.capHomologyMap_naturality R (TopCat.toSSet.map f) p q phi) c


private def cochainCohomologyMap {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ) :
    CochainCohomology R Y p →ₗ[R] CochainCohomology R X p :=
  Simplicial.cochainCohomologyMap R (TopCat.toSSet.map f) p


private theorem cochainCohomologyEquiv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ)
    (alpha : CochainCohomology R Y p) :
    cochainCohomologyEquiv R X p (cochainCohomologyMap R f p alpha) =
      cohomologyMap R p f (cochainCohomologyEquiv R Y p alpha) := by
  set eX := (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex R X) p)).toLinearEquiv
  set eY := (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex R Y) p)).toLinearEquiv
  have hnat := congrArg (ShortComplex.homologyFunctor (ModuleCat.{0} R)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality (singularChainComplexMap R f) p)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have ha : eX (cohomologyMap R p f (eY.symm alpha)) =
      cochainCohomologyMap R f p (eY (eY.symm alpha)) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat) (eY.symm alpha)
  rw [eY.apply_symm_apply] at ha
  exact eX.symm_apply_eq.2 ha.symm


private theorem capCohomologyLinear_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (alpha : CochainCohomology R Y p) (c : Homology R X (p + q)) :
    homologyMap R q f
        (capCohomologyLinear R X p q (cochainCohomologyMap R f p alpha) c) =
      capCohomologyLinear R Y p q alpha (homologyMap R (p + q) f c) :=
  LinearMap.congr_fun
    (Simplicial.capCohomologyLinear_naturality R (TopCat.toSSet.map f) p q alpha) c


private def standardCapCohomologyLinear (X : TopCat.{0}) (p q : ℕ) :
    Cohomology R X p →ₗ[R] (Homology R X (p + q) →ₗ[R] Homology R X q) :=
  (capCohomologyLinear R X p q).comp (cochainCohomologyEquiv R X p).symm.toLinearMap


private theorem standardCapCohomologyLinear_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (alpha : Cohomology R Y p) (c : Homology R X (p + q)) :
    homologyMap R q f
        (standardCapCohomologyLinear R X p q (cohomologyMap R p f alpha) c) =
      standardCapCohomologyLinear R Y p q alpha (homologyMap R (p + q) f c) := by
  have hpull :
      (cochainCohomologyEquiv R X p).symm (cohomologyMap R p f alpha) =
        cochainCohomologyMap R f p ((cochainCohomologyEquiv R Y p).symm alpha) := by
    apply (cochainCohomologyEquiv R X p).injective
    rw [LinearEquiv.apply_symm_apply, cochainCohomologyEquiv_naturality,
      LinearEquiv.apply_symm_apply]
  change homologyMap R q f
      (capCohomologyLinear R X p q
        ((cochainCohomologyEquiv R X p).symm (cohomologyMap R p f alpha)) c) = _
  rw [hpull]
  exact capCohomologyLinear_naturality R f p q
    ((cochainCohomologyEquiv R Y p).symm alpha) c

end AlgebraicTopology.Singular

namespace HodgeLean.Foundations.QuotientDuality.LocalTraceChecks

private abbrev P := TopCat.of Unit
private def c : Homology ℚ P 0 :=
  (asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))).inv.hom (1 : ℚ)
private def u : Cohomology ℚ P 0 := cohomologyUnitZero ℚ P
private theorem eval_one : orientationIntegral P 0 c u = 1 := by
  change cohomologyEquivDualHomology ℚ P 0 (cohomologyUnitZero ℚ P) _ = _
  rw [cohomologyEquivDualHomology_cohomologyUnitZero]
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (Iso.inv_hom_id
      (asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))))) 1
private theorem c_ne : c ≠ 0 := by
  intro h
  have he := eval_one
  rw [h] at he
  simp [orientationIntegral] at he

private instance point_projection_iso :
    IsIso (relativeChainProjection ℚ (pointComplementPair (() : P))) := by
  have he : IsEmpty (pointComplementPair (() : P)).snd :=
    ⟨fun z => z.property (Subsingleton.elim z.val ())⟩
  have hz : ((chainPairFunctor ℚ).obj (pointComplementPair (() : P))).hom = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    apply SSet.chainComplex_hom_ext
    intro σ
    exact (he.false (((pointComplementPair (() : P)).snd.toSSetObjEquiv _ σ)
      StdSimplex.barycenter)).elim
  exact CategoryTheory.Limits.cokernel.π_of_zero hz

private def loc : Homology ℚ P 0 ≃ₗ[ℚ] orientationGroup P 0 () :=
  (HomologicalComplex.homologyMapIso
    (asIso (relativeChainProjection ℚ (pointComplementPair (() : P)))) 0).toLinearEquiv
private theorem loc_ne : localOrientation P 0 c () ≠ 0 := loc.map_ne_zero_iff.mpr c_ne

private def pointOrientation : LocalRationalOrientation P 0 where
  generator := fun x => localOrientation P 0 c x
  generates := by
    intro x
    cases x
    let e : ℚ ≃ₗ[ℚ] orientationGroup P 0 () :=
      (asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))).toLinearEquiv.symm.trans loc
    have h : LinearMap.toSpanSingleton ℚ _ (localOrientation P 0 c ()) = e.toLinearMap := by
      apply LinearMap.ext
      intro r
      change r • loc c = loc ((asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))).inv.hom r)
      rw [← map_smul]
      congr 1
      change r • ((asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))).inv.hom 1) = _
      rw [← map_smul]
      congr 1
      exact mul_one r
    rw [h]
    exact e.bijective
  vanishes := by
    intro x i hi
    let ei : Homology ℚ P i ≃ₗ[ℚ] orientationGroup P i () :=
      (HomologicalComplex.homologyMapIso
      (asIso (relativeChainProjection ℚ (pointComplementPair (() : P)))) i).toLinearEquiv
    have hz : CategoryTheory.Limits.IsZero (Homology ℚ P i) :=
      (AlgebraicTopology.singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
        (ModuleCat ℚ) i (ModuleCat.of ℚ ℚ) P hi).isZero_homology
    haveI : Subsingleton (Homology ℚ P i) := ModuleCat.subsingleton_of_isZero hz
    cases x
    exact ⟨fun a b => ei.symm.injective (Subsingleton.elim _ _)⟩
  coherent := by
    intro x
    cases x
    let U : TopologicalSpace.Opens P := ⟨{()}, isOpen_discrete _⟩
    refine ⟨U, rfl, localOrientation P 0 c (), ?_⟩
    intro y hy
    have he : y = () := hy
    subst y
    have hm : supportInclusionPairMap P
        (Set.singleton_subset_iff.mpr (show (() : P) ∈ U from rfl)) =
        𝟙 (pointComplementPair (() : P)) := by
      apply MorphismProperty.Arrow.Hom.ext <;> rfl
    rw [hm]
    change ((relativeHomologyFunctor ℚ 0).map (𝟙 _)).hom _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl

example : pointOrientation.generator () ≠ 0 := loc_ne

/-- Negating a selected local generator changes the global normalization.
Source: Hatcher, Algebraic Topology, Theorem 3.26. -/
theorem check_local_fundamental :
    localOrientation P 0 (-c) () ≠ pointOrientation.generator () := by
  intro h
  have he : (- (1 : ℚ)) = 1 := by
    have hc : -c = c := loc.injective h
    have ht := congrArg (orientationIntegral P 0 · u) hc
    change cohomologyEquivDualHomology ℚ P 0 u (-c) =
      cohomologyEquivDualHomology ℚ P 0 u c at ht
    rw [map_neg] at ht
    change -orientationIntegral P 0 c u = orientationIntegral P 0 c u at ht
    simpa only [eval_one] using ht
  norm_num at he
example := check_local_fundamental

private def v : RelativeCohomology ℚ (pointComplementPair (() : P)) 0 :=
  (relativeCohomologyEquivDualHomology ℚ (pointComplementPair (() : P)) 0).symm
    ((cohomologyEquivDualHomology ℚ P 0 u).comp loc.symm.toLinearMap)
private theorem local_eval_one :
    relativeCohomologyEquivDualHomology ℚ (pointComplementPair (() : P)) 0 v
      (localOrientation P 0 c ()) = 1 := by
  simp only [v, LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
  change cohomologyEquivDualHomology ℚ P 0 u (loc.symm (loc c)) = 1
  rw [loc.symm_apply_apply]
  exact eval_one

/-- Doubling the local class changes the trace of its actual support-forgetting image.
Source: Hatcher, Algebraic Topology, section 3.3. -/
theorem check_local_trace_normalization :
    orientationIntegral P 0 c
      (relativeCohomologyToAbsolute ℚ (pointComplementPair (() : P)) 0 ((2 : ℚ) • v)) ≠ 1 := by
  change cohomologyEquivDualHomology ℚ P 0 _ c ≠ 1
  have hn := cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ
    (pointComplementPair (() : P)) 0 ((2 : ℚ) • v) c
  change cohomologyEquivDualHomology ℚ (pointComplementPair (() : P)).fst 0 _ c ≠ 1
  rw [hn]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  change 2 * (relativeCohomologyEquivDualHomology ℚ _ 0 v
    (localOrientation P 0 c ())) ≠ 1
  rw [local_eval_one]
  norm_num
example := check_local_trace_normalization

/-- The identity singleton-fibre map cannot send a generator to its negative.
Source: Hatcher, Algebraic Topology, section 2.2. -/
theorem check_local_homeomorph_fundamental :
    relativeHomologyMap ℚ 0 (singletonFibrePairMap (𝟙 P) () () (fun z _ => Subsingleton.elim z ()))
      (localOrientation P 0 c ()) ≠ localOrientation P 0 (-c) () := by
  have hmap : singletonFibrePairMap (𝟙 P) () () (fun z _ => Subsingleton.elim z ()) =
      𝟙 (pointComplementPair (() : P)) := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  rw [hmap]
  change ((relativeHomologyFunctor ℚ 0).map (𝟙 _)).hom _ ≠ _
  rw [CategoryTheory.Functor.map_id]
  exact Ne.symm check_local_fundamental
example := check_local_homeomorph_fundamental

local instance : TopologicalSpace (Fin 2) := ⊥
local instance : DiscreteTopology (Fin 2) := ⟨rfl⟩
private abbrev twoVertices := TopCat.of (Fin 2)
private def exchange : twoVertices ⟶ twoVertices :=
  TopCat.ofHom ⟨Equiv.swap (0 : Fin 2) 1, continuous_of_discreteTopology⟩
set_option backward.isDefEq.respectTransparency false in
private theorem twoVertices_boundary :
    (SingularChainComplex ℚ twoVertices).d 1 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  have hf : (TopCat.toSSet.obj twoVertices).δ (0 : Fin 2) σ =
      (TopCat.toSSet.obj twoVertices).δ (1 : Fin 2) σ := by
    apply TopCat.toSSetObj₀Equiv.injective
    exact PreconnectedSpace.constant inferInstance
      ((twoVertices.toSSetObjEquiv _ σ).continuous)
  change (TopCat.toSSet.obj twoVertices).ιChainComplex σ ≫
    ((TopCat.toSSet.obj twoVertices).chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 = _
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_smul, hf, add_neg_cancel, CategoryTheory.Limits.comp_zero]

private theorem twoVertices_coboundary :
    (SingularCochainComplex ℚ twoVertices).d 0 1 = 0 := by
  change ModuleCat.ofHom ((SingularChainComplex ℚ twoVertices).d 1 0).hom.dualMap = 0
  rw [twoVertices_boundary]
  ext φ c
  exact map_zero φ

private def zeroIso : Cohomology ℚ twoVertices 0 ≅
    (SingularCochainComplex ℚ twoVertices).X 0 :=
  (SingularCochainComplex ℚ twoVertices).isoHomologyπ₀.symm ≪≫
    (SingularCochainComplex ℚ twoVertices).iCyclesIso 0 1 (by simp) twoVertices_coboundary

private def vertex (x : twoVertices) := TopCat.toSSetObj₀Equiv.symm x

private def vertexChain (x : twoVertices) : (SingularChainComplex ℚ twoVertices).X 0 :=
  ((TopCat.toSSet.obj twoVertices).ιChainComplex (vertex x)
    (R := ModuleCat.of ℚ ℚ)).hom 1

private def indicator : Module.Dual ℚ ((SingularChainComplex ℚ twoVertices).X 0) :=
  (CategoryTheory.Limits.Sigma.desc (fun σ => ModuleCat.ofHom
    ((LinearMap.ringLmapEquivSelf ℚ ℚ ℚ).symm
      (if TopCat.toSSetObj₀Equiv σ = (0 : Fin 2) then 1 else 0)))).hom

private theorem indicator_vertex (x : twoVertices) :
    indicator (vertexChain x) = if x = 0 then 1 else 0 := by
  change ModuleCat.Hom.hom
    ((TopCat.toSSet.obj twoVertices).ιChainComplex (vertex x)
      (R := ModuleCat.of ℚ ℚ) ≫
      (ModuleCat.ofHom indicator : (SingularChainComplex ℚ twoVertices).X 0 ⟶ ModuleCat.of ℚ ℚ)) 1 = _
  change ModuleCat.Hom.hom (Limits.Sigma.ι (fun _ => ModuleCat.of ℚ ℚ) (vertex x) ≫
    Limits.Sigma.desc (fun σ => ModuleCat.ofHom
      ((LinearMap.ringLmapEquivSelf ℚ ℚ ℚ).symm
        (if TopCat.toSSetObj₀Equiv σ = (0 : Fin 2) then 1 else 0)))) 1 = _
  rw [CategoryTheory.Limits.Sigma.ι_comp_desc]
  simp [vertex]

private def vertexClass : Cohomology ℚ twoVertices 0 := zeroIso.inv indicator

private theorem vertexClass_nonzero : vertexClass ≠ 0 := by
  intro h
  have he := congrArg (fun v => (show Module.Dual ℚ _ from zeroIso.hom v) (vertexChain 0)) h
  simp only [vertexClass, ← ModuleCat.comp_apply, Iso.inv_hom_id,
    ModuleCat.id_apply, map_zero] at he
  rw [indicator_vertex] at he
  norm_num at he

example : ∃ v : Cohomology ℚ twoVertices 0, v ≠ 0 := ⟨vertexClass, vertexClass_nonzero⟩

private theorem zeroIso_naturality :
    HomologicalComplex.homologyMap (singularCochainComplexMap ℚ exchange) 0 ≫
      zeroIso.hom = zeroIso.hom ≫ (singularCochainComplexMap ℚ exchange).f 0 := by
  dsimp only [zeroIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.iCyclesIso_hom]
  rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc]
  change (SingularCochainComplex ℚ twoVertices).isoHomologyπ₀.inv ≫
    HomologicalComplex.cyclesMap (singularCochainComplexMap ℚ exchange) 0 ≫
      (SingularCochainComplex ℚ twoVertices).iCycles 0 = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

private theorem exchange_vertexChain (x : twoVertices) :
    ((singularChainComplexMap ℚ exchange).f 0).hom (vertexChain x) =
      vertexChain (exchange x) := by
  have he := SSet.ι_chainComplexMap_f _ _
    (TopCat.toSSet.map exchange) (ModuleCat.of ℚ ℚ) (vertex x)
  have hv : (TopCat.toSSet.map exchange).app _ (vertex x) = vertex (exchange x) := by
    apply TopCat.toSSetObj₀Equiv.injective
    change exchange (TopCat.toSSetObj₀Equiv (vertex x)) =
      TopCat.toSSetObj₀Equiv (vertex (exchange x))
    simp only [vertex, Equiv.apply_symm_apply]
  rw [hv] at he
  exact congrArg (fun f => f.hom 1) he

/-- The exchange changes an actual rational cohomology class in degree zero.
Source: Hatcher, Algebraic Topology, §3.1, degree-zero cohomology. -/
private theorem exchange_cohomology_nontrivial :
    cohomologyMap ℚ 0 exchange vertexClass ≠ vertexClass := by
  intro h
  have he := congrArg (fun v => (show Module.Dual ℚ _ from zeroIso.hom v)
    (vertexChain 0)) h
  have hn := congrArg (fun f => f.hom vertexClass) zeroIso_naturality
  change zeroIso.hom (cohomologyMap ℚ 0 exchange vertexClass) =
    (singularCochainComplexMap ℚ exchange).f 0 (zeroIso.hom vertexClass) at hn
  rw [hn] at he
  have hi : zeroIso.hom vertexClass = indicator := by
    change (zeroIso.inv ≫ zeroIso.hom).hom indicator = indicator
    rw [Iso.inv_hom_id]; rfl
  rw [hi] at he
  change indicator (((singularChainComplexMap ℚ exchange).f 0).hom (vertexChain 0)) =
    indicator (vertexChain 0) at he
  rw [exchange_vertexChain, indicator_vertex, indicator_vertex] at he
  norm_num [exchange, Equiv.swap_apply_left] at he

example : cohomologyMap ℚ 0 exchange ≠ LinearMap.id := by
  intro h
  exact exchange_cohomology_nontrivial (congrArg (fun f => f vertexClass) h)


private abbrev G := Equiv.Perm (Fin 2)
private instance : ContinuousConstSMul G twoVertices :=
  ⟨fun _ => continuous_of_discreteTopology⟩
private def swap : G := Equiv.swap 0 1
private theorem deck_swap : deckMap G twoVertices swap = exchange := by
  ext x
  rfl

private theorem cochain_value :
    (show Module.Dual ℚ _ from (deckCochain G twoVertices swap).f 0 indicator) (vertexChain 0) = 0 := by
  change indicator (((singularChainComplexMap ℚ (deckMap G twoVertices swap)).f 0).hom
    (vertexChain 0)) = 0
  rw [deck_swap, exchange_vertexChain, indicator_vertex]
  norm_num [exchange, Equiv.swap_apply_left]

private def constantOne : twoVertices ⟶ twoVertices :=
  TopCat.ofHom ⟨fun _ => (1 : Fin 2), continuous_const⟩

private theorem zeroIso_naturality_map (f : twoVertices ⟶ twoVertices) :
    HomologicalComplex.homologyMap (singularCochainComplexMap ℚ f) 0 ≫
      zeroIso.hom = zeroIso.hom ≫ (singularCochainComplexMap ℚ f).f 0 := by
  dsimp only [zeroIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.iCyclesIso_hom]
  rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc]
  change (SingularCochainComplex ℚ twoVertices).isoHomologyπ₀.inv ≫
    HomologicalComplex.cyclesMap (singularCochainComplexMap ℚ f) 0 ≫
      (SingularCochainComplex ℚ twoVertices).iCycles 0 = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

private theorem constantOne_indicator :
    (singularCochainComplexMap ℚ constantOne).f 0 indicator = 0 := by
  have hmap (x : twoVertices) :
      ((singularChainComplexMap ℚ constantOne).f 0).hom (vertexChain x) =
        vertexChain 1 := by
    have he := SSet.ι_chainComplexMap_f _ _
      (TopCat.toSSet.map constantOne) (ModuleCat.of ℚ ℚ) (vertex x)
    have hv : (TopCat.toSSet.map constantOne).app _ (vertex x) = vertex 1 := by
      apply TopCat.toSSetObj₀Equiv.injective
      rfl
    rw [hv] at he
    exact congrArg (fun f => f.hom 1) he
  have hm : (ModuleCat.ofHom ((singularCochainComplexMap ℚ constantOne).f 0 indicator) :
      (SingularChainComplex ℚ twoVertices).X 0 ⟶ ModuleCat.of ℚ ℚ) = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    have hs : σ = vertex (TopCat.toSSetObj₀Equiv σ) :=
      (Equiv.symm_apply_apply _ _).symm
    rw [hs]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change indicator (((singularChainComplexMap ℚ constantOne).f 0).hom
      (vertexChain (TopCat.toSSetObj₀Equiv σ))) = 0
    rw [hmap, indicator_vertex]
    norm_num
  exact congrArg ModuleCat.Hom.hom hm

private theorem constantOne_pullback : cohomologyMap ℚ 0 constantOne vertexClass = 0 := by
  apply zeroIso.toLinearEquiv.injective
  have hn := congrArg (fun f => f.hom vertexClass) (zeroIso_naturality_map constantOne)
  change zeroIso.hom (cohomologyMap ℚ 0 constantOne vertexClass) =
    (singularCochainComplexMap ℚ constantOne).f 0 (zeroIso.hom vertexClass) at hn
  have hi : zeroIso.hom vertexClass = indicator := by
    change (zeroIso.inv ≫ zeroIso.hom).hom indicator = indicator
    rw [Iso.inv_hom_id]; rfl
  rw [hi, constantOne_indicator] at hn
  change zeroIso.hom (cohomologyMap ℚ 0 constantOne vertexClass) = zeroIso.hom 0
  rw [map_zero]
  exact hn

private def pointIn : P ⟶ twoVertices := TopCat.ofHom ⟨fun _ => 0, continuous_const⟩
private def back : twoVertices ⟶ P := TopCat.ofHom ⟨fun _ => (), continuous_const⟩
private def vertexFundamental : Homology ℚ twoVertices 0 :=
  homologyMap ℚ 0 (pointIn ≫ constantOne) c
private theorem vertexFundamental_ne : vertexFundamental ≠ 0 := by
  intro hz
  have hid : (pointIn ≫ constantOne) ≫ back = 𝟙 P := by ext x
  have h : homologyMap ℚ 0 back vertexFundamental = c := by
    unfold vertexFundamental
    rw [← LinearMap.comp_apply, ← homologyMap_comp, hid, homologyMap_id]
    rfl
  rw [hz, map_zero] at h
  exact c_ne h.symm

/-- A nonzero class on one component leaves the other component in the kernel.
Source: Bredon, Sheaf Theory, V.9; Hatcher, section 3.3, cap naturality. -/
theorem check_local_middle_duality :
    vertexFundamental ≠ 0 ∧
      ¬ Function.Injective (localTracePairing twoVertices 0 0 vertexFundamental) := by
  refine ⟨vertexFundamental_ne, ?_⟩
  intro hi
  have hcap : capCohomologyLinear ℚ twoVertices 0 0
      ((cochainCohomologyEquiv ℚ twoVertices 0).symm vertexClass) vertexFundamental = 0 := by
    have hn := standardCapCohomologyLinear_naturality ℚ constantOne 0 0 vertexClass
      (homologyMap ℚ 0 pointIn c)
    rw [constantOne_pullback] at hn
    simp only [standardCapCohomologyLinear, LinearMap.comp_apply, map_zero,
      LinearMap.zero_apply] at hn
    change 0 = capCohomologyLinear ℚ twoVertices 0 0
      ((cochainCohomologyEquiv ℚ twoVertices 0).symm vertexClass)
        (homologyMap ℚ 0 constantOne (homologyMap ℚ 0 pointIn c)) at hn
    unfold vertexFundamental
    rw [homologyMap_comp]
    exact hn.symm
  have hz : localTracePairing twoVertices 0 0 vertexFundamental vertexClass =
      localTracePairing twoVertices 0 0 vertexFundamental (0 : Cohomology ℚ twoVertices 0) := by
    ext b
    simp [localTracePairing, hcap]
  exact vertexClass_nonzero (hi hz)
example := check_local_middle_duality

/-- A nontrivial deck action need not preserve a specified evaluation trace.
Source: Hatcher, Algebraic Topology, section 3.3, orientation dependence. -/
theorem check_local_deck_trace_pairing :
    ∃ z : Homology ℚ twoVertices 0, z ≠ 0 ∧
      orientationIntegral twoVertices 0 z (deckRepresentation G twoVertices 0 swap vertexClass) ≠
        orientationIntegral twoVertices 0 z vertexClass := by
  have hne : cohomologyEquivDualHomology ℚ twoVertices 0
      (cohomologyMap ℚ 0 exchange vertexClass) ≠
      cohomologyEquivDualHomology ℚ twoVertices 0 vertexClass :=
    fun h => exchange_cohomology_nontrivial
      ((cohomologyEquivDualHomology ℚ twoVertices 0).injective h)
  have hex : ∃ z, cohomologyEquivDualHomology ℚ twoVertices 0
      (cohomologyMap ℚ 0 exchange vertexClass) z ≠
      cohomologyEquivDualHomology ℚ twoVertices 0 vertexClass z := by
    by_contra! h
    exact hne (LinearMap.ext h)
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ?_, ?_⟩
  · intro h
    subst z
    simp at hz
  · change cohomologyEquivDualHomology ℚ twoVertices 0
      (cohomologyMap ℚ 0 (deckMap G twoVertices swap) vertexClass) z ≠ _
    rw [deck_swap]
    exact hz
example := check_local_deck_trace_pairing

/-- A local degree-two normalization fails the degree-one trace identity.
Source: Hatcher, Algebraic Topology, Proposition 2.30. -/
theorem check_local_degree_one_trace :
    relativeHomologyMap ℚ 0
      (singletonFibrePairMap (𝟙 P) () () (fun z _ => Subsingleton.elim z ()))
      (localOrientation P 0 ((2 : ℚ) • c) ()) =
        (2 : ℚ) • localOrientation P 0 c () ∧
    orientationIntegral P 0 ((2 : ℚ) • c) (cohomologyMap ℚ 0 (𝟙 P) u) ≠
      orientationIntegral P 0 c u := by
  constructor
  · have hmap : singletonFibrePairMap (𝟙 P) () () (fun z _ => Subsingleton.elim z ()) =
        𝟙 (pointComplementPair (() : P)) := by
      apply MorphismProperty.Arrow.Hom.ext <;> rfl
    rw [hmap]
    change ((relativeHomologyFunctor ℚ 0).map (𝟙 _)).hom _ = _
    rw [CategoryTheory.Functor.map_id]
    exact (relativeHomologyProjection ℚ (pointComplementPair (() : P)) 0).hom.map_smul _ _
  · rw [cohomologyMap_id]
    change cohomologyEquivDualHomology ℚ P 0 u ((2 : ℚ) • c) ≠ _
    rw [map_smul]
    change 2 * orientationIntegral P 0 c u ≠ orientationIntegral P 0 c u
    rw [eval_one]
    norm_num
example := check_local_degree_one_trace

end HodgeLean.Foundations.QuotientDuality.LocalTraceChecks
