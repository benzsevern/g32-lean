import HodgeLean.Foundations.QuotientDuality.PersistenceDefs
import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import Mathlib.Tactic.NormNum
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! # Independent primitive persistence tests

Two vertices carry a nonidentity action on actual relative singular classes.
The full point pair detects the missing exceptional term in degree zero.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality.PersistenceChecks
local instance persistenceTopology : TopologicalSpace (Fin 2) := ⊥
local instance persistenceDiscrete : DiscreteTopology (Fin 2) := ⟨rfl⟩

/-- The finite polyhedron consisting of two vertices.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
private abbrev twoVertices : TopCat.{0} := TopCat.of (Fin 2)

/-- Exchange of the two vertices.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
private def exchange : twoVertices ⟶ twoVertices :=
  TopCat.ofHom ⟨Equiv.swap (0 : Fin 2) 1, continuous_of_discreteTopology⟩

private theorem exchange_nontrivial : exchange ≠ 𝟙 twoVertices := by
  intro h
  have he := congrArg (fun f : twoVertices ⟶ twoVertices => f 0) h
  change Equiv.swap (0 : Fin 2) 1 0 = 0 at he
  norm_num [Equiv.swap_apply_left] at he

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
    neg_smul, hf, add_neg_cancel, Limits.comp_zero, CategoryTheory.Limits.comp_zero]

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

private def emptyEquiv (X : TopCat.{0}) (n : ℕ) :
    RelativeCohomology ℚ (emptySubspacePair X) n ≃ₗ[ℚ] Cohomology ℚ X n :=
  LinearEquiv.ofBijective (relativeCohomologyToAbsolute ℚ (emptySubspacePair X) n) (by
    let e := HomologicalComplex.homologyMapIso
      (HomologicalComplex.linearDualIso
        (asIso (relativeChainProjection ℚ (emptySubspacePair X)))) n
    exact (ConcreteCategory.isIso_iff_bijective e.hom).mp e.isIso_hom)

private def relativeVertex := (emptyEquiv twoVertices 0).symm vertexClass

private def emptyPullback {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    RelativeCohomology ℚ (emptySubspacePair Y) n →ₗ[ℚ]
      RelativeCohomology ℚ (emptySubspacePair X) n := by
  simpa only [Set.preimage_empty] using persistenceRelativePullback ℚ f ∅ n

private theorem relative_square {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (u : RelativeCohomology ℚ (emptySubspacePair Y) n) :
    emptyEquiv X n (emptyPullback f n u) =
      cohomologyMap ℚ n f (emptyEquiv Y n u) := by
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
      (persistencePairMap f ∅))
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun v => HomologicalComplex.homologyMap v n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  have hr := ConcreteCategory.congr_hom hhom u
  change relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (f ⁻¹' ∅)) n
      (relativeCohomologyMap ℚ n (persistencePairMap f ∅) u) =
    cohomologyMap ℚ n f (relativeCohomologyToAbsolute ℚ (emptySubspacePair Y) n u) at hr
  have hE (Z : TopCat.{0}) (v : RelativeCohomology ℚ (emptySubspacePair Z) n) :
      emptyEquiv Z n v = relativeCohomologyToAbsolute ℚ (emptySubspacePair Z) n v := rfl
  rw [hE, hE]
  unfold emptyPullback
  simpa only [Set.preimage_empty, persistenceRelativePullback, emptySubspacePair,
    TopPair.ofSubset] using hr

private theorem relative_moved :
    emptyPullback exchange 0 relativeVertex ≠ relativeVertex := by
  intro h
  have he := congrArg (emptyEquiv twoVertices 0) h
  rw [relative_square] at he
  simp only [relativeVertex, LinearEquiv.apply_symm_apply] at he
  exact exchange_cohomology_nontrivial he

private theorem relative_ne : relativeVertex ≠ 0 := by
  intro h
  have he := congrArg (emptyEquiv twoVertices 0) h
  simp only [relativeVertex, LinearEquiv.apply_symm_apply, map_zero] at he
  exact vertexClass_nonzero he

/-- A comparison cannot identify the actual exchange pullback with the identity.
Source: Hatcher, Algebraic Topology, section 3.1.
HC no distance; AV milestone no distance. -/
theorem check_persistence_pair_comparison :
    emptyPullback exchange 0 relativeVertex ≠ relativeVertex := relative_moved
example := check_persistence_pair_comparison

/-- The retained exceptional term cannot be replaced by only positive-degree information.
Source: Hatcher, Algebraic Topology, section 3.1, the sequence of a pair.
HC no distance; AV milestone no distance. -/
theorem check_persistence_retained_exact :
    let P := TopPair.ofSubset (X := TopCat.of Unit) Set.univ
    let F := persistencePairMap (𝟙 (TopCat.of Unit)) Set.univ
    ∃ v : Cohomology ℚ P.fst 0,
      v ≠ 0 ∧ cohomologyMap ℚ 0 (TopPair.Hom.fst F) v = v ∧
      cohomologyMap ℚ 0 P.map v ≠ 0 := by
  dsimp only
  refine ⟨cohomologyUnitZero ℚ (TopCat.of Unit),
    cohomologyUnitZero_ne_zero ℚ (TopCat.of Unit), ?_, ?_⟩
  · exact LinearMap.congr_fun (cohomologyMap_id ℚ (TopCat.of Unit) 0)
      (cohomologyUnitZero ℚ (TopCat.of Unit))
  · let back : (TopPair.ofSubset (X := TopCat.of Unit) Set.univ).snd ⟶ TopCat.of Unit :=
      (TopPair.ofSubset (X := TopCat.of Unit) Set.univ).map
    let sectionMap : TopCat.of Unit ⟶ (TopPair.ofSubset (X := TopCat.of Unit) Set.univ).snd :=
      TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
    intro h
    have he := congrArg (cohomologyMap ℚ 0 sectionMap) h
    change ((cohomologyMap ℚ 0 sectionMap).comp (cohomologyMap ℚ 0 back))
      (cohomologyUnitZero ℚ _) = _ at he
    rw [← cohomologyMap_comp, show sectionMap ≫ back = 𝟙 _ from rfl,
      cohomologyMap_id, map_zero] at he
    exact cohomologyUnitZero_ne_zero ℚ _ he
example := check_persistence_retained_exact

/-- A nontrivial sign character detects use of the wrong eigenvalue.
Source: Serre, Linear Representations of Finite Groups, section 2.6.
HC no distance; AV milestone no distance. -/
theorem check_persistence_primitive_exact :
    ∃ u : RelativeCohomology ℚ (emptySubspacePair twoVertices) 0,
      u ≠ 0 ∧ emptyPullback exchange 0 u = -(u) ∧
      emptyPullback exchange 0 u ≠ u := by
  let T := emptyPullback exchange 0
  let u := relativeVertex - T relativeVertex
  have hTT : T.comp T = LinearMap.id := by
    ext u
    apply (emptyEquiv twoVertices 0).injective
    change emptyEquiv twoVertices 0 (emptyPullback exchange 0
      (emptyPullback exchange 0 u)) = emptyEquiv twoVertices 0 u
    rw [relative_square, relative_square, ← LinearMap.comp_apply,
      ← cohomologyMap_comp]
    have hh : exchange ≫ exchange = 𝟙 twoVertices := by
      apply ConcreteCategory.hom_ext
      intro x
      change Equiv.swap (0 : Fin 2) 1 (Equiv.swap (0 : Fin 2) 1 x) = x
      exact Equiv.swap_apply_self _ _ x
    rw [hh, cohomologyMap_id]; rfl
  have hu : u ≠ 0 := by
    intro h
    exact relative_moved (sub_eq_zero.mp h).symm
  have he : T u = -u := by
    dsimp only [u]
    rw [map_sub, ← LinearMap.comp_apply, hTT, LinearMap.id_apply, neg_sub]
  refine ⟨u, hu, he, ?_⟩
  intro h
  have htwo : (2 : ℚ) • u = 0 := by
    have hneg : -u = u := he.symm.trans h
    rw [two_smul]
    calc u + u = u + -u := congrArg (u + ·) hneg.symm
         _ = 0 := add_neg_cancel u
  exact hu ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
example := check_persistence_primitive_exact

/-- The sign-eigenvector has an actual preimage different from itself.
Source: Hatcher, Algebraic Topology, section 3.1.
HC no distance; AV milestone no distance. -/
theorem check_persistence_retained_preimage :
    ∃ u : RelativeCohomology ℚ (emptySubspacePair twoVertices) 0,
      u ≠ 0 ∧ emptyPullback exchange 0 u = -u ∧
      emptyPullback exchange 0 (-u) = u ∧ -u ≠ u := by
  obtain ⟨u, hu, he, hnot⟩ := check_persistence_primitive_exact
  refine ⟨u, hu, he, ?_, ?_⟩
  · rw [map_neg, he, neg_neg]
  · intro h
    exact hnot (he.trans h)
example := check_persistence_retained_preimage

/-- Omitting a nonidentity tower transition changes the transported nonzero class.
Source: Hatcher, Algebraic Topology, section 3.1, functoriality.
HC no distance; AV milestone no distance. -/
theorem check_persistence_retained_transport :
    let W : Fin 2 → TopCat.{0} := fun _ => twoVertices
    let w : ∀ i : Fin 1, W i.succ ⟶ W i.castSucc := fun _ => exchange
    let total := HodgeLean.Foundations.Program.s2e_towerTotalMap W
      (𝟙 twoVertices) w (Fin.last 1)
    ∃ u : RelativeCohomology ℚ (emptySubspacePair twoVertices) 0,
      u ≠ 0 ∧ emptyPullback total 0 u ≠ u := by
  dsimp only
  refine ⟨relativeVertex, relative_ne, ?_⟩
  rw [show Fin.last 1 = (0 : Fin 1).succ from rfl,
    HodgeLean.Foundations.Program.s2e_towerTotalMap_succ]
  simpa only [Fin.castSucc_zero, HodgeLean.Foundations.Program.s2e_towerTotalMap_zero,
    Category.comp_id] using relative_moved
example := check_persistence_retained_transport

/-- A factor two corrupts the actual relative-to-absolute comparison square.
Source: Hatcher, Algebraic Topology, section 3.1, naturality.
HC no distance; AV milestone no distance. -/
theorem check_persistence_pair_squares :
    emptyEquiv twoVertices 0 (emptyPullback exchange 0 relativeVertex) ≠
      (2 : ℚ) • cohomologyMap ℚ 0 exchange (emptyEquiv twoVertices 0 relativeVertex) := by
  rw [relative_square]
  intro h
  have hn : cohomologyMap ℚ 0 exchange (emptyEquiv twoVertices 0 relativeVertex) ≠ 0 := by
    intro hz
    have hzero : emptyPullback exchange 0 relativeVertex = 0 := by
      apply (emptyEquiv twoVertices 0).injective
      rw [relative_square, hz, map_zero]
    have hh := congrArg (emptyEquiv twoVertices 0) hzero
    rw [relative_square, map_zero] at hh
    have hz' := congrArg (cohomologyMap ℚ 0 exchange) hh
    change ((cohomologyMap ℚ 0 exchange).comp (cohomologyMap ℚ 0 exchange))
      (emptyEquiv twoVertices 0 relativeVertex) = _ at hz'
    rw [← cohomologyMap_comp] at hz'
    have hex : exchange ≫ exchange = 𝟙 twoVertices := by
      apply ConcreteCategory.hom_ext
      intro x
      change Equiv.swap (0 : Fin 2) 1 (Equiv.swap (0 : Fin 2) 1 x) = x
      exact Equiv.swap_apply_self _ _ x
    rw [hex, cohomologyMap_id, map_zero] at hz'
    have hh' : relativeVertex = 0 := (emptyEquiv twoVertices 0).injective
      (hz'.trans (map_zero _).symm)
    exact relative_ne hh'
  have he : cohomologyMap ℚ 0 exchange (emptyEquiv twoVertices 0 relativeVertex) = 0 := by
    have hh := h
    rw [two_smul] at hh
    exact (add_eq_left.mp hh.symm)
  exact hn he
example := check_persistence_pair_squares

private theorem exchange_relative_involutive :
    Function.Involutive (emptyPullback exchange 0) := by
  intro u
  apply (emptyEquiv twoVertices 0).injective
  rw [relative_square, relative_square, ← LinearMap.comp_apply, ← cohomologyMap_comp]
  have hh : exchange ≫ exchange = 𝟙 twoVertices := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Equiv.swap_apply_self (0 : Fin 2) 1 x
  rw [hh, cohomologyMap_id]
  rfl

/-- The actual relative comparison is bijective; its zero perturbation is not.
Source: Hatcher, Algebraic Topology, section 3.1.
HC no distance; AV milestone no distance. -/
theorem check_persistence_pair_comparison_bijective :
    Function.Bijective (emptyPullback exchange 0) ∧
      ¬ Function.Injective
        (0 : RelativeCohomology ℚ (emptySubspacePair twoVertices) 0 →ₗ[ℚ]
          RelativeCohomology ℚ (emptySubspacePair twoVertices) 0) := by
  refine ⟨exchange_relative_involutive.bijective, ?_⟩
  intro h
  exact relative_ne (h (show (0 : RelativeCohomology ℚ
    (emptySubspacePair twoVertices) 0 →ₗ[ℚ] _) relativeVertex = 0 from rfl))
example := check_persistence_pair_comparison_bijective

/-- The sign preimage is unique for the actual transition, and zero cannot replace it.
Source: Schoen (1988), Lemma 2.8.
HC no distance; AV milestone no distance. -/
theorem check_persistence_retained_preimage_unique :
    ∃ v : RelativeCohomology ℚ (emptySubspacePair twoVertices) 0,
      v ≠ 0 ∧ (∃! u, emptyPullback exchange 0 u = v) ∧
      ¬ ∃ u, (0 : RelativeCohomology ℚ (emptySubspacePair twoVertices) 0 →ₗ[ℚ]
        RelativeCohomology ℚ (emptySubspacePair twoVertices) 0) u = v := by
  refine ⟨relativeVertex, relative_ne, ?_, ?_⟩
  · refine ⟨emptyPullback exchange 0 relativeVertex,
      exchange_relative_involutive _, ?_⟩
    intro u hu
    apply exchange_relative_involutive.injective
    rw [hu, exchange_relative_involutive]
  · rintro ⟨u, hu⟩
    exact relative_ne hu.symm
example := check_persistence_retained_preimage_unique

/-- Empty-subspace relative lifts are unique, including for a nonzero sign class.
Source: Hatcher, Algebraic Topology, section 3.1, the sequence of a pair.
HC no distance; AV milestone no distance. -/
theorem check_persistence_primitive_exact_unique :
    ∃ u : RelativeCohomology ℚ (emptySubspacePair twoVertices) 0,
      u ≠ 0 ∧ emptyPullback exchange 0 u = -u ∧
      ∃! w, emptyPullback exchange 0 w = -w ∧
        relativeCohomologyToAbsolute ℚ (emptySubspacePair twoVertices) 0 w =
          emptyEquiv twoVertices 0 u := by
  obtain ⟨u, hu, he, _⟩ := check_persistence_primitive_exact
  refine ⟨u, hu, he, u, ⟨he, rfl⟩, ?_⟩
  intro w hw
  exact (emptyEquiv twoVertices 0).injective hw.2
example := check_persistence_primitive_exact_unique

/-- The actual weighted sum is nonzero and has a unique transition preimage.
Source: Schoen (1988), Lemma 2.8, weighted character projection.
HC no distance; AV milestone no distance. -/
theorem check_persistence_retained_transport_weighted :
    let v := HodgeLean.Foundations.Program.s2e_weightedSum 2
      (fun t : ZMod 2 => if t = 0 then (1 : ℚ) else -1)
      (fun t : Fin 2 => if t = 0 then relativeVertex else
        emptyPullback exchange 0 relativeVertex)
    v ≠ 0 ∧ (∃! u, emptyPullback exchange 0 u = v) ∧
      ¬ ∃ u, emptyPullback exchange 0 u = (0 : RelativeCohomology ℚ
        (emptySubspacePair twoVertices) 0) ∧ u ≠ 0 := by
  dsimp only
  have hv : HodgeLean.Foundations.Program.s2e_weightedSum 2
      (fun t : ZMod 2 => if t = 0 then (1 : ℚ) else -1)
      (fun t : Fin 2 => if t = 0 then relativeVertex else
        emptyPullback exchange 0 relativeVertex) =
      relativeVertex - emptyPullback exchange 0 relativeVertex := by
    simp [HodgeLean.Foundations.Program.s2e_weightedSum, Fin.sum_univ_two, sub_eq_add_neg]
  rw [hv]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact relative_moved (sub_eq_zero.mp h).symm
  · refine ⟨emptyPullback exchange 0 _, exchange_relative_involutive _, ?_⟩
    intro u hu
    apply exchange_relative_involutive.injective
    rw [hu, exchange_relative_involutive]
  · rintro ⟨u, hu, hn⟩
    exact hn (exchange_relative_involutive.injective (hu.trans (map_zero _).symm))
example := check_persistence_retained_transport_weighted

/-- Forgetting a nonzero whole-support class commutes with exchange and detects its omission.
Source: Hatcher, Algebraic Topology, section 3.1, support naturality.
HC no distance; AV milestone no distance. -/
theorem check_persistence_pair_squares_support :
    ∃ u : CohomologyWithSupport ℚ twoVertices Set.univ 0,
      cohomologyMap ℚ 0 exchange (forgetSupport ℚ twoVertices Set.univ 0 u) =
        forgetSupport ℚ twoVertices (exchange ⁻¹' Set.univ) 0
          (cohomologyWithSupportMap ℚ 0 exchange Set.univ u) ∧
      forgetSupport ℚ twoVertices (exchange ⁻¹' Set.univ) 0
          (cohomologyWithSupportMap ℚ 0 exchange Set.univ u) ≠
        forgetSupport ℚ twoVertices Set.univ 0 u := by
  let u := (wholeSupportCohomologyLinearEquiv ℚ twoVertices 0).symm vertexClass
  have hu : forgetSupport ℚ twoVertices Set.univ 0 u = vertexClass :=
    (wholeSupportCohomologyLinearEquiv ℚ twoVertices 0).apply_symm_apply _
  refine ⟨u, cohomologyMap_forgetSupport ℚ 0 exchange Set.univ u, ?_⟩
  rw [← cohomologyMap_forgetSupport, hu]
  exact exchange_cohomology_nontrivial
example := check_persistence_pair_squares_support

/-- Without exceptional vanishing a nonzero invariant class need not have a relative lift.
Source: Hatcher, Algebraic Topology, section 3.1, exactness of the pair sequence.
HC no distance; AV milestone no distance. -/
theorem check_persistence_retained_exact_no_lift :
    let P := TopPair.ofSubset (X := TopCat.of Unit) Set.univ
    ¬ ∃ u : RelativeCohomology ℚ P 0,
      relativeCohomologyToAbsolute ℚ P 0 u = cohomologyUnitZero ℚ (TopCat.of Unit) := by
  dsimp only
  let P := TopPair.ofSubset (X := TopCat.of Unit) Set.univ
  have hdual := congrArg HomologicalComplex.linearDualMap
    (subspaceChainMap_relativeChainProjection ℚ P)
  rw [HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun f => HomologicalComplex.homologyMap f 0) hdual
  rw [HomologicalComplex.homologyMap_comp] at hhom
  have hzero : HomologicalComplex.linearDualMap
      (0 : (SingularChainComplex ℚ P.snd) ⟶ (relativeChainFunctor ℚ).obj P) = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    simp [HomologicalComplex.linearDualMap, LinearMap.dualMap]
  rw [hzero, HomologicalComplex.homologyMap_zero] at hhom
  rintro ⟨u, hu⟩
  have hh := ConcreteCategory.congr_hom hhom u
  change cohomologyMap ℚ 0 P.map (relativeCohomologyToAbsolute ℚ P 0 u) = 0 at hh
  rw [hu] at hh
  have hunit : cohomologyMap ℚ 0 P.map (cohomologyUnitZero ℚ (TopCat.of Unit)) ≠ 0 := by
    let sectionMap : TopCat.of Unit ⟶ P.snd :=
      TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
    intro h
    have he := congrArg (cohomologyMap ℚ 0 sectionMap) h
    change ((cohomologyMap ℚ 0 sectionMap).comp (cohomologyMap ℚ 0 P.map)) _ = _ at he
    rw [← cohomologyMap_comp, show sectionMap ≫ P.map = 𝟙 _ from rfl,
      cohomologyMap_id, map_zero] at he
    exact cohomologyUnitZero_ne_zero ℚ _ he
  exact hunit hh
example := check_persistence_retained_exact_no_lift

end HodgeLean.Foundations.QuotientDuality.PersistenceChecks
