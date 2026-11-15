import HodgeLean.Foundations.Program.PrymParabolicIntersectionTriangleModel
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalClassReduction

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

/-- A real linear path from the identity to the triangle coordinate map.
Source: `standardAffineSimplex`, `hga_triangleCoordinate`, barycentric coordinates. -/
def hga_trianglePlaneHomotopy (t : ℝ) (z : ℂ) : ℂ :=
  ((((3 - 4 * t) * z.re + 2 * t * z.im) / 3 : ℝ) : ℂ) +
    (((-t * z.re + (3 - 4 * t) * z.im) / 3 : ℝ) : ℂ) * Complex.I

theorem hga_trianglePlaneHomotopy_eq_zero (t : ℝ) (z : ℂ) :
    hga_trianglePlaneHomotopy t z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [hga_trianglePlaneHomotopy] at hre him
    have h1 : (3 - 4 * t) * z.re + 2 * t * z.im = 0 := by linarith
    have h2 : -t * z.re + (3 - 4 * t) * z.im = 0 := by linarith
    have hx : ((3 - 4 * t) ^ 2 + 2 * t ^ 2) * z.re = 0 := by
      linear_combination (3 - 4 * t) * h1 - 2 * t * h2
    have hy : ((3 - 4 * t) ^ 2 + 2 * t ^ 2) * z.im = 0 := by
      linear_combination t * h1 + (3 - 4 * t) * h2
    have hp : 0 < (3 - 4 * t) ^ 2 + 2 * t ^ 2 := by
      by_cases ht : t = 0
      · rw [ht]; norm_num
      · have hsq := sq_pos_of_ne_zero ht
        nlinarith [sq_nonneg (3 - 4 * t)]
    have hr : z.re = 0 := (mul_eq_zero.mp hx).resolve_left hp.ne'
    have hi : z.im = 0 := (mul_eq_zero.mp hy).resolve_left hp.ne'
    exact Complex.ext hr hi
  · rintro rfl
    simp [hga_trianglePlaneHomotopy]

/-- The linear deformation on the one-dimensional complex punctured pair.
Source: `hga_trianglePlaneHomotopy_eq_zero`. -/
def hga_trianglePlanePairMap (t : ℝ) : puncturedPair ℂ 1 ⟶ puncturedPair ℂ 1 :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun z i ↦ hga_trianglePlaneHomotopy t (z i), by
      apply continuous_pi
      intro i
      unfold hga_trianglePlaneHomotopy
      fun_prop⟩) (by
        intro z hz
        change (fun i ↦ hga_trianglePlaneHomotopy t (z i)) ≠ 0
        intro h
        apply hz
        funext i
        exact (hga_trianglePlaneHomotopy_eq_zero t (z i)).mp (congrFun h i))

theorem hga_continuous_trianglePlaneHomotopy :
    Continuous (fun p : ℝ × ℂ ↦ hga_trianglePlaneHomotopy p.1 p.2) := by
  unfold hga_trianglePlaneHomotopy
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- The triangle coordinate map is homotopic to the identity as a map of punctured planes.
Source: `hga_trianglePlaneHomotopy_eq_zero`. -/
def hga_trianglePlanePairHomotopy :
    TopPair.Homotopy (𝟙 (puncturedPair ℂ 1)) (hga_trianglePlanePairMap 1) where
  fst :=
    { toFun := fun p i ↦ hga_trianglePlaneHomotopy (p.1 : ℝ) (p.2 i)
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact hga_continuous_trianglePlaneHomotopy.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            ((continuous_apply i).comp continuous_snd))
      map_zero_left := fun z ↦ by
        funext i
        change hga_trianglePlaneHomotopy 0 (z i) = z i
        apply Complex.ext <;> simp [hga_trianglePlaneHomotopy]
      map_one_left := fun z ↦ rfl }
  snd :=
    { toFun := fun p ↦ ⟨fun i ↦ hga_trianglePlaneHomotopy (p.1 : ℝ) (p.2.1 i), by
        intro h
        apply p.2.2
        funext i
        exact (hga_trianglePlaneHomotopy_eq_zero (p.1 : ℝ) (p.2.1 i)).mp (congrFun h i)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        exact hga_continuous_trianglePlaneHomotopy.comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        funext i
        change hga_trianglePlaneHomotopy 0 (z.1 i) = z.1 i
        apply Complex.ext <;> simp [hga_trianglePlaneHomotopy]
      map_one_left := fun z ↦ rfl }
  w := rfl


theorem hga_trianglePlanePairMap_homology (R : Type) [CommRing R] (n : ℕ)
    (c : RelativeHomology R (puncturedPair ℂ 1) n) :
    relativeHomologyMap R n (hga_trianglePlanePairMap 1) c = c := by
  have h := hga_trianglePlanePairHomotopy.relativeHomologyMap_apply_eq (R := R) n c
  simpa only [relativeHomologyMap_id, LinearMap.id_apply] using h.symm

theorem hga_triangleCoordinate_standardAffine (a : StdSimplex ℝ (Fin 3)) :
    hga_trianglePlaneHomotopy 1
      ((((standardAffineSimplex 2 a 0 : ℝ) : ℂ)) +
        (((standardAffineSimplex 2 a 1 : ℝ) : ℂ)) * Complex.I) =
      hga_triangleCoordinate a := by
  apply Complex.ext <;>
    simp [hga_trianglePlaneHomotopy, hga_triangleCoordinate, standardAffineSimplex] <;>
    linarith [hg5_sum3 a]

/-- The complex line written as a single complex coordinate, with the origin removed.
Source: `b6m_surfaceCoordinateEquiv`; Mathlib `ContinuousLinearEquiv.funUnique`. -/
def hga_complexLinePairIso : puncturedPair ℂ 1 ≅ pointComplementPair (0 : ℂ) :=
  TopPair.isoOfSubset b6m_surfaceCoordinateEquiv.symm.toHomeomorph
    (fun _ ↦ not_congr b6m_surfaceCoordinateEquiv.symm.map_eq_zero_iff)

theorem hga_complex_coordinates_one (z : Fin 1 → ℂ) :
    Complex.piCoordCLE 1 z = ![(z 0).re, (z 0).im] := by
  funext i
  change (Complex.piBasisOneI 1).repr z i = _
  simp only [Complex.piBasisOneI, Module.Basis.repr_reindex_apply,
    Module.Basis.smulTower'_repr, Pi.basisFun_repr, Complex.coe_basisOneI_repr]
  fin_cases i <;> rfl

theorem hga_complex_coordinates_one_symm (x : Fin 2 → ℝ) :
    ((Complex.piCoordCLE 1).symm x) 0 =
      (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  have h := hga_complex_coordinates_one ((Complex.piCoordCLE 1).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  have hr := congrFun h 0
  have hi := congrFun h 1
  apply Complex.ext
  · simpa using hr.symm
  · simpa using hi.symm

/-- The triangle extension in the defining real coordinates of the local class.
Source: `standardComplexRealPairIso`, `hga_triangleExtension_pairMap`. -/
def hga_triangleRealPairMap {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3) :
    puncturedPair ℝ 2 ⟶ pointComplementPair (σ b) :=
  (standardComplexRealPairIso 1).inv ≫ hga_trianglePlanePairMap 1 ≫
    hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap σ hσ b hb

theorem hga_triangleRealPairMap_standardAffine {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3)
    (a : StdSimplex ℝ (Fin 3)) :
    (TopPair.Hom.fst (hga_triangleRealPairMap σ hσ b hb)) (standardAffineSimplex 2 a) = σ a := by
  change hga_triangleExtension σ
    (hga_trianglePlaneHomotopy 1
      (((Complex.piCoordCLE 1).symm (standardAffineSimplex 2 a)) 0)) = σ a
  rw [hga_complex_coordinates_one_symm, hga_triangleCoordinate_standardAffine]
  exact hga_triangleExtension_coordinate σ a

open scoped Simplicial in
theorem hga_triangleRealPairMap_simplex {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3) :
    (TopCat.toSSet.map (TopPair.Hom.fst (hga_triangleRealPairMap σ hσ b hb))).app _
      (standardSingularSimplex 2) = b3Rest2_triSimplex σ := by
  apply ((TopCat.of T).toSSetObjEquiv _).injective
  ext a
  exact hga_triangleRealPairMap_standardAffine σ hσ b hb a

theorem hga_triangleRealPairMap_complexClass (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3) :
    relativeHomologyMap R 2 (hga_triangleRealPairMap σ hσ b hb)
      (standardLocalClass R 2) =
    relativeHomologyMap R 2
      (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap σ hσ b hb)
      (standardComplexLocalClass R 1) := by
  simp only [hga_triangleRealPairMap, relativeHomologyMap_comp, LinearMap.comp_apply]
  change _ = relativeHomologyMap R 2 (hga_triangleExtension_pairMap σ hσ b hb)
    (relativeHomologyMap R 2 hga_complexLinePairIso.hom
      (relativeHomologyMap R 2 (standardComplexRealPairIso 1).inv
        (standardLocalClass R 2)))
  rw [hga_trianglePlanePairMap_homology]

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangleRealPairMap_chain {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3) :
    b6m_localImageChain ℤ (pointComplementPair (σ b))
      (hga_triangleRealPairMap σ hσ b hb) =
      Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ) := by
  change ((SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.Hom.fst (hga_triangleRealPairMap σ hσ b hb)))
    (ModuleCat.of ℤ ℤ)).f 2).hom
      (Simplicial.chainOfSimplex ℤ (standardSingularSimplex 2)) = _
  rw [Simplicial.chainOfSimplex_map, hga_triangleRealPairMap_simplex]

set_option backward.isDefEq.respectTransparency false in
theorem hga_cycleClass_of_native_cycle (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (z : LinearMap.ker (K.sc n).g.hom) (c : K.cycles n)
    (hc : (K.iCycles n).hom c = z.1) :
    (K.sc n).moduleCatHomologyClass z = (K.homologyπ n).hom c := by
  have he : (K.sc n).moduleCatCyclesIso.inv.hom z = c := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have h := ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles z
    change (K.iCycles n).hom ((K.sc n).moduleCatCyclesIso.inv.hom z) = z.1 at h
    exact h.trans hc.symm
  have h := ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_π z
  change (K.homologyπ n).hom ((K.sc n).moduleCatCyclesIso.inv.hom z) = _ at h
  rw [he] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangle_localClass {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3) :
    let P := pointComplementPair (σ b)
    let z : LinearMap.ker (((relativeChainFunctor ℤ).obj P).sc 2).g.hom :=
      ⟨((relativeChainProjection ℤ P).f 2).hom
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)),
        hga_triangle_relative_cycle σ (σ b)
          (hga_triangle_face_ne_interior σ hσ b (by intro i; rw [hb]; norm_num))⟩
    (((relativeChainFunctor ℤ).obj P).sc 2).moduleCatHomologyClass z =
      relativeHomologyMap ℤ 2
        (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap σ hσ b hb)
        (standardComplexLocalClass ℤ 1) := by
  intro P z
  let F := hga_triangleRealPairMap σ hσ b hb
  calc
    _ = (((relativeChainFunctor ℤ).obj P).homologyπ 2).hom
        (b6m_localImageCycle ℤ P F) := by
      apply hga_cycleClass_of_native_cycle
      rw [b6m_localImageCycle_inclusion]
      change ((relativeChainProjection ℤ P).f 2).hom
        (b6m_localImageChain ℤ P (hga_triangleRealPairMap σ hσ b hb)) = _
      rw [hga_triangleRealPairMap_chain]
    _ = relativeHomologyMap ℤ 2 F (standardLocalClass ℤ 2) :=
      b6m_localImageCycle_class ℤ P F
    _ = _ := hga_triangleRealPairMap_complexClass ℤ σ hσ b hb

set_option backward.isDefEq.respectTransparency false in
open scoped Topology in
theorem hga_local_maps_eq_of_eventuallyEq (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] (y : T) (d n : ℕ)
    (F G : puncturedPair ℂ d ⟶ pointComplementPair y)
    (h : Filter.EventuallyEq (𝓝 (0 : Fin d → ℂ))
      (fun z : Fin d → ℂ ↦ TopPair.Hom.fst F z) (fun z : Fin d → ℂ ↦ TopPair.Hom.fst G z)) :
    relativeHomologyMap R n F = relativeHomologyMap R n G := by
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp h
  have hm : neighborhoodPointComplementPairMap U 0 ≫ F =
      neighborhoodPointComplementPairMap U 0 ≫ G := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      apply Subtype.ext
      have hF := TopPair.Hom.w_apply F ⟨z.1.1, z.2⟩
      have hG := TopPair.Hom.w_apply G ⟨z.1.1, z.2⟩
      exact hF.trans ((hUsub z.1.2).trans hG.symm)
    · ext z
      exact hUsub z.2
  have hi : b6m_subspacePairMap (TopCat.of (Fin d → ℂ)) U {0}ᶜ =
      neighborhoodPointComplementPairMap U 0 := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl
  have hb := b6m_closed_support_excision_bijective R hU isClosed_singleton
    (Set.singleton_subset_iff.mpr h0U) n
  rw [hi] at hb
  ext c
  obtain ⟨b, rfl⟩ := hb.2 c
  have he := congrArg (fun H ↦ relativeHomologyMap R n H b) hm
  simpa only [relativeHomologyMap_comp, LinearMap.comp_apply] using he

#print axioms hga_trianglePlaneHomotopy
#print axioms hga_trianglePlaneHomotopy_eq_zero
#print axioms hga_trianglePlanePairMap
#print axioms hga_continuous_trianglePlaneHomotopy
#print axioms hga_trianglePlanePairHomotopy
#print axioms hga_trianglePlanePairMap_homology
#print axioms hga_triangleCoordinate_standardAffine
#print axioms hga_complexLinePairIso
#print axioms hga_complex_coordinates_one

#print axioms hga_complex_coordinates_one_symm

#print axioms hga_triangleRealPairMap
#print axioms hga_triangleRealPairMap_standardAffine

#print axioms hga_triangleRealPairMap_simplex

#print axioms hga_triangleRealPairMap_complexClass

#print axioms hga_triangleRealPairMap_chain

#print axioms hga_cycleClass_of_native_cycle

#print axioms hga_triangle_localClass

#print axioms hga_local_maps_eq_of_eventuallyEq

end HodgeLean.Foundations.Program
