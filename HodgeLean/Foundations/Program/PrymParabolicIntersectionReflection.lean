import HodgeLean.Foundations.Program.PrymParabolicIntersectionPermutation

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

theorem hga_standardAffineSimplex_two_injective : Function.Injective (standardAffineSimplex 2) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change a.weights 0 - a.weights 2 = b.weights 0 - b.weights 2 at h0
  change a.weights 1 - a.weights 2 = b.weights 1 - b.weights 2 at h1
  apply hg5_simplex_ext <;> linarith [hg5_sum3 a, hg5_sum3 b]

theorem hga_triangleRetraction_zero_weights (i : Fin 3) :
    (hga_triangleRetraction 0).weights i = 1 / 3 := by
  fin_cases i <;>
    norm_num [hga_triangleRetraction, hga_normalize_barycentric,
      Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_three]

theorem hga_vertexSwap_weights (a : StdSimplex ℝ (Fin 3)) :
    (StdSimplex.map (![1, 0, 2] : Fin 3 → Fin 3) a).weights 0 = a.weights 1 ∧
    (StdSimplex.map (![1, 0, 2] : Fin 3 → Fin 3) a).weights 1 = a.weights 0 ∧
    (StdSimplex.map (![1, 0, 2] : Fin 3 → Fin 3) a).weights 2 = a.weights 2 := by
  have hf : Function.Injective (![1, 0, 2] : Fin 3 → Fin 3) := by decide
  exact ⟨Finsupp.mapDomain_apply_of_injective hf a.weights 1,
    Finsupp.mapDomain_apply_of_injective hf a.weights 0,
    Finsupp.mapDomain_apply_of_injective hf a.weights 2⟩

/-- Exchange the two coordinates of the punctured real plane.
Source: the coordinate transposition on `Fin 2 → ℝ`. -/
def hga_realSwapPairMap : puncturedPair ℝ 2 ⟶ puncturedPair ℝ 2 :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun z : Fin 2 → ℝ ↦ ![z 1, z 0], by fun_prop⟩) (by
      intro z hz h
      apply hz
      funext i
      fin_cases i
      · exact congrFun h 1
      · exact congrFun h 0)

theorem hga_realSwap_standardSimplex :
    (TopCat.toSSet.map (TopPair.Hom.fst hga_realSwapPairMap)).app _
      (standardSingularSimplex 2) =
      b3Rest2_triSimplex (hga_vertexTriangle
        ⟨standardAffineSimplex 2, continuous_standardAffineSimplex 2⟩ ![1, 0, 2]) := by
  apply ((TopCat.of (Fin 2 → ℝ)).toSSetObjEquiv _).injective
  ext a i
  obtain ⟨h0, h1, h2⟩ := hga_vertexSwap_weights a
  fin_cases i
  · change a.weights 1 - a.weights 2 =
      (StdSimplex.map (![1, 0, 2] : Fin 3 → Fin 3) a).weights 0 -
        (StdSimplex.map (![1, 0, 2] : Fin 3 → Fin 3) a).weights 2
    rw [h0, h2]
  · change a.weights 0 - a.weights 2 =
      (StdSimplex.map (![1, 0, 2] : Fin 3 → Fin 3) a).weights 1 -
        (StdSimplex.map (![1, 0, 2] : Fin 3 → Fin 3) a).weights 2
    rw [h1, h2]

set_option backward.isDefEq.respectTransparency false in
theorem hga_realSwap_standardLocalClass :
    relativeHomologyMap ℤ 2 hga_realSwapPairMap (standardLocalClass ℤ 2) =
      -standardLocalClass ℤ 2 := by
  let σ : C(StdSimplex ℝ (Fin 3), Fin 2 → ℝ) :=
    ⟨standardAffineSimplex 2, continuous_standardAffineSimplex 2⟩
  let b := hga_triangleRetraction 0
  have hb : ∀ i, 0 < b.weights i := by
    intro i
    rw [hga_triangleRetraction_zero_weights]
    norm_num
  have hσb : σ b = 0 := by
    funext i
    fin_cases i <;> simp [σ, b, standardAffineSimplex, hga_triangleRetraction_zero_weights]
  have hrel := hga_triangleSwap_relative_classes σ hga_standardAffineSimplex_two_injective b hb
  rw [hσb] at hrel
  let c := (standardLocalCycle ℤ 2).hom 1
  let d := b6m_localImageCycle ℤ (puncturedPair ℝ 2) hga_realSwapPairMap
  have hc : (((relativeChainFunctor ℤ).obj (puncturedPair ℝ 2)).iCycles 2).hom c =
      ((relativeChainProjection ℤ (puncturedPair ℝ 2)).f 2).hom
        (Simplicial.chainOfSimplex ℤ (b3Rest2_triSimplex σ)) :=
    ConcreteCategory.congr_hom (standardLocalCycle_inclusion ℤ 2) 1
  have hd : (((relativeChainFunctor ℤ).obj (puncturedPair ℝ 2)).iCycles 2).hom d =
      ((relativeChainProjection ℤ (puncturedPair ℝ 2)).f 2).hom
        (Simplicial.chainOfSimplex ℤ
          (b3Rest2_triSimplex (hga_vertexTriangle σ ![1, 0, 2]))) := by
    rw [b6m_localImageCycle_inclusion]
    change ((relativeChainProjection ℤ (puncturedPair ℝ 2)).f 2).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst hga_realSwapPairMap))
        (ModuleCat.of ℤ ℤ)).f 2).hom (Simplicial.chainOfSimplex ℤ (standardSingularSimplex 2))) = _
    rw [Simplicial.chainOfSimplex_map, hga_realSwap_standardSimplex]
  have h := hrel c d hc hd
  change standardLocalClass ℤ 2 +
    (show RelativeHomology ℤ (puncturedPair ℝ 2) 2 from
      (((relativeChainFunctor ℤ).obj (puncturedPair ℝ 2)).homologyπ 2).hom
        (b6m_localImageCycle ℤ (puncturedPair ℝ 2) hga_realSwapPairMap)) = 0 at h
  rw [b6m_localImageCycle_class] at h
  calc
    _ = (standardLocalClass ℤ 2 +
        relativeHomologyMap ℤ 2 hga_realSwapPairMap (standardLocalClass ℤ 2)) -
        standardLocalClass ℤ 2 := by abel
    _ = -standardLocalClass ℤ 2 := by rw [h, zero_sub]

/-- Coordinate exchange transported to the complex line.
Source: the standard real coordinate equivalence of the complex line. -/
def hga_complexSwapPairMap : puncturedPair ℂ 1 ⟶ puncturedPair ℂ 1 :=
  (standardComplexRealPairIso 1).hom ≫ hga_realSwapPairMap ≫
    (standardComplexRealPairIso 1).inv

set_option backward.isDefEq.respectTransparency false in
theorem hga_complexSwap_standardLocalClass :
    relativeHomologyMap ℤ 2 hga_complexSwapPairMap (standardComplexLocalClass ℤ 1) =
      -standardComplexLocalClass ℤ 1 := by
  have hi : relativeHomologyMap ℤ 2 (standardComplexRealPairIso 1).hom
      (standardComplexLocalClass ℤ 1) = standardLocalClass ℤ 2 := by
    change relativeHomologyMap ℤ 2 (standardComplexRealPairIso 1).hom
      (relativeHomologyMap ℤ 2 (standardComplexRealPairIso 1).inv
        (standardLocalClass ℤ 2)) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
      Iso.inv_hom_id, relativeHomologyMap_id, LinearMap.id_apply]
  unfold hga_complexSwapPairMap
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply]
  rw [hi, hga_realSwap_standardLocalClass, map_neg]
  rfl

theorem hga_complexSwapPairMap_apply (z : Fin 1 → ℂ) (i : Fin 1) :
    (TopPair.Hom.fst hga_complexSwapPairMap z) i =
      ((z i).im : ℂ) + ((z i).re : ℂ) * Complex.I := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change ((Complex.piCoordCLE 1).symm
    ![(Complex.piCoordCLE 1 z) 1, (Complex.piCoordCLE 1 z) 0]) 0 = _
  rw [hga_complex_coordinates_one_symm, hga_complex_coordinates_one]
  rfl

/-- Complex conjugation on the punctured complex line.
Source: complex conjugation preserves the complement of zero. -/
def hga_complexConjPairMap : puncturedPair ℂ 1 ⟶ puncturedPair ℂ 1 :=
  hga_complexScalarPairMap ⟨star, continuous_star⟩
    (fun z hz ↦ star_ne_zero.mpr hz)

set_option backward.isDefEq.respectTransparency false in
open scoped Topology in
theorem hga_complexConj_standardLocalClass :
    relativeHomologyMap ℤ 2 hga_complexConjPairMap (standardComplexLocalClass ℤ 1) =
      -standardComplexLocalClass ℤ 1 := by
  let f : C(ℂ, ℂ) := ⟨fun z ↦ -Complex.I * z, by fun_prop⟩
  have hρ : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have hne : ∀ z, z ≠ 0 → f z ≠ 0 := fun z hz ↦ mul_ne_zero hρ hz
  have hf0 : f 0 = 0 := mul_zero _
  have hf : HasDerivAt f (-Complex.I) 0 := by
    simpa only [f, ContinuousMap.coe_mk, mul_one, id_eq] using
      (hasDerivAt_id (0 : ℂ)).const_mul (-Complex.I)
  have hp := hga_complexScalar_preservesLocalClass ℤ f hne hf0 (-Complex.I) hρ hf
  have hm : relativeHomologyMap ℤ 2 (hga_complexScalarPairMap f hne ≫
      hga_complexConjPairMap) = relativeHomologyMap ℤ 2 hga_complexSwapPairMap := by
    apply hga_local_maps_eq_of_eventuallyEq ℤ (0 : Fin 1 → ℂ) 1 2
    apply Filter.Eventually.of_forall
    intro z
    funext i
    change TopPair.Hom.fst (hga_complexScalarPairMap f hne ≫
      hga_complexConjPairMap) z i = TopPair.Hom.fst hga_complexSwapPairMap z i
    rw [hga_complexSwapPairMap_apply]
    change star (-Complex.I * z i) = ((z i).im : ℂ) + ((z i).re : ℂ) * Complex.I
    apply Complex.ext <;> simp
  have h := congrArg (fun m ↦ m (standardComplexLocalClass ℤ 1)) hm
  simpa only [relativeHomologyMap_comp, LinearMap.comp_apply, hp,
    hga_complexSwap_standardLocalClass] using h

#print axioms hga_complexConjPairMap
#print axioms hga_complexConj_standardLocalClass

#print axioms hga_complexSwapPairMap_apply

#print axioms hga_complexSwapPairMap
#print axioms hga_complexSwap_standardLocalClass

#print axioms hga_standardAffineSimplex_two_injective

#print axioms hga_triangleRetraction_zero_weights

#print axioms hga_vertexSwap_weights

#print axioms hga_realSwapPairMap
#print axioms hga_realSwap_standardSimplex

#print axioms hga_realSwap_standardLocalClass

end HodgeLean.Foundations.Program
