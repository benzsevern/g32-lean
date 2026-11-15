import HodgeLean.Foundations.QuotientDuality.ProperCycleRealVectorShift
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Low-degree local homology of actual tangential products -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A map into the actual subspace whose ambient composite is homotopic to the identity kills degree-zero relative homology.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, homotopy invariance and the relative sequence.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_zero_of_ambient_section
    (P : TopPair.{0}) (q : P.fst ⟶ P.snd) (H : TopCat.Homotopy (q ≫ P.map) (𝟙 P.fst)) :
    IsZero (RelativeHomology ℚ P 0) := by
  let C := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  have he := (H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ)).homologyMap_eq 0
  change HomologicalComplex.homologyMap (C.map (q ≫ P.map)) 0 =
    HomologicalComplex.homologyMap (C.map (𝟙 P.fst)) 0 at he
  rw [C.map_comp, HomologicalComplex.homologyMap_comp, C.map_id,
    HomologicalComplex.homologyMap_id] at he
  letI : Epi (HomologicalComplex.homologyMap (relativeChainShortComplex ℚ P).f 0) := by
    change Epi (HomologicalComplex.homologyMap (C.map P.map) 0)
    exact epi_of_epi_fac he
  apply HomologicalComplex.ExactAt.isZero_homology
  refine (relativeChainShortComplex_shortExact ℚ P).exactAt_X₃ 0 inferInstance ?_
  intro j hj
  simp only [ComplexShape.down_Rel] at hj
  omega

/-- A real tangential factor gives a literal section of the point-complement inclusion up to ambient homotopy.
Source: Hatcher, Algebraic Topology, section 2.1, homotopy invariance.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_product_local_zero (Y : TopCat.{0}) (y : Y) :
    Subsingleton (orientationGroup (TopCat.of (ℝ × Y)) 0 (0, y)) := by
  let P := pointComplementPair (M := ℝ × Y) (0, y)
  have hmem (z : ℝ × Y) : (1, z.2) ∈ ({(0, y)}ᶜ : Set (ℝ × Y)) := by
    intro h
    have hh : (1 : ℝ) = 0 := congrArg Prod.fst h
    exact one_ne_zero hh
  let q : P.fst ⟶ P.snd := TopCat.ofHom
    (⟨fun (z : ℝ × Y) => ⟨(1, z.2), hmem z⟩,
      (continuous_const.prodMk continuous_snd).subtype_mk hmem⟩ :
      C(ℝ × Y, ({(0, y)}ᶜ : Set (ℝ × Y))))
  let H : TopCat.Homotopy (q ≫ P.map) (𝟙 P.fst) :=
    { toFun := fun (uz : unitInterval × (ℝ × Y)) => ((1 - (uz.1 : ℝ)) + (uz.1 : ℝ) * uz.2.1, uz.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro z
        change ((1 - (0 : ℝ)) + 0 * z.1, z.2) = (1, z.2)
        simp
      map_one_left := by
        intro z
        change ((1 - (1 : ℝ)) + 1 * z.1, z.2) = z
        simp <;> rfl }
  exact ModuleCat.subsingleton_of_isZero (properCycle_relative_zero_of_ambient_section P q H)

end HodgeLean.Foundations.QuotientDuality
