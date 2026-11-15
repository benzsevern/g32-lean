import HodgeLean.Foundations.Curves.SymmetricCharts.StageThree.Defs
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Basic

/-! # Independent retained assembly tests

Actual cubic quotients and their insertion kernels test the retained constructions.
No stage-three interface is imported.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

private def p : ComplexPoint E := Over.homMk finitePoint finitePoint_over
private def q : ComplexPoint E := Over.homMk infinity infinity_over

private theorem points_ne : p ≠ q := by
  intro h
  have H := congrArg (fun f : ComplexPoint E => f.left) h
  exact infinity_ne_finitePoint H.symm

private def x : (g3_power E 1).left :=
  (p ≫ (MonoidalCategory.rightUnitor E).inv).left (default : Spec ↧ℂ)

private def W : Index E 1 := Classical.choose
  (s2_projective_invariantAffineIndex_cover ℂ _ (g3_power E 1).hom _ (action E 1) x)

private theorem xW : x ∈ (W.val : Set (g3_power E 1).left) :=
  Classical.choose_spec
    (s2_projective_invariantAffineIndex_cover ℂ _ (g3_power E 1).hom _ (action E 1) x)

private def toCurve : symmetricPower E 1 ≅ E :=
  (Classical.choice retained_comparison_example).symm ≪≫ MonoidalCategory.rightUnitor E

private theorem chart_nonempty : Nonempty (affineChart E 1 W) :=
  ⟨(affineProjection E 1 W) ⟨x, xW⟩⟩

private theorem retained_charts_falsification : ¬ IsEmpty (affineChart E 1 W) := by
  intro he
  exact he.false chart_nonempty.some

/-- A nonempty actual invariant chart survives transport to its quotient target.
Source: SGA 1, Exposé V, §1, invariant affine quotient.
HC no distance; AV milestone no distance.
-/
theorem retained_charts_example : ∃ y : E.left,
    y ∈ Set.range (retainedChart E 1 toCurve W) := by
  exact ⟨_, chart_nonempty.some, rfl⟩

example : ∃ y : E.left,
    y ∈ Set.range (retainedChart E 1 toCurve W) := retained_charts_example

example : Nonempty (g3_power E 0 ≅ symmetricPower E 0) := degree_zero_example

private theorem retained_geometry_falsification : topologicalKrullDim (symmetricPower E 1).left ≠ 0 := by
  rw [smooth_dimension_example]
  norm_num

/-- The positive-degree cubic quotient has dimension one.
Source: Milne, Jacobian Varieties, §3, Proposition 3.2.
HC no distance; AV milestone no distance.
-/
theorem retained_geometry_example : topologicalKrullDim (symmetricPower E 1).left = 1 :=
  smooth_dimension_example

example : topologicalKrullDim (symmetricPower E 1).left = 1 := retained_geometry_example

private def tuple : ComplexPoint (g3_power E 2) := s2_lift 2 (![p, q] : Fin 2 → ComplexPoint E)
private def transposition : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private theorem tuple_ne : Point.map (s2_permute E 2 transposition) tuple ≠ tuple := by
  intro h
  have H := congrArg (fun f : ComplexPoint (g3_power E 2) => f ≫ g3_proj E 2 (0 : Fin 2)) h
  have hh : s2_permute E 2 transposition ≫ g3_proj E 2 (0 : Fin 2) =
      g3_proj E 2 (1 : Fin 2) := by
    simpa [s2_permute, transposition] using
      (s2_check_lift_proj 2 (fun i => g3_proj E 2 (transposition.symm i)) (0 : Fin 2))
  change (tuple ≫ s2_permute E 2 transposition) ≫ g3_proj E 2 (0 : Fin 2) =
    tuple ≫ g3_proj E 2 (0 : Fin 2) at H
  rw [Category.assoc, hh] at H
  have H' : q = p := by simpa [tuple, s2_check_lift_proj] using H
  exact points_ne H'.symm

private theorem symmetric_power_assembly_falsification :
    ¬ Function.Injective (Point.map (projection E 2)) := by
  intro hi
  apply tuple_ne
  apply hi
  change (tuple ≫ s2_permute E 2 transposition) ≫ projection E 2 = tuple ≫ projection E 2
  rw [Category.assoc]
  have hinv : s2_permute E 2 transposition ≫ projection E 2 = projection E 2 := by
    apply Over.OverMorphism.ext
    apply s2_gluedQuotientMap_invariant
    exact s2_projective_invariantAffineIndex_cover ℂ _ (g3_power E 2).hom _ (action E 2)
  rw [hinv]

/-- The quotient records a genuine two-point divisor rather than a constant tuple.
Source: Milne, Jacobian Varieties, §3, permutation orbits.
HC no distance; AV milestone no distance.
-/
theorem symmetric_power_assembly_example :
    s2_lift 2 (![p, q] : Fin 2 → ComplexPoint E) ≠
      s2_lift 2 (![p, p] : Fin 2 → ComplexPoint E) := by
  intro h
  have H := congrArg (fun f => f ≫ g3_proj E 2 (1 : Fin 2)) h
  simp only [s2_check_lift_proj] at H
  exact points_ne H.symm

example : s2_lift 2 (![p, q] : Fin 2 → ComplexPoint E) ≠
    s2_lift 2 (![p, p] : Fin 2 → ComplexPoint E) := symmetric_power_assembly_example

private def z : Fin 2 → ComplexPoint E := ![p, q]
private def singleton : Finset (Fin 2) := {1}

private theorem actual_points_injective : Function.Injective z := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [z, points_ne, Ne.symm points_ne]

private theorem selected_point : subsetPoints (r := 1) z singleton ⟨0, by simp [singleton]⟩ = q := by
  have hm := (singleton.orderIsoOfFin rfl ⟨0, by simp [singleton]⟩).property
  have hn : (singleton.orderIsoOfFin rfl ⟨0, by simp [singleton]⟩).val = (1 : Fin 2) :=
    Finset.mem_singleton.mp hm
  change z _ = q
  rw [hn]
  rfl

private theorem paired_subset_indexing_falsification :
    subsetPoints (r := 1) z singleton ⟨0, by simp [singleton]⟩ ≠ z (pairLabel 1 0 0) := by
  rw [selected_point]
  exact points_ne.symm

/-- The selected odd branch is the second actual cubic point.
Source: Schoen (1988), §2, pp. 12–14, retained pair ordering.
HC no distance; AV milestone no distance.
-/
theorem paired_subset_indexing_example :
    subsetPoints (r := 1) z singleton ⟨0, by simp [singleton]⟩ = z (pairLabel 1 0 1) := selected_point

example : subsetPoints (r := 1) z singleton ⟨0, by simp [singleton]⟩ = z (pairLabel 1 0 1) :=
  paired_subset_indexing_example

private theorem repeated_sum :
    (Finset.univ : Finset (Fin 2)).sup
      (stageZeroBranches E (symmetricPower E 1) 0 1 (projection E 1) (fun _ => p)) =
      branchIdeal E 0 p := by
  change (Finset.univ : Finset (Fin 2)).sup (fun _ => branchIdeal E 0 p) = _
  exact Finset.sup_const Finset.univ_nonempty _

private theorem stage_zero_assembly_falsification :
    ¬ IsEmpty (s2c_subscheme (symmetricPower E 1)
      ((Finset.univ : Finset (Fin 2)).sup
        (stageZeroBranches E (symmetricPower E 1) 0 1 (projection E 1) (fun _ => p)))).left := by
  rw [repeated_sum]
  intro he
  have hn := excess_branches_example
  have hid : intersectionIdeal E 0 2 (fun _ => p) = branchIdeal E 0 p := by
    simp only [intersectionIdeal, iSup_const]
  change Nonempty (s2c_subscheme (symmetricPower E 1)
    (intersectionIdeal E 0 2 (fun _ => p))).left at hn
  rw [hid] at hn
  exact he.false hn.some

/-- The selected odd branch of two distinct cubic points is a smooth actual subscheme.
Source: Schoen (1988), Lemma 2.2; Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
theorem stage_zero_assembly_example :
    Smooth (s2c_subscheme (symmetricPower E 1)
      (singleton.sup (stageZeroBranches E (symmetricPower E 1) 0 1 (projection E 1) z))).hom := by
  have H := (branch_intersections E 0 1 (by omega) (fun _ => q)
    (by intro i j _; exact Subsingleton.elim _ _)).2.1
  letI : SmoothOfRelativeDimension 0 (branchIntersection E 0 1 (fun _ => q)).hom := H
  have HS : Smooth (branchIntersection E 0 1 (fun _ => q)).hom :=
    SmoothOfRelativeDimension.smooth 0 _
  rw [singleton, Finset.sup_singleton]
  change Smooth (s2c_subscheme (symmetricPower E 1) (branchIdeal E 0 q)).hom
  have hid : intersectionIdeal E 0 1 (fun _ => q) = branchIdeal E 0 q := by
    change (⨆ _ : Fin 1, branchIdeal E 0 q) = _
    exact iSup_const
  change Smooth (s2c_subscheme (symmetricPower E 1)
    (intersectionIdeal E 0 1 (fun _ => q))).hom at HS
  rw [hid] at HS
  exact HS

example : Smooth (s2c_subscheme (symmetricPower E 1)
    (singleton.sup (stageZeroBranches E (symmetricPower E 1) 0 1 (projection E 1) z))).hom :=
  stage_zero_assembly_example

#print axioms retained_charts_example
#print axioms retained_geometry_example
#print axioms symmetric_power_assembly_example
#print axioms paired_subset_indexing_example
#print axioms stage_zero_assembly_example
#print axioms retained_charts_falsification
#print axioms retained_geometry_falsification
#print axioms symmetric_power_assembly_falsification
#print axioms paired_subset_indexing_falsification
#print axioms stage_zero_assembly_falsification
end HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
