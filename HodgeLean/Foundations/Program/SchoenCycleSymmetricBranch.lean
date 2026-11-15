import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

/-! # Marked tuple incidence in the retained branch image
Insertion of a marked point realizes the corresponding branch image on complex points.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The retained branch insertion prepends its marked point to every tuple. -/
theorem s2e_branchInsertion_tuple (Z : Over (Spec ↧ℂ)) (n : ℕ)
    (p : ComplexPoint Z) (f : Fin n → ComplexPoint Z) :
    s2_lift n f ≫ s2c_branchInsertion Z n p = s2_lift (n + 1) (Fin.cons p f) := by
  unfold s2c_branchInsertion
  rw [s2e_comp_lift]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change s2_lift n f ≫ (CartesianMonoidalCategory.toUnit _ ≫ p) = p
    rw [← Category.assoc]
    have hu : s2_lift n f ≫ CartesianMonoidalCategory.toUnit _ = 𝟙 _ :=
      (SemiCartesianMonoidalCategory.isTerminalTensorUnit).hom_ext _ _
    rw [hu, Category.id_comp]
  · exact s2_check_lift_proj n f j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An unordered tuple containing the marked point factors through its actual branch insertion. -/
theorem s2e_symmetricQuotientEvaluation_branch_image
    (Z B : Over (Spec ↧ℂ)) (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (s : Sym (ComplexPoint Z) (n + 1)) (p : ComplexPoint Z) (hp : p ∈ s) :
    ∃ z : ComplexPoint (g3_power Z n),
      Point.map (s2c_branchInsertion Z n p ≫ γ) z =
        s2e_symmetricQuotientEvaluation (n + 1) γ s := by
  classical
  obtain ⟨f, hf⟩ := s2e_sym_exists_enumeration (s.erase p hp)
  have hcons : (List.ofFn (Fin.cons p f) : Multiset (ComplexPoint Z)) = s := by
    rw [List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    change p ::ₘ (List.ofFn f : Multiset (ComplexPoint Z)) = s
    rw [hf]
    exact congrArg Sym.toMultiset (Sym.cons_erase hp)
  refine ⟨s2_lift n f, ?_⟩
  change s2_lift n f ≫ (s2c_branchInsertion Z n p ≫ γ) = _
  rw [← Category.assoc, s2e_branchInsertion_tuple]
  exact (s2e_symmetricQuotientEvaluation_eq (n + 1) γ hγ s _ hcons).symm

/-- A marked tuple maps into the support of the retained branch ideal. -/
theorem s2e_symmetricQuotientEvaluation_mem_branch_support
    (Z B : Over (Spec ↧ℂ)) (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (s : Sym (ComplexPoint Z) (n + 1)) (p : ComplexPoint Z) (hp : p ∈ s) :
    Point.underlying (s2e_symmetricQuotientEvaluation (n + 1) γ s) ∈
      (s2c_branchIdeal Z B n γ p).support := by
  obtain ⟨z, hz⟩ := s2e_symmetricQuotientEvaluation_branch_image Z B n γ hγ s p hp
  rw [← hz, Point.underlying_map]
  exact (s2c_branchInsertion Z n p ≫ γ).left.range_subset_ker_support ⟨z.underlying, rfl⟩

end HodgeLean.Foundations.Program
