import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.MarkedDefs

/-! Independent nodal and branch-incidence tests of designated chart constructions.
HC no distance; AV milestone no distance. -/
noncomputable section
open TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology.Marked

namespace CheckData
private abbrev p : Fin 1 → MvPolynomial (Fin 2) ℂ :=
  fun _ => MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)
private abbrev N := zeroSet p
/-- The nodal chart used by the wrapper and auxiliary examples.
Source: explicit affine-plane and nodal coordinate constructions. -/
abbrev c : Chart N :=
  ⟨⊤, (2 : ℕ), (1 : ℕ), p, Homeomorph.Set.univ N⟩
/-- The nonzero tip of the horizontal branch.
Source: explicit affine-plane and nodal coordinate constructions. -/
def a : N := ⟨![(1 : ℂ), (0 : ℂ)], by simp [zeroSet, p]⟩
/-- The nonzero tip of the vertical branch.
Source: explicit affine-plane and nodal coordinate constructions. -/
def b : N := ⟨![(0 : ℂ), (1 : ℂ)], by simp [zeroSet, p]⟩
/-- The common vertex of the two branches.
Source: explicit affine-plane and nodal coordinate constructions. -/
def o : N := ⟨(0 : Fin 2 → ℂ), by simp [zeroSet, p]⟩
/-- The two designated coordinate branches.
Source: explicit affine-plane and nodal coordinate constructions. -/
abbrev D (j : Fin 2) : Set N := locus p (MvPolynomial.X j)
/-- The chart retaining both designated branch generators.
Source: explicit affine-plane and nodal coordinate constructions. -/
abbrev markedNode : SubsetChart N D :=
  { c with
    count := fun _ => (1 : ℕ)
    marked := fun j _ => MvPolynomial.X j
    membership := by
      intro x j
      simp only [D, locus, Set.mem_setOf_eq, MvPolynomial.eval_X]
      change (x.val.val j = (0 : ℂ) ↔ ∀ _ : Fin 1, x.val.val j = (0 : ℂ))
      simp }

private abbrev negNode : N ≃ₜ N where
  toFun z := ⟨-z.val, by intro j; simpa [p] using z.property j⟩
  invFun z := ⟨-z.val, by intro j; simpa [p] using z.property j⟩
  left_inv z := by apply Subtype.ext; exact neg_neg z.val
  right_inv z := by apply Subtype.ext; exact neg_neg z.val
  continuous_toFun := continuous_subtype_val.neg.subtype_mk
    (fun z => by intro j; simpa [p] using z.property j)
  continuous_invFun := continuous_subtype_val.neg.subtype_mk
    (fun z => by intro j; simpa [p] using z.property j)
/-- The negated nodal chart for a nonidentity transition.
Source: explicit affine-plane and nodal coordinate constructions. -/
abbrev d : Chart N := { c with coordinates := c.coordinates.trans negNode }

/-- Negating coordinates changes a branch tip and the return transition restores it.
Source: explicit coordinates on the carrier xy = 0. -/
theorem nonidentity_transition :
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) ∧
    (transition d c ⟨transition c d ⟨a, by trivial⟩, by trivial⟩).val (0 : Fin 2) = (1 : ℂ) := by
  change (- (1 : ℂ)) = (-1 : ℂ) ∧ - (-(1 : ℂ)) = (1 : ℂ)
  norm_num

example :
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) ∧
    (transition d c ⟨transition c d ⟨a, by trivial⟩, by trivial⟩).val
      (0 : Fin 2) = (1 : ℂ) := nonidentity_transition

private abbrev plane := CategoryTheory.Over.mk
  (AlgebraicGeometry.ComplexPoint.complexAffineSpace (Fin 2) ↘
    AlgebraicGeometry.Spec ↧ℂ)
private abbrev emptyP : Fin 0 → MvPolynomial (Fin 2) ℂ := Fin.elim0
private def emptyHome : (Fin 2 → ℂ) ≃ₜ zeroSet emptyP :=
  (Homeomorph.Set.univ _).symm.trans (Homeomorph.setCongr (by
    ext z
    simp [zeroSet]))
private abbrev planeChart : Chart (AlgebraicGeometry.ComplexPoint plane) where
  domain := ⊤
  n := (2 : ℕ)
  m := (0 : ℕ)
  equations := emptyP
  coordinates := (Homeomorph.Set.univ _).trans
    ((AlgebraicGeometry.ComplexPoint.affineSpaceHomeomorph (Fin 2)).trans emptyHome)
/-- The actual affine-plane chart retaining regular coordinate functions.
Source: explicit affine-plane and nodal coordinate constructions. -/
abbrev regularPlane : RegularChart plane
    (AlgebraicGeometry.AffineSpace.coord (AlgebraicGeometry.Spec ↧ℂ)) :=
  { planeChart with
    marked := MvPolynomial.X
    evaluation := by
      intro x j
      simp only [MvPolynomial.eval_X]
      change AlgebraicGeometry.ComplexPoint.affineSpaceHomeomorph (Fin 2) x.val j = _
      rw [AlgebraicGeometry.ComplexPoint.evaluate_top_eq_appTop]
      rfl }
/-- The affine-plane point with coordinate values one and two.
Source: explicit affine-plane and nodal coordinate constructions. -/
def planePoint : AlgebraicGeometry.ComplexPoint plane :=
  (AlgebraicGeometry.ComplexPoint.affineSpaceHomeomorph (Fin 2)).symm ![(1 : ℂ), (2 : ℂ)]

end CheckData

open CheckData

private lemma actual_regular_values :
    MvPolynomial.eval (coordinate regularPlane.toChart planePoint (by trivial)).val
      (regularPlane.marked (0 : Fin 2)) = (1 : ℂ) ∧
    MvPolynomial.eval (coordinate regularPlane.toChart planePoint (by trivial)).val
      (regularPlane.marked (1 : Fin 2)) = (2 : ℂ) := by
  simp only [regularPlane, MvPolynomial.eval_X]
  change (AlgebraicGeometry.ComplexPoint.affineSpaceHomeomorph (Fin 2) planePoint) (0 : Fin 2) = (1 : ℂ) ∧
    (AlgebraicGeometry.ComplexPoint.affineSpaceHomeomorph (Fin 2) planePoint) (1 : Fin 2) = (2 : ℂ)
  simp only [planePoint, Homeomorph.apply_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  trivial

/-- Regular functions retain their values on the actual affine plane.
Source: affineSpaceHomeomorph and evaluate_top_eq_appTop. -/
theorem affine_regular_falsification : MvPolynomial.eval
    (coordinate regularPlane.toChart planePoint (by trivial)).val
      (regularPlane.marked (0 : Fin 2)) = (1 : ℂ) ∧
    ¬ MvPolynomial.eval
      (coordinate regularPlane.toChart planePoint (by trivial)).val
        (regularPlane.marked (0 : Fin 2)) = (2 : ℂ) := by
  refine ⟨actual_regular_values.1, ?_⟩
  rw [actual_regular_values.1]
  norm_num

example : MvPolynomial.eval
    (coordinate regularPlane.toChart planePoint (by trivial)).val
      (regularPlane.marked (0 : Fin 2)) = (1 : ℂ) ∧
    ¬ MvPolynomial.eval
      (coordinate regularPlane.toChart planePoint (by trivial)).val
        (regularPlane.marked (0 : Fin 2)) = (2 : ℂ) := affine_regular_falsification

/-- A distinguishing nodal test for local subsets.
Source: explicit coordinates on the carrier xy = 0. -/
theorem local_subsets_falsification : o ∈ markedNode.domain ∧
    o ∈ D (0 : Fin 2) ∩ D (1 : Fin 2) ∧ a ∈ D (1 : Fin 2) ∧
    b ∈ D (0 : Fin 2) ∧ ¬ a ∈ D (0 : Fin 2) := by simp [D, locus, a, b, o]

example : o ∈ markedNode.domain ∧
    o ∈ D (0 : Fin 2) ∩ D (1 : Fin 2) ∧ a ∈ D (1 : Fin 2) ∧
    b ∈ D (0 : Fin 2) ∧ ¬ a ∈ D (0 : Fin 2) := local_subsets_falsification

/-- A distinguishing nodal test for transition continuous.
Source: explicit coordinates on the carrier xy = 0. -/
theorem transition_continuous_falsification : Continuous (transition c c) ∧
    ¬ (transition c c ⟨coordinate c a (by trivial), by trivial⟩).val = b.val := by
  constructor
  · exact continuous_subtype_val
  · intro h
    have hh := congrFun h (0 : Fin 2)
    change (1 : ℂ) = (0 : ℂ) at hh
    exact one_ne_zero hh

example : Continuous (transition c c) ∧
    ¬ (transition c c ⟨coordinate c a (by trivial), by trivial⟩).val = b.val := transition_continuous_falsification

/-- A distinguishing nodal test for transition cocycle.
Source: explicit coordinates on the carrier xy = 0. -/
theorem transition_cocycle_falsification : transition c c ⟨coordinate c a (by trivial), by trivial⟩ = a ∧
    ¬ transition c c ⟨coordinate c a (by trivial), by trivial⟩ = b := by
  constructor
  · rfl
  · intro h
    have hh := congrArg (fun z : N => z.val (0 : Fin 2)) h
    change (1 : ℂ) = (0 : ℂ) at hh
    exact one_ne_zero hh

example : transition c c ⟨coordinate c a (by trivial), by trivial⟩ = a ∧
    ¬ transition c c ⟨coordinate c a (by trivial), by trivial⟩ = b := transition_cocycle_falsification

/-- A distinguishing nodal test for transition subsets.
Source: explicit coordinates on the carrier xy = 0. -/
theorem transition_subsets_falsification : MvPolynomial.eval (transition markedNode.toChart markedNode.toChart
      ⟨a, by trivial⟩).val (markedNode.marked (1 : Fin 2) (0 : Fin 1)) = (0 : ℂ) ∧
    ¬ MvPolynomial.eval a.val (markedNode.marked (0 : Fin 2) (0 : Fin 1)) = (0 : ℂ) := by simp [transition, markedNode, c, a]

example : MvPolynomial.eval (transition markedNode.toChart markedNode.toChart
      ⟨a, by trivial⟩).val (markedNode.marked (1 : Fin 2) (0 : Fin 1)) = (0 : ℂ) ∧
    ¬ MvPolynomial.eval a.val (markedNode.marked (0 : Fin 2) (0 : Fin 1)) = (0 : ℂ) := transition_subsets_falsification

/-- Both branch generators vanish at the vertex, and not at a branch tip.
Source: explicit coordinates on the carrier xy = 0. -/
theorem intersection_subsets_falsification :
    (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart o (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) ∧
    ¬ (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart a (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) := by
  simp only [markedNode, MvPolynomial.eval_X]
  change (∀ j : Fin 2, ∀ _ : Fin 1, o.val j = (0 : ℂ)) ∧
    ¬ (∀ j : Fin 2, ∀ _ : Fin 1, a.val j = (0 : ℂ))
  constructor
  · intro j k; rfl
  · intro h
    exact one_ne_zero (h (0 : Fin 2) (0 : Fin 1))

example :
    (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart o (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) ∧
    ¬ (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart a (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) :=
  intersection_subsets_falsification

/-- The negating transition is continuous on its open overlap and changes a nonzero point.
Source: Munkres, Topology, §§16 and 18; explicit nodal coordinates. -/
theorem transition_continuous_example :
    Continuous (transition c d) ∧ IsOpen (overlap c d) ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) := by
  refine ⟨?_, ?_, nonidentity_transition.1⟩
  · exact CheckData.negNode.continuous.comp continuous_subtype_val
  · change IsOpen (Set.univ : Set _)
    exact isOpen_univ

example : Continuous (transition c d) ∧ IsOpen (overlap c d) ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) :=
  transition_continuous_example

/-- Identity and composition at a branch tip retain the actual transition values.
Source: Munkres, Topology, §18; explicit nodal coordinates. -/
theorem transition_cocycle_example :
    transition c c ⟨coordinate c a (by trivial), by trivial⟩ =
      coordinate c a (by trivial) ∧
    transition d c ⟨transition c d
      ⟨coordinate c a (by trivial), by trivial⟩, by trivial⟩ =
      transition c c ⟨coordinate c a (by trivial), by trivial⟩ ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) := by
  refine ⟨rfl, ?_, nonidentity_transition.1⟩
  apply Subtype.ext
  exact neg_neg a.val

example :
    transition c c ⟨coordinate c a (by trivial), by trivial⟩ =
      coordinate c a (by trivial) ∧
    transition d c ⟨transition c d
      ⟨coordinate c a (by trivial), by trivial⟩, by trivial⟩ =
      transition c c ⟨coordinate c a (by trivial), by trivial⟩ ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) :=
  transition_cocycle_example

#print axioms transition_continuous_example
#print axioms transition_cocycle_example

#print axioms CheckData.nonidentity_transition
#print axioms affine_regular_falsification
#print axioms local_subsets_falsification
#print axioms transition_continuous_falsification
#print axioms transition_cocycle_falsification
#print axioms transition_subsets_falsification
#print axioms intersection_subsets_falsification

end HodgeLean.Foundations.ComplexTopology.Marked
