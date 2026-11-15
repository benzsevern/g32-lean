import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.MarkedChecks
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.MarkedIdeal

/-! Designated-subset local charts, their overlap laws and finite intersections.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology.Marked

open CheckData

/-- Affine regular.
Source: Hartshorne, Algebraic Geometry, II.2, Proposition 2.3; II.3. -/
theorem affine_regular_aux (X : Over (Spec ↧ℂ)) [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {r : ℕ} (f : Fin r → Γ(X.left, ⊤)) :
    ∃ c : RegularChart X f, c.domain = ⊤ := by
  letI : Algebra ℂ Γ(X.left, ⊤) := overSpecAlgebra X ⊤
  letI : Algebra.FiniteType ℂ Γ(X.left, ⊤) := affine_globalSections_finiteType X
  obtain ⟨n, m, g, p, hg, hp⟩ := finite_presentation_equations (S := Γ(X.left, ⊤))
  choose q hq using fun j => hg (f j)
  let h := (affinePointModel X).trans (presentationPointHomeomorph g hg p hp)
  refine ⟨{
    domain := ⊤
    n := n
    m := m
    equations := p
    coordinates := (Homeomorph.Set.univ (ComplexPoint X)).trans h
    marked := q
    evaluation := ?_ }, rfl⟩
  intro x j
  change MvPolynomial.eval (fun i => affinePointModel X x.val (g (MvPolynomial.X i)))
    (q j) = _
  rw [eval_generators, hq, affinePointModel_apply]

example : MvPolynomial.eval
    (coordinate regularPlane.toChart planePoint (by trivial)).val
      (regularPlane.marked (0 : Fin 2)) = (1 : ℂ) ∧
    ¬ MvPolynomial.eval
      (coordinate regularPlane.toChart planePoint (by trivial)).val
        (regularPlane.marked (0 : Fin 2)) = (2 : ℂ) := affine_regular_falsification

/-- Local subsets.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5; Bochnak–Coste–Roy, Theorem 9.2.1. -/
theorem local_subsets_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {r : ℕ} (Z : Fin r → Over (Spec ↧ℂ)) (i : ∀ j, Z j ⟶ X)
    [∀ j, IsClosedImmersion (i j).left] (x : ComplexPoint X) :
    ∃ c : SubsetChart (ComplexPoint X) (fun j => Set.range (Point.map (i j))),
      x ∈ c.domain := by
  obtain ⟨A, hA, hxA, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X.left) (x := x.underlying)
      (U := ⊤) (by trivial)
  letI : IsAffine (openScheme X A).left := hA
  letI : LocallyOfFiniteType (openScheme X A).hom :=
    inferInstanceAs (LocallyOfFiniteType (A.ι ≫ X.hom))
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsNoetherianRing Γ(X.left, A) :=
    IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  have hfg (j : Fin r) := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian ((i j).left.ker.ideal ⟨A, hA⟩))
  choose count g hg using hfg
  have hg' (j : Fin r) : Ideal.span (Set.range (g j)) = (i j).left.ker.ideal ⟨A, hA⟩ :=
    Ideal.submodule_span_eq.symm.trans (hg j)
  let Y := openScheme X A
  letI : Algebra ℂ Γ(Y.left, ⊤) := overSpecAlgebra Y ⊤
  letI : Algebra.FiniteType ℂ Γ(Y.left, ⊤) := affine_globalSections_finiteType Y
  obtain ⟨n, m, f, p, hf, hp⟩ := finite_presentation_equations (S := Γ(Y.left, ⊤))
  let φ := A.ι.appLE A ⊤ A.ι_preimage_self.ge
  choose q hq using fun j k => hf (φ (g j k))
  let h := (affinePointModel Y).trans (presentationPointHomeomorph f hf p hp)
  let W : Opens (ComplexPoint X) := ⟨Point.overOpen A, Point.isOpen_overOpen A⟩
  refine ⟨{ domain := W
            n := n
            m := m
            equations := p
            coordinates := (openHomeomorph X A).symm.trans h
            count := count
            marked := q
            membership := ?_ }, hxA⟩
  intro z j
  rw [image_iff_generators (i j) ⟨A, hA⟩ (g j) (hg' j) z.val z.property]
  apply forall_congr'
  intro k
  let y := (openHomeomorph X A).symm z
  have hy : Point.map (openInclusion X A) y = z.val :=
    congrArg Subtype.val ((openHomeomorph X A).apply_symm_apply z)
  have hev := evaluate_appLE (openInclusion X A) A ⊤ A.ι_preimage_self.ge
    (g j k) y (by trivial)
  rw [hy] at hev
  change Point.evaluate A (g j k) z.val = 0 ↔
    MvPolynomial.eval (fun l => affinePointModel Y y (f (MvPolynomial.X l))) (q j k) = 0
  rw [eval_generators, hq, affinePointModel_apply]
  rw [hev]
  rfl

example : o ∈ markedNode.domain ∧
    o ∈ D (0 : Fin 2) ∩ D (1 : Fin 2) ∧ a ∈ D (1 : Fin 2) ∧
    b ∈ D (0 : Fin 2) ∧ ¬ a ∈ D (0 : Fin 2) := local_subsets_falsification

/-- Transition continuous.
Source: Munkres, Topology, §16, subspace topology. -/
theorem transition_continuous_aux {X : Type*} [TopologicalSpace X] (c d : Chart X) :
    Continuous (transition c d) ∧ IsOpen (overlap c d) := by
  constructor
  · apply d.coordinates.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (c.coordinates.symm.continuous.comp continuous_subtype_val)
  · exact d.domain.isOpen.preimage (continuous_subtype_val.comp c.coordinates.symm.continuous)

example : Continuous (transition c d) ∧ IsOpen (overlap c d) ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) :=
  transition_continuous_example

/-- Transition cocycle.
Source: Munkres, Topology, §§16 and 18, composition of chart maps. -/
theorem transition_cocycle_aux {X : Type*} [TopologicalSpace X] (c d e : Chart X)
    (x : X) (hc : x ∈ c.domain) (hd : x ∈ d.domain) (he : x ∈ e.domain) :
    transition c c ⟨coordinate c x hc, by simpa [coordinate, overlap]⟩ = coordinate c x hc ∧
    transition d e ⟨transition c d ⟨coordinate c x hc,
      by simpa [coordinate, overlap] using hd⟩,
      by simpa [transition, coordinate, overlap] using he⟩ =
    transition c e ⟨coordinate c x hc, by simpa [coordinate, overlap] using he⟩ := by
  simp [transition, coordinate]

example :
    transition c c ⟨coordinate c a (by trivial), by trivial⟩ =
      coordinate c a (by trivial) ∧
    transition d c ⟨transition c d
      ⟨coordinate c a (by trivial), by trivial⟩, by trivial⟩ =
      transition c c ⟨coordinate c a (by trivial), by trivial⟩ ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) :=
  transition_cocycle_example

/-- Transition subsets.
Source: Hartshorne, Algebraic Geometry, II.5; Munkres, Topology, §16. -/
theorem transition_subsets_aux {X : Type*} [TopologicalSpace X] {r : ℕ} {D : Fin r → Set X}
    (c d : SubsetChart X D) (z : overlap c.toChart d.toChart) (j : Fin r) :
    (∀ k, MvPolynomial.eval z.val.val (c.marked j k) = (0 : ℂ)) ↔
      ∀ k, MvPolynomial.eval (transition c.toChart d.toChart z).val (d.marked j k) = (0 : ℂ) := by
  have hc := c.membership (c.coordinates.symm z.val) j
  have hd := d.membership
    ⟨(c.coordinates.symm z.val).val, z.property⟩ j
  simpa only [Homeomorph.apply_symm_apply, transition] using hc.symm.trans hd

example : MvPolynomial.eval (transition markedNode.toChart markedNode.toChart
      ⟨a, by trivial⟩).val (markedNode.marked (1 : Fin 2) (0 : Fin 1)) = (0 : ℂ) ∧
    ¬ MvPolynomial.eval a.val (markedNode.marked (0 : Fin 2) (0 : Fin 1)) = (0 : ℂ) := transition_subsets_falsification

/-- Finite intersections retain their incidence in the chart.
Source: Hartshorne, Algebraic Geometry, II.5; elementary set intersections. -/
theorem intersection_subsets_aux {X : Type*} [TopologicalSpace X] {r : ℕ} {D : Fin r → Set X}
    (c : SubsetChart X D) (x : c.domain) (J : Finset (Fin r)) :
    (∀ j ∈ J, x.val ∈ D j) ↔
      ∀ j ∈ J, ∀ k, MvPolynomial.eval (c.coordinates x).val (c.marked j k) = (0 : ℂ) := by
  exact forall_congr' fun j => forall_congr' fun _ => c.membership x j

example :
    (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart o (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) ∧
    ¬ (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart a (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) :=
  intersection_subsets_falsification

end HodgeLean.Foundations.ComplexTopology.Marked
