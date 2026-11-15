import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Lattice quotients are tori

Torus track S8, the topology part of T9. This retires no hypothesis.
HC no distance; AV milestone no distance.

Source: Mathlib's `ZLattice` and `AddCircle` APIs.
-/

noncomputable section

namespace HodgeLean.Foundations.LatticeTorus

open Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

private instance discrete_toIntSubmodule (Λ : AddSubgroup V) [DiscreteTopology Λ] :
    DiscreteTopology Λ.toIntSubmodule := inferInstanceAs (DiscreteTopology Λ)

private def coordinateMap : V →+ UnitAddTorus ι where
  toFun x i := ((b.ofZLatticeBasis ℝ L).equivFun x i : UnitAddCircle)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

private theorem coordinateMap_continuous : Continuous (coordinateMap L b) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' 1).comp
    ((continuous_apply i).comp (continuous_equivFun_basis (b.ofZLatticeBasis ℝ L)))

private theorem coordinateMap_ker : L.toAddSubgroup = (coordinateMap L b).ker := by
  ext x
  change x ∈ L ↔ (fun i => ((b.ofZLatticeBasis ℝ L).equivFun x i : UnitAddCircle)) = 0
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ,
    (b.ofZLatticeBasis ℝ L).mem_span_iff_repr_mem ℤ]
  simp only [funext_iff, Pi.zero_apply, AddCircle.coe_eq_zero_iff, zsmul_eq_mul,
    mul_one, Basis.equivFun_apply, Set.mem_range]
  rfl

private theorem coordinateMap_surjective : Function.Surjective (coordinateMap L b) := by
  intro y
  choose x hx using fun i => QuotientAddGroup.mk_surjective (y i)
  refine ⟨(b.ofZLatticeBasis ℝ L).equivFun.symm x, ?_⟩
  ext i
  change (((b.ofZLatticeBasis ℝ L).equivFun
    ((b.ofZLatticeBasis ℝ L).equivFun.symm x) i : ℝ) : UnitAddCircle) = y i
  simpa only [LinearEquiv.apply_symm_apply] using hx i

private theorem quotient_compact : CompactSpace (V ⧸ L.toAddSubgroup) := by
  have h := IsZLattice.isCompact_range_of_periodic L
    (QuotientAddGroup.mk : V → V ⧸ L.toAddSubgroup)
    (QuotientAddGroup.isOpenQuotientMap_mk.continuous) (by
      intro x y hy
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff y).mpr hy, add_zero])
  rw [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at h
  exact ⟨h⟩

/-- Coordinates in an integer basis identify the lattice quotient with a product of circles,
as a topological additive group. The basis is extended to a real basis of the ambient space.
Source: Mathlib's `Module.Basis.ofZLatticeBasis` and `QuotientAddGroup.liftEquiv`.
-/
def quotientEquivOfBasis : ContinuousAddEquiv (V ⧸ L.toAddSubgroup) (UnitAddTorus ι) := by
  let e := QuotientAddGroup.liftEquiv L.toAddSubgroup
    (coordinateMap_surjective L b) (coordinateMap_ker L b)
  have hc : Continuous e :=
    (QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff).mp
      (coordinateMap_continuous L b)
  letI := quotient_compact L
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- The quotient equivalence sends a representative to its basis coordinates modulo the integers.
Source: Mathlib's `QuotientAddGroup.liftEquiv_coe` and `Module.Basis.equivFun_apply`.
-/
theorem quotientEquivOfBasis_mk (x : V) (i : ι) :
    quotientEquivOfBasis L b (QuotientAddGroup.mk x) i =
      ((b.ofZLatticeBasis ℝ L).repr x i : UnitAddCircle) := rfl

/-- A full lattice quotient is the standard torus of the real dimension of its ambient space.
Source: Mathlib's `ZLattice.rank` and `Module.finBasisOfFinrankEq`, using `quotientEquivOfBasis`.
-/
def quotientEquiv :
    ContinuousAddEquiv (V ⧸ L.toAddSubgroup) (UnitAddTorus (Fin (finrank ℝ V))) := by
  letI := ZLattice.module_free ℝ L
  letI := ZLattice.module_finite ℝ L
  exact quotientEquivOfBasis L (finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L))

example : (V ⧸ L.toAddSubgroup) ≃ₜ UnitAddTorus (Fin (finrank ℝ V)) :=
  (quotientEquiv L).toHomeomorph

example (Λ : AddSubgroup V) [DiscreteTopology Λ] [IsZLattice ℝ Λ.toIntSubmodule] :
    ContinuousAddEquiv (V ⧸ Λ) (UnitAddTorus (Fin (finrank ℝ V))) :=
  quotientEquiv Λ.toIntSubmodule

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Compactness of a subgroup quotient forces its real span to be the whole vector space.
Discreteness is not needed for this implication.
Source: Mathlib's `Submodule.exists_le_ker_of_lt_top`; a nonzero real linear functional
is surjective, and the real line is not compact.
-/
theorem span_eq_top_of_compact_quotient [CompactSpace (V ⧸ L.toAddSubgroup)] :
    Submodule.span ℝ (L : Set V) = ⊤ := by
  by_contra h
  obtain ⟨f, hf, hLf⟩ := (Submodule.span ℝ (L : Set V)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr h)
  have hker : L.toAddSubgroup ≤ f.toAddMonoidHom.ker := by
    intro x hx
    exact hLf (Submodule.subset_span hx)
  let g := QuotientAddGroup.lift L.toAddSubgroup f.toAddMonoidHom hker
  have hg : Continuous g :=
    QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp f.continuous_of_finiteDimensional
  have hsurj : Function.Surjective g :=
    QuotientAddGroup.lift_surjective_of_surjective L.toAddSubgroup f.toAddMonoidHom
      (LinearMap.surjective hf) hker
  have hc := isCompact_univ.image hg
  rw [Set.image_univ, Set.range_eq_univ.mpr hsurj] at hc
  exact noncompact_univ ℝ hc

omit [IsZLattice ℝ L] in
/-- A discrete subgroup of a finite-dimensional real vector space with compact quotient
is a full integer lattice.
Source: Mathlib's `IsZLattice` definition and `span_eq_top_of_compact_quotient`.
-/
theorem isZLattice_of_compact_quotient [CompactSpace (V ⧸ L.toAddSubgroup)] :
    IsZLattice ℝ L :=
  ⟨span_eq_top_of_compact_quotient L⟩

omit [IsZLattice ℝ L] in
example [CompactSpace (V ⧸ L.toAddSubgroup)] : IsZLattice ℝ L :=
  isZLattice_of_compact_quotient L

/-! ## Concrete checks and falsification -/

/-- The usual integer lattice in the real line.
Source: Mathlib's `AddSubgroup.zmultiples` (integer multiples of one).
-/
def integerLattice : Submodule ℤ ℝ := (AddSubgroup.zmultiples (1 : ℝ)).toIntSubmodule

example : (1 : ℝ) ∈ integerLattice := AddSubgroup.mem_zmultiples 1

/-- The integer lattice is discrete.
Source: Mathlib's `NormedSpace.discreteTopology_zmultiples`.
-/
instance : DiscreteTopology integerLattice :=
  NormedSpace.discreteTopology_zmultiples (1 : ℝ)

/-- The integer lattice spans the real line.
Source: Mathlib's `IsZLattice`; the generator one is a real basis.
-/
instance : IsZLattice ℝ integerLattice where
  span_top := by
    apply top_unique
    intro x _
    have h : (1 : ℝ) ∈ Submodule.span ℝ (integerLattice : Set ℝ) :=
      Submodule.subset_span (AddSubgroup.mem_zmultiples 1)
    simpa using (Submodule.span ℝ (integerLattice : Set ℝ)).smul_mem x h

example : DiscreteTopology integerLattice := inferInstance

example : IsZLattice ℝ integerLattice := by
  have : CompactSpace (ℝ ⧸ integerLattice.toAddSubgroup) := quotient_compact integerLattice
  exact isZLattice_of_compact_quotient integerLattice

/-- The real line modulo the integers is the unit additive circle, with its group topology.
Source: Mathlib's definition of `UnitAddCircle` as `AddCircle 1`.
-/
def integerQuotientCircle : ContinuousAddEquiv (ℝ ⧸ integerLattice.toAddSubgroup) UnitAddCircle :=
  ContinuousAddEquiv.refl _

example (x : ℝ) : integerQuotientCircle (QuotientAddGroup.mk x) = (x : UnitAddCircle) := rfl

example : quotientEquiv integerLattice 0 = 0 := map_zero _

example : quotientEquivOfBasis integerLattice
    (finBasisOfFinrankEq ℤ integerLattice (ZLattice.rank ℝ integerLattice)) 0 = 0 := by
  exact map_zero _

/-- The non-spanning integer axis in the real plane.
Source: Mathlib's `AddSubgroup.zmultiples`, applied to `(1, 0)`.
-/
def integerAxis : Submodule ℤ (ℝ × ℝ) :=
  (AddSubgroup.zmultiples ((1, 0) : ℝ × ℝ)).toIntSubmodule

example : ((1, 0) : ℝ × ℝ) ∈ integerAxis := AddSubgroup.mem_zmultiples _

/-- Integer multiples of the first coordinate vector form a discrete subgroup.
Source: Mathlib's `NormedSpace.discreteTopology_zmultiples`.
-/
instance : DiscreteTopology integerAxis :=
  NormedSpace.discreteTopology_zmultiples ((1, 0) : ℝ × ℝ)

example : DiscreteTopology integerAxis := inferInstance

/-- The integer axis does not span the real plane.
Source: Mathlib's `Submodule.span_le` and `LinearMap.snd`.
-/
theorem integerAxis_span_ne_top : Submodule.span ℝ (integerAxis : Set (ℝ × ℝ)) ≠ ⊤ := by
  have hle : Submodule.span ℝ (integerAxis : Set (ℝ × ℝ)) ≤
      (LinearMap.snd ℝ ℝ ℝ).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    simp
  intro h
  have h01 := hle (h ▸ (Submodule.mem_top : ((0, 1) : ℝ × ℝ) ∈ ⊤))
  simp at h01

/-- Discreteness alone is insufficient: the integer axis is not a full lattice.
Source: Mathlib's `IsZLattice.span_top` and `integerAxis_span_ne_top`.
-/
theorem integerAxis_not_isZLattice : ¬ IsZLattice ℝ integerAxis := by
  intro h
  exact integerAxis_span_ne_top h.span_top

/-- The quotient of the plane by the integer axis is not compact.
Source: `span_eq_top_of_compact_quotient` and `integerAxis_span_ne_top`.
-/
theorem integerAxis_quotient_not_compact : ¬ CompactSpace ((ℝ × ℝ) ⧸ integerAxis.toAddSubgroup) := by
  intro h
  exact integerAxis_span_ne_top (span_eq_top_of_compact_quotient integerAxis)

/-- The subgroup `ℤ + ℤ√2` of the real line, expressed as the subgroup generated by `√2` and `1`.
Here `AddSubgroup.closure` is algebraic generation, not topological closure.
Source: Mathlib's `dense_addSubgroupClosure_pair_iff`.
-/
def irrationalSubgroup : AddSubgroup ℝ := AddSubgroup.closure {Real.sqrt 2, 1}

example : Real.sqrt 2 ∈ irrationalSubgroup := AddSubgroup.subset_closure (by simp)

/-- Membership in the irrational subgroup is exactly an integer combination of `√2` and one.
Source: Mathlib's `AddSubgroup.mem_closure_pair`.
-/
theorem mem_irrationalSubgroup_iff (x : ℝ) :
    x ∈ irrationalSubgroup ↔ ∃ m n : ℤ, (m : ℝ) * Real.sqrt 2 + n = x := by
  simpa [irrationalSubgroup, zsmul_eq_mul] using
    (AddSubgroup.mem_closure_pair (x := Real.sqrt 2) (y := 1) (z := x))

/-- The subgroup generated by one and the square root of two is dense in the real line.
Source: Mathlib's `dense_addSubgroupClosure_pair_iff` and `irrational_sqrt_two`.
-/
theorem irrationalSubgroup_dense : Dense (irrationalSubgroup : Set ℝ) := by
  exact dense_addSubgroupClosure_pair_iff.mpr (by simpa using irrational_sqrt_two)

/-- A dense irrational subgroup cannot be discrete.
Source: Mathlib's `AddSubgroup.isClosed_of_discreteTopology` and `not_isOpen_singleton`.
-/
theorem irrationalSubgroup_not_discrete : ¬ DiscreteTopology irrationalSubgroup := by
  intro h
  have heq : irrationalSubgroup = ⊤ := by
    apply SetLike.coe_injective
    change (irrationalSubgroup : Set ℝ) = Set.univ
    rw [← irrationalSubgroup_dense.closure_eq,
      AddSubgroup.isClosed_of_discreteTopology.closure_eq]
  have : DiscreteTopology (⊤ : AddSubgroup ℝ) := heq ▸ h
  have : DiscreteTopology ℝ := (Homeomorph.Set.univ ℝ).discreteTopology_iff.mp inferInstance
  exact not_isOpen_singleton (0 : ℝ) (isOpen_discrete _)

#print axioms quotientEquivOfBasis
#print axioms quotientEquivOfBasis_mk
#print axioms quotientEquiv
#print axioms span_eq_top_of_compact_quotient
#print axioms isZLattice_of_compact_quotient
#print axioms integerQuotientCircle
#print axioms integerAxis_span_ne_top
#print axioms integerAxis_not_isZLattice
#print axioms integerAxis_quotient_not_compact
#print axioms irrationalSubgroup_dense
#print axioms mem_irrationalSubgroup_iff
#print axioms irrationalSubgroup_not_discrete

end HodgeLean.Foundations.LatticeTorus
