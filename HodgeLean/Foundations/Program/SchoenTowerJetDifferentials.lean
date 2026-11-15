import HodgeLean.Foundations.Program.SchoenTowerPointJets
import Mathlib.RingTheory.Nakayama

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- A derivation sends the square of an ideal into its product with the target module.
Source: Hartshorne, Algebraic Geometry, II.8, Leibniz rule. -/
theorem s2t_derivation_square_mem {K A M : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [AddCommGroup M] [Module K M] [Module A M]
    (I : Ideal A) (D : Derivation K A M) (z : A) (hz : z ∈ I ^ 2) :
    D z ∈ I • (⊤ : Submodule A M) := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on (C := fun x => D x ∈ I • (⊤ : Submodule A M))
    hz ?_ ?_
  · intro a ha b hb
    rw [D.leibniz]
    exact Submodule.add_mem _
      (Submodule.smul_mem_smul ha (Submodule.mem_top))
      (Submodule.smul_mem_smul hb (Submodule.mem_top))
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- A differential generator remains a generator after a scalar translation and a change in
the square of an ideal contained in the Jacobson radical.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem s2t_differential_generator_of_same_jet {K A M : Type*}
    [CommRing K] [CommRing A] [Algebra K A] [AddCommGroup M]
    [Module K M] [Module A M] (I : Ideal A) (D : Derivation K A M)
    (hI : I ≤ Ideal.jacobson ⊥) (a b : A) (c : K)
    (hjet : b - (a + algebraMap K A c) ∈ I ^ 2)
    (hspan : Submodule.span A {D a} = ⊤) : Submodule.span A {D b} = ⊤ := by
  have hfg : (⊤ : Submodule A M).FG := by
    rw [← hspan]
    exact Submodule.fg_span_singleton (D a)
  have hdiff : D b - D a ∈ I • (⊤ : Submodule A M) := by
    simpa only [map_sub, map_add, D.map_algebraMap, add_zero] using
      s2t_derivation_square_mem I D _ hjet
  have hle : Submodule.span A {D a} ≤ Submodule.span A {D b} ⊔
      I • (⊤ : Submodule A M) := by
    apply Submodule.span_le.mpr
    rintro _ (rfl : _ = D a)
    change D a ∈ Submodule.span A {D b} ⊔ I • (⊤ : Submodule A M)
    have hb : D b ∈ Submodule.span A {D b} ⊔ I • (⊤ : Submodule A M) :=
      (le_sup_left : Submodule.span A {D b} ≤ _) (Submodule.subset_span (Set.mem_singleton _))
    have hd : D b - D a ∈ Submodule.span A {D b} ⊔ I • (⊤ : Submodule A M) :=
      (le_sup_right : I • (⊤ : Submodule A M) ≤ _) hdiff
    simpa only [sub_sub_cancel] using Submodule.sub_mem _ hb hd
  apply top_unique
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg hI (hspan.symm.le.trans hle)

end HodgeLean.Foundations.Program
