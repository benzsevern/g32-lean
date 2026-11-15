import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapComparison

/-! Singular representatives adapted to the fixed-cycle cap morphism.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every class in the total degree has a representative for the fixed-cycle morphism.
Source: Hatcher, Algebraic Topology, section 2.1, homology as cycles modulo boundaries.
HC no distance; AV milestone no distance.
-/
theorem exists_fixedTotalCycle (X : TopCat.{0}) (p q : ℕ)
    (c : Homology ℚ X ((p + 1) + (q + 1))) :
    ∃ (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
      (hz : boundary ℚ (p + q + 1) z = 0),
      ((SingularChainComplex ℚ X).sc ((p + 1) + (q + 1))).moduleCatHomologyClass
        (fixedTotalCycle X p q z hz) = c := by
  let K := SingularChainComplex ℚ X
  obtain ⟨w, hw⟩ := (K.sc ((p + 1) + (q + 1))).moduleCatHomologyClass_surjective c
  have hwcycle : boundary ℚ (p + 1 + q) w.1 = 0 := by
    have h := w.property
    change (K.d (p + 1 + (q + 1))
      ((ComplexShape.down ℕ).next (p + 1 + (q + 1)))).hom w.1 = 0 at h
    erw [ChainComplex.next_nat_succ] at h
    exact h
  let hdeg : p + q + 2 = (p + 1) + (q + 1) := by omega
  let z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2) :=
    (K.XIsoOfEq hdeg).inv.hom w.1
  have ht (m : ℕ) (h : p + q + 1 = m) (v : K.X (m + 1))
      (hv : (K.d (m + 1) m).hom v = 0) :
      (K.d (p + q + 2) (p + q + 1)).hom
        ((K.XIsoOfEq (congrArg (fun j => j + 1) h)).inv.hom v) = 0 := by
    cases h
    exact hv
  have hz : boundary ℚ (p + q + 1) z = 0 :=
    ht (p + 1 + q) (by omega) w.1 hwcycle
  have he : fixedTotalCycle X p q z hz = w := by
    apply Subtype.ext
    change (K.XIsoOfEq hdeg).hom.hom ((K.XIsoOfEq hdeg).inv.hom w.1) = w.1
    exact ConcreteCategory.congr_hom (K.XIsoOfEq hdeg).inv_hom_id w.1
  refine ⟨z, hz, ?_⟩
  rw [he]
  exact hw

#print axioms exists_fixedTotalCycle
end HodgeLean.Foundations.RationalHomologyManifold
