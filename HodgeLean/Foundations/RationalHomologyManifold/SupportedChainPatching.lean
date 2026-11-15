import HodgeLean.Foundations.RationalHomologyManifold.ChainCoefficients
import HodgeLean.Foundations.RationalHomologyManifold.FiniteChainPatching

/-! Finite patching in the actual rational singular chain group.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Compatible prescribed coefficients from finitely many actual chains extend to one actual chain.
Source: Bredon, Sheaf Theory, second edition, VI.12; finite supported-chain patching.
HC no distance; AV milestone no distance.
-/
theorem singularChain_finite_coefficient_patching {κ : Type} [Fintype κ]
    (X : TopCat.{0}) (n : ℕ) (z : κ → (SingularChainComplex ℚ X).X n)
    (hits : κ → (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) → Prop)
    (hcompat : ∀ i j s, hits i s → hits j s →
      (singularChainCoefficient X n s).hom (z i) =
        (singularChainCoefficient X n s).hom (z j)) :
    ∃ w : (SingularChainComplex ℚ X).X n, ∀ i s, hits i s →
      (singularChainCoefficient X n s).hom w =
        (singularChainCoefficient X n s).hom (z i) := by
  let e := (chainGroupFinsuppIso ℚ X n).toLinearEquiv
  have hc : ∀ i j s, hits i s → hits j s → e (z i) s = e (z j) s := hcompat
  obtain ⟨c, hc⟩ := finite_coefficient_patching (fun i => e (z i)) hits hc
  refine ⟨e.symm c, fun i s hs => ?_⟩
  change e (e.symm c) s = e (z i) s
  rw [LinearEquiv.apply_symm_apply]
  exact hc i s hs

#print axioms singularChain_finite_coefficient_patching
/-- A chain supported on simplices in the image of a continuous map lifts to an actual source chain.
Source: Hatcher, Algebraic Topology, section 2.1, free singular chain groups and induced maps.
HC no distance; AV milestone no distance.
-/
theorem singularChain_lift_of_coefficient_support {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (z : (SingularChainComplex ℚ Y).X n)
    (h : ∀ s, (singularChainCoefficient Y n s).hom z ≠ 0 →
      ∃ t, (TopCat.toSSet.map f).app _ t = s) :
    ∃ y : (SingularChainComplex ℚ X).X n,
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n y = z := by
  classical
  let e := (chainGroupFinsuppIso ℚ Y n).toLinearEquiv
  let c := e z
  have hc (s : c.support) : ∃ t : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)),
      (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) t =
        (s : (TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) :=
    h s (Finsupp.mem_support_iff.mp s.property)
  choose t ht using hc
  refine ⟨∑ s : c.support,
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) (t s)).hom (c s)), ?_⟩
  apply e.injective
  simp only [map_sum]
  change (∑ s : c.support, e ((SSet.chainComplexMap (TopCat.toSSet.map f)
    (ModuleCat.of ℚ ℚ)).f n
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) (t s)).hom (c s)))) = c
  calc
    _ = ∑ s : c.support, Finsupp.single
      (s : (TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) (c s) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hnat := ConcreteCategory.congr_hom
        (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
          (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) (t s)) (c s)
      change (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n
        (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) (t s)).hom (c s)) =
        (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map f).app _ (t s))).hom (c s)) at hnat
      rw [hnat, ht s]
      exact chainGroupFinsuppIso_iota ℚ Y n s (c s)
    _ = c := by
      calc
        _ = ∑ s ∈ c.support, Finsupp.single s (c s) :=
          Finset.sum_coe_sort c.support (fun s => Finsupp.single s (c s))
        _ = c := Finsupp.sum_single c

#print axioms singularChain_lift_of_coefficient_support
end HodgeLean.Foundations.RationalHomologyManifold
