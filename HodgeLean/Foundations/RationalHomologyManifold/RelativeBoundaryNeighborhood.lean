import HodgeLean.Foundations.RationalHomologyManifold.FiniteChainSupportNeighborhood

/-! Actual ambient primitives near supported sets for vanishing relative cycle classes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A cycle has zero actual module homology class precisely when it is a boundary.
Source: Hatcher, Algebraic Topology, section 2.1; homology as cycles modulo boundaries.
HC no distance; AV milestone no distance.
-/
theorem moduleCycleClass_zero_iff_boundary {R : Type} [CommRing R]
    (S : ShortComplex (ModuleCat R)) (z : LinearMap.ker S.g.hom) :
    S.moduleCatHomologyClass z = 0 ↔ ∃ b, S.f.hom b = z.val := by
  change S.moduleCatHomologyIso.inv.hom ((LinearMap.range S.moduleCatToCycles).mkQ z) = 0 ↔ _
  rw [map_eq_zero_iff _ ((ModuleCat.mono_iff_injective S.moduleCatHomologyIso.inv).mp inferInstance),
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Subtype.ext hb⟩

#print axioms moduleCycleClass_zero_iff_boundary
/-- A vanishing relative cycle class has an actual ambient primitive on an open neighborhood of its support set.
Source: Hatcher, Algebraic Topology, section 2.1, and Bredon, Sheaf Theory, second edition, VI.12; relative boundaries and finite chain supports.
HC no distance; AV milestone no distance.
-/
theorem relativeCycleClass_zero_ambient_boundary_near_set (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (K : Set X) (z : (SingularChainComplex ℚ X).X n)
    (hz : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Kᶜ)).sc n).g.hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f n).hom z) = 0)
    (hclass : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Kᶜ)).sc n).moduleCatHomologyClass
        ⟨((relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f n).hom z, hz⟩ = 0) :
    ∃ (b : (SingularChainComplex ℚ X).X (n + 1)) (V : TopologicalSpace.Opens X), K ⊆ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n z =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n
          ((SingularChainComplex ℚ X).d (n + 1) n b) := by
  let P := TopPair.ofSubset (X := X) Kᶜ
  let C := (relativeChainFunctor ℚ).obj P
  let π := relativeChainProjection ℚ P
  obtain ⟨v, hv⟩ := (moduleCycleClass_zero_iff_boundary (C.sc n) ⟨(π.f n).hom z, hz⟩).mp hclass
  let hp := ChainComplex.prev ℕ n
  let r := (C.XIsoOfEq hp).hom.hom v
  have hr : C.d (n + 1) n r = (π.f n).hom z := by
    have hd := congrArg (fun f => f.hom v) (C.XIsoOfEq_hom_comp_d hp n)
    exact hd.trans hv
  obtain ⟨b, hb⟩ := relativeChainProjection_surjective P (n + 1) r
  have hπ := ConcreteCategory.congr_hom (π.comm (n + 1) n) b
  change C.d (n + 1) n (π.f (n + 1) b) =
    π.f n ((SingularChainComplex ℚ X).d (n + 1) n b) at hπ
  rw [hb, hr] at hπ
  obtain ⟨V, hKV, hV⟩ := supportedChainProjection_eq_near_set X n K z
    ((SingularChainComplex ℚ X).d (n + 1) n b) hπ
  exact ⟨b, V, hKV, hV⟩

#print axioms relativeCycleClass_zero_ambient_boundary_near_set
end HodgeLean.Foundations.RationalHomologyManifold
