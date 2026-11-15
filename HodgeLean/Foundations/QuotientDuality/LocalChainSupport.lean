import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_OpenLift

/-! Finite singular chains avoiding a point vanish on a neighborhood of that point. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- A chain in a point complement is killed by restriction to some open neighborhood.
Source: Hatcher, Algebraic Topology, proof of Lemma 3.27. -/
theorem complement_chain_vanishes_near_point (X : TopCat.{0}) [T2Space X]
    (x : X) (k : ℕ)
    (c : (((chainPairFunctor ℚ).obj (pointComplementPair x)).left.X k)) :
    ∃ U : Opens X, x ∈ U ∧
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f k).hom
        (((((chainPairFunctor ℚ).obj (pointComplementPair x)).hom).f k).hom c) = 0 := by
  classical
  let P := TopPair.ofSubset (X := X) ({x} : Set X)ᶜ
  let j := ((chainPairFunctor ℚ).obj P).hom
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp
    (C_chain_mem_iSup_range (TopCat.toSSet.obj P.snd) k c)
  let S : Set X := ⋃ σ ∈ s,
    Set.range (fun t => (P.snd.toSSetObjEquiv _ σ t).1)
  have hSc : IsCompact S := s.isCompact_biUnion (fun σ _ => isCompact_range
    (continuous_subtype_val.comp (P.snd.toSSetObjEquiv _ σ).continuous))
  have hxS : x ∉ S := by
    simp only [S, Set.mem_iUnion, Set.mem_range, not_exists]
    intro σ hσ t ht
    exact (P.snd.toSSetObjEquiv _ σ t).property (Set.mem_singleton_iff.mpr ht)
  let U : Opens X := ⟨Sᶜ, hSc.isClosed.isOpen_compl⟩
  let Q := TopPair.ofSubset (X := X) (U : Set X)ᶜ
  let jQ := ((chainPairFunctor ℚ).obj Q).hom
  have hr : (j.f k).hom c ∈ LinearMap.range (jQ.f k).hom := by
    suffices h : (⨆ σ ∈ s, LinearMap.range
        ((TopCat.toSSet.obj P.snd).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom) ≤
        (LinearMap.range (jQ.f k).hom).comap (j.f k).hom from h hs
    refine iSup₂_le fun σ hσ => ?_
    rintro _ ⟨r, rfl⟩
    change (j.f k).hom
      (((TopCat.toSSet.obj P.snd).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom r) ∈
        LinearMap.range (jQ.f k).hom
    have key := congrArg (fun f => f.hom r)
      (SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map P.map)
        (R := ModuleCat.of ℚ ℚ) (x := σ))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key
    have key' : (j.f k).hom
        (((TopCat.toSSet.obj P.snd).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom r) =
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map P.map).app _ σ)).hom r := key
    rw [key']
    apply C_simplex_mem_range (U : Set X)ᶜ _ _ r
    intro t ht
    apply ht
    simp only [S, Set.mem_iUnion, Set.mem_range]
    exact ⟨σ, hσ, t, rfl⟩
  obtain ⟨b, hb⟩ := hr
  refine ⟨U, hxS, ?_⟩
  rw [← hb]
  exact congrArg (fun f => (f.f k).hom b) (subspaceChainMap_relativeChainProjection ℚ Q)

/-- A cycle representing zero has an actual boundary witness in the next degree.
Source: Hatcher, Algebraic Topology, section 2.1, definition of homology. -/
theorem cycle_boundary_of_homology_zero (C : ChainCategory ℚ) (n : ℕ)
    (z : C.cycles n) (hz : (C.homologyπ n).hom z = 0) :
    ∃ b : C.X (n + 1), (C.d (n + 1) n).hom b = (C.iCycles n).hom z := by
  have he := (ShortComplex.mk (C.toCycles (n + 1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n + 1) n)).exact_of_g_is_cokernel
      (C.homologyIsCokernel (n + 1) n (by simp))
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp he z hz
  refine ⟨b, ?_⟩
  change (C.toCycles (n + 1) n).hom b = z at hb
  have h := congrArg (C.iCycles n).hom hb
  change ((C.toCycles (n + 1) n ≫ C.iCycles n).hom b) = _ at h
  rw [C.toCycles_i] at h
  exact h

#print axioms cycle_boundary_of_homology_zero

#print axioms complement_chain_vanishes_near_point
end HodgeLean.Foundations.QuotientDuality
