import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSoftness
import HodgeLean.Foundations.RationalHomologyManifold.CompactSubdivisionEquality

/-! Actual global representatives in the supported subdivision-limit sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every global section of the actual subdivision-limit sheaf comes from an ambient singular chain at a finite stage.
Source: Bredon, Sheaf Theory, second edition, VI.12; global finite-stage representatives on compact spaces.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_global_ambient_rep (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n : ℕ)
    (s : ((subdivisionLimitSheafComplex X).X n).obj.obj (Opposite.op ⊤)) :
    ∃ (M : ℕ) (w : (SingularChainComplex ℚ X).X n),
      (subdivisionAmbientSectionMap X n ⊤ M).hom w = s := by
  obtain ⟨N, hNU, hKN, M, w, hw⟩ := subdivisionLimitSheaf_extend_by_ambient X n
    Set.univ isClosed_univ ⊤ (fun _ _ => trivial) s
  have hN : N = ⊤ := le_antisymm le_top (fun x _ => hKN (Set.mem_univ x))
  subst N
  refine ⟨M, w, ?_⟩
  change ((subdivisionLimitSheafComplex X).X n).obj.map (𝟙 (Opposite.op (⊤ : Opens X)))
      ((subdivisionAmbientSectionMap X n ⊤ M).hom w) =
    ((subdivisionLimitSheafComplex X).X n).obj.map (𝟙 (Opposite.op (⊤ : Opens X))) s at hw
  simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hw

#print axioms subdivisionLimitSheaf_global_ambient_rep
/-- Equal global ambient subdivision sections are represented by equal actual chains after a finite subdivision.
Source: Bredon, Sheaf Theory, second edition, VI.12; global equality in the supported subdivision limit.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSection_global_eq_eventually (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n m : ℕ) (z w : (SingularChainComplex ℚ X).X n)
    (h : (subdivisionAmbientSectionMap X n ⊤ m).hom z =
      (subdivisionAmbientSectionMap X n ⊤ m).hom w) :
    ∃ R : ℕ, (rationalSubdivisionIterate X R).f n z =
      (rationalSubdivisionIterate X R).f n w := by
  obtain ⟨N, hNU, R, hKN, he⟩ := subdivisionAmbientSection_eq_near_compact X n m ⊤ z w h
    Set.univ isCompact_univ (fun _ _ => trivial)
  have hN : N = ⊤ := le_antisymm le_top (fun x _ => hKN (Set.mem_univ x))
  subst N
  exact ⟨R, topSupportedChainProjection_injective X n he⟩

#print axioms subdivisionAmbientSection_global_eq_eventually
end HodgeLean.Foundations.RationalHomologyManifold
