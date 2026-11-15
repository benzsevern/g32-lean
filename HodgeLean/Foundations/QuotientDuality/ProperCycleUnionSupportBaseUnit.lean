import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeSupportCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyUnionUnitTransport
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeUnitAugmentation

/-! # Actual normal cap base evaluation in intersection-support coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Literal identity coordinates identify intersection with the whole support with the original normal support pair.
Source: Munkres, Topology, section 16, subspaces; AlgebraicTopology.Singular.TopPair.isoOfSubset.
HC no distance; AV milestone no distance. -/
def properCycle_support_univ_pair_iso (X : TopCat.{0}) (S : Set X) :
    TopPair.ofSubset (X := X) (S ∩ Set.univ)ᶜ ≅ TopPair.ofSubset (X := X) Sᶜ :=
  TopPair.isoOfSubset (Homeomorph.refl _) (by
    intro x
    change x ∉ S ↔ ¬ (x ∈ S ∧ True)
    tauto)

/-- The specified inverse normal-support and complement-union identifications compose to the literal original union inclusion.
Source: properCycle_support_univ_pair_iso; properCycle_support_complement_union_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_support_univ_union_inclusion (X : TopCat.{0}) (S : Set X) :
    (properCycle_support_univ_pair_iso X S).inv ≫
      (properCycle_support_complement_union_iso X S Set.univ).inv =
      TopPair.ofSubsetHom (𝟙 X)
        (show Sᶜ ⊆ Sᶜ ∪ (Set.univ : Set X)ᶜ from Set.subset_union_left) := by
  ext z : 2 <;> rfl

/-- The original support-relative cap is the customary union-relative cap after the specified inverse complement-union pair map.
Source: properCycle_support_cap_source_iso; AlgebraicTopology.Singular.unionRelativeTriadCapCohomologyLinear.
HC no distance; AV milestone no distance. -/
theorem properCycle_union_relative_support_cap_apply
    (X : TopCat.{0}) (S T : Set X) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Sᶜ) p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) (S ∩ T)ᶜ) (p+q)) :
    (properCycle_union_relative_support_cap X S T hS hT p q a).hom z =
      unionRelativeTriadCapCohomologyLinear ℚ X Sᶜ Tᶜ p q
        (triadToUnionRelativeChainMap_quasiIso_of_isOpen X Sᶜ Tᶜ hS.isOpen_compl hT.isOpen_compl)
        a (relativeHomologyMap ℚ (p+q)
          (properCycle_support_complement_union_iso X S T).inv z) := by
  rfl

/-- The original normal cap in intersection-support coordinates has cup-unit evaluation one on the specified normalized source class.
Source: properCycle_empty_union_normalized_cap_unit; properCycle_support_univ_union_inclusion; properCycle_union_relative_support_cap_apply.
HC no distance; AV milestone no distance. -/
theorem properCycle_union_support_normalized_base_unit
    (X : TopCat.{0}) (S : Set X) (hS : IsClosed S) (p : ℕ) (hp : Even p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) Sᶜ) p) (hz : z ≠ 0) :
    letI : IsIso (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ)) := HodgeLean.RealDefs.isIso_relativeChainProjection _ ⟨fun v => v.2 (Set.mem_univ v.1)⟩
    let E := HomologicalComplex.homologyMapIso
      (asIso (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ))) 0
    cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X)
      (E.inv.hom ((properCycle_union_relative_support_cap X S Set.univ hS isClosed_univ p 0
        (normalizedRelativeCoclass z hz)).hom
        (relativeHomologyMap ℚ p (properCycle_support_univ_pair_iso X S).inv z))) = 1 := by
  letI : IsIso (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ)) := HodgeLean.RealDefs.isIso_relativeChainProjection _ ⟨fun v => v.2 (Set.mem_univ v.1)⟩
  let G := HomologicalComplex.homologyMap
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ)) 0
  let E := HomologicalComplex.homologyMapIso
    (asIso (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (Set.univ : Set X)ᶜ))) 0
  have hE : E.inv = inv G := by
    apply (cancel_epi G).mp
    change E.hom ≫ E.inv = G ≫ inv G
    rw [E.hom_inv_id, IsIso.hom_inv_id]
  have hc := congrArg (fun f => relativeHomologyMap ℚ p f z)
    (properCycle_support_univ_union_inclusion X S)
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hc
  change cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X)
    (E.inv.hom ((properCycle_union_relative_support_cap X S Set.univ hS isClosed_univ p 0
      (normalizedRelativeCoclass z hz)).hom
      (relativeHomologyMap ℚ p (properCycle_support_univ_pair_iso X S).inv z))) = 1
  rw [hE, properCycle_union_relative_support_cap_apply]
  erw [hc]
  dsimp only [G]
  exact properCycle_empty_union_normalized_cap_unit_of_eq X Sᶜ (Set.univ : Set X)ᶜ
    hS.isOpen_compl Set.compl_univ p hp z hz

end HodgeLean.Foundations.QuotientDuality
