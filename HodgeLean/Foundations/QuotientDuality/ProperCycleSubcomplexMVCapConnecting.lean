import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapConnectingAllDegrees

/-! # The original cap and relative Mayer--Vietoris connecting maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original descended even quotient cap on homology uses the actual tail comparison, including its degree-zero endpoint.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap on homology.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_cap_homology_map
    {K : SSet.{0}} (A T : K.Subcomplex) (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    (properCycle_subcomplex_quotient (A ⊔ T)).homology (p + q) ⟶
      (properCycle_subcomplex_quotient T).homology q :=
  properCycle_cap_tail_homology_map (properCycle_subcomplex_quotient (A ⊔ T)) p q ≫
    HomologicalComplex.homologyMap (properCycle_even_subcomplex_cap_chain_map A T p hp φ hA hφ) q

/-- The actual original quotient cap commutes with the constructed relative Mayer--Vietoris connecting maps in every degree, without an exactness or compatibility premise.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative cap and Mayer--Vietoris boundary.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_mv_cap_connecting
    (X : TopCat.{0}) (A P Q : (TopCat.toSSet.obj X).Subcomplex)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q + 1) hp φ hA hφ ≫
        (properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ (q + 1) q (by simp) =
      (properCycle_fixed_subcomplex_sequence_shortExact X A P Q).δ
          (p + (q + 1)) (p + q) (by change (p + q) + 1 = p + (q + 1); omega) ≫
        properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ := by
  have h := properCycle_cap_tail_connecting _ _
    (properCycle_fixed_subcomplex_sequence_shortExact X A P Q)
    (properCycle_subcomplex_quotient_sequence_shortExact X P Q) p q
    (properCycle_even_subcomplex_mv_cap_morphism A P Q p hp φ hA hφ)
  change (properCycle_cap_tail_homology_iso (properCycle_subcomplex_quotient (A ⊔ (P ⊔ Q))) p q).hom ≫
      HomologicalComplex.homologyMap (properCycle_even_subcomplex_cap_chain_map A (P ⊔ Q) p hp φ hA hφ) (q + 1) ≫
        (properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ (q + 1) q (by simp) =
    (properCycle_fixed_subcomplex_sequence_shortExact X A P Q).δ
        (p + (q + 1)) (p + q) (by change (p + q) + 1 = p + (q + 1); omega) ≫
      properCycle_cap_tail_homology_map (properCycle_subcomplex_quotient (A ⊔ (P ⊓ Q))) p q ≫
        HomologicalComplex.homologyMap (properCycle_even_subcomplex_cap_chain_map A (P ⊓ Q) p hp φ hA hφ) q at h
  have hu : properCycle_cap_tail_homology_map (properCycle_subcomplex_quotient (A ⊔ (P ⊔ Q))) p (q + 1) =
      (properCycle_cap_tail_homology_iso (properCycle_subcomplex_quotient (A ⊔ (P ⊔ Q))) p q).hom := by
    rfl
  dsimp only [properCycle_subcomplex_cap_homology_map]
  rw [hu, Category.assoc]
  exact h

end HodgeLean.Foundations.QuotientDuality
