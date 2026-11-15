import HodgeLean.Adapters.NormalConeB4aClassHolomorphicTransition

/-! # Normal-coclass comparison for the frozen holomorphic charts

Route: local algebraic opens make all chart transitions analytic. Inverse
regularity and dimension equality supply the hypotheses of the normal
orientation comparison on the original ambient analytic space.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Topology TopologicalSpace AlgebraicTopology.Singular

/-- Normal coclasses of any two frozen holomorphic charts flattening the same
support agree on a sufficiently small common neighborhood. -/
theorem a3b4a_classHolomorphicChart_normalCoclass_overlap
    (X : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] {r s c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (e' : OpenPartialHomeomorph (ComplexPoint X) ((Fin s → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (he' : a3b4_IsHolChart X.hom e')
    (S : Set (ComplexPoint X)) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hS' : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0)
    (x : ComplexPoint X) (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hxS : x ∈ S) :
    ∃ (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ e.source)
      (hW' : (W : Set (ComplexPoint X)) ⊆ e'.source),
      x ∈ W ∧ chartNormalProjectionCoclass (Fin r → ℂ) c e S hS W hW =
        chartNormalProjectionCoclass (Fin s → ℂ) c e' S hS' W hW' := by
  let t := e.symm.trans e'
  have ht : AnalyticOnNhd ℂ t t.source :=
    a3b4a_classHolomorphicChart_transition_analytic X e e' he he'
  have hxT : e x ∈ t.source := ⟨e.map_source hx, by
    change e.symm (e x) ∈ e'.source
    rwa [e.left_inv hx]⟩
  have hdim := a3b4a_classAnalyticChart_finrank t ht ⟨e x, hxT⟩
  simp only [Module.finrank_prod, Module.finrank_fin_fun] at hdim
  have hrs : r = s := Nat.add_right_cancel hdim
  subst s
  exact exists_open_chartNormalProjectionCoclass_eq c e e' S hS hS' x hx
    ((hS x hx).mp hxS) hx' (ht _ hxT)
    (a3b4a_classAnalyticInverse_finiteDimensional t ht _ (t.map_source hxT))

end HodgeLean.Adapters
