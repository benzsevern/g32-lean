import HodgeLean.Foundations.QuotientDuality.ProperCycleEmbeddedOpenPurity

/-! # Actual original supported groups from embedded neighborhood models -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular Topology TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite-model calculation gives vanishing of the literal original relative group on every open inside its neighborhood image.
Source: Bredon, Sheaf Theory, second edition, V.9; Hatcher, Algebraic Topology, section 2.2.
HC no distance; AV milestone no distance. -/
lemma properCycle_embedded_original_relative_vanishes {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (X : TopCat.{0}) [T1Space X] (f : K.space → X) (hf : IsEmbedding f)
    (A : Set X) (hmark : ∀ z : K.space, f z ∈ A ↔ z.val ∈ D.space)
    (Q : Opens X) (hQ : (Q : Set X) ⊆ Set.range f)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : X, x ∈ Q →
      Subsingleton (orientationGroup X j x))
    (d n : ℕ) (hbound : n + (2 * d + 1) ≤ N)
    (hpieces : ∀ x : K.space, f x ∈ Q → x.val ∈ D.space →
      ∃ (S : Set X) (L : Geometry.SimplicialComplex ℝ E), L.faces ⊆ K.faces ∧
        (∀ z : K.space, f z ∈ S ↔ z.val ∈ L.space) ∧
          ∃ (m : ℕ) (φ : OpenPartialHomeomorph S (Fin m → ℂ)) (hxS : f x ∈ S),
            m ≤ d ∧ (⟨f x, hxS⟩ : S) ∈ φ.source) :
    IsZero (RelativeCohomology ℚ (neighborhoodSupportComplementPair (Q : Set X) A) n) := by
  let U : Opens K.space := ⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩
  have hnb : ∀ x : K.space, x ∈ U → Set.range f ∈ 𝓝 (f x) := by
    intro x hx
    exact Filter.mem_of_superset (Q.isOpen.mem_nhds hx) hQ
  have hlocal : ∀ j : ℕ, j ≠ N → ∀ x : K.space, x ∈ U →
      Subsingleton (orientationGroup X j (f x)) := fun j hj x hx => hvan j hj (f x) hx
  have hz := properCycle_embedded_marked_open_relative_vanishes
    K D hK hDK V hV X f hf U hnb N hlocal d n hbound hpieces
  let e : U ≃ₜ Q := hf.homeomorphOfSubsetRange hQ
  let p : neighborhoodSupportComplementPair (U : Set K.space) {z : K.space | z.val ∈ D.space} ≅
      neighborhoodSupportComplementPair (Q : Set X) A :=
    TopPair.isoOfSubset e (fun z => not_congr (hmark z.val))
  let H := (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
    (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso p))
  exact hz.of_iso H

end HodgeLean.Foundations.QuotientDuality
