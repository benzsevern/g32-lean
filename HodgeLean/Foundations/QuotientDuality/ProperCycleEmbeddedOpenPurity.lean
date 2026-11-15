import HodgeLean.Foundations.QuotientDuality.ProperCycleEmbeddedFaceDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenSubcomplexPurity
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSubcomplex

/-! # Actual support purity inside embedded neighborhood models -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular Topology TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Local concentration and actual complex charts on retained marks determine support purity in an embedded finite neighborhood model.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9;
Hatcher, Algebraic Topology, section 2.2.
HC no distance; AV milestone no distance. -/
lemma properCycle_embedded_marked_open_relative_vanishes {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (X : TopCat.{0}) [T1Space X] (f : K.space → X) (hf : IsEmbedding f)
    (U : Opens K.space) (hnb : ∀ x : K.space, x ∈ U → Set.range f ∈ 𝓝 (f x))
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : K.space, x ∈ U →
      Subsingleton (orientationGroup X j (f x)))
    (d n : ℕ) (hbound : n + (2 * d + 1) ≤ N)
    (hpieces : ∀ x : K.space, x ∈ U → x.val ∈ D.space →
      ∃ (S : Set X) (L : Geometry.SimplicialComplex ℝ E), L.faces ⊆ K.faces ∧
        (∀ z : K.space, f z ∈ S ↔ z.val ∈ L.space) ∧
          ∃ (m : ℕ) (φ : OpenPartialHomeomorph S (Fin m → ℂ)) (hxS : f x ∈ S),
            m ≤ d ∧ (⟨f x, hxS⟩ : S) ∈ φ.source) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set K.space) {z : K.space | z.val ∈ D.space}) n) := by
  have hlocal : ∀ j : ℕ, j ≠ N → ∀ x : K.space, x ∈ U →
      Subsingleton (orientationGroup (TopCat.of K.space) j x) := by
    intro j hj x hx
    let H := properCycle_neighborhood_embedding_local_homology_iso
      (TopCat.of K.space) X f hf x (hnb x hx) j
    exact @Function.Injective.subsingleton _ _ H.toLinearEquiv H.toLinearEquiv.injective (hvan j hj x hx)
  apply properCycle_finite_subcomplex_open_relative_vanishes K D hK hDK V hV U N hlocal
    (2 * d + 1) n hbound
  intro s hs x hx hxs
  have hxD : x.val ∈ D.space := D.convexHull_subset_space hs (intrinsicInterior_subset hxs)
  obtain ⟨S, L, hLK, hmark, m, φ, hxS, hm, hφ⟩ := hpieces x hx hxD
  have hxL : x.val ∈ L.space := (hmark x).mp hxS
  have hsL : s ∈ L.faces :=
    (s2v_hardt6rb_open_face_mem_subcomplex_iff K L hLK s (hDK hs) hxs).mp hxL
  have hcard := properCycle_embedded_mark_face_card_le_of_complex_chart
    K L hK hLK V hV X f hf S hmark s hsL x hxs (hnb x hx) m φ hφ
  omega

end HodgeLean.Foundations.QuotientDuality
