import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveClosedNeighborhood

/-! # Original open collars as literal ambient subspaces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual categorical open collar gives a strong homotopy retraction on its literal ambient image, retaining the original support inclusion.
Source: Munkres, Topology, section 18, embeddings and subspace homeomorphisms; Hatcher, Algebraic Topology, section 0, deformation retractions.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_collar_as_subspace
    (X : TopCat.{0}) (S : Set X) (U : TopCat.{0})
    (j : TopCat.of S ⟶ U) (k : U ⟶ X)
    (hj : j ≫ k = (TopPair.ofSubset (X := X) S).map)
    (hk : Topology.IsOpenEmbedding k) (r : U ⟶ TopCat.of S)
    (hjr : j ≫ r = 𝟙 (TopCat.of S)) (H : TopCat.Homotopy (𝟙 U) (r ≫ j)) :
    ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧
      ∃ (jV : TopCat.of S ⟶ TopCat.of V) (rV : TopCat.of V ⟶ TopCat.of S),
        jV ≫ (TopPair.ofSubset (X := X) V).map = (TopPair.ofSubset (X := X) S).map ∧
        jV ≫ rV = 𝟙 (TopCat.of S) ∧
        Nonempty (TopCat.Homotopy (𝟙 (TopCat.of V)) (rV ≫ jV)) := by
  let V := Set.range k
  let e : U ≃ₜ V := hk.isEmbedding.toHomeomorph
  let eh : U ⟶ TopCat.of V := TopCat.ofHom ⟨e, e.continuous⟩
  let ei : TopCat.of V ⟶ U := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hei : eh ≫ ei = 𝟙 U := by ext u; exact e.symm_apply_apply u
  have heik : eh ≫ (TopPair.ofSubset (X := X) V).map = k := by ext u; rfl
  let jV := j ≫ eh
  let rV := ei ≫ r
  have hfactor : jV ≫ (TopPair.ofSubset (X := X) V).map =
      (TopPair.ofSubset (X := X) S).map := by
    rw [Category.assoc, heik]
    exact hj
  have hfix : jV ≫ rV = 𝟙 (TopCat.of S) := by
    dsimp only [jV, rV]
    rw [Category.assoc, ← Category.assoc eh, hei, Category.id_comp, hjr]
  let HV : TopCat.Homotopy (𝟙 (TopCat.of V)) (rV ≫ jV) :=
    { toFun := fun tv => e (H (tv.1, e.symm tv.2))
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro v
        change e (H (0, e.symm v)) = v
        exact (congrArg e (H.map_zero_left (e.symm v))).trans (e.apply_symm_apply v)
      map_one_left := by
        intro v
        change e (H (1, e.symm v)) = e (j (r (e.symm v)))
        exact congrArg e (H.map_one_left (e.symm v)) }
  refine ⟨V, hk.isOpen_range, ?_, jV, rV, hfactor, hfix, ⟨HV⟩⟩
  intro s hs
  exact ⟨j ⟨s, hs⟩, ConcreteCategory.congr_hom hj ⟨s, hs⟩⟩

end HodgeLean.Foundations.QuotientDuality
