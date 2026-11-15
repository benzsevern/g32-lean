import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCollar

/-! # Actual support-fixing deformation data on literal neighborhoods
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual collar maps together with the retained equality fixing every original support point throughout the deformation.
Source: Hatcher, Algebraic Topology, section 0, strong deformation retractions.
HC no distance; AV milestone no distance. -/
structure ProperCycleStrongSupportCollar (X : TopCat.{0}) (S : Set X) where
  collar : ProperCycleSupportCollar X S
  fixed : ∀ (t : unitInterval) (s : TopCat.of S),
    collar.deformation (t, collar.inclusion s) = collar.inclusion s

/-- A categorical strong deformation neighborhood retains its fixed original support under the literal ambient-image coordinates.
Source: Munkres, Topology, section 18; Hatcher, Algebraic Topology, section 0.
HC no distance; AV milestone no distance. -/
lemma properCycle_strong_open_collar_data
    (X : TopCat.{0}) (S : Set X) (U : TopCat.{0})
    (j : TopCat.of S ⟶ U) (k : U ⟶ X)
    (hj : j ≫ k = (TopPair.ofSubset (X := X) S).map)
    (hk : Topology.IsOpenEmbedding k) (r : U ⟶ TopCat.of S)
    (hjr : j ≫ r = 𝟙 (TopCat.of S)) (H : TopCat.Homotopy (𝟙 U) (r ≫ j))
    (hfixed : ∀ (t : unitInterval) (s : TopCat.of S), H (t, j s) = j s) :
    Nonempty (ProperCycleStrongSupportCollar X S) := by
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
        exact (congrArg e (H.map_zero_left (e.symm v))).trans (e.apply_symm_apply v)
      map_one_left := by
        intro v
        exact congrArg e (H.map_one_left (e.symm v)) }
  let C : ProperCycleSupportCollar X S :=
    { neighborhood := V
      isOpen := hk.isOpen_range
      contains := fun s hs => ⟨j ⟨s, hs⟩, ConcreteCategory.congr_hom hj ⟨s, hs⟩⟩
      inclusion := jV
      retraction := rV
      inclusion_factor := hfactor
      inclusion_retraction := hfix
      deformation := HV }
  refine ⟨⟨C, ?_⟩⟩
  intro t s
  change e (H (t, e.symm (e (j s)))) = e (j s)
  rw [e.symm_apply_apply]
  exact congrArg e (hfixed t s)

end HodgeLean.Foundations.QuotientDuality
