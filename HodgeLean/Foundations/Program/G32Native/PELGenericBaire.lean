import HodgeLean.Foundations.Program.G32Native.PELRationalEquationCountability
import Mathlib.Topology.Baire.Lemmas

noncomputable section
namespace HodgeLean.Foundations

/-- Outside a countable collection of proper containment loci, any rational
algebraic subgroup containing a fibre contains all fibres. The analytic input
is stated separately as the empty-interior property of each proper locus. -/
theorem pel_dense_maximal_containment {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {n : ℕ} (H : X → Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hc : ∀ G, g2_IsRatAlgSubgroup G → IsClosed {x | H x ⊆ G})
    (hi : ∀ G, g2_IsRatAlgSubgroup G → (¬ ∀ x, H x ⊆ G) →
      interior {x | H x ⊆ G} = ∅) :
    Dense {x | ∀ G, g2_IsRatAlgSubgroup G → H x ⊆ G → ∀ y, H y ⊆ G} := by
  let S := {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ) |
    g2_IsRatAlgSubgroup G ∧ ¬ ∀ x, H x ⊆ G}
  have hS : S.Countable := (pel_countable_ratAlgSubgroups n).mono fun _ h => h.1
  letI := hS.to_subtype
  have hd : Dense (⋂ G : S, ({x | H x ⊆ G.val}ᶜ : Set X)) := by
    apply dense_iInter_of_isOpen
    · intro G
      exact (hc G.val G.property.1).isOpen_compl
    · intro G
      exact interior_eq_empty_iff_dense_compl.mp (hi G.val G.property.1 G.property.2)
  apply hd.mono
  intro x hx G hG hxG
  by_contra hnot
  have hxnot := Set.mem_iInter.mp hx (⟨G, hG, hnot⟩ : S)
  exact hxnot hxG

/-- A maximal containment point attains the intersection defining the family
algebraic group. This is a set-theoretic step independent of the topology. -/
theorem pel_family_group_eq_at_maximal {X : Type*} {n : ℕ}
    (H : X → Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) (x : X)
    (ha : g2_IsRatAlgSubgroup (H x))
    (hm : ∀ G, g2_IsRatAlgSubgroup G → H x ⊆ G → ∀ y, H y ⊆ G) :
    H x = ⋂₀ {G | g2_IsRatAlgSubgroup G ∧ ∀ y, H y ⊆ G} := by
  apply Set.Subset.antisymm
  · intro g hg G hG
    exact hG.2 x hg
  · intro g hg
    exact hg (H x) ⟨ha, hm (H x) ha (Set.Subset.refl _)⟩

/-- The fibre groups attain the family intersection densely once the proper
containment loci have empty interior. -/
theorem pel_dense_family_group {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {n : ℕ} (H : X → Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (ha : ∀ x, g2_IsRatAlgSubgroup (H x))
    (hc : ∀ G, g2_IsRatAlgSubgroup G → IsClosed {x | H x ⊆ G})
    (hi : ∀ G, g2_IsRatAlgSubgroup G → (¬ ∀ x, H x ⊆ G) →
      interior {x | H x ⊆ G} = ∅) :
    Dense {x | H x = ⋂₀ {G | g2_IsRatAlgSubgroup G ∧ ∀ y, H y ⊆ G}} :=
  (pel_dense_maximal_containment H hc hi).mono fun x hx =>
    pel_family_group_eq_at_maximal H x (ha x) hx

end HodgeLean.Foundations
