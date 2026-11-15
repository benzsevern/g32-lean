import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sets.Opens

/-! # Finite compositions of local ambient deformations

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Finitely many ambient deformations fixing a subset combine their open
regions sent into that subset. Earlier deformations are pulled back in the
open regions, so no control on their displacement is needed.
Source: Hatcher, Algebraic Topology, §0, composition of homotopies.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_finite_deformation
    {X A : Type*} [TopologicalSpace X] (S : Set X)
    (f : A → C(X, X)) (H : ∀ a, ContinuousMap.Homotopy (ContinuousMap.id X) (f a))
    (hfix : ∀ a x, x ∈ S → f a x = x)
    (U : A → Opens X) (hinto : ∀ a, Set.MapsTo (f a) (U a) S) (l : List A) :
    ∃ (F : C(X, X)), Nonempty (ContinuousMap.Homotopy (ContinuousMap.id X) F) ∧
      (∀ x ∈ S, F x = x) ∧ ∃ V : Opens X,
        (∀ a ∈ l, S ∩ U a ⊆ V) ∧ Set.MapsTo F V S := by
  induction l with
  | nil =>
    exact ⟨ContinuousMap.id X, ⟨ContinuousMap.Homotopy.refl _⟩, fun _ _ => rfl,
      ⊥, by simp, fun _ h => False.elim h⟩
  | cons a l ih =>
    obtain ⟨F, ⟨HF⟩, hF, V, hV, hFS⟩ := ih
    let G := (f a).comp F
    let V' : Opens X := V ⊔ ⟨F ⁻¹' U a, (U a).isOpen.preimage F.continuous⟩
    have HG : ContinuousMap.Homotopy (ContinuousMap.id X) G :=
      HF.trans (by simpa only [ContinuousMap.id_comp] using (H a).compContinuousMap F)
    refine ⟨G, ⟨HG⟩, ?_, V', ?_, ?_⟩
    · intro x hx
      exact (congrArg (f a) (hF x hx)).trans (hfix a x hx)
    · intro b hb x hx
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact Or.inr (by change F x ∈ U a; rw [hF x hx.1]; exact hx.2)
      · exact Or.inl (hV b hb hx)
    · intro x hx
      rcases hx with hx | hx
      · change f a (F x) ∈ S
        rw [hfix a (F x) (hFS hx)]
        exact hFS hx
      · exact hinto a hx

#print axioms s4_assembly_finite_deformation
/-- A compact subset covered by local ambient deformations has one open
neighbourhood sent into it by a map homotopic to the ambient identity.
Source: Hatcher, Algebraic Topology, §0; the finite subcover property.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_compact_deformation
    {X A : Type*} [TopologicalSpace X] (S : Set X) (hS : IsCompact S)
    (f : A → C(X, X)) (H : ∀ a, ContinuousMap.Homotopy (ContinuousMap.id X) (f a))
    (hfix : ∀ a x, x ∈ S → f a x = x)
    (U : A → Opens X) (hinto : ∀ a, Set.MapsTo (f a) (U a) S)
    (hcover : S ⊆ ⋃ a, (U a : Set X)) :
    ∃ (F : C(X, X)), Nonempty (ContinuousMap.Homotopy (ContinuousMap.id X) F) ∧
      (∀ x ∈ S, F x = x) ∧ ∃ V : Opens X, S ⊆ V ∧ Set.MapsTo F V S := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun a => (U a : Set X))
    (fun a => (U a).isOpen) hcover
  obtain ⟨F, HF, hF, V, hV, hFS⟩ :=
    s4_assembly_finite_deformation S f H hfix U hinto t.toList
  refine ⟨F, HF, hF, V, ?_, hFS⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact hV a (Finset.mem_toList.mpr ha) ⟨hx, hxa⟩

#print axioms s4_assembly_compact_deformation
end HodgeLean.Foundations.Program
