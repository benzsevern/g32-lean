import HodgeLean.Foundations.Program.G32Native.UnionConormalComparisonMono

/-! # Reflection of monicity and noncontainment along scheme isomorphisms -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Pullback along a scheme isomorphism reflects monicity. -/
lemma unionConormal_mono_of_iso_pullback
    {X Y : Scheme.{0}} (b : X ⟶ Y) [IsIso b]
    {M N : Y.Modules} (f : M ⟶ N) [Mono ((Scheme.Modules.pullback b).map f)] :
    Mono f := by
  let e : Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback (inv b) ≅
      𝟭 Y.Modules :=
    Scheme.Modules.pullbackComp (inv b) b ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id b) ≪≫ Scheme.Modules.pullbackId Y
  haveI : (Scheme.Modules.pullback b).Faithful := Functor.Faithful.of_comp_iso e
  exact (Scheme.Modules.pullback b).mono_of_mono_map inferInstance

/-- Noncontainment is retained by two commuting isomorphism squares. -/
lemma unionConormal_noncontainment_of_iso_squares
    {Q₁ Q₂ V Q₁' Q₂' V' : Scheme.{0}}
    (i₁ : Q₁ ⟶ V) (i₂ : Q₂ ⟶ V) (i₁' : Q₁' ⟶ V') (i₂' : Q₂' ⟶ V')
    (b₁ : Q₁' ⟶ Q₁) (b₂ : Q₂' ⟶ Q₂) (j : V' ⟶ V)
    [IsIso b₁]
    (h₁ : b₁ ≫ i₁ = i₁' ≫ j) (h₂ : b₂ ≫ i₂ = i₂' ≫ j)
    (hnot : ¬ Set.range i₁ ⊆ Set.range i₂) :
    ¬ Set.range i₁' ⊆ Set.range i₂' := by
  intro hc
  apply hnot
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', hx⟩ := (ConcreteCategory.bijective_of_isIso b₁.base).surjective x
  obtain ⟨y, hy⟩ := hc (Set.mem_range_self (f := i₁') x')
  refine ⟨b₂ y, ?_⟩
  have he₁ := congrArg (fun f : Q₁' ⟶ V => f x') h₁
  have he₂ := congrArg (fun f : Q₂' ⟶ V => f y) h₂
  change i₁ (b₁ x') = j (i₁' x') at he₁
  change i₂ (b₂ y) = j (i₂' y) at he₂
  rw [he₂, hy, ← he₁, hx]

#print axioms unionConormal_mono_of_iso_pullback
#print axioms unionConormal_noncontainment_of_iso_squares
end HodgeLean.Foundations.Program.G32Native
