import HodgeLean.Foundations.Program.SchoenAdjoinDegreeZero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original generators generate the actual adjoin subalgebra over its inherited degree zero. -/
theorem s2_adjoin_generators {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A)
    [GradedRing (s2_subringGradedPiece 𝒜 (Algebra.adjoin (𝒜 0) (Set.range v)).toSubring)] :
    Algebra.adjoin
      (s2_subringGradedPiece 𝒜 (Algebra.adjoin (𝒜 0) (Set.range v)).toSubring 0)
      (Set.range (fun i => (⟨v i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ :
        Algebra.adjoin (𝒜 0) (Set.range v)))) = ⊤ := by
  let R := Algebra.adjoin (𝒜 0) (Set.range v)
  let Q := Algebra.adjoin (s2_subringGradedPiece 𝒜 R.toSubring 0)
    (Set.range (fun i => (⟨v i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : R)))
  apply top_unique
  intro x _
  change x ∈ Q
  have hx := x.property
  suffices ∀ (a : A) (ha : a ∈ R), (⟨a, ha⟩ : R) ∈ Q from this x.val hx
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap a =>
    exact Q.algebraMap_mem (s2_adjoinDegreeZeroEquiv 𝒜 (Set.range v) a)
  | add a b ha hb ia ib => exact Q.add_mem ia ib
  | mul a b ha hb ia ib => exact Q.mul_mem ia ib

end HodgeLean.Foundations.Program
