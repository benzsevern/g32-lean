import HodgeLean.Adapters.NormalConeB4aGysinTensorPoint

noncomputable section
namespace HodgeLean.Adapters

/-- Complex algebra evaluations form a closed subspace of the space of
all complex-valued functions on the source algebra. -/
theorem a3b4a_gysin_algHom_isClosedEmbedding
    (R : Type) [CommRing R] [Algebra ℂ R] :
    Topology.IsClosedEmbedding (fun w : R →ₐ[ℂ] ℂ => (w : R → ℂ)) := by
  have hind : Topology.IsInducing (fun w : R →ₐ[ℂ] ℂ => (w : R → ℂ)) := ⟨rfl⟩
  have hemb : Topology.IsEmbedding (fun w : R →ₐ[ℂ] ℂ => (w : R → ℂ)) :=
    ⟨hind, fun f g h => AlgHom.ext (congrFun h)⟩
  refine ⟨hemb, ?_⟩
  have hrange : Set.range (fun w : R →ₐ[ℂ] ℂ => (w : R → ℂ)) =
      {f : R → ℂ | f 0 = 0 ∧ f 1 = 1 ∧
        (∀ x y, f (x + y) = f x + f y) ∧
        (∀ x y, f (x * y) = f x * f y) ∧
        ∀ c : ℂ, f (algebraMap ℂ R c) = c} := by
    ext f
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.map_zero, w.map_one, w.map_add, w.map_mul, w.commutes⟩
    · rintro ⟨h0, h1, hadd, hmul, hscalar⟩
      refine ⟨{
        toFun := f
        map_zero' := h0
        map_one' := h1
        map_add' := hadd
        map_mul' := hmul
        commutes' := hscalar }, rfl⟩
  rw [hrange]
  have hadd : IsClosed {f : R → ℂ | ∀ x y, f (x + y) = f x + f y} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
  have hmul : IsClosed {f : R → ℂ | ∀ x y, f (x * y) = f x * f y} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x * y)) ((continuous_apply x).mul (continuous_apply y))
  have hscalar : IsClosed {f : R → ℂ | ∀ c : ℂ, f (algebraMap ℂ R c) = c} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun c => isClosed_eq (continuous_apply (algebraMap ℂ R c)) continuous_const
  exact (isClosed_eq (continuous_apply (0 : R)) continuous_const).inter
    ((isClosed_eq (continuous_apply (1 : R)) continuous_const).inter
      (hadd.inter (hmul.inter hscalar)))

end HodgeLean.Adapters
