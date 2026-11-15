import HodgeLean.Foundations.Program.SchoenCycleC2OpenDimensionHelpers
import HodgeLean.Foundations.Program.SchoenTowerN1bProofs
import HodgeLean.Foundations.Program.SchoenTowerFoundC1b

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The retained Cartier universal property preserves dimension between
smooth integral complex schemes. -/
theorem s2e_cartier_universal_dimension
    {X B : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (b : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : X.left, ∃ U : X.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap b.left).ideal U) ≃ₗ[Γ(X.left, U)] Γ(X.left, U)))
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ X, u ≫ b = f) :
    dim X.left = dim B.left := by
  let U : B.left.Opens := ⟨(I.support : Set _)ᶜ, I.support.isClosed.isOpen_compl⟩
  let V := b.left ⁻¹ᵁ U
  have hs := n1bc_cartier_pullback_support_ne_top b.left I hcartier
  have hV : (V : Set X.left).Nonempty := by
    by_contra hn
    apply hs
    apply top_unique
    intro x _
    have hx : ¬ x ∈ V := fun hx => hn ⟨x, hx⟩
    rw [Scheme.IdealSheafData.support_comap]
    exact not_not.mp hx
  have hU : (U : Set B.left).Nonempty := by
    obtain ⟨x, hx⟩ := hV
    exact ⟨b.left x, hx⟩
  obtain ⟨e, _, _⟩ := s2t_cartierUniversal_offCentre I b.left (by
    intro T f hf
    let T' : Over (Spec ↧ℂ) := Over.mk (f ≫ B.hom)
    let f' : T' ⟶ B := Over.homMk f rfl
    obtain ⟨u, hu, huniq⟩ := huniv T' f' hf
    refine ⟨u.left, congrArg (fun v => v.left) hu, ?_⟩
    intro v hv
    have hvbase : v ≫ X.hom = T'.hom := by
      rw [← b.w, ← Category.assoc, hv]
      rfl
    let v' : T' ⟶ X := Over.homMk v hvbase
    have heq : v' ≫ b = f' := by
      apply Over.OverMorphism.ext
      exact hv
    exact congrArg (fun v => v.left) (huniq v' heq)) U (fun _ hx => hx)
  let : Nonempty U := hU.to_subtype
  let : Nonempty V := hV.to_subtype
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have he : dim V.toScheme = dim U.toScheme := by
    unfold TopologicalSpace.dim
    rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact (s2e_smooth_open_dimension X V hV).symm.trans
    (he.trans (s2e_smooth_open_dimension B U hU))

/-- Every level of a finite tower with the retained Cartier universal
properties has the initial level's dimension. -/
theorem s2e_cartier_tower_dimension
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (I : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (huniv : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f) :
    ∀ i, dim (B i).left = dim (B 0).left := by
  apply Fin.induction
  · rfl
  · intro i hi
    exact (s2e_cartier_universal_dimension (b i) (I i) (hcartier i) (huniv i)).trans hi

end HodgeLean.Foundations.Program
