import HodgeLean.Foundations.Program.RelativeFrameOperatorPoleGluing

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_pole_field_exists {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x₀ : Fin D.m) (k : rf4_Src D)
    (hk : rf4_delta D ε k = rf4_poleDatum D ε S.small x₀) :
    ∃ θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ, HurwitzPrymRR_IsLinear θ ∧
      (∀ i p, p ∈ (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i).source →
        D.P.chart i (S.h.symm p) ∈ D.P.piece i → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        θ ⟨p, v⟩ = rf4_extendBdd (k.1.val i) (D.P.chart i (S.h.symm p)) *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) p v)) ∧
      ∀ x p, p ∈ (S.w x).source → S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x) →
        ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        θ ⟨p, v⟩ = rf4_poleInnerCoeff D ε k x₀ x (S.w x p) *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) p v) := by
  classical
  let I := Sum (Fin D.P.n) (Fin D.m)
  let e : I → OpenPartialHomeomorph X ℂ := Sum.elim
    (fun i ↦ S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) S.w
  let U : I → Set ℂ := Sum.elim D.P.piece (fun x ↦ rf4_innerDisc (D.deg x) D.r (ε x))
  let f : I → ℂ → ℂ := Sum.elim (fun i ↦ rf4_extendBdd (k.1.val i))
    (rf4_poleInnerCoeff D ε k x₀)
  have hcover (p : X) : ∃ i, p ∈ (e i).source ∧ e i p ∈ U i := by
    rcases rf4_plumbing_cover_coordinates S p with ⟨i, hi, hui⟩ | ⟨x, hx, hux⟩
    · refine ⟨Sum.inl i, ?_, hui⟩
      change p ∈ Set.univ ∩ _
      exact ⟨Set.mem_univ p, hi⟩
    · exact ⟨Sum.inr x, hx, hux⟩
  have hag : ∀ i j p, p ∈ (e i).source → e i p ∈ U i → p ∈ (e j).source → e j p ∈ U j →
      ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      f i (e i p) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e i) p v) =
        f j (e j p) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e j) p v) := by
    intro i j p hi hui hj huj v
    rcases i with i | x <;> rcases j with j | y
    · have hi' : p ∈ Set.univ ∩ S.h.symm ⁻¹' (D.P.chart i).source := hi
      have hj' : p ∈ Set.univ ∩ S.h.symm ⁻¹' (D.P.chart j).source := hj
      exact rf4_outerForm_agree S k.1 p i j ⟨hi'.2, hui⟩ ⟨hj'.2, huj⟩ v
    · have hi' : p ∈ Set.univ ∩ S.h.symm ⁻¹' (D.P.chart i).source := hi
      exact rf4_pole_outer_inner_agree S x₀ k hk p i y ⟨hi'.2, hui⟩ ⟨hj, huj⟩ v
    · have hj' : p ∈ Set.univ ∩ S.h.symm ⁻¹' (D.P.chart j).source := hj
      exact (rf4_pole_outer_inner_agree S x₀ k hk p j x ⟨hj'.2, huj⟩ ⟨hi, hui⟩ v).symm
    · have hxy : x = y := by
        by_contra hne
        exact Set.disjoint_left.mp (S.disjoint hne)
          ⟨S.w x p, hui, (S.w x).left_inv hi⟩ ⟨S.w y p, huj, (S.w y).left_inv hj⟩
      subst y
      rfl
  refine ⟨rf4_localGlue e U hcover f, rf4_localGlue_fibre e U hcover f, ?_, ?_⟩
  · intro i p hp hU v
    exact rf4_localGlue_eq_of_agree e U hcover f hag (Sum.inl i) p hp hU v
  · intro x p hp hU v
    exact rf4_localGlue_eq_of_agree e U hcover f hag (Sum.inr x) p hp hU v

end HodgeLean.Foundations.Program
