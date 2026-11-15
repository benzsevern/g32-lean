import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsAssembly
import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsFill

/-! # Open bodies for the pullback monodromy foundations draft -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65t_transport_pullback_aux (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (U V : Set ℂ) (hU : IsOpen U) (hV : IsOpen V) (A : ℂ → E →L[ℂ] E)
    (hA : AnalyticOnNhd ℂ A U) (φ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ V)
    (hmaps : MapsTo φ V U) (x y : V) (γ : Path x y) :
    b65f_transport E (b65t_pull E φ A) (fun t ↦ (γ.extend t).val) =
      b65f_transport E A (fun t ↦ φ (γ.extend t).val) :=
  b65t_transport_pullback_proof E U V hU hV A hA φ hφ hmaps x y γ

theorem b65t_pullback_transport_aux (x y : b65s_regular) (γ : Path x y) :
    b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ b65r_phi (γ.extend t).val) :=
  b65t_pullback_transport_proof x y γ

theorem b65t_puncture_fill_aux (X : Set (OnePoint ℂ)) (hX : IsOpen X)
    (F : Finset (OnePoint ℂ)) (x : ↥(X \ (F : Set (OnePoint ℂ)))) :
    Function.Surjective (FundamentalGroup.map (b65t_fill X F) x) ∧
      (FundamentalGroup.map (b65t_fill X F) x).ker =
        Subgroup.normalClosure (b65t_peripheral X F x) ∧
      ∀ (G : Type) [Group G] (ρ : FundamentalGroup ↥(X \ (F : Set (OnePoint ℂ))) x →* G),
        (∀ c ∈ b65t_peripheral X F x, ρ c = 1) →
          ∃! σ : FundamentalGroup ↥X (b65t_fill X F x) →* G,
            σ.comp (FundamentalGroup.map (b65t_fill X F) x) = ρ :=
  b65t_puncture_fill_proof X hX F x

theorem b65t_covering_index_aux {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (hp : IsCoveringMap p) (e : E) (hfin : (p ⁻¹' {p e}).Finite) :
    0 < (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.index ∧
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.index ≤ Nat.card (p ⁻¹' {p e}) :=
  b65t_covering_index_proof p hp e hfin

theorem b65t_reflection_class_aux (g : b4b_Group)
    (K : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hK : b65r_operator (b4b_toMatrix g) =
      (K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
        b65r_operator (b4b_toMatrix (b4b_generators 0)) * ↑(K⁻¹)) :
    ∃ h : b4b_Group, h * b4b_generators 0 * h⁻¹ = g :=
  b65t_reflection_class_proof g K hK

theorem b65t_reflection_in_image_aux (x : b65s_regular)
    (ρ : FundamentalGroup b65s_regular x →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hρ : ∀ γ : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹)) :
    ∃ g : b4b_Group, g * b4b_generators 0 * g⁻¹ ∈ ρ.range :=
  b65t_reflection_in_image_proof x ρ C hρ

theorem b65t_pullback_monodromy_aux (x : b65s_regular) :
    ∃ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      Function.Surjective ρ ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        ∀ γ : Path x x,
          b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
            (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
              b65r_operator (b4b_toMatrix
                (ρ (FundamentalGroup.map b65s_inclusion x
                  (FundamentalGroup.fromPath ⟦γ⟧)))) * ↑(C⁻¹) :=
  b65t_pullback_monodromy_of_fill (fun X hX F x ↦ b65t_puncture_fill_aux X hX F x) x

end HodgeLean.Foundations.Program
