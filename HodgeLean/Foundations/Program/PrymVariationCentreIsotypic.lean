import HodgeLean.Foundations.Program.PrymVariationCentreKill
import HodgeLean.Foundations.Program.HurwitzPrym

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The two column spaces for the natural representation and its conjugate.
Source: G32 v0.16, §3.3; Fulton-Harris, §3.5. -/
def b63d_repSpace : Fin 2 → Type :=
  ![Fin 4 → ℂ, HurwitzPrymRex_Bar (Fin 4 → ℂ)]

instance (i : Fin 2) : AddCommGroup (b63d_repSpace i) :=
  Fin.cases (inferInstanceAs (AddCommGroup (Fin 4 → ℂ)))
    (Fin.cases (inferInstanceAs (AddCommGroup (HurwitzPrymRex_Bar (Fin 4 → ℂ))))
      (fun j ↦ Fin.elim0 j)) i

instance (i : Fin 2) : Module ℂ (b63d_repSpace i) :=
  Fin.cases (inferInstanceAs (Module ℂ (Fin 4 → ℂ)))
    (Fin.cases (inferInstanceAs (Module ℂ (HurwitzPrymRex_Bar (Fin 4 → ℂ))))
      (fun j ↦ Fin.elim0 j)) i

instance (i : Fin 2) : FiniteDimensional ℂ (b63d_repSpace i) :=
  Fin.cases (inferInstanceAs (FiniteDimensional ℂ (Fin 4 → ℂ)))
    (Fin.cases (inferInstanceAs (FiniteDimensional ℂ (HurwitzPrymRex_Bar (Fin 4 → ℂ))))
      (fun j ↦ Fin.elim0 j)) i

example : Module.finrank ℂ (b63d_repSpace 0) = 4 := b63d_naturalRep_finrank

/-- The natural representation and its conjugate as a finite family.
Source: G32 v0.16, §3.3; Fulton-Harris, §3.5. -/
def b63d_repPair (i : Fin 2) : Representation ℂ b4b_Group (b63d_repSpace i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun j ↦ Fin.elim0 j)) i
  · exact b63d_naturalRep
  · exact HurwitzPrymRex_barRep b63d_naturalRep

instance (i : Fin 2) : (b63d_repPair i).IsIrreducible := by
  fin_cases i
  · exact b63d_naturalRep_isIrreducible
  · exact HurwitzPrymRex_barRep_isIrreducible b63d_naturalRep

example : b63d_repPair 0 = b63d_naturalRep := rfl

theorem b63d_repPair_distinct (i j : Fin 2) (hij : i ≠ j)
    (φ : Representation.IntertwiningMap (b63d_repPair i) (b63d_repPair j)) : φ = 0 := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact b63d_natural_conjugate_intertwiner_zero φ
  · exact b63d_conjugate_natural_intertwiner_zero φ
  · exact False.elim (hij rfl)

theorem b63d_finrank_primitive_image {M : Type} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (σ : Representation ℂ b4b_Group M)
    (W : Submodule ℂ M) (hW : ∀ g, W ≤ W.comap (σ g)) :
    Module.finrank ℂ (W.map (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • σ g)) =
      Module.finrank ℂ (b4_HomG b63d_naturalRep (fun g ↦ σ g) W) +
        Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep) (fun g ↦ σ g) W) := by
  have hkill : ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ b4b_Group V'), ρ'.IsIrreducible →
      (∀ i, ∀ φ : Representation.IntertwiningMap ρ' (b63d_repPair i), φ = 0) →
        (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • ρ' g) = 0 := by
    intro V' _ _ _ ρ' _ hh
    exact b63d_projector_kills ρ' (hh 0) (hh 1)
  have h := b4_finrank_map_isotypic σ W hW b63d_repPair b63d_repPair_distinct
    (fun g ↦ (b4b_projectorCoeff g : ℂ)) hkill
  rw [Fin.sum_univ_two] at h
  change Module.finrank ℂ (W.map (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • σ g)) =
    Module.finrank ℂ (b4_HomG b63d_naturalRep (fun g ↦ σ g) W) *
      Module.finrank ℂ (LinearMap.range (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g)) +
    Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep) (fun g ↦ σ g) W) *
      Module.finrank ℂ (LinearMap.range (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
        HurwitzPrymRex_barRep b63d_naturalRep g)) at h
  simpa only [b63d_naturalRep_projector_rank, b63d_conjugateRep_projector_rank, mul_one] using h

end HodgeLean.Foundations.Program
