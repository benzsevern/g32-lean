import HodgeLean.Foundations.Program.PrymVariationCentreIsotypic
import HodgeLean.Foundations.Program.PrymVariationCentreParameterMultiplicity

noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

/-- The complex representation on the ambient periods of the given surface.
Source: Birkenhake-Lange, §11.4; `b4_latticeAct_mul`. -/
def b63d_periodRep (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    Representation ℂ b4b_Group (ℂ ⊗[ℤ] b3_periodLattice ℂ C) where
  toFun g := b4_cplxAct ℂ g
  map_one' := by
    change b2_cplxMap (b4_latticeAct ℂ (C := C) 1) = LinearMap.id
    rw [b4_latticeAct_one hG, b2_cplxMap_id]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul c x =>
      change c ⊗ₜ[ℤ] b4_latticeAct ℂ (g * h) x =
        c ⊗ₜ[ℤ] b4_latticeAct ℂ g (b4_latticeAct ℂ h x)
      rw [b4_latticeAct_mul hG]
      rfl
    | add x y hx hy => simp only [map_add, Module.End.mul_apply, hx, hy]

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (g : b4b_Group) : b63d_periodRep C hG g = b4_cplxAct ℂ (C := C) g := rfl

theorem b63d_exact_periodF_rank (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hm : Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3 ∧
      Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
        (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3) :
    Module.finrank ℂ (b4_prymF ℂ (C := C) b4b_projectorCoeff) = 6 := by
  have hkill : ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ b4b_Group V'), ρ'.IsIrreducible →
      (∀ i, ∀ φ : Representation.IntertwiningMap ρ' (b63d_repPair i), φ = 0) →
        (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • ρ' g) = 0 := by
    intro V' _ _ _ ρ' _ hh
    exact b63d_projector_kills ρ' (hh 0) (hh 1)
  have h := b4_prymF_finrank (by simp : Module.finrank ℂ ℂ = 1) hG
    (b63d_periodRep C hG) (fun _ ↦ rfl) b63d_repPair b63d_repPair_distinct
    b4b_projectorCoeff hkill
  rw [Fin.sum_univ_two] at h
  change Module.finrank ℂ (b4_prymF ℂ (C := C) b4b_projectorCoeff) =
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) *
      Module.finrank ℂ (LinearMap.range (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b63d_naturalRep g)) +
    Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
      (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) *
      Module.finrank ℂ (LinearMap.range (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
        HurwitzPrymRex_barRep b63d_naturalRep g)) at h
  simpa only [hm.1, hm.2, b63d_naturalRep_projector_rank,
    b63d_conjugateRep_projector_rank, mul_one] using h

end HodgeLean.Foundations.Program
