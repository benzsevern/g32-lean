import HodgeLean.Foundations.Program.G32Native.PairedC3PositiveNativeVanishing
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.InvertibleExactness

/-! # Sections of the original extension after a native positive twist -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules AlgebraicGeometry.ProjSpace

/-- Tensoring the original sequence with the positive native line power
lifts a free quotient through its original tensored projection.
Source: Hartshorne, Algebraic Geometry, III, Theorem 5.1. -/
theorem paired_c3_twisted_extension_section (k a b d : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    (e₁ : E.X₁ ≅ SheafOfModules.free (Fin a))
    [(E.X₂ ⊗ (twistingSheaf ℂ k).tensorPow d).IsQuasicoherent]
    [(E.X₃ ⊗ (twistingSheaf ℂ k).tensorPow d).IsQuasicoherent]
    (e₃ : E.X₃ ⊗ (twistingSheaf ℂ k).tensorPow d ≅
      SheafOfModules.free (Fin b)) :
    ∃ s : E.X₃ ⊗ (twistingSheaf ℂ k).tensorPow d ⟶
      E.X₂ ⊗ (twistingSheaf ℂ k).tensorPow d,
      s ≫ (E.g ▷ (twistingSheaf ℂ k).tensorPow d) = 𝟙 _ := by
  let T := E.map (tensorRight ((twistingSheaf ℂ k).tensorPow d))
  letI : T.X₂.IsQuasicoherent := inferInstanceAs
    (E.X₂ ⊗ (twistingSheaf ℂ k).tensorPow d).IsQuasicoherent
  letI : T.X₃.IsQuasicoherent := inferInstanceAs
    (E.X₃ ⊗ (twistingSheaf ℂ k).tensorPow d).IsQuasicoherent
  have hT : T.ShortExact :=
    (isInvertible_twistingSheaf ℂ k).shortExact_tensorRight_tensorPow d E hE
  exact paired_c3_positive_kernel_free_quotient_section k a b d T hT
    ((tensorRight ((twistingSheaf ℂ k).tensorPow d)).mapIso e₁) e₃

#print axioms paired_c3_twisted_extension_section
end HodgeLean.Foundations.Program.G32Native
