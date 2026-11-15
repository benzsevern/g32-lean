import HodgeLean.Foundations.Program.G32Native.PairedC3MixedFixedFrames
import HodgeLean.Foundations.Program.G32Native.PairedConormalFramedRelation
import Lean.Elab.Tactic.Omega

/-! # Fibrewise nonvanishing for the actual mixed modification relation -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- Fixed-rank frames of the actual mixed source and middle bundle force
the actual presentation relation to stay nonzero at every complex point.
Source: Hartshorne, Algebraic Geometry, II.5, right exactness of tensor products. -/
theorem paired_c3_modification_relation_fibre_nonzero
    (k a b : ℕ) (hrank : a + b = k)
    (p : pairedC3Proj k ⟶ Spec ↧ℂ)
    (A M I : (pairedC3Proj k).Modules)
    (eA : A ≅ pairedC3SplitBundle k a b)
    (u : I ⟶ A ⊞ SheafOfModules.unit (pairedC3Proj k).ringCatSheaf)
    (v : A ⊞ SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ M)
    (huv : u ≫ v = 0) (hs : (ShortComplex.mk u v huv).ShortExact)
    (hM : ∀ y : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free (Fin k)))
    (x : ComplexPoint (Over.mk p)) :
    (Scheme.Modules.pullback x.left).map u ≠ 0 := by
  have hA : ∀ y : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj A ≅ SheafOfModules.free (Fin k)) := by
    intro y
    obtain ⟨U, hy, ⟨e⟩⟩ := paired_c3_split_bundle_fixed_frames k a b y
    refine ⟨U, hy, ⟨(Scheme.Modules.pullback U.ι).mapIso eA ≪≫ e ≪≫ ?_⟩⟩
    exact eqToIso (congrArg (fun n =>
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules)) hrank)
  have hUnit : ∀ y : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj
        (SheafOfModules.unit (pairedC3Proj k).ringCatSheaf) ≅ SheafOfModules.free (Fin 1)) := by
    intro y
    refine ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _ ≪≫ ?_⟩⟩
    exact (coproductUniqueIso (fun _ : Fin 1 =>
      SheafOfModules.unit (⊤ : (pairedC3Proj k).Opens).toScheme.ringCatSheaf)).symm
  let e : cokernel u ≅ M :=
    (cokernelIsCokernel u).coconePointUniqueUpToIso hs.gIsCokernel
  refine conormal_relation_pullback_ne_zero_of_fixedFrames
    (Q := Over.mk p) u e (k + 1) k (by omega) ?_ ?_ x
  · intro y
    obtain ⟨U, hy, ⟨e⟩⟩ := paired_c3_biprod_fixed_frames A _ k 1 hA hUnit y
    exact ⟨U, hy, ⟨e.symm⟩⟩
  · intro y
    obtain ⟨U, hy, ⟨e⟩⟩ := hM y
    exact ⟨U, hy, ⟨e.symm⟩⟩

#print axioms paired_c3_modification_relation_fibre_nonzero
end HodgeLean.Foundations.Program.G32Native
