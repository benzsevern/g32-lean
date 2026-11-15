import HodgeLean.Foundations.QuotientDuality.PersistenceLinear
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Eigenvectors in nonnegative cochain exact sequences. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Module.End
namespace HodgeLean.Foundations.QuotientDuality

variable {K : Type} [Field K]

lemma persistence_sequence_eigen_lift
    (S : ShortComplex (CochainComplex (ModuleCat K) ℕ)) (hS : S.ShortExact)
    (σ : S ⟶ S) (ζ : K)
    (h₁ : ∀ n, Module.End.IsSemisimple (HomologicalComplex.homologyMap σ.τ₁ n).hom)
    (h₃ : ∀ n, Module.End.IsSemisimple (HomologicalComplex.homologyMap σ.τ₃ n).hom)
    (hvan : ∀ n (x : S.X₃.homology n),
      (HomologicalComplex.homologyMap σ.τ₃ n) x = ζ • x → x = 0)
    (n : ℕ) (v : S.X₂.homology n)
    (hv : (HomologicalComplex.homologyMap σ.τ₂ n) v = ζ • v) :
    ∃! u : S.X₁.homology n,
      (HomologicalComplex.homologyMap σ.τ₁ n) u = ζ • u ∧
      (HomologicalComplex.homologyMap S.f n) u = v := by
  have hf (j : ℕ) :
      HomologicalComplex.homologyMap σ.τ₁ j ≫ HomologicalComplex.homologyMap S.f j =
      HomologicalComplex.homologyMap S.f j ≫ HomologicalComplex.homologyMap σ.τ₂ j := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      σ.comm₁₂]
  have hg (j : ℕ) :
      HomologicalComplex.homologyMap σ.τ₂ j ≫ HomologicalComplex.homologyMap S.g j =
      HomologicalComplex.homologyMap S.g j ≫ HomologicalComplex.homologyMap σ.τ₃ j := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      σ.comm₂₃]
  have hres : (HomologicalComplex.homologyMap S.g n) v = 0 := by
    apply hvan n
    rw [← ConcreteCategory.comp_apply, ← hg, ConcreteCategory.comp_apply, hv]
    exact map_smul _ _ _
  have hex := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₂ n)
  obtain ⟨x, hx⟩ := hex v hres
  obtain ⟨u, hu, huv⟩ := persistence_semisimple_eigen_lift
    (HomologicalComplex.homologyMap σ.τ₁ n).hom
    (HomologicalComplex.homologyMap σ.τ₂ n).hom
    (HomologicalComplex.homologyMap S.f n).hom
    (fun x => ConcreteCategory.congr_hom (hf n) x) (h₁ n) ζ v hv ⟨x, hx⟩
  refine ⟨u, ⟨hu, huv⟩, ?_⟩
  intro u' hu'
  have hz : (HomologicalComplex.homologyMap S.f n) (u' - u) = 0 := by
    rw [map_sub, hu'.2, huv, sub_self]
  have he : (HomologicalComplex.homologyMap σ.τ₁ n) (u' - u) = ζ • (u' - u) := by
    rw [map_sub, hu'.1, hu, smul_sub]
  apply sub_eq_zero.mp
  cases n with
  | zero =>
    haveI := hS.mono_f
    haveI : Mono (S.f.f 0) := inferInstance
    haveI := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0
      (by intro i hi; change i + 1 = 0 at hi; omega)
    exact (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap S.f 0)).mp
      inferInstance (hz.trans (map_zero _).symm)
  | succ j =>
    have hj : (ComplexShape.up ℕ).Rel j (j + 1) := rfl
    have hex' := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₁ j (j+1) hj)
    obtain ⟨y, hy⟩ := hex' (u' - u) hz
    have hδ := HomologicalComplex.HomologySequence.δ_naturality σ hS hS j (j+1) hj
    obtain ⟨z, hze, hzu⟩ := persistence_semisimple_eigen_lift
      (HomologicalComplex.homologyMap σ.τ₃ j).hom
      (HomologicalComplex.homologyMap σ.τ₁ (j+1)).hom
      (hS.δ j (j+1) hj).hom
      (fun x => (ConcreteCategory.congr_hom hδ x).symm) (h₃ j) ζ (u' - u) he ⟨y, hy⟩
    rw [hvan j z hze, map_zero] at hzu
    exact hzu.symm

end HodgeLean.Foundations.QuotientDuality
