import HodgeLean.Foundations.BundleThom.RelativeSubcomplexMonomorphismHelpers
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-! # Gluing rational coclasses on actual short exact chain sequences

A compatible functional on middle homology extends over right homology, and universal coefficients retain the actual coclass.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- A rational dual coclass annihilating the left chain map extends across an actual short exact chain sequence.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficients and Mayer–Vietoris gluing. -/
theorem i1_rationalChainCoclass_gluing
    (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact) (n : ℕ)
    (u : S.X₂.linearDualCochainComplex.homology n)
    (hu : HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap S.f) n u = 0) :
    ∃ v : S.X₃.linearDualCochainComplex.homology n,
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap S.g) n v = u := by
  letI : Module.Injective ℚ ℚ := Module.injective_of_isSemisimpleRing ℚ ℚ
  letI : CategoryTheory.Injective (ModuleCat.of ℚ ℚ) :=
    Module.injective_object_of_injective_module ℚ ℚ
  have hH := hS.homology_exact₂ n
  let φ := ModuleCat.ofHom (S.X₂.linearDualHomologyEquiv n u)
  have hφ : HomologicalComplex.homologyMap S.f n ≫ φ = 0 := by
    apply ModuleCat.hom_ext
    ext z
    change S.X₂.linearDualHomologyEquiv n u (HomologicalComplex.homologyMap S.f n z) = 0
    rw [← HomologicalComplex.linearDualHomologyEquiv_naturality, hu, map_zero]
    rfl
  let ψ := hH.descToInjective φ hφ
  let v := (S.X₃.linearDualHomologyEquiv n).symm ψ.hom
  refine ⟨v, ?_⟩
  apply (S.X₂.linearDualHomologyEquiv n).injective
  ext z
  rw [HomologicalComplex.linearDualHomologyEquiv_naturality]
  change (S.X₃.linearDualHomologyEquiv n v) (HomologicalComplex.homologyMap S.g n z) = _
  rw [show S.X₃.linearDualHomologyEquiv n v = ψ.hom from
    (S.X₃.linearDualHomologyEquiv n).apply_symm_apply ψ.hom]
  exact ConcreteCategory.congr_hom (hH.comp_descToInjective φ hφ) z

/-- Compatible coclasses on the actual relative intersection–union chain sequence have an actual union extension.
Source: Hatcher, Algebraic Topology, §3.1, relative Mayer–Vietoris gluing. -/
theorem i1_relativeSubcomplexCoclass_gluing
    (X : SSet) (Z U V : X.Subcomplex) (n : ℕ)
    (u : (i1_relativeSubcomplexChainSequence X Z U V).X₂.linearDualCochainComplex.homology n)
    (hu : HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
      (i1_relativeSubcomplexChainSequence X Z U V).f) n u = 0) :
    ∃ v : (i1_relativeSubcomplexChainSequence X Z U V).X₃.linearDualCochainComplex.homology n,
      HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (i1_relativeSubcomplexChainSequence X Z U V).g) n v = u :=
  i1_rationalChainCoclass_gluing (i1_relativeSubcomplexChainSequence X Z U V)
    (i1_relativeSubcomplexChainSequence_shortExact X Z U V) n u hu

end HodgeLean.Foundations.BundleThom
