import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNComparisonFactor
import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalFramesMono
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChangeTransport

/-! # Native comparison monicity from a total-transform union -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- A natural total-transform ideal comparison invertible along the retained
component, a union identity, and equal local slice ranks make the native
retained-component comparison monic.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8;
Fulton, Intersection Theory, Appendix B.6. -/
lemma paired_conormal_union_composite_mono
    {Q T Q' H X V : Scheme.{0}} [IsIntegral Q']
    (i₀ : Q ⟶ X) (t : T ⟶ V) (i₁ : Q' ⟶ V) (j : H ⟶ V)
    [IsClosedImmersion t] [IsClosedImmersion i₁] [IsClosedImmersion j]
    (σ : V ⟶ X) (p : T ⟶ Q) (a : Q' ⟶ T)
    (h : p ≫ i₀ = t ≫ σ) (ha : a ≫ t = i₁)
    (hc : (a ≫ p) ≫ i₀ = i₁ ≫ ((𝟙 V) ≫ σ))
    [IsIso ((Scheme.Modules.pullback i₁).map (idealPullbackMap i₀ t σ p h))]
    (hunion : t.ker = i₁.ker ⊓ j.ker)
    (hnot : ¬ Set.range i₁ ⊆ Set.range j) (n : ℕ)
    (hfree : ∀ x : Q', ∃ U : Q'.Opens, x ∈ U ∧
      Nonempty (Scheme.Modules.restrict
        ((Scheme.Modules.pullback (a ≫ p)).obj (s2c_conormal i₀)) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules)) ∧
      Nonempty (Scheme.Modules.restrict (s2c_conormal i₁) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules))) :
    Mono (comparisonMap i₀ i₁ ((𝟙 V) ≫ σ) (a ≫ p) hc) := by
  let m := idealPullbackMap i₀ t σ p h
  have h₁ : IsIso ((Scheme.Modules.pullback (a ≫ t)).map m) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackCongr ha) m).mpr inferInstance
  haveI : IsIso ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback t).map m)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp a t) m).mpr h₁
  haveI : IsIso ((Scheme.Modules.pullback a).map (comparisonMap i₀ t σ p h)) := by
    rw [unionConormal_comparisonMap_eq_prefix, Functor.map_comp]
    infer_instance
  let e : (Scheme.Modules.pullback a).obj (s2c_conormal t) ≅
      (Scheme.Modules.pullback (a ≫ p)).obj (s2c_conormal i₀) :=
    (asIso ((Scheme.Modules.pullback a).map (comparisonMap i₀ t σ p h))).symm ≪≫
      (Scheme.Modules.pullbackComp a p).app (s2c_conormal i₀)
  haveI : Mono (unionConormalFirst t i₁ a ha) := by
    apply unionConormal_mono_of_local_frames t i₁ j a ha hunion hnot n
    intro x
    obtain ⟨U, hx, ⟨eM⟩, eN⟩ := hfree x
    exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso e ≪≫ eM⟩, eN⟩
  haveI : Mono (comparisonMap t i₁ (𝟙 V) a
      (ha.trans (Category.comp_id i₁).symm)) := by
    change Mono (unionConormalFirst t i₁ a ha)
    infer_instance
  haveI : IsIso ((Scheme.Modules.pullback i₁).map
      ((Scheme.Modules.pullback (𝟙 V)).map m)) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (Scheme.Modules.pullbackId V) (Scheme.Modules.pullback i₁)) m).mpr
      (by change IsIso ((Scheme.Modules.pullback i₁).map (idealPullbackMap i₀ t σ p h))
          infer_instance)
  exact paired_conormal_composite_mono_on_source i₀ t i₁ σ (𝟙 V) p a h
    (ha.trans (Category.comp_id i₁).symm) hc

#print axioms paired_conormal_union_composite_mono
end HodgeLean.Foundations.Program.G32Native
