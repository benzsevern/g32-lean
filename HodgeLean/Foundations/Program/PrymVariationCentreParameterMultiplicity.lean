import HodgeLean.Foundations.Program.PrymVariationCentreMultiplicity

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63d_parameter_multiplicities (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := (b63l_parameterFibre b C V hV t)) g) ⊤) = 6 ∧
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := (b63l_parameterFibre b C V hV t)) g) (b3_periodF ℂ (b63l_parameterFibre b C V hV t))) = 3 ∧
    Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
      (fun g ↦ b4_cplxAct ℂ (C := (b63l_parameterFibre b C V hV t)) g) (b3_periodF ℂ (b63l_parameterFibre b C V hV t))) = 3 := by
  have hq : Function.Injective (b6_branch t.val) :=
    (b6t_polydisc_neighbourhood b hb).2.2.2 (hV t.property)
  exact ⟨b63d_natural_top_multiplicity (b63l_parameterFibre b C V hV t) hG
      (b63d_projection b C f V hV t) hf hs hgal (b6_branch t.val) hq hbranch hrot,
    b63d_period_multiplicities (b63l_parameterFibre b C V hV t) hG
      (b63d_projection b C f V hV t) hf hs hgal (b6_branch t.val) hq hbranch hrot⟩

end HodgeLean.Foundations.Program
