import HodgeLean.Foundations.Program.PrymFamilyCentreDefs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLoopRepresentatives

/-! # B6-3g, parts 2 and 3: naturality of integral period comparisons

An integral period comparison `P` with `P [γ] = ∫_γ` carries the homology action of a
holomorphic deck transformation to its pushforward `b4_latticeAct` on the period lattice, since
loop classes exhaust `H₁` of a compact connected Riemann surface.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program

/-- The homology map of a continuous map sends the class of a smooth loop to the class of any
smooth loop with the composite parametrization.
Source: Hatcher, *Algebraic Topology*, §2.1 (functoriality of singular homology). -/
theorem b63g2_homologyMap_loopClass {C D : Type} [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (f : C(C, D)) (γ : b3_SmoothLoop ℂ C) (δ : b3_SmoothLoop ℂ D)
    (h : ∀ t : ℝ, f (γ.1 t) = δ.1 t) :
    homologyMap ℤ 1 (TopCat.ofHom f) (b6m_loopClass C γ) = b6m_loopClass D δ := by
  let p : C(UnitAddCircle, C) := ⟨γ.2.1.lift, by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact γ.2.2.continuous⟩
  let q : C(UnitAddCircle, D) := ⟨δ.2.1.lift, by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact δ.2.2.continuous⟩
  have heq : f.comp p = q := by
    ext t
    induction t using Quotient.inductionOn with
    | h t => exact h t
  change homologyMap ℤ 1 (TopCat.ofHom f)
    (((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℤ p)) = _
  rw [b6m_homologyMap_loopCycle, heq]
  rfl

/-- **Period naturality for a holomorphic group action**: an integral period comparison carries
the homology action of `g` to the pushforward `b4_latticeAct g`.
Source: Farkas–Kra, *Riemann Surfaces*, Ch. III; Birkenhake–Lange, §11.4;
`b6m_smooth_loopClass_surjective`, `b4_latticeAct_isPushforward`. -/
theorem b63g2_period_homologyMap (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (g : b4b_Group) (f : C(C, C)) (hf : ∀ x, f x = g • x) (x : b6m_H1 C) :
    P (homologyMap ℤ 1 (TopCat.ofHom f) x) = b4_latticeAct ℂ g (P x) := by
  obtain ⟨γ, rfl⟩ := b6m_smooth_loopClass_surjective C x
  rw [b63g2_homologyMap_loopClass f γ (b4cov_mapLoop _ (hG g) γ) (fun t ↦ hf _), hP, hP]
  exact (b4_latticeAct_isPushforward hG g γ (b4cov_mapLoop _ (hG g) γ) rfl).symm

/-- **Period naturality for the centre**: on a parameter fibre, an integral period comparison
carries `b63d_centre` to the central period action `b4b_centreAct`.
Source: G32 v0.16, §3.3; Birkenhake–Lange, §11.4; `b63g2_period_homologyMap`. -/
theorem b63g2_period_centre (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x))
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      Ps (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    Ps (b63d_centre b C hC V hV s x) =
      b4b_centreAct (b63l_parameterFibre b C V hV s) hG (Ps x) := by
  classical
  simp only [b63d_centre, b4b_centreAct, LinearMap.sum_apply, map_sum,
    AddMonoidHom.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs
  · exact b63g2_period_homologyMap _ hG Ps hP g _ (fun _ ↦ rfl) x
  · simp

end HodgeLean.Foundations.Program
