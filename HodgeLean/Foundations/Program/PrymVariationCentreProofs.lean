import HodgeLean.Foundations.Program.PrymVariationCentreEigenRanks
import HodgeLean.Foundations.Program.PrymVariationCentreDimensions
import HodgeLean.Foundations.Program.PrymVariationCentreTransport
import HodgeLean.Foundations.Program.PrymVariationCentreRange
import HodgeLean.Foundations.Program.PrymVariationCentrePeriod
import HodgeLean.Foundations.Program.PrymVariationCentrePolynomial
import HodgeLean.Foundations.Program.PrymVariationCentreParameterMultiplicity
import HodgeLean.Foundations.Program.PrymVariationCentreDistinct
import HodgeLean.Foundations.Program.PrymVariationCentreConjugateProjector
import HodgeLean.Foundations.Program.PrymVariationCentreOrbit

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63d_centre_range_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    ∃ Z : b63l_parameterLattice b C hC V hV t →ₗ[ℤ] b63l_parameterLattice b C hC V hV t,
      ∀ x, (Z x).val = b63d_centre b C hC V hV t x.val := by
  exact b63d_centre_range_helper b C hC V hV t

theorem b63d_prymOperator_sq_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    ∃ J : b63l_parameterLattice b C hC V hV t →ₗ[ℤ] b63l_parameterLattice b C hC V hV t,
      (∀ x, (J x).val = b63d_operator b C hC V hV t x.val) ∧
      ∀ x, J (J x) = (-3 : ℤ) • x := by
  rcases b63d_centre_range_helper b C hC V hV t with ⟨Z, hZ⟩
  let J : b63l_parameterLattice b C hC V hV t →ₗ[ℤ]
      b63l_parameterLattice b C hC V hV t := LinearMap.id + 2 • Z
  refine ⟨J, ?_, ?_⟩
  · intro x
    simp [J, b63d_operator, hZ]
  · intro x
    apply Subtype.ext
    let D := b63l_parameterFibre b C V hV t
    let hD : ∀ g : b4b_Group, Continuous (fun q : D ↦ g • q) :=
      fun g ↦ (hG g).continuous
    let T := b63d_homologyAct D hD b63d_scalarElement
    have hcentre (q : b6m_H1 D) : b63d_centre b C hC V hV t q = T q := by
      classical
      simp only [b63d_centre]
      simp_rw [b63d_scalarElement_unique]
      rw [Fintype.sum_ite_eq']
      rfl
    have hp : T (T x.val) + T x.val + x.val = 0 := by
      exact b63d_homology_saturation_polynomial D hG x.val x.property
    have hJ (u : b63l_parameterLattice b C hC V hV t) :
        (J u).val = u.val + 2 • T u.val := by
      dsimp only [J]
      simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply]
      change u.val + 2 • (Z u).val = _
      rw [hZ, hcentre]
    change ↑(J (J x)) = (-3 : ℤ) • x.val
    rw [hJ, hJ]
    change (x.val + 2 • T x.val) + 2 • T (x.val + 2 • T x.val) = (-3 : ℤ) • x.val
    have hT2 : T (2 • T x.val) = 2 • T (T x.val) := map_nsmul T 2 (T x.val)
    rw [map_add, hT2]
    rw [← sub_eq_zero]
    calc
      (x.val + 2 • T x.val + 2 • (T x.val + 2 • T (T x.val))) -
          (-3 : ℤ) • x.val = 4 • (T (T x.val) + T x.val + x.val) := by abel
      _ = 0 := by rw [hp, smul_zero]

theorem b63d_prymOperator_filtration_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x)) :
    ∃ (Z J : b63l_periodLattice (b63l_parameterFibre b C V hV t) →ₗ[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)),
      (∀ x, (Z x).val = b4b_centreAct (b63l_parameterFibre b C V hV t) hG x.val) ∧
      J = LinearMap.id + 2 • Z ∧
      (∀ x, (J x).val = b63d_periodOperator (b63l_parameterFibre b C V hV t) hG x.val) ∧
      b63l_periodF (b63l_parameterFibre b C V hV t) ≤ (b63l_periodF (b63l_parameterFibre b C V hV t)).comap (J.baseChange ℂ) := by
  exact b63d_period_operator_filtration (b63l_parameterFibre b C V hV t) hG

theorem b63d_periodOperator_sq_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (x : b63l_periodLattice (b63l_parameterFibre b C V hV t)) :
    b63d_periodOperator (b63l_parameterFibre b C V hV t) hG (b63d_periodOperator (b63l_parameterFibre b C V hV t) hG x.val) = (-3 : ℤ) • x.val := by
  let D := b63l_parameterFibre b C V hV t
  let T := b4_latticeAct ℂ (C := D) b63d_scalarElement
  have hcentre (y : b3_periodLattice ℂ D) : b4b_centreAct D hG y = T y := by
    classical
    simp only [b4b_centreAct, AddMonoidHom.finsetSum_apply]
    simp_rw [b63d_scalarElement_unique]
    calc
      (∑ g : b4b_Group, (if g = b63d_scalarElement then
          b4_latticeAct ℂ g else 0) y) =
          ∑ g : b4b_Group, if g = b63d_scalarElement then
            b4_latticeAct ℂ g y else 0 := by
              apply Finset.sum_congr rfl
              intro g hg
              split <;> rfl
      _ = T y := by rw [Fintype.sum_ite_eq']
  have hp : T (T x.val) + T x.val + x.val = 0 :=
    b63d_period_saturation_polynomial D hG x.val x.property
  simp only [b63d_periodOperator, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply]
  change x.val + 2 • b4b_centreAct D hG x.val +
      2 • b4b_centreAct D hG (x.val + 2 • b4b_centreAct D hG x.val) =
    (-3 : ℤ) • x.val
  rw [hcentre, hcentre]
  change (x.val + 2 • T x.val) + 2 • T (x.val + 2 • T x.val) =
    (-3 : ℤ) • x.val
  rw [map_add, map_nsmul T 2 (T x.val)]
  rw [← sub_eq_zero]
  calc
    (x.val + 2 • T x.val + 2 • (T x.val + 2 • T (T x.val))) -
        (-3 : ℤ) • x.val = 4 • (T (T x.val) + T x.val + x.val) := by abel
    _ = 0 := by rw [hp, smul_zero]

theorem b63d_chevalleyWeil_hodge_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
    (Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (g32h_omega)) : ℝ) = g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    (Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (star g32h_omega)) : ℝ) =
      (g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) : ℝ) - g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (g32h_omega)) = 3 ∧
    Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) hG (star g32h_omega)) = 3 := by
  have hm := b63d_parameter_multiplicities b C hC V hV t hG hb f hf hs hgal hbranch hrot
  have he := b63d_saturated_eigen_ranks (b63l_parameterFibre b C V hV t) hG hm.2
  refine ⟨?_, ?_, he.1, he.2⟩
  · exact (congrArg (fun n : ℕ ↦ (n : ℝ)) he.1).trans b63d_root_holoCW.symm
  · have hr : (g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) : ℝ) -
        g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) = 3 := by
      rw [b63d_root_multCW, b63d_root_holoCW]
      norm_num
    exact (congrArg (fun n : ℕ ↦ (n : ℝ)) he.2).trans hr.symm

theorem b63d_lattice_rank_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV t)) ∧
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_periodLattice (b63l_parameterFibre b C V hV t))) := by
  let D := b63l_parameterFibre b C V hV t
  letI : Module.Finite ℤ (b3_periodLattice ℂ D) := b3_periodLattice_finite (by simp)
  letI : Module.Free ℤ (b3_periodLattice ℂ D) := b3_periodLattice_free
  letI : Module.Finite ℤ (b63l_periodLattice D) := inferInstance
  letI : Module.Free ℤ (b63l_periodLattice D) := inferInstance
  have hm := b63d_parameter_multiplicities b C hC V hV t hG hb f hf hs hgal hbranch hrot
  have hd := b63d_saturated_dimensions D hG hm.2
  let β := Module.finBasisOfFinrankEq ℤ (b63l_periodLattice D) hd.1
  obtain ⟨P, hP, hOp, E, hE⟩ := b63l_period_image_comparison D hG
  let E' : b63l_parameterLattice b C hC V hV t ≃ₗ[ℤ] b63l_periodLattice D := E
  exact ⟨⟨β.map E'.symm⟩, ⟨β⟩⟩

theorem b63d_dim_eq_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
    (Module.finrank ℂ ((ℂ ⊗[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)) ⧸ (b63l_periodF (b63l_parameterFibre b C V hV t))) : ℤ) =
      g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) ∧
    Module.finrank ℂ ((ℂ ⊗[ℤ] b63l_periodLattice (b63l_parameterFibre b C V hV t)) ⧸ (b63l_periodF (b63l_parameterFibre b C V hV t))) = 6 ∧
    Module.finrank ℂ (b63l_periodF (b63l_parameterFibre b C V hV t)) = 6 := by
  have hm := b63d_parameter_multiplicities b C hC V hV t hG hb f hf hs hgal hbranch hrot
  have hd := b63d_saturated_dimensions (b63l_parameterFibre b C V hV t) hG hm.2
  refine ⟨?_, hd.2.2, hd.2.1⟩
  rw [hd.2.2, b63d_root_multCW]
  rfl

theorem b63d_centre_transport_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (s : V) (x : b6m_H1 (b63l_parameterFibre b C V hV s)) :
    b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩)
      (b63d_centre b C hC V hV s x) =
    b63d_centre b C hC V hV t
      (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩) x) := by
  exact b63d_centre_transport_helper b C hC V hV t s x

end HodgeLean.Foundations.Program
