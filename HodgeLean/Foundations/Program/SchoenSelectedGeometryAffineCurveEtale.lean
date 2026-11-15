import HodgeLean.Adapters.NormalConeB4aGysinBridgeProofs
import HodgeLean.Foundations.Program.SchoenSelectedGeometryEvaluationLengthFinite
import HodgeLean.Foundations.Program.SchoenSelectedGeometryGenericSimple
import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteZeros
import HodgeLean.Foundations.Program.SchoenSelectedGeometryUnramifiedLength
import Mathlib.RingTheory.Smooth.Fiber

noncomputable section
set_option maxHeartbeats 400000
open Set Topology AlgebraicGeometry ComplexAlgHom HodgeLean.Adapters
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- A finite flat integral affine curve map locally injective on complex evaluations is etale over the origin.
Source: local fibre-length conservation on the original source and generic separability. -/
theorem s0_affine_curve_etale_at_zero
    {n : ℕ} (S : Type) [CommRing S] [IsDomain S] [Ring.DimensionLEOne S]
    [Algebra ℂ S] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Module.FinitePresentation (complexPolynomialRing n) S]
    [Module.Flat (complexPolynomialRing n) S]
    (w₀ : S →ₐ[ℂ] ℂ)
    (hzero : w₀.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) S) =
      MvPolynomial.aeval (0 : Fin n → ℂ)) [Filter.NeBot (𝓝[≠] w₀)]
    (N : Set (S →ₐ[ℂ] ℂ)) (hN : IsOpen N) (hwN : w₀ ∈ N)
    (hi : Set.InjOn (fun w : S →ₐ[ℂ] ℂ ↦
      w.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) S)) N) :
    letI : (RingHom.ker w₀).IsPrime := RingHom.ker_isPrime w₀
    Algebra.IsEtaleAt (complexPolynomialRing n) (RingHom.ker w₀) := by
  classical
  let A := complexPolynomialRing n
  let u₀ : A →ₐ[ℂ] ℂ := MvPolynomial.aeval (0 : Fin n → ℂ)
  letI : (RingHom.ker w₀).IsPrime := RingHom.ker_isPrime w₀
  obtain ⟨m, hm⟩ := s0_evaluation_length_finite u₀ w₀ hzero
  obtain ⟨N₀, hN₀, hwN₀, hcons⟩ :=
    a3b4a_gysin_flat_polynomial_source_length_conservation S (RingHom.ker w₀) w₀ rfl hzero m hm
  obtain ⟨δ, hδ, hsum⟩ := hcons (N ∩ N₀) (hN.inter hN₀) ⟨hwN, hwN₀⟩ inter_subset_right
  obtain ⟨f, hf, hsimp⟩ := s0_generic_simple_evaluations (B := A) (T := S)
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have hfin := s0_finite_zero_evaluations (k := ℂ) f hf
  let α : (S →ₐ[ℂ] ℂ) → (Fin n → ℂ) := fun w j ↦ w (algebraMap A S (MvPolynomial.X j))
  have hα : Continuous α := continuous_pi fun j ↦
    ComplexPoint.continuous_affineAlgebraHom_apply S (algebraMap A S (MvPolynomial.X j))
  have hα₀ : α w₀ = 0 := by
    funext j
    have hj := congrArg (fun v : A →ₐ[ℂ] ℂ ↦ v (MvPolynomial.X j)) hzero
    change w₀ (algebraMap A S (MvPolynomial.X j)) =
      (MvPolynomial.aeval (0 : Fin n → ℂ)) (MvPolynomial.X j) at hj
    rw [MvPolynomial.aeval_X] at hj
    exact hj
  let U := (N ∩ N₀) ∩ {w | ‖α w‖ < δ}
  have hU : IsOpen U := (hN.inter hN₀).inter (isOpen_lt hα.norm continuous_const)
  have hwU : w₀ ∈ U := ⟨⟨hwN, hwN₀⟩, by simp [hα₀, hδ]⟩
  letI : T2Space (S →ₐ[ℂ] ℂ) :=
    Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, DFunLike.coe_injective⟩
  obtain ⟨w, hw, hwf⟩ := (infinite_of_mem_nhds w₀ (hU.mem_nhds hwU)).exists_notMem_finite hfin
  obtain ⟨F, hF, hlen⟩ := hsum (α w) hw.2
  have hFeq : F = {w} := by
    apply Finset.ext
    intro z
    rw [Finset.mem_singleton, hF]
    constructor
    · intro hz
      apply hi hz.1.1 hw.1.1
      apply MvPolynomial.algHom_ext
      intro j
      exact hz.2 j
    · rintro rfl
      exact ⟨hw.1, fun _ ↦ rfl⟩
  have hbase : w.comp (IsScalarTower.toAlgHom ℂ A S) = MvPolynomial.aeval (α w) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, MvPolynomial.aeval_X]
    rfl
  have hone := hsimp (MvPolynomial.aeval (α w)) w hbase hwf
  rw [hFeq, Finset.sum_singleton, hone] at hlen
  letI : Algebra.IsUnramifiedAt A (RingHom.ker w₀) :=
    s0_unramified_of_evaluation_length_one u₀ w₀ hzero (hm.trans hlen.symm)
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (RingHom.ker w₀)

#print axioms s0_affine_curve_etale_at_zero
end HodgeLean.Foundations.Program
