import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.StandardEtaleHolomorphic

/-! # Holomorphic evaluation in arbitrary étale algebras

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Set Filter Topology HodgeLean.Foundations.Analytic
open AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexAlgHom
namespace AlgebraicGeometry.SingularCycles

/-- Continuous evaluations in an étale algebra are holomorphic over holomorphic base evaluations.
Source: SGA 1, Exposé XII, §1; standard étale neighbourhoods and holomorphic simple roots. -/
theorem etale_holomorphic_evaluation {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {U : Set M} (hU : IsOpen U)
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra A B] [IsScalarTower ℂ A B] [Algebra.Etale A B]
    (e : U → (B →ₐ[ℂ] ℂ)) (he : ∀ b, Continuous (fun y => e y b))
    (hbase : ∀ a, S.IsHolFun (fun y => e y (algebraMap A B a))) (b : B) :
    S.IsHolFun (fun y => e y b) := by
  apply holFun_of_local S
  intro x
  let q : Ideal B := RingHom.ker (e x).toRingHom
  haveI : q.IsPrime := RingHom.ker_isPrime (e x).toRingHom
  obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) q
  letI := hstd
  let L := Localization.Away s
  let P : StandardEtalePresentation A L := Nonempty.some inferInstance
  let W : Set U := {y | e y s ≠ 0}
  let V : Set M := Subtype.val '' W
  have hVU : V ⊆ U := fun y ⟨z, _, heq⟩ => heq ▸ z.2
  have hVo : IsOpen V := hU.isOpenMap_subtype_val W (isOpen_ne.preimage (he s))
  have hxV : (x : M) ∈ V := ⟨x, hs, rfl⟩
  refine ⟨V, hVU, hVo, hxV, ?_⟩
  have hnon : ∀ y : V, e ⟨y, hVU y.2⟩ s ≠ 0 := by
    intro y
    obtain ⟨v, hv, hvy⟩ := y.2
    have hy : (⟨y, hVU y.2⟩ : U) = v := Subtype.ext hvy.symm
    rw [hy]
    exact hv
  let v : V → nonvanishingAlgHom B s := fun y => ⟨e ⟨y, hVU y.2⟩, hnon y⟩
  let E : V → (L →ₐ[ℂ] ℂ) := fun y => nonvanishingAlgHomExtension B s (v y)
  have hvcont : Continuous v := by
    apply Continuous.subtype_mk
    rw [continuous_induced_rng]
    apply continuous_pi
    intro c
    exact (he c).comp (continuous_subtype_val.subtype_mk fun y => hVU y.2)
  have hE : Continuous E :=
    (localizationAwayAlgHomHomeomorph B s).continuous_symm.comp hvcont
  have hEa : ∀ a : A, S.IsHolFun (fun y : V => E y (algebraMap A L a)) := by
    intro a
    have heq : (fun y : V => E y (algebraMap A L a)) =
        (fun y : V => e ⟨y, hVU y.2⟩ (algebraMap A B a)) := by
      funext y
      rw [IsScalarTower.algebraMap_apply A B L]
      exact nonvanishingAlgHomExtension_algebraMap B s (v y) _
    rw [heq]
    exact anb_isHolFun_restrict S.atlas hVU (hbase a)
  have h := standardEtale_holomorphic_evaluation S hVo P E
    (fun c => (continuous_affineAlgebraHom_apply L c).comp hE) hEa (algebraMap B L b)
  have heq : (fun y : V => E y (algebraMap B L b)) =
      (fun y : V => e ⟨y, hVU y.2⟩ b) := by
    funext y
    exact nonvanishingAlgHomExtension_algebraMap B s (v y) b
  rw [heq] at h
  exact h

end AlgebraicGeometry.SingularCycles
