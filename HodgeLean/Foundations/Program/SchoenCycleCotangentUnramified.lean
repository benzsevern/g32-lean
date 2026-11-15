import HodgeLean.Foundations.Program.SchoenCycleAugmentedNakayama
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential TensorProduct
namespace HodgeLean.Foundations.Program

/-- A cotangent basis represented by elements from the source algebra forces a local augmented algebra with finite differentials to be unramified over that source.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; EGA IV, 17.11.1. -/
theorem s2e_formallyUnramified_of_source_cotangent_basis
    (k P R σ : Type*) [Field k] [CommRing P] [CommRing R] [IsLocalRing R]
    [Algebra k P] [Algebra k R] [Algebra P R] [IsScalarTower k P R]
    [Module.Finite R Ω[R⁄P]] (ε : R →ₐ[k] k)
    (c : σ → IsLocalRing.maximalIdeal R)
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal R).toCotangent (c i))
    (hbase : ∀ i, ∃ a : P, algebraMap P R a = (c i).val) :
    Algebra.FormallyUnramified P R := by
  letI : Algebra R k := ε.toAlgebra
  letI : IsScalarTower k R k := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  letI : Algebra P k := ((algebraMap R k).comp (algebraMap P R)).toAlgebra
  letI : IsScalarTower P R k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower k P k := .to₁₂₄ k P R k
  have hsR : Function.Surjective (algebraMap R k) := fun a => ⟨algebraMap k R a, ε.commutes a⟩
  have hsP : Function.Surjective (algebraMap P k) := by
    intro a
    refine ⟨algebraMap k P a, ?_⟩
    rw [← IsScalarTower.algebraMap_apply k P k]
    rfl
  letI : Algebra.FormallyUnramified P k :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId P k) hsP
  have hker : RingHom.ker (algebraMap R k) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal _ hsR
  let I := RingHom.ker (algebraMap R k)
  let cI : σ → I := fun i => ⟨(c i).val, by
    change (c i).val ∈ RingHom.ker (algebraMap R k)
    rw [hker]
    exact (c i).property⟩
  let E := (Ideal.Cotangent.equivOfEq _ _ hker.symm).restrictScalars k
  let B := b.map E
  let L := (kerCotangentToTensor P R k).restrictScalars k
  have hL : L = 0 := by
    apply B.ext
    intro i
    change kerCotangentToTensor P R k (E (b i)) = 0
    rw [hb]
    change kerCotangentToTensor P R k (I.toCotangent (cI i)) = 0
    rw [kerCotangentToTensor_toCotangent]
    obtain ⟨a, ha⟩ := hbase i
    rw [← ha, Derivation.map_algebraMap, tmul_zero]
  have hs : Function.Surjective L := by
    intro z
    apply (exact_kerCotangentToTensor_mapBaseChange P R k hsR z).mp
    exact Subsingleton.elim _ _
  letI : Subsingleton (TensorProduct R k Ω[R⁄P]) := subsingleton_of_forall_eq 0 (by
    intro z
    obtain ⟨y, rfl⟩ := hs z
    exact DFunLike.congr_fun hL y)
  exact ⟨s2e_augmented_nakayama k R Ω[R⁄P] ε inferInstance⟩

#print axioms s2e_formallyUnramified_of_source_cotangent_basis
end HodgeLean.Foundations.Program
