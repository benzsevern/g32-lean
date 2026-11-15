import HodgeLean.Foundations.Program.SchoenCycleResidueSlice

/-! # Intersections of the paired residue hyperplanes
Restriction to a subset of the residue coordinates gives the actual linear
map whose kernel parametrizes their intersection.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

/-- Restrict the residue coefficients to the selected pairs.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
def s2e_residueCoordinateRestriction (M : Type*) [AddCommGroup M] [Module ℂ M]
    {r : ℕ} (T : Finset (Fin r)) :
    (M × (Fin r → ℂ)) →ₗ[ℂ] (T → ℂ) :=
  (LinearMap.pi (fun t : T => (LinearMap.proj t.val : (Fin r → ℂ) →ₗ[ℂ] ℂ))).comp
    (LinearMap.snd ℂ M (Fin r → ℂ))

example (M : Type*) [AddCommGroup M] [Module ℂ M] {r : ℕ}
    (T : Finset (Fin r)) (v : M) (a : Fin r → ℂ) (t : T) :
    s2e_residueCoordinateRestriction M T (v, a) t = a t.val := rfl

/-- Every assignment of the selected residue coordinates extends to the
whole coefficient space. -/
theorem s2e_residueCoordinateRestriction_surjective
    (M : Type*) [AddCommGroup M] [Module ℂ M] {r : ℕ} (T : Finset (Fin r)) :
    Function.Surjective (s2e_residueCoordinateRestriction M T) := by
  classical
  intro b
  let a : Fin r → ℂ := fun i => if hi : i ∈ T then b ⟨i, hi⟩ else 0
  refine ⟨(0, a), ?_⟩
  funext t
  change a t.val = b t
  dsimp only [a]
  rw [dif_pos t.property]

/-- The selected residue hyperplanes impose exactly one independent linear
condition per selected pair. -/
theorem s2e_residueCoordinateRestriction_kernel_finrank
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    {r : ℕ} (T : Finset (Fin r)) :
    Module.finrank ℂ (LinearMap.ker (s2e_residueCoordinateRestriction M T)) + T.card =
      Module.finrank ℂ M + r := by
  have h := LinearMap.finrank_range_add_finrank_ker (s2e_residueCoordinateRestriction M T)
  rw [LinearMap.range_eq_top.mpr (s2e_residueCoordinateRestriction_surjective M T),
    finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
    Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

/-- The kernel of the coordinate restriction consists exactly of coefficient
vectors vanishing on the selected pairs. -/
theorem s2e_residueCoordinateRestriction_mem_kernel
    (M : Type*) [AddCommGroup M] [Module ℂ M] {r : ℕ}
    (T : Finset (Fin r)) (v : M) (a : Fin r → ℂ) :
    (v, a) ∈ LinearMap.ker (s2e_residueCoordinateRestriction M T) ↔
      ∀ i ∈ T, a i = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext t
    exact h t.val t.property

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinate kernel imposes vanishing of the actual differential
residues at exactly the selected points. -/
theorem s2e_selected_residue_vanishing_iff
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (T : Finset (Fin r)) (θ : b3_HolForm E C) (a : Fin r → ℂ) :
    (θ, a) ∈ LinearMap.ker (s2e_residueCoordinateRestriction (b3_HolForm E C) T) ↔
      ∀ j ∈ T, b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (x j) = 0 := by
  rw [s2e_residueCoordinateRestriction_mem_kernel]
  simp only [s2e_pairedDifferentialLinear_residue_coordinate hE w x 1 hres θ a, mul_one]

/-- The selected intersections inside the actual differential family have
the same independent codimension as their residue parameter kernels. -/
theorem s2e_selected_differential_intersection_finrank
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (T : Finset (Fin r)) :
    Module.finrank ℂ ((LinearMap.ker
      (s2e_residueCoordinateRestriction (b3_HolForm E C) T)).map
        (s2e_pairedDifferentialLinear hE w)) + T.card =
      Module.finrank ℂ (b3_HolForm E C) + r := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI := b3Forms_holForm_finiteDimensional (C := C) hE
  rw [← (Submodule.equivMapOfInjective (s2e_pairedDifferentialLinear hE w)
    (s2e_pairedDifferentialLinear_injective hE w x hres)
    (LinearMap.ker (s2e_residueCoordinateRestriction (b3_HolForm E C) T))).finrank_eq]
  exact s2e_residueCoordinateRestriction_kernel_finrank (b3_HolForm E C) T

/-- Under the selected genus equation, the linear residue intersection has
the expected vector-space dimension preceding projectivization. -/
theorem s2e_selected_differential_intersection_dimension
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (T : Finset (Fin r)) :
    Module.finrank ℂ ((LinearMap.ker
      (s2e_residueCoordinateRestriction (b3_HolForm E C) T)).map
        (s2e_pairedDifferentialLinear hE w)) = k + 1 - T.card := by
  have h := s2e_selected_differential_intersection_finrank hE w x hres T
  omega

/-- More than `k` selected residue conditions leave only the zero
differential under the selected genus equation. -/
theorem s2e_selected_differential_intersection_eq_bot
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (T : Finset (Fin r)) (hT : k < T.card) :
    (LinearMap.ker (s2e_residueCoordinateRestriction (b3_HolForm E C) T)).map
      (s2e_pairedDifferentialLinear hE w) = ⊥ := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI := b3Forms_holForm_finiteDimensional (C := C) hE
  have h := s2e_residueCoordinateRestriction_kernel_finrank (b3_HolForm E C) T
  have hdim : Module.finrank ℂ
      (LinearMap.ker (s2e_residueCoordinateRestriction (b3_HolForm E C) T)) = 0 := by omega
  rw [Submodule.finrank_eq_zero.mp hdim, Submodule.map_bot]

/-- Every intersection of at most `k` residue hyperplanes contains an
actual nonzero differential from the selected family. -/
theorem s2e_selected_differential_intersection_nonzero
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (T : Finset (Fin r)) (hT : T.card ≤ k) :
    ∃ f : TangentBundle 𝓘(ℂ, E) C → ℂ,
      f ∈ (LinearMap.ker (s2e_residueCoordinateRestriction (b3_HolForm E C) T)).map
        (s2e_pairedDifferentialLinear hE w) ∧ f ≠ 0 := by
  let L := (LinearMap.ker (s2e_residueCoordinateRestriction (b3_HolForm E C) T)).map
    (s2e_pairedDifferentialLinear hE w)
  have hdim : Module.finrank ℂ L = k + 1 - T.card :=
    s2e_selected_differential_intersection_dimension hE w x hres hgenus T
  have hpos : 0 < Module.finrank ℂ L := by rw [hdim]; omega
  letI : Nontrivial L := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨f, hf⟩ := exists_ne (0 : L)
  refine ⟨f.val, f.property, ?_⟩
  intro hz
  apply hf
  apply Subtype.ext
  change f.val = 0
  exact hz

end HodgeLean.Foundations.Program
