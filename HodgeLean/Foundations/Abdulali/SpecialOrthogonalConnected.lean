import HodgeLean.Foundations.Abdulali.OrthogonalReflectionGeneration
import HodgeLean.Foundations.Abdulali.ReflectionPairComponent
import Mathlib.Data.List.Induction

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations Matrix
namespace HodgeLean.Foundations.Abdulali

/-- Every standard bilinear isometry is a finite word of nonisotropic reflections. -/
theorem orthogonal_exists_reflection_word (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ).transpose * g = 1) :
    ∃ l : List {w : Fin n → ℂ // w ⬝ᵥ w ≠ 0},
      (l.map (fun w => orthogonalReflectionGL w.val w.property)).prod = g := by
  classical
  let W := {w : Fin n → ℂ // w ⬝ᵥ w ≠ 0}
  let R : W → Matrix.GeneralLinearGroup (Fin n) ℂ := fun w => orthogonalReflectionGL w.val w.property
  have hinv (w : W) : (R w)⁻¹ = R w := by apply Units.ext; rfl
  let H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
    { carrier := {g | ∃ l : List W, (l.map R).prod = g}
      one_mem' := ⟨[], rfl⟩
      mul_mem' := by
        rintro _ _ ⟨l, rfl⟩ ⟨k, rfl⟩
        exact ⟨l++k, by rw [List.map_append, List.prod_append]⟩
      inv_mem' := by
        rintro _ ⟨l, rfl⟩
        refine ⟨l.reverse, ?_⟩
        simp only [List.prod_inv_reverse, List.map_reverse, List.map_map,
          Function.comp_def, hinv] }
  apply orthogonal_reflections_generate n H ?_ g hg
  intro w hw
  exact ⟨[⟨w, hw⟩], by simp only [List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]; rfl⟩

/-- Even reflection words belong to the identity component of the actual
standard special orthogonal group. -/
theorem even_reflection_word_mem_component (n : ℕ)
    (l : List {w : Fin n → ℂ // w ⬝ᵥ w ≠ 0}) (he : Even l.length) :
    (l.map (fun w => orthogonalReflectionGL w.val w.property)).prod ∈
      g1_identityComponent (specialOrthogonalMatrixGroup (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  let C := g1_identityComponentSubgroup
    (specialOrthogonalMatrixGroup (1 : Matrix (Fin n) (Fin n) ℂ))
  suffices h : (l.map (fun w : {w : Fin n → ℂ // w ⬝ᵥ w ≠ 0} =>
    orthogonalReflectionGL w.val w.property)).prod ∈ C from h
  induction l using List.twoStepInduction with
  | nil => exact C.one_mem
  | singleton w => norm_num at he
  | cons_cons w u l ih _ =>
    have hel : Even l.length := by simpa [List.length_cons, Nat.even_add_one] using he
    have hp : orthogonalReflectionGL w.val w.property *
        orthogonalReflectionGL u.val u.property ∈ C :=
      reflection_pair_mem_component w.val u.val w.property u.property
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using C.mul_mem hp (ih hel)

/-- The standard complex special orthogonal matrix group is Zariski connected
in every dimension, including zero and one. -/
theorem specialOrthogonal_standard_isConnected (n : ℕ) :
    g1_IsConnected (specialOrthogonalMatrixGroup (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  classical
  let G := specialOrthogonalMatrixGroup (1 : Matrix (Fin n) (Fin n) ℂ)
  letI := g1_zariski ℂ n
  have hsub : (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) ⊆
      g1_identityComponent G := by
    intro g hg
    obtain ⟨horth, hdet⟩ := (mem_specialOrthogonalMatrixGroup 1 g).mp hg
    rw [mul_one] at horth
    obtain ⟨l, hl⟩ := orthogonal_exists_reflection_word n g horth
    have hd : ∀ k : List {w : Fin n → ℂ // w ⬝ᵥ w ≠ 0},
        ((k.map (fun w => orthogonalReflectionGL w.val w.property)).prod :
          Matrix (Fin n) (Fin n) ℂ).det = (-1 : ℂ)^k.length := by
      intro k
      induction k with
      | nil => simp only [List.map_nil, List.prod_nil, Units.val_one, Matrix.det_one,
          List.length_nil, pow_zero]
      | cons w k ih =>
        have hr : (orthogonalReflectionGL w.val w.property :
            Matrix (Fin n) (Fin n) ℂ).det = -1 := orthogonalReflectionMatrix_det w.val w.property
        simp only [List.map_cons, List.prod_cons, Units.val_mul, Matrix.det_mul,
          hr, List.length_cons, pow_succ, ih]
        ring
    have he : Even l.length := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp
      ((hd l).symm.trans (by rw [hl]; exact hdet))
    rw [← hl]
    exact even_reflection_word_mem_component n l he
  have heq : g1_identityComponent G = (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :=
    Set.Subset.antisymm (connectedComponentIn_subset _ _) hsub
  change IsConnected (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr G.carrier.one_mem

end HodgeLean.Foundations.Abdulali
