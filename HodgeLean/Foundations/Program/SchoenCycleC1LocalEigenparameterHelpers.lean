import HodgeLean.Foundations.Program.SchoenCycleC1LocalResidueHelpers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.GroupWithZero.Associated

/-! # Regular local parameters with exact finite stabilizer characters -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open scoped BigOperators

/-- The finite character sum of actual local algebra automorphisms is an
exact eigenvector for the specified character. -/
theorem s2e_c1_finite_character_sum_equivariant
    {k R G : Type*} [Field k] [CommRing R] [Algebra k R]
    [Group G] [Fintype G] (a : G →* (R ≃ₐ[k] R)) (χ : G →* kˣ)
    (t : R) (h : G) :
    a h (∑ g : G, ((χ g : k)⁻¹) • a g t) =
      (χ h : k) • ∑ g : G, ((χ g : k)⁻¹) • a g t := by
  have he (g : G) : a h (((χ g : k)⁻¹) • a g t) =
      (χ h : k) • (((χ (h * g) : k)⁻¹) • a (h * g) t) := by
    rw [map_smul, map_mul a, map_mul χ, Units.val_mul, smul_smul]
    change (χ g : k)⁻¹ • a h (a g t) =
      ((χ h : k) * ((χ h : k) * (χ g : k))⁻¹) • a h (a g t)
    congr 1
    rw [mul_inv_rev, mul_left_comm, mul_inv_cancel₀ (χ h).ne_zero, mul_one]
  rw [map_sum]
  calc
    (∑ g : G, a h (((χ g : k)⁻¹) • a g t)) =
        ∑ g : G, (χ h : k) • (((χ (h * g) : k)⁻¹) • a (h * g) t) :=
      Finset.sum_congr rfl (fun g _ => he g)
    _ = ∑ g : G, (χ h : k) • (((χ g : k)⁻¹) • a g t) :=
      Function.Bijective.sum_comp (Group.mulLeft_bijective h)
        (fun g : G => (χ h : k) • (((χ g : k)⁻¹) • a g t))
    _ = _ := Finset.smul_sum.symm

/-- Finite character averaging changes a parameter by a unit and makes
its residue character an exact identity in the local ring. -/
theorem s2e_c1_local_eigenparameter_of_residue_character
    {k R G : Type*} [Field k] [CharZero k] [CommRing R] [IsLocalRing R] [Algebra k R]
    [Group G] [Fintype G] (φ : R →ₐ[k] k) (a : G →* (R ≃ₐ[k] R)) (χ : G →* kˣ)
    (t : R) (hmult : ∀ g : G, ∃ v : R, a g t = t * v ∧ φ v = (χ g : k)) :
    ∃ u : Rˣ, ∀ g : G, a g (t * (u : R)) = (χ g : k) • (t * (u : R)) := by
  choose v hv hφv using hmult
  let w : R := ∑ g : G, ((χ g : k)⁻¹) • v g
  have hφw : φ w = (Fintype.card G : k) := by
    simp [w, hφv, smul_eq_mul]
  have hs : Function.Surjective φ.toRingHom := fun c =>
    ⟨algebraMap k R c, by
      change φ (algebraMap k R c) = c
      simpa only [Algebra.algebraMap_self_apply] using φ.commutes c⟩
  letI : IsLocalHom φ.toRingHom := IsLocalHom.of_surjective φ.toRingHom hs
  have hw : IsUnit w := isUnit_of_map_unit φ.toRingHom w (by
    apply isUnit_iff_ne_zero.mpr
    change φ w ≠ 0
    rw [hφw]
    exact_mod_cast Fintype.card_ne_zero (α := G))
  have hsum : t * w = ∑ g : G, ((χ g : k)⁻¹) • a g t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    rw [mul_smul_comm, ← hv g]
  refine ⟨hw.unit, ?_⟩
  intro g
  rw [hw.unit_spec, hsum]
  exact s2e_c1_finite_character_sum_equivariant a χ t g

/-- Every finite scalar-preserving action on a characteristic-zero DVR
has an exact regular eigenparameter, with its character constructed from
actual parameter multipliers. -/
theorem s2e_c1_dvr_finite_action_eigenparameter
    {k R G : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra k R] [Group G] [Fintype G]
    (φ : R →ₐ[k] k) (a : G →* (R ≃ₐ[k] R)) (t : R) (ht : Irreducible t) :
    ∃ χ : G →* kˣ, ∃ u : Rˣ,
      (∀ g : G, a g (t * (u : R)) = (χ g : k) • (t * (u : R))) ∧
      ∀ g : G, ∃ v : Rˣ, a g t = t * (v : R) ∧ φ (v : R) = (χ g : k) := by
  have hex (g : G) : ∃ v : Rˣ, a g t = t * (v : R) := by
    have hg : Irreducible (a g t) := (MulEquiv.irreducible_iff (a g).toMulEquiv).mpr ht
    obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible R ht hg
    exact ⟨v, hv.symm⟩
  choose v hv using hex
  have hv1 : (v 1 : R) = 1 := by
    apply mul_left_cancel₀ ht.ne_zero
    rw [← hv 1, map_one]
    simp
  have hvmul (g h : G) : (v (g * h) : R) = (v g : R) * a g (v h : R) := by
    apply mul_left_cancel₀ ht.ne_zero
    rw [← hv (g * h), map_mul a]
    change a g (a h t) = t * ((v g : R) * a g (v h : R))
    rw [hv h, map_mul, hv g, mul_assoc]
  let χ : G →* kˣ := {
    toFun g := Units.map φ.toMonoidHom (v g)
    map_one' := by
      apply Units.ext
      change φ (v 1 : R) = 1
      rw [hv1, map_one]
    map_mul' := by
      intro g h
      apply Units.ext
      change φ (v (g * h) : R) = φ (v g : R) * φ (v h : R)
      rw [hvmul, map_mul, s2e_c1_local_residue_fixed_by_algebraEquiv φ (a g)] }
  have hχ (g : G) : φ (v g : R) = (χ g : k) := rfl
  obtain ⟨u, hu⟩ := s2e_c1_local_eigenparameter_of_residue_character φ a χ t
    (fun g => ⟨(v g : R), hv g, hχ g⟩)
  exact ⟨χ, u, hu, fun g => ⟨v g, hv g, hχ g⟩⟩

end HodgeLean.Foundations.Program
