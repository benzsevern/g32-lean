import HodgeLean.Foundations.Program.RigidStartingSystemDefs

noncomputable section
namespace HodgeLean.Foundations.Program

variable {A : Type*} [Ring A] [Algebra ℂ A]

def b65r_commutator (R : A) : A →ₗ[ℂ] A where
  toFun T := R*T - T*R
  map_add' T U := by noncomm_ring
  map_smul' c T := by simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem b65r_commutator_cubic (R : A) (a b : ℂ) (hR : R*R = a • R + b • 1) :
    (b65r_commutator R)^3 = (a^2 + 4*b) • b65r_commutator R := by
  have hR3 : R*R*R = (a*a+b) • R + (a*b) • (1 : A) := by
    rw [hR]
    simp only [add_mul, smul_mul_assoc, one_mul, hR, smul_add, smul_smul]
    module
  ext T
  change R*(R*(R*T-T*R)-(R*T-T*R)*R) -
    (R*(R*T-T*R)-(R*T-T*R)*R)*R = (a^2+4*b) • (R*T-T*R)
  calc
    _ = (R*R*R)*T - 3 • ((R*R)*T*R) + 3 • (R*T*(R*R)) - T*(R*R*R) := by
      noncomm_ring
    _ = _ := by
      rw [hR3, hR]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        smul_add, smul_sub, smul_smul]
      module

theorem b65r_bijective_of_commutator_cubic [FiniteDimensional ℂ A]
    (R : A) (a b k : ℂ) (hR : R*R = a • R + b • 1)
    (hk : k ≠ 0) (hkc : k^2 ≠ a^2+4*b) :
    Function.Bijective (fun T : A ↦ k • T - (R*T-T*R)) := by
  let L : A →ₗ[ℂ] A := k • LinearMap.id - b65r_commutator R
  have hi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro T hT
    have hDT : b65r_commutator R T = k • T := by
      change k • T - (R*T-T*R) = 0 at hT
      exact (sub_eq_zero.mp hT).symm
    have hcube : ((b65r_commutator R)^3) T = k^3 • T := by
      change b65r_commutator R (b65r_commutator R (b65r_commutator R T)) = _
      simp only [hDT, map_smul, smul_smul]
      congr 1
      ring
    rw [b65r_commutator_cubic R a b hR] at hcube
    change (a^2+4*b) • b65r_commutator R T = k^3 • T at hcube
    rw [hDT, smul_smul] at hcube
    have he : ((a^2+4*b)*k-k^3) • T = 0 := by rw [sub_smul, hcube, sub_self]
    have hscalar : (a^2+4*b)*k-k^3 ≠ 0 := by
      have heq : (a^2+4*b)*k-k^3 = -(k*(k^2-(a^2+4*b))) := by ring
      rw [heq]
      exact neg_ne_zero.mpr (mul_ne_zero hk (sub_ne_zero.mpr hkc))
    exact (smul_eq_zero.mp he).resolve_left hscalar
  exact ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩

end HodgeLean.Foundations.Program
