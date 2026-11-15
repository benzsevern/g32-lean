import HodgeLean.Foundations.Program.TorusAlgebraizationB54Charts

noncomputable section
namespace HodgeLean.Foundations.Program
open HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] {r : A} (hr : r ∈ G 1)

def b54_awayComponent (n : ℕ) : G n →+ Away G r where
  toFun a := Away.mk G hr n a (by simpa using a.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_zero]
    change Localization.mk (0 : A) (⟨r ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers r) = 0
    exact Localization.mk_zero _
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add]
    exact (Localization.add_mk_self (M := Submonoid.powers r)
      (a : A) ⟨r ^ n, ⟨n, rfl⟩⟩ (b : A)).symm

def b54_awayNormalize : A →+* Away G r :=
  (DirectSum.toSemiring (b54_awayComponent G hr)
    (by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_one]
      change Localization.mk (1 : A) ⟨r ^ 0, _⟩ = 1
      simp only [pow_zero]
      exact Localization.mk_one)
    (by
      intro i j a b
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_mul]
      change Localization.mk ((a : A) * (b : A)) ⟨r ^ (i + j), _⟩ =
        Localization.mk (a : A) ⟨r ^ i, _⟩ * Localization.mk (b : A) ⟨r ^ j, _⟩
      rw [Localization.mk_mul]
      congr 1
      exact Subtype.ext (pow_add r i j))).comp (DirectSum.decomposeRingEquiv G).toRingHom

theorem b54_awayNormalize_homogeneous (n : ℕ) (a : A) (ha : a ∈ G n) :
    b54_awayNormalize G hr a = Away.mk G hr n a (by simpa using ha) := by
  simp only [b54_awayNormalize, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [show (DirectSum.decomposeRingEquiv G) a = DirectSum.of _ n ⟨a, ha⟩ from
    DirectSum.decompose_of_mem G ha, DirectSum.toSemiring_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem b54_awayNormalize_fromZero (a : G 0) :
    b54_awayNormalize G hr (algebraMap (G 0) A a) = fromZeroRingHom G (.powers r) a := by
  change b54_awayNormalize G hr (a : A) = _
  rw [b54_awayNormalize_homogeneous G hr 0 a a.property]
  apply HomogeneousLocalization.val_injective
  simp [Away.val_mk, fromZeroRingHom, HomogeneousLocalization.val_mk,
    NumDenSameDeg.embedding]

theorem b54_awayNormalize_self : b54_awayNormalize G hr r = 1 := by
  rw [b54_awayNormalize_homogeneous G hr 1 r hr]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one, Away.val_mk]
  simpa only [pow_one] using
    (Localization.mk_self (⟨r, ⟨1, pow_one r⟩⟩ : Submonoid.powers r))

end HodgeLean.Foundations.Program
