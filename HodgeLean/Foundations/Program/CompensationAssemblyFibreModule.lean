import HodgeLean.Foundations.Program.CompensationAssemblyTorusModule
import HodgeLean.Foundations.Program.CompensationAssemblyFibreTrace

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_fibreTrace_cup_pullback (X Y : TopCat.{0}) (k i j : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (a : Cohomology ℚ X i)
    (b : Cohomology ℚ (TopCat.of (X × Y)) (j + k)) :
    cq_fibreTrace X Y k (i + j) e
      (cup (TopCat.of (X × Y)) (Nat.add_assoc i j k).symm
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) b) =
      cup X rfl a (cq_fibreTrace X Y k j e b) := by
  let f : TopCat.of (X × UnitAddTorus (Fin k)) ⟶ TopCat.of (X × Y) :=
    TopCat.ofHom ⟨((Homeomorph.refl X).prodCongr e).symm,
      ((Homeomorph.refl X).prodCongr e).symm.continuous⟩
  have hp : cohomologyMap ℚ i f
      (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) =
      cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a := by
    change (cohomologyMap ℚ i f ∘ₗ
      cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)) a = _
    rw [← cohomologyMap_comp]
    rfl
  change cq_productTorusTrace X k (i + j)
    (cohomologyMap ℚ ((i + j) + k) f
      (cup (TopCat.of (X × Y)) _
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) b)) =
    cup X rfl a (cq_productTorusTrace X k j (cohomologyMap ℚ (j + k) f b))
  rw [cohomologyMap_cup, hp]
  exact cq_productTorusTrace_cup_pullback X k i j a _

def cq_fibreIntegral (Y : TopCat.{0}) (k : ℕ) (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    Cohomology ℚ Y (0 + k) →ₗ[ℚ] ℚ :=
  (pointCohomologyZeroEquiv (R := ℚ)).toLinearMap ∘ₗ
    cq_fibreTrace (TopCat.of PUnit) Y k 0 e ∘ₗ
      cohomologyMap ℚ (0 + k) (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)

theorem cq_fibreTrace_pullback_snd (X Y : TopCat.{0}) (k : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (b : Cohomology ℚ Y (0 + k)) :
    cq_fibreTrace X Y k 0 e
      (cohomologyMap ℚ (0 + k) (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) b) =
      cq_fibreIntegral Y k e b • unit (R := ℚ) X := by
  let f : X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let c := cohomologyMap ℚ (0 + k)
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (PUnit × Y) ⟶ Y) b
  have hp : cohomologyMap ℚ (0 + k) (cq_fibreProductMap f Y) c =
      cohomologyMap ℚ (0 + k) (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) b := by
    change (cohomologyMap ℚ (0 + k) (cq_fibreProductMap f Y) ∘ₗ
      cohomologyMap ℚ (0 + k) (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)) b = _
    rw [← cohomologyMap_comp]
    rfl
  have hpt : cq_fibreTrace (TopCat.of PUnit) Y k 0 e c =
      cq_fibreIntegral Y k e b • unit (R := ℚ) (TopCat.of PUnit) := by
    apply (pointCohomologyZeroEquiv (R := ℚ)).injective
    rw [pointCohomologyZeroEquiv_smul_unit]
    rfl
  have ht := cq_fibreTrace_naturality f Y k 0 e c
  rw [hp, hpt, map_smul, cohomologyMap_unit] at ht
  exact ht

theorem cq_fibreTrace_cross (X Y : TopCat.{0}) (k i : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) (a : Cohomology ℚ X i)
    (b : Cohomology ℚ Y (0 + k)) :
    cq_fibreTrace X Y k (i + 0) e
      (cup (TopCat.of (X × Y)) (Nat.add_assoc i 0 k).symm
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)
        (cohomologyMap ℚ (0 + k) (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) b)) =
      cq_fibreIntegral Y k e b • a := by
  rw [cq_fibreTrace_cup_pullback, cq_fibreTrace_pullback_snd, map_smul, cup_one]

theorem cq_fibreTrace_surjective (X Y : TopCat.{0}) (k n : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    Function.Surjective (cq_fibreTrace X Y k n e) :=
  (cq_productTorusTrace_surjective X k n).comp
    (cohomologyHomeomorphEquiv ((Homeomorph.refl X).prodCongr e) (n + k)).surjective

theorem cq_fibreIntegral_surjective (Y : TopCat.{0}) (k : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k)) :
    Function.Surjective (cq_fibreIntegral Y k e) := by
  have hs : Function.Surjective
      (cohomologyMap ℚ (0 + k)
        (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (PUnit × Y) ⟶ Y)) := by
    change Function.Surjective
      (cohomologyHomeomorphEquiv (Homeomorph.uniqueProd PUnit Y) (0 + k)).symm
    exact (cohomologyHomeomorphEquiv (Homeomorph.uniqueProd PUnit Y) (0 + k)).symm.surjective
  exact (pointCohomologyZeroEquiv (R := ℚ)).surjective.comp
    ((cq_fibreTrace_surjective (TopCat.of PUnit) Y k 0 e).comp hs)

theorem cq_fibreIntegral_eq_scalar (Y : TopCat.{0}) (k : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k))
    (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ) (b : Cohomology ℚ Y (0 + k)) :
    cq_fibreIntegral Y k e b =
      I b * cq_fibreIntegral Y k e (I.symm 1) := by
  have hb : b = I b • I.symm 1 := by
    apply I.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    cq_fibreIntegral Y k e b = cq_fibreIntegral Y k e (I b • I.symm 1) :=
      congrArg (cq_fibreIntegral Y k e) hb
    _ = _ := (cq_fibreIntegral Y k e).map_smul (I b) (I.symm 1)

theorem cq_fibreIntegral_unit_ne_zero (Y : TopCat.{0}) (k : ℕ)
    (e : Y ≃ₜ UnitAddTorus (Fin k))
    (I : Cohomology ℚ Y (0 + k) ≃ₗ[ℚ] ℚ) :
    cq_fibreIntegral Y k e (I.symm 1) ≠ 0 := by
  obtain ⟨b, hb⟩ := cq_fibreIntegral_surjective Y k e 1
  intro hz
  have h := cq_fibreIntegral_eq_scalar Y k e I b
  rw [hb, hz, mul_zero] at h
  exact one_ne_zero h

end HodgeLean.Foundations.Program
