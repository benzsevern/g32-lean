import HodgeLean.Foundations.Program.SchoenCycleC1FinalWeightedIdeal
import HodgeLean.Foundations.Program.SchoenCycleC1WeightedResidueEtale

/-! # Weighted final branch ideals in represented local rings -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The final weighted identity persists in any represented local ring. -/
theorem s2e_c1_final_weighted_ideal_power_map
    (k m : ℕ) (B : Fin (k + 1) → Scheme)
    (b : ∀ j : Fin k, B j.succ ⟶ B j.castSucc)
    (c : ∀ j, B (Fin.last k) ⟶ B j)
    (hc : c (Fin.last k) = 𝟙 _) (hb : ∀ j : Fin k, c j.succ ≫ b j = c j.castSucc)
    {J : Type*} [Fintype J]
    (D : ∀ j, J → (B j).IdealSheafData)
    (E : ∀ j : Fin k, (B j.castSucc).IdealSheafData) (n : J → ℕ)
    (hstep : ∀ j : Fin k,
      (∏ t, ((D j.castSucc t).comap (b j)) ^ n t) =
        (∏ t, D j.succ t ^ n t) * ((E j).comap (b j)) ^ m)
    (U : (B (Fin.last k)).affineOpens)
    (g : J → Γ(B (Fin.last k), U)) (eE : Fin k → Γ(B (Fin.last k), U))
    (hg : ∀ t, ((D 0 t).comap (c 0)).ideal U = Ideal.span {g t})
    (hE : ∀ j, ((E j).comap (c j.castSucc)).ideal U = Ideal.span {eE j})
    (hfinal : ∀ t, (D (Fin.last k) t).ideal U = ⊤)
    {R : Type*} [CommRing R] (φ : Γ(B (Fin.last k), U) →+* R) :
    (∏ t, (Ideal.span {φ (g t)}) ^ n t) =
      (Ideal.span {∏ j, φ (eE j)}) ^ m := by
  have H := congrArg (Ideal.map φ)
    (s2e_c1_final_weighted_ideal_power k m B b c hc hb D E n hstep U g eE hg hE hfinal)
  rw [show Ideal.map φ (∏ t, Ideal.span {g t} ^ n t) =
      ∏ t, Ideal.map φ (Ideal.span {g t} ^ n t) from
      map_prod (Ideal.mapHom φ) _ _] at H
  simpa only [ Ideal.map_pow, Ideal.map_span, Set.image_singleton,
    map_prod] using H

/-- Weighted ideal identities on an affine chart can be used in a factorial
represented ring without requiring the affine section ring to be factorial. -/
theorem s2e_c1_integralClosure_etale_of_mapped_weighted_ideal_power
    {A R K L J : Type*} [CommRing A] [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [IsIntegrallyClosed R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.IsSeparable K L] [Fintype J]
    (φ : A →+* R) (g : J → A) (n : J → ℕ)
    (hg : ∀ j, φ (g j) ≠ 0) (E : A)
    (P : PowerBasis K L) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank K L = m) (d : Rˣ) (hd : (d : R) = (m : R))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hz : P.gen ^ m = algebraMap R L a / algebraMap R L b)
    (hv : ∀ p : R, Prime p → Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      (∑ j, (n j : ℤ) * ((emultiplicity p (φ (g j))).toNat : ℤ)))
    (hI : (∏ j, (Ideal.span {g j}) ^ n j) = (Ideal.span {E}) ^ m) :
    Algebra.Etale R (integralClosure R L) := by
  have H := congrArg (Ideal.map φ) hI
  rw [show Ideal.map φ (∏ j, Ideal.span {g j} ^ n j) =
      ∏ j, Ideal.map φ (Ideal.span {g j} ^ n j) from
      map_prod (Ideal.mapHom φ) _ _] at H
  simp only [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at H
  exact s2e_c1_integralClosure_etale_of_weighted_ideal_power P m hm hdim d hd
    a b ha hb hz (fun j => φ (g j)) n hg hv (φ E) H

end HodgeLean.Foundations.Program
