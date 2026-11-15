import HodgeLean.Foundations.Program.UniversalFamilyCoverProofs

/-! # B6-0c: Landherr coverage and uniformization

The implication from membership to coverage uses Hermitian classification, period
realization and algebraization of rational Hodge markings. The comparison retains the
specified marking after multiplication by a positive integer.
HC no distance; AV milestone no distance. Analytic variation is outside this interface.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- The geometric Hermitian form has signature (3,3).
Source: van Geemen, LNM 1594, §§5.2–5.3. -/
theorem b60c_signature (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    hermSignature (b60c_H P hP) = (3, 3) :=
  b60c_signature_aux P hP

example (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    hermSignature (b60c_H P hP) = (3, 3) := b60c_signature P hP

/-- Restricted Landherr classification for forms arising from members.
Source: Landherr, Abh. Math. Sem. Hamburg 11 (1936), 245–248; van Geemen, LNM 1594, §5.4. -/
theorem b60c_landherr (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ e : b60c_V P ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, b60_H (e x) (e y) = b60c_H P hP x y :=
  b60c_landherr_aux P hP

example (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ e : b60c_V P ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, b60_H (e x) (e y) = b60c_H P hP x y := b60c_landherr P hP

/-- A member has a polarized K-linear rational Hodge marking at a domain point.
Source: van Geemen, LNM 1594, §§5.7–5.11; G32 v0.16, §2.1. -/
theorem b60c_period_realization (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ τ : g32m_Domain, ∃ e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1,
      (∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x)) ∧
      (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P ∧
      exteriorPower.map 2 e.toLinearMap
        (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
        polarizationVec (torusCohomology_cupProductOf P.X) P.pol :=
  b60c_period_realization_aux P hP

example (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ τ : g32m_Domain, ∃ e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1,
      (∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x)) ∧
      (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P ∧
      exteriorPower.map 2 e.toLinearMap
        (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
        polarizationVec (torusCohomology_cupProductOf P.X) P.pol := b60c_period_realization P hP

/-- Clear denominators in a specified polarized K-linear Hodge marking.
Source: Birkenhake–Lange, Complex Abelian Varieties, 2nd ed., §1.2; G32 v0.16, Lemma 2.2. -/
theorem b60c_uniformization (P : g32t_Sixfold) (τ : g32m_Domain)
    (e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1)
    (hJ : ∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x))
    (hF : (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P)
    (hpol : exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
      polarizationVec (torusCohomology_cupProductOf P.X) P.pol) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : P.X ⟶ (b60b_univ τ).X,
      IsMonHom f ∧ ccm2_IsogenyOnPoints f ∧
      (∀ x, homPullback f 1 x = (N : ℚ) • e x) ∧
      (∀ x, homPullback f 1 ((b60b_univ τ).W.J x) = P.W.J (homPullback f 1 x)) ∧
      homPullback f 2 (b60b_univ τ).pol = ((N : ℚ) ^ 2) • P.pol :=
  b60c_uniformization_aux P τ e hJ hF hpol

example (P : g32t_Sixfold) (τ : g32m_Domain)
    (e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1)
    (hJ : ∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x))
    (hF : (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P)
    (hpol : exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
      polarizationVec (torusCohomology_cupProductOf P.X) P.pol) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : P.X ⟶ (b60b_univ τ).X,
      IsMonHom f ∧ ccm2_IsogenyOnPoints f ∧
      (∀ x, homPullback f 1 x = (N : ℚ) • e x) ∧
      (∀ x, homPullback f 1 ((b60b_univ τ).W.J x) = P.W.J (homPullback f 1 x)) ∧
      homPullback f 2 (b60b_univ τ).pol = ((N : ℚ) ^ 2) • P.pol := b60c_uniformization P τ e hJ hF hpol

/-- Every member maps by a polarized K-linear isogeny to a constructed fibre.
Source: G32 v0.16, Lemma 2.2; van Geemen, LNM 1594, §§5.4–5.11. -/
theorem b60c_cover (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ τ : g32m_Domain, g32t_KIsog P (b60b_univ τ) :=
  b60c_cover_aux P hP

example (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ τ : g32m_Domain, g32t_KIsog P (b60b_univ τ) := b60c_cover P hP

/-- Existence of the universal-family record with the specified fibres.
Source: G32 v0.16, §2.1 and Lemma 2.2; `g32m_UniversalFamily`. -/
theorem b60c_family : ∃ F : g32m_UniversalFamily, F.univ = b60b_univ :=
  b60c_family_aux

example : ∃ F : g32m_UniversalFamily, F.univ = b60b_univ := b60c_family

/-- Input check at the explicit origin of the bounded domain. -/
example : g32t_IsMember (b60b_univ ⟨0, g32m_zero_mem⟩) :=
  b60b_member ⟨0, g32m_zero_mem⟩

/-- The identity marking satisfies every input of the comparison. -/
example (τ : g32m_Domain) :
    let P := b60b_univ τ
    let e := LinearEquiv.refl ℚ (HQ P.X 1)
    (∀ x, e (P.W.J x) = P.W.J (e x)) ∧
    (b60c_F P).map (e.toLinearMap.baseChange ℂ) = b60c_F P ∧
    exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf P.X) P.pol) =
      polarizationVec (torusCohomology_cupProductOf P.X) P.pol := by
  dsimp only
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · simp
  · simp

/-- Field-level chain check, using the explicit fibre function throughout. -/
example :
    let F : g32m_UniversalFamily :=
      { univ := b60b_univ, member := b60b_member, cover := b60c_cover }
    F.univ = b60b_univ ∧
      (∀ τ, g32t_IsMember (F.univ τ)) ∧
      (∀ P, g32t_IsMember P → ∃ τ, g32t_KIsog P (F.univ τ)) :=
  ⟨rfl, b60b_member, b60c_cover⟩

end HodgeLean.Foundations.Program
