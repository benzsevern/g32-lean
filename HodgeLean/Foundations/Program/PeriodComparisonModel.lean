import HodgeLean.Foundations.Program.PeriodComparisonModelProofs
import HodgeLean.Foundations.Program.UniversalFamilyCover

/-! # B6-4d stage 1: general theta-model comparison

The implication from weight-one integral Riemann data supplies a specified comparison
and its filtration, action, conjugation and evaluation identities. The later rational
fibre marking and its geometric polarization comparison are outside this stage.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The comparison carries the homology filtration to degree-one holomorphic cohomology.
Source: Birkenhake–Lange, §§1.2–1.3 and §2.2; `b5_period_filtration`; `b2bpol_hodgeOne_eq_map`. -/
theorem b64d_model_homologyCohomology_F (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    F.map (b64d_model_homologyCohomology Λ F hF Q hQ).toLinearMap = cohomologyHodgePiece (b5_model Λ F hF Q) 1 (1, 0) :=
  b64d_model_homologyCohomology_F_aux Λ F hF Q hQ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    F.map (b64d_model_homologyCohomology Λ F hF Q hQ).toLinearMap = cohomologyHodgePiece (b5_model Λ F hF Q) 1 (1, 0) :=
  b64d_model_homologyCohomology_F Λ F hF Q hQ

/-- A skew lattice action becomes the negative contravariant cohomology action.
Source: Birkenhake–Lange, §1.2 (dual analytic and rational representations); `b60b_musical_skew`. -/
theorem b64d_model_homologyCohomology_intertwines (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (J : Λ →+ Λ)
    (hskew : ∀ x y, Q (J x) y = -Q x (J y)) (x : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64d_model_homologyCohomology Λ F hF Q hQ (b2_cplxMap J x) =
      -(b4b_cohomologyAction Λ (b5_model Λ F hF Q) (b5_periodEquiv Λ F hF Q hQ) J).baseChange ℂ
        (b64d_model_homologyCohomology Λ F hF Q hQ x) :=
  b64d_model_homologyCohomology_intertwines_aux Λ F hF Q hQ J hskew x

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (J : Λ →+ Λ)
    (hskew : ∀ x y, Q (J x) y = -Q x (J y)) (x : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64d_model_homologyCohomology Λ F hF Q hQ (b2_cplxMap J x) =
      -(b4b_cohomologyAction Λ (b5_model Λ F hF Q) (b5_periodEquiv Λ F hF Q hQ) J).baseChange ℂ
        (b64d_model_homologyCohomology Λ F hF Q hQ x) :=
  b64d_model_homologyCohomology_intertwines Λ F hF Q hQ J hskew x

/-- The comparison respects the real structures.
Source: Birkenhake–Lange, §1.2; `b2bpol_sigma_musical`; `HodgeBlocks.sigmaQ_baseChange`. -/
theorem b64d_model_homologyCohomology_conj (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (x : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64d_model_homologyCohomology Λ F hF Q hQ (b2_conj Λ x) =
      HodgeBlocks.sigmaQ _ (b64d_model_homologyCohomology Λ F hF Q hQ x) :=
  b64d_model_homologyCohomology_conj_aux Λ F hF Q hQ x

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (x : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b64d_model_homologyCohomology Λ F hF Q hQ (b2_conj Λ x) =
      HodgeBlocks.sigmaQ _ (b64d_model_homologyCohomology Λ F hF Q hQ x) :=
  b64d_model_homologyCohomology_conj Λ F hF Q hQ x

/-- Evaluation on marked periods recovers the original integral form after scalar extension.
Source: Birkenhake–Lange, §§1.2–1.3; `b2bpol_pairing_musical`; `b4b_transportForm`. -/
theorem b64d_model_homologyCohomology_pairing (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (x y : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b2_abelianPairing (b5_model Λ F hF Q) (b64d_model_homologyCohomology Λ F hF Q hQ x)
      (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom y) =
      Q.baseChange ℂ x y :=
  b64d_model_homologyCohomology_pairing_aux Λ F hF Q hQ x y

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (x y : ℂ ⊗[ℤ] Λ) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
    letI := b5_smooth Λ F hF Q hQ
    letI := b5_projective Λ F hF Q hQ
    b2_abelianPairing (b5_model Λ F hF Q) (b64d_model_homologyCohomology Λ F hF Q hQ x)
      (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom y) =
      Q.baseChange ℂ x y :=
  b64d_model_homologyCohomology_pairing Λ F hF Q hQ x y

/-- The general comparison agrees with the specified universal-fibre comparison.
Source: `b60b_homologyCohomologyEquiv`; Birkenhake–Lange, §§1.2–1.3. -/
theorem b64d_model_homologyCohomology_specializes (τ : g32m_Domain) :
    HEq (b64d_model_homologyCohomology b60_Lattice (b60_F τ) (b60_weight_one τ)
      b60_E ((b60_riemann_iff τ).2 τ.property)) (b60b_homologyCohomologyEquiv τ) :=
  b64d_model_homologyCohomology_specializes_aux τ

example (τ : g32m_Domain) :
    HEq (b64d_model_homologyCohomology b60_Lattice (b60_F τ) (b60_weight_one τ)
      b60_E ((b60_riemann_iff τ).2 τ.property)) (b60b_homologyCohomologyEquiv τ) :=
  b64d_model_homologyCohomology_specializes τ

set_option maxHeartbeats 400000 in
/-- The general filtration statement has the existing universal-fibre specialization. -/
example (τ : g32m_Domain) :
    letI := (torusCohomology_cupProductOf (b60b_model τ)).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian (b60b_model τ))
      (spec_bettiDeRhamIso_abelian (b60b_model τ))
      (hodgeDecomposition_of_abelian (b60b_model τ))
      (torusCohomology_cupProductOf (b60b_model τ))
    (b60_F τ).map
      (b64d_model_homologyCohomology b60_Lattice (b60_F τ) (b60_weight_one τ)
        b60_E ((b60_riemann_iff τ).2 τ.property)).toLinearMap = S.weight1.H (1, 0) :=
  b64d_model_homologyCohomology_F b60_Lattice (b60_F τ) (b60_weight_one τ)
    b60_E ((b60_riemann_iff τ).2 τ.property)

set_option maxHeartbeats 400000 in
/-- The same lattice action specializes with the negative dual-action convention. -/
example (τ : g32m_Domain) (x : ℂ ⊗[ℤ] b60_Lattice) :
    b64d_model_homologyCohomology b60_Lattice (b60_F τ) (b60_weight_one τ)
      b60_E ((b60_riemann_iff τ).2 τ.property) (b60_omegaC x) =
    -(b60b_J τ).baseChange ℂ
      (b64d_model_homologyCohomology b60_Lattice (b60_F τ) (b60_weight_one τ)
        b60_E ((b60_riemann_iff τ).2 τ.property) x) := by
  have hskew (u v : b60_Lattice) : b60_E (b60_omega u) v = -b60_E u (b60_omega v) := by
    simp only [b60_E, b60_omega, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    fin_cases i <;> norm_num [b60_diag] <;> ring
  exact b64d_model_homologyCohomology_intertwines b60_Lattice (b60_F τ)
    (b60_weight_one τ) b60_E ((b60_riemann_iff τ).2 τ.property)
    b60_omega.toAddMonoidHom hskew x

set_option maxRecDepth 2000 in
/-- The remaining rational identities feed the existential fibre index in the period-map field. -/
example (P : g32h_PrymFamily) (s : P.S) (τ : g32m_Domain)
    (e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ (P.fiber s).X 1)
    (hJ : ∀ x, e ((b60b_univ τ).W.J x) = (P.fiber s).W.J (e x))
    (hF : (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F (P.fiber s))
    (hpol : exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
      polarizationVec (torusCohomology_cupProductOf (P.fiber s).X) (P.fiber s).pol) :
    ∃ u : P.S, g32t_KIsog (P.fiber u) (b60b_univ τ) := by
  obtain ⟨N, hN, f, hf, hi, _, hfJ, hfpol⟩ :=
    b60c_uniformization (P.fiber s) τ e hJ hF hpol
  refine ⟨s, f, hf, hi, hfJ, (N : ℚ) ^ 2, ?_, hfpol⟩
  exact pow_pos (by exact_mod_cast hN) 2

end HodgeLean.Foundations.Program
