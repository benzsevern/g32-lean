import HodgeLean.Foundations.Program.PrymFamilyCentreDefs
import HodgeLean.Foundations.Program.PrymFamilyCentreEigen
import HodgeLean.Foundations.Program.PrymFamilyCentreWeil

/-! # B6-3g, parts 2 and 3: proof obligations

One auxiliary statement for each public statement of `PrymFamilyCentre.lean`, with bodies from
period naturality (`PrymFamilyCentreNaturality.lean`), eigenparts through the integral
comparison (`PrymFamilyCentreEigen.lean`) and the annihilator count for the model Weil action
(`PrymFamilyCentreWeil.lean`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63g2_centre_isometry_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x))
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      Ps (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s)))
    (hQ : b3_IsIntersectionForm ℂ Q)
    (x y : b63l_parameterLattice b C hC V hV s) :
    b63e_singularQ b C hC V hV s Ps Q (b63g2_centre b C hC V hV s x)
        (b63g2_centre b C hC V hV s y) =
      b63e_singularQ b C hC V hV s Ps Q x y := by
  change Q (Ps (b63d_centre b C hC V hV s x.val)) (Ps (b63d_centre b C hC V hV s y.val)) =
    Q (Ps x.val) (Ps y.val)
  rw [b63g2_period_centre b C hC V hV s hG Ps hP, b63g2_period_centre b C hC V hV s hG Ps hP,
    b63d_period_centre_scalar]
  exact b4_intersectionForm_invariant (by simp) hG Q hQ _ _ _

theorem b63g2_operator_skew_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x))
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      Ps (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    ∀ x y, b63e_singularQ b C hC V hV s Ps Q (b63g2_operator b C hC V hV s x) y =
      -b63e_singularQ b C hC V hV s Ps Q x (b63g2_operator b C hC V hV s y) := by
  set B := b63e_singularQ b C hC V hV s Ps Q
  set c := b63g2_centre b C hC V hV s
  have hJ : ∀ x, b63g2_operator b C hC V hV s x = x + (2 : ℤ) • c x := fun x ↦ by
    simp [b63g2_operator, c, two_smul]
  have hiso := b63g2_centre_isometry_aux b C hC V hV s hG Ps hP Q hQ
  have hkey : ∀ u w, B (u + c u + c (c u)) w = 0 := by
    intro u w
    have h := b63g2_operator_sq b C hC V hV s hG u
    rw [hJ, hJ, map_add, map_zsmul] at h
    have h4 : (4 : ℤ) • (u + c u + c (c u)) = 0 := by
      linear_combination (norm := module) h
    have hB : (4 : ℤ) * B (u + c u + c (c u)) w = 0 := by
      rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_zsmul, h4, map_zero,
        LinearMap.zero_apply]
    omega
  have hc : ∀ x y, B (c x) y = -B x (c y) - B x y := by
    intro x y
    have h1 := hiso (c x) y
    have h2 := hkey x (c y)
    have h3 := hiso x y
    simp only [map_add, LinearMap.add_apply] at h2
    linarith
  intro x y
  rw [hJ, hJ, map_add, map_zsmul, map_add, map_zsmul, LinearMap.add_apply,
    LinearMap.smul_apply, hc]
  simp only [smul_eq_mul]
  ring

theorem b63g2_operator_filtration_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    b63e_transportedF b C hC V hV P s t ≤ (b63e_transportedF b C hC V hV P s t).comap
      (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom) := by
  classical
  set E := b63e_transportMap b C hC V hV P s t
  set Z := (b4b_centreAct (b63l_parameterFibre b C V hV t) (hG t)).toIntLinearMap
  have hcomm : E.comp (b63g2_operator b C hC V hV s).toAddMonoidHom.toIntLinearMap =
      (LinearMap.id + Z + Z).comp E := by
    apply LinearMap.ext
    intro x
    change P t (b6m_H1Equiv _ (b63g2_operator b C hC V hV s x).val) =
      P t (b6m_H1Equiv _ x.val) + Z (P t (b6m_H1Equiv _ x.val)) +
        Z (P t (b6m_H1Equiv _ x.val))
    rw [b63g2_operator_val]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply, two_smul,
      LinearMap.smul_apply, map_add]
    rw [b63d_centre_transport b C hC V hV t s,
      b63g2_period_centre b C hC V hV t (hG t) (P t) (hP t)]
    simp only [Z, AddMonoidHom.coe_toIntLinearMap, add_assoc]
  have hZ : b3_periodF ℂ (b63l_parameterFibre b C V hV t) ≤
      (b3_periodF ℂ (b63l_parameterFibre b C V hV t)).comap (Z.baseChange ℂ) := by
    have h : b3_periodF ℂ (b63l_parameterFibre b C V hV t) ≤
        (b3_periodF ℂ (b63l_parameterFibre b C V hV t)).comap
          ((b4_latticeAct ℂ b63d_scalarElement).toIntLinearMap.baseChange ℂ) :=
      b4_cplxAct_periodF (E := ℂ) (hG t) b63d_scalarElement
    rw [← b63d_period_centre_scalar _ (hG t)] at h
    exact h
  intro v hv
  change (E.baseChange ℂ) (((b63g2_operator b C hC V hV s).toAddMonoidHom.toIntLinearMap.baseChange
    ℂ) v) ∈ b3_periodF ℂ (b63l_parameterFibre b C V hV t)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomm, LinearMap.baseChange_comp,
    LinearMap.comp_apply]
  have hv' : E.baseChange ℂ v ∈ b3_periodF ℂ (b63l_parameterFibre b C V hV t) := hv
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_id, LinearMap.add_apply,
    LinearMap.id_apply]
  exact add_mem (add_mem hv' (hZ hv')) (hZ hv')

theorem b63g2_weil_h10_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (hn : 0 < n)
    (φ : Λ →+ Λ) (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ n φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (1, 0)) =
      Module.finrank ℂ ↥(F ⊓
        Module.End.eigenspace (b2_cplxMap φ) (-HodgeBlocks.WeilAction.omegaC (n : ℚ))) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hμsq : HodgeBlocks.WeilAction.omegaC (n : ℚ) * HodgeBlocks.WeilAction.omegaC (n : ℚ) =
      -(n : ℂ) := by
    rw [← sq, HodgeBlocks.WeilAction.omegaC_sq hn']
    push_cast
    ring
  have hcomp : (b63g_modelMap Λ F hF Q hQ φ).comp (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom =
      (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom.comp φ := by
    ext l
    simp [b63g_modelMap]
  exact b63g2_dual_eigen (b5_model Λ F hF Q) F hF (b5_periodEquiv Λ F hF Q hQ)
    (b5_period_filtration Λ F hF Q hQ) φ (b63g_modelMap Λ F hF Q hQ φ) hcomp _
    (HodgeBlocks.WeilAction.omegaC_ne_zero hn') (b63g2_cplxMap_sq φ n hsq _ hμsq)
    (b63g2_omegaC_star _)

theorem b63g2_weil_h01_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (hn : 0 < n)
    (φ : Λ →+ Λ) (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ n φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (0, 1)) =
      Module.finrank ℂ ↥(F ⊓
        Module.End.eigenspace (b2_cplxMap φ) (HodgeBlocks.WeilAction.omegaC (n : ℚ))) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hμsq : HodgeBlocks.WeilAction.omegaC (n : ℚ) * HodgeBlocks.WeilAction.omegaC (n : ℚ) =
      -(n : ℂ) := by
    rw [← sq, HodgeBlocks.WeilAction.omegaC_sq hn']
    push_cast
    ring
  have hcomp : (b63g_modelMap Λ F hF Q hQ φ).comp (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom =
      (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom.comp φ := by
    ext l
    simp [b63g_modelMap]
  rw [← HodgeBlocks.WeilAction.finrank_map_sigmaQ,
    HodgeBlocks.WeilAction.map_inf_Vs_H01_sigmaQ]
  have h := b63g2_dual_eigen (b5_model Λ F hF Q) F hF (b5_periodEquiv Λ F hF Q hQ)
    (b5_period_filtration Λ F hF Q hQ) φ (b63g_modelMap Λ F hF Q hQ φ) hcomp
    (-HodgeBlocks.WeilAction.omegaC (n : ℚ))
    (neg_ne_zero.mpr (HodgeBlocks.WeilAction.omegaC_ne_zero hn'))
    (b63g2_cplxMap_sq φ n hsq _ (by rw [neg_mul_neg, hμsq]))
    (by rw [star_neg, b63g2_omegaC_star])
  rw [neg_neg] at h
  exact h

theorem b63g2_eigen_rank_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V)
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom)
          (HodgeBlocks.WeilAction.omegaC 3)) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom)
          (-HodgeBlocks.WeilAction.omegaC 3)) = 3 := by
  obtain ⟨E, hE, hF⟩ := b63e_lattice_period_transport b C hC V hV hG P hP s t
  have hCW := b63d_chevalleyWeil_hodge b C hC V hV t (hG t) hb f hf hs hgal hbranch hrot
  let c := b63g2_centre b C hC V hV s
  let ι := (b63l_periodLattice (b63l_parameterFibre b C V hV t)).subtype
  let Z := (b4b_centreAct (b63l_parameterFibre b C V hV t) (hG t)).toIntLinearMap
  have hι : Function.Injective (ι.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι
      (b63l_periodLattice (b63l_parameterFibre b C V hV t)).subtype_injective
  have hc : ∀ x, ι (E (c x)) = Z (ι (E x)) := by
    intro x
    change (E (c x)).val = Z (E x).val
    rw [hE, hE]
    change P t (b6m_H1Equiv _ (b63d_centre b C hC V hV s x.val)) =
      Z (P t (b6m_H1Equiv _ x.val))
    rw [b63d_centre_transport b C hC V hV t s,
      b63g2_period_centre b C hC V hV t (hG t) (P t) (hP t)]
    rfl
  have hJ : (b63g2_operator b C hC V hV s).toAddMonoidHom.toIntLinearMap =
      LinearMap.id + c + c := by
    ext x
    simp [b63g2_operator, c, two_smul, add_assoc]
  have key := b63g2_eigen_transfer E ι hι c _ Z hJ hc (b3_periodF ℂ _) g32h_omega _
    b63g2_one_add_two_omega
  have key2 := b63g2_eigen_transfer E ι hι c _ Z hJ hc (b3_periodF ℂ _) (star g32h_omega) _
    b63g2_one_add_two_star_omega
  have h1 : Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) (hG t) g32h_omega) =
      3 := hCW.2.2.1
  have k1 : Module.finrank ℂ ↥((((b3_periodF ℂ (b63l_parameterFibre b C V hV t)).comap
      (ι.baseChange ℂ)) ⊓ (LinearMap.ker (Z.baseChange ℂ - g32h_omega • LinearMap.id)).comap
        (ι.baseChange ℂ))) = 3 := h1
  have g1 := key.trans k1
  have hF' : b63e_transportedF b C hC V hV P s t =
      (((b3_periodF ℂ (b63l_parameterFibre b C V hV t)).comap (ι.baseChange ℂ)).comap
        ((E : b63l_parameterLattice b C hC V hV s →ₗ[ℤ]
          b63l_periodLattice (b63l_parameterFibre b C V hV t)).baseChange ℂ)) := hF
  rw [hF']
  have h2 : Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) (hG t)
      (star g32h_omega)) = 3 := hCW.2.2.2
  have k2 : Module.finrank ℂ ↥((((b3_periodF ℂ (b63l_parameterFibre b C V hV t)).comap
      (ι.baseChange ℂ)) ⊓ (LinearMap.ker (Z.baseChange ℂ - star g32h_omega • LinearMap.id)).comap
        (ι.baseChange ℂ))) = 3 := h2
  exact ⟨g1, key2.trans k2⟩

end HodgeLean.Foundations.Program
