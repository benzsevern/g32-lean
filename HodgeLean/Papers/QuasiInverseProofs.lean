import HodgeLean.Papers.QuasiInverseDefs
import HodgeLean.Papers.G32Narrow
import HodgeLean.Adapters.AbelianHomPullbackDegrees

/-! # Morphism-level quasi-inverses: proofs of the frozen statements -/

noncomputable section

set_option maxRecDepth 2000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

private theorem qinv_over_hom_ext_of_point_map {X : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {f g : X ⟶ X} (h : Point.map f = Point.map g) : f = g := by
  refine Over.OverMorphism.ext ?_
  have hf : f.left ≫ X.hom = X.hom := Over.w f
  have hg : g.left ≫ X.hom = X.hom := Over.w g
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply X.hom x hx a]
  have := congrArg (fun z => z.left)
    (congrFun h (Over.homMk (pointOfClosedPoint X.hom x hx) (by simp) :
      Over.mk (𝟙 (Spec ↧ℂ)) ⟶ X))
  change (pointOfClosedPoint X.hom x hx ≫ f.left) a =
    (pointOfClosedPoint X.hom x hx ≫ g.left) a
  exact congrArg (fun φ : Spec ↧ℂ ⟶ X.left => φ a) this

private theorem qinv_other_comp {P Q : g32t_Sixfold} (f : P.X ⟶ Q.X)
    (f_mon : IsMonHom f)
    (w : qinv_Witness P Q f) : f ≫ w.g = 𝟙 P.X ^ (w.N : ℤ) := by
  letI : IsMonHom f := f_mon
  letI : IsMonHom w.g := w.g_mon
  apply qinv_over_hom_ext_of_point_map
  funext x
  obtain ⟨y, rfl⟩ := w.g_isogeny.2 x
  rw [Point.map_comp_apply]
  have hgf : Point.map f (Point.map w.g y) = Point.map (𝟙 Q.X ^ (w.N : ℤ)) y := by
    rw [← Point.map_comp_apply, w.gf]
  rw [hgf]
  rw [← Point.map_comp_apply, GrpObj.zpow_comp, Category.id_comp]
  rw [← Point.map_comp_apply, GrpObj.comp_zpow, Category.comp_id]

theorem qinv_wtr_KIsog_reverse_of_witness_aux {n : ℕ} (P Q : wtr_Variety n)
    (f : P.X ⟶ Q.X) (f_mon : IsMonHom f) (f_isogeny : ccm2_IsogenyOnPoints f)
    (f_K : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      ∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x))
    (c : ℚ) (c_pos : 0 < c)
    (f_pol : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      homPullback f 2 Q.pol = c • P.pol)
    (w : qinv_Witness P Q f) : wtr_KIsog Q P := by
  letI := (torusCohomology_cupProductOf P.X).finite
  letI := (torusCohomology_cupProductOf Q.X).finite
  have hcomp (m : ℕ) : homPullback w.g m ∘ₗ homPullback f m =
      ((w.N : ℚ) ^ m) • LinearMap.id := by
    rw [← spec_homPullback_comp, w.gf, spec_homPullback_zpow_degree,
      spec_homPullback_id, Int.cast_natCast]
  have hother (m : ℕ) : homPullback f m ∘ₗ homPullback w.g m =
      ((w.N : ℚ) ^ m) • LinearMap.id := by
    rw [← spec_homPullback_comp, qinv_other_comp f f_mon w,
      spec_homPullback_zpow_degree, spec_homPullback_id, Int.cast_natCast]
  have hfinj : Function.Injective (homPullback f 1) := by
    intro x y hxy
    have h := congrArg (homPullback w.g 1) hxy
    have hc := LinearMap.congr_fun (hcomp 1) x
    have hd := LinearMap.congr_fun (hcomp 1) y
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, pow_one] at hc hd
    rw [hc, hd] at h
    have hz : (w.N : ℚ) • (x - y) = 0 := by rw [smul_sub, h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by exact_mod_cast w.N_pos.ne'))
  refine ⟨w.g, w.g_mon, w.g_isogeny, ?_, ?_⟩
  · intro x
    apply hfinj
    rw [f_K]
    have hx := LinearMap.congr_fun (hother 1) x
    have hJx := LinearMap.congr_fun (hother 1) (P.W.J x)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, pow_one] at hx hJx
    calc
      homPullback f 1 (homPullback w.g 1 (P.W.J x)) =
          (w.N : ℚ) • P.W.J x := hJx
      _ = P.W.J ((w.N : ℚ) • x) := (map_smul _ _ _).symm
      _ = P.W.J (homPullback f 1 (homPullback w.g 1 x)) := congrArg P.W.J hx.symm
  · refine ⟨(w.N : ℚ) ^ 2 / c, div_pos (sq_pos_of_pos (by exact_mod_cast w.N_pos)) c_pos, ?_⟩
    have hp := congrArg (homPullback w.g 2) f_pol
    have hq := LinearMap.congr_fun (hcomp 2) Q.pol
    simp only [map_smul, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hp hq
    rw [hq] at hp
    calc
      homPullback w.g 2 P.pol = c⁻¹ • (c • homPullback w.g 2 P.pol) :=
        (inv_smul_smul₀ (ne_of_gt c_pos) _).symm
      _ = c⁻¹ • ((w.N : ℚ) ^ 2 • Q.pol) := congrArg (c⁻¹ • ·) hp.symm
      _ = ((w.N : ℚ) ^ 2 / c) • Q.pol := by rw [smul_smul, div_eq_mul_inv, mul_comm]

theorem qinv_KIsog_reverse_of_witness_aux (P Q : g32t_Sixfold)
    (f : P.X ⟶ Q.X) (f_mon : IsMonHom f) (f_isogeny : ccm2_IsogenyOnPoints f)
    (f_K : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      ∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x))
    (c : ℚ) (c_pos : 0 < c)
    (f_pol : letI := (torusCohomology_cupProductOf P.X).finite
      letI := (torusCohomology_cupProductOf Q.X).finite
      homPullback f 2 Q.pol = c • P.pol)
    (w : qinv_Witness P Q f) : g32t_KIsog Q P := by
  exact qinv_wtr_KIsog_reverse_of_witness_aux (n := 3) P Q f f_mon f_isogeny
    f_K c c_pos f_pol w

theorem qinv_reverse_of_premise_aux (h : qinv_premise) :
    ∀ P Q, g32t_IsMember P → g32t_IsMember Q →
      g32t_KIsog P Q → g32t_KIsog Q P := by
  intro P Q _ _ hf
  obtain ⟨f, f_mon, f_isogeny, f_K, c, c_pos, f_pol⟩ := hf
  obtain ⟨w⟩ := h P Q f f_mon f_isogeny
  exact qinv_KIsog_reverse_of_witness_aux P Q f f_mon f_isogeny f_K c c_pos f_pol w

theorem qinv_g32_theoremA_of_premises_aux (B : qinv_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  let C : g32n_premises :=
    { F := B.F
      P := B.P
      h46 := B.h46
      R := B.R
      hpol := B.hpol
      spread := B.spread
      reverse := qinv_reverse_of_premise_aux B.qinv }
  exact g32n_theoremA_of_premises C A W pol

end HodgeLean.Papers
