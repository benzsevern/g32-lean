import HodgeLean.Papers.G34NarrowDefs
import HodgeLean.Papers.G32Transport

/-! # Generic Weil transfer with reverse isogenies: proofs of the frozen statements -/

noncomputable section

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers
private theorem g34n_contract_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (f : V →ₗ[ℚ] W)
    (om : ⋀[ℚ]^2 V) (φ : Module.Dual ℚ W) :
    f (Foundations.Symplectic.contract om (φ.comp f)) =
      Foundations.Symplectic.contract (exteriorPower.map 2 f om) φ := by
  let L : ⋀[ℚ]^2 V →ₗ[ℚ] W :=
    f.comp ((LinearMap.applyₗ (φ.comp f)).comp Foundations.Symplectic.contract)
  let R : ⋀[ℚ]^2 V →ₗ[ℚ] W :=
    ((LinearMap.applyₗ φ).comp Foundations.Symplectic.contract).comp
      (exteriorPower.map 2 f)
  have hLR : L = R := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp [L, R, Foundations.Symplectic.contract_ιMulti]
  exact LinearMap.congr_fun hLR om

private theorem g34n_surjective_of_map_nondegenerate
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ V] [Module.Finite ℚ W]
    (f : V →ₗ[ℚ] W) (ωV : ⋀[ℚ]^2 V) (ωW : ⋀[ℚ]^2 W)
    (hW : Foundations.Symplectic.IsNondegenerate ωW) (c : ℚ) (hc : c ≠ 0)
    (hmap : exteriorPower.map 2 f ωV = c • ωW)
    (hdim : Module.finrank ℚ V = Module.finrank ℚ W) : Function.Surjective f := by
  letI : Module.Free ℚ V := Module.Free.of_divisionRing ℚ V
  let fd : Module.Dual ℚ W →ₗ[ℚ] Module.Dual ℚ V := LinearMap.lcomp ℚ ℚ f
  have hfd : Function.Injective fd := by
    intro φ ψ hφψ
    apply LinearMap.ext
    intro y
    have hz : Foundations.Symplectic.contract ωW (φ - ψ) = 0 := by
      have hcomp : (φ - ψ).comp f = 0 := by
        change fd (φ - ψ) = 0
        rw [map_sub, hφψ, sub_self]
      have hn := g34n_contract_map f ωV (φ - ψ)
      rw [hmap, hcomp, map_zero, map_zero] at hn
      have hcz : c • Foundations.Symplectic.contract ωW (φ - ψ) = 0 := by
        simpa only [map_smul, LinearMap.smul_apply] using hn.symm
      exact (smul_eq_zero.mp hcz).resolve_left hc
    exact LinearMap.congr_fun
      (sub_eq_zero.mp (hW.1 (hz.trans (map_zero _).symm))) y
  have hdimd : Module.finrank ℚ (Module.Dual ℚ W) =
      Module.finrank ℚ (Module.Dual ℚ V) := by
    simpa only [Subspace.dual_finrank_eq] using hdim.symm
  have hfdsurj :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimd).mp hfd
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
  intro x y hxy
  rw [← sub_eq_zero]
  apply LinearMap.eval_separatingLeft (R := ℚ) (M := V) (x - y)
  intro ψ
  obtain ⟨φ, rfl⟩ := hfdsurj ψ
  change φ (f (x - y)) = 0
  rw [map_sub, hxy, sub_self, map_zero]

private theorem g34n_derivationExt_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (f : V →ₗ[ℚ] W)
    (Jv : Module.End ℚ V) (Jw : Module.End ℚ W)
    (hJ : ∀ x, f (Jv x) = Jw (f x)) (n : ℕ) :
    (HodgeBlocks.derivationExt Jw n).comp (exteriorPower.map n f) =
      (exteriorPower.map n f).comp (HodgeBlocks.derivationExt Jv n) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    exteriorPower.map_apply_ιMulti, HodgeBlocks.derivationExt_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hij : j = i
  · subst j
    simp [hJ]
  · simp [hij]

private def g34n_exteriorCast {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m n : ℕ} (h : m = n) : ⋀[ℚ]^m V → ⋀[ℚ]^n V := by
  subst n
  exact id

@[simp] private theorem g34n_exteriorCast_symm {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m n : ℕ} (h : m = n) (w : ⋀[ℚ]^m V) :
    g34n_exteriorCast h.symm (g34n_exteriorCast h w) = w := by
  subst n
  rfl

@[simp] private theorem g34n_exteriorCast_cancel {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m n : ℕ} (h : m = n) (g : n = m) (w : ⋀[ℚ]^m V) :
    g34n_exteriorCast g (g34n_exteriorCast h w) = w := by
  subst n
  rfl

private theorem g34n_kernel_cast {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ}
    (A : HodgeBlocks.WeilAction M d) {k l : ℕ} (h : k = l)
    (w : ⋀[ℚ]^(k + k) V)
    (hw : HodgeBlocks.WeilAction.derivationKernelOperatorQ A k w = 0) :
    HodgeBlocks.WeilAction.derivationKernelOperatorQ A l
      (g34n_exteriorCast (congrArg (fun n => n + n) h) w) = 0 := by
  subst l
  exact hw

private def g34n_cohomCast (X : Over (Spec ↧ℂ)) {p q : ℕ} (h : p = q) :
    HQ X (2 * p) →ₗ[ℚ] HQ X (2 * q) :=
  (HQ.castEquiv X (congrArg (fun n => 2 * n) h)).toLinearMap

private theorem g34n_homPullback_cast {P Q : Over (Spec ↧ℂ)} (f : P ⟶ Q)
    [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    {p q : ℕ} (h : p = q) (x : HQ Q p) :
    homPullback f q (HQ.castEquiv Q h x) = HQ.castEquiv P h (homPullback f p x) := by
  subst q
  rfl

private theorem g34n_span_cast (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p q : ℕ} (h : p = q) (x : HQ X (2 * p))
    (hx : x ∈ algebraicCycleClassSpan X p) :
    g34n_cohomCast X h x ∈ algebraicCycleClassSpan X q := by
  subst q
  simpa [g34n_cohomCast] using hx

private theorem g34n_weilImage_cast (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {k l : ℕ} (h : k = l)
    (w : ⋀[ℚ]^(k + k) (HQ X 1)) :
    g34n_cohomCast X h
        (HQ.castEquiv X (two_mul k).symm ((cupProductOf X).cupWedgeMap (k + k) w)) =
      HQ.castEquiv X (two_mul l).symm
        ((cupProductOf X).cupWedgeMap (l + l)
          (g34n_exteriorCast (congrArg (fun n => n + n) h) w)) := by
  subst l
  rfl

theorem g34n_weilAlg_pullback_aux {n : ℕ} (P Q : wtr_Variety n)
    (hP : wtr_PolarizedWeil n P) (hQ : wtr_PolarizedWeil n Q)
    (h : wtr_KIsog P Q) (hAlg : wtr_WeilAlg Q) : wtr_WeilAlg P := by
  let TP := torusCohomology_cupProductOf P.X
  let TQ := torusCohomology_cupProductOf Q.X
  letI := TP.finite
  letI := TQ.finite
  obtain ⟨f, hfmon, hfisog, hJ, c, hc, hpol⟩ := h
  letI : IsMonHom f := hfmon
  let φ := homPullback f 1
  have hdim : Module.finrank ℚ (HQ Q.X 1) = Module.finrank ℚ (HQ P.X 1) := by
    rw [TP.finrank_eq, TQ.finrank_eq, hP.dim_eq, hQ.dim_eq]
  have hpolWedge : exteriorPower.map 2 φ (polarizationVec TQ Q.pol) =
      c • polarizationVec TP P.pol := by
    apply (TP.cupWedgeEquiv 2).injective
    simp only [TorusCohomology.cupWedgeEquiv_apply]
    calc
      (cupProductOf P.X).cupWedgeMap 2
          (exteriorPower.map 2 φ (polarizationVec TQ Q.pol)) =
          homPullback f 2
            ((cupProductOf Q.X).cupWedgeMap 2 (polarizationVec TQ Q.pol)) :=
        (LinearMap.congr_fun (spec_homPullback_cupWedgeMap f 2)
          (polarizationVec TQ Q.pol)).symm
      _ = c • (cupProductOf P.X).cupWedgeMap 2 (polarizationVec TP P.pol) := by
        rw [cupWedgeMap_polarizationVec TQ Q.pol, hpol,
          cupWedgeMap_polarizationVec TP P.pol]
      _ = (cupProductOf P.X).cupWedgeMap 2 (c • polarizationVec TP P.pol) := by
        rw [map_smul]
  have hφsurj : Function.Surjective φ :=
    g34n_surjective_of_map_nondegenerate φ _ _ hP.nondegenerate c (ne_of_gt hc)
      hpolWedge hdim
  have hφinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hφsurj
  intro hWP
  have hkP : Module.finrank ℂ ↥(P.W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
        (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
          (torusCohomology_cupProductOf P.X)).weight1.H
          (1, 0)) = n := by
    have hk := two_mul_finrank_vs_inf_h10_eq (finiteBetti_abelian P.X)
      (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
      (torusCohomology_cupProductOf P.X)
      (by norm_num : (0 : ℚ) < 3) P.W hWP
    rw [hP.dim_eq] at hk
    omega
  have hkQ : Module.finrank ℂ ↥(Q.W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian Q.X)
        (spec_bettiDeRhamIso_abelian Q.X) (hodgeDecomposition_of_abelian Q.X)
          (torusCohomology_cupProductOf Q.X)).weight1.H
          (1, 0)) = n := by
    have hk := two_mul_finrank_vs_inf_h10_eq (finiteBetti_abelian Q.X)
      (spec_bettiDeRhamIso_abelian Q.X) (hodgeDecomposition_of_abelian Q.X)
      (torusCohomology_cupProductOf Q.X)
      (by norm_num : (0 : ℚ) < 3) Q.W hQ.isWeilType
    rw [hQ.dim_eq] at hk
    omega
  rw [show hWP = hP.isWeilType from Subsingleton.elim _ _]
  rw [WeilClassesAlgebraic]
  let k := Module.finrank ℂ ↥(P.W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
        (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
          (torusCohomology_cupProductOf P.X)).weight1.H (1, 0))
  change weilClassOf (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
    (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W
      hP.isWeilType ≤ algebraicCycleClassSpan P.X k
  unfold weilClassOf
  change (P.W.weilClasses _ _).map
    ((HQ.castEquiv P.X _).toLinearMap ∘ₗ (cupProductOf P.X).cupWedgeMap (k + k)) ≤
      algebraicCycleClassSpan P.X k
  have hk : k = n := hkP
  subst k
  intro x hx
  rcases hx with ⟨wP, hwP, rfl⟩
  have hkdegP : Module.finrank ℂ ↥(P.W.Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
          (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
            (torusCohomology_cupProductOf P.X)).weight1.H (1, 0)) +
      Module.finrank ℂ ↥(P.W.Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
          (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
            (torusCohomology_cupProductOf P.X)).weight1.H (1, 0)) = n + n := by omega
  let wPnn : ⋀[ℚ]^(n + n) (HQ P.X 1) :=
    g34n_exteriorCast (congrArg (fun n => n + n) hkP) wP
  have hφextSurj : Function.Surjective (exteriorPower.map (n + n) φ) :=
    exteriorPower.map_surjective hφsurj
  obtain ⟨wQ, hwQmap⟩ := hφextSurj wPnn
  have hder : (HodgeBlocks.derivationExt P.W.J (n + n)).comp (exteriorPower.map (n + n) φ) =
      (exteriorPower.map (n + n) φ).comp (HodgeBlocks.derivationExt Q.W.J (n + n)) :=
    g34n_derivationExt_map φ Q.W.J P.W.J hJ (n + n)
  have hquad : (HodgeBlocks.WeilAction.derivationKernelOperatorQ P.W n).comp
      (exteriorPower.map (n + n) φ) =
      (exteriorPower.map (n + n) φ).comp
        (HodgeBlocks.WeilAction.derivationKernelOperatorQ Q.W n) := by
    unfold HodgeBlocks.WeilAction.derivationKernelOperatorQ
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_assoc, hder,
      ← LinearMap.comp_assoc, hder]
    ext z
    simp
  have hwPker0 : HodgeBlocks.WeilAction.derivationKernelOperatorQ P.W
      (Module.finrank ℂ ↥(P.W.Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
          (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
            (torusCohomology_cupProductOf P.X)).weight1.H (1, 0))) wP = 0 := by
    rw [← LinearMap.mem_ker,
      ← P.W.weilClasses_eq_ker_derivationKernelOperatorQ
        (h10_sup_h01_eq_top (finiteBetti_abelian P.X)
          (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X) TP)
        hP.isWeilType (by norm_num : (0 : ℚ) < 3)]
    exact hwP
  have hwPker : HodgeBlocks.WeilAction.derivationKernelOperatorQ P.W n wPnn = 0 := by
    exact g34n_kernel_cast P.W hkP wP hwPker0
  have hwQker : HodgeBlocks.WeilAction.derivationKernelOperatorQ Q.W n wQ = 0 := by
    apply (exteriorPower.map_injective_field hφinj)
    have hz := LinearMap.congr_fun hquad wQ
    simpa [hwQmap, hwPker] using hz.symm
  have hkdegQ : Module.finrank ℂ ↥(Q.W.Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian Q.X)
          (spec_bettiDeRhamIso_abelian Q.X) (hodgeDecomposition_of_abelian Q.X)
            (torusCohomology_cupProductOf Q.X)).weight1.H (1, 0)) +
      Module.finrank ℂ ↥(Q.W.Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian Q.X)
          (spec_bettiDeRhamIso_abelian Q.X) (hodgeDecomposition_of_abelian Q.X)
            (torusCohomology_cupProductOf Q.X)).weight1.H (1, 0)) = n + n := by omega
  let wQ0 : ⋀[ℚ]^(_ + _) (HQ Q.X 1) :=
    g34n_exteriorCast (congrArg (fun n => n + n) hkQ).symm wQ
  have hwQ : wQ0 ∈ Q.W.weilClasses
      (h10_sup_h01_eq_top (finiteBetti_abelian Q.X)
        (spec_bettiDeRhamIso_abelian Q.X) (hodgeDecomposition_of_abelian Q.X) TQ)
      hQ.isWeilType := by
    rw [Q.W.weilClasses_eq_ker_derivationKernelOperatorQ _ hQ.isWeilType
      (by norm_num : (0 : ℚ) < 3), LinearMap.mem_ker]
    exact g34n_kernel_cast Q.W hkQ.symm wQ hwQker
  have hyAlg := hAlg hQ.isWeilType
  rw [WeilClassesAlgebraic] at hyAlg
  have hy0 := hyAlg (Submodule.mem_map_of_mem hwQ)
  have hy : HQ.castEquiv Q.X (two_mul n).symm
      ((cupProductOf Q.X).cupWedgeMap (n + n) wQ) ∈
        algebraicCycleClassSpan Q.X n := by
    have hc := g34n_span_cast Q.X hkQ _ hy0
    change g34n_cohomCast Q.X hkQ
      (HQ.castEquiv Q.X (two_mul _).symm
        ((cupProductOf Q.X).cupWedgeMap (_ + _) wQ0)) ∈
          algebraicCycleClassSpan Q.X n at hc
    rw [g34n_weilImage_cast Q.X hkQ wQ0] at hc
    simpa [wQ0] using hc
  have hcup := LinearMap.congr_fun (spec_homPullback_cupWedgeMap f (n + n)) wQ
  have hfixed : homPullback f (n + n) ((cupProductOf Q.X).cupWedgeMap (n + n) wQ) =
      (cupProductOf P.X).cupWedgeMap (n + n) wPnn := by
    simpa [φ, hwQmap] using hcup
  have hxPn : HQ.castEquiv P.X (two_mul n).symm
      ((cupProductOf P.X).cupWedgeMap (n + n) wPnn) ∈
        algebraicCycleClassSpan P.X n := by
    apply g32tr_isogeny_pullback_span_aux f hfisog n
    refine Submodule.mem_map.mpr ⟨_, hy, ?_⟩
    calc
      homPullback f (2 * n)
          (HQ.castEquiv Q.X (two_mul n).symm
            ((cupProductOf Q.X).cupWedgeMap (n + n) wQ)) =
          HQ.castEquiv P.X (two_mul n).symm
            (homPullback f (n + n)
              ((cupProductOf Q.X).cupWedgeMap (n + n) wQ)) :=
        g34n_homPullback_cast (P := P.X) (Q := Q.X) f
          (p := n + n) (q := 2 * n) (two_mul n).symm _
      _ = HQ.castEquiv P.X (two_mul n).symm
          ((cupProductOf P.X).cupWedgeMap (n + n) wPnn) := by rw [hfixed]
  have hxP0 := g34n_span_cast P.X hkP.symm _ hxPn
  change g34n_cohomCast P.X hkP.symm
    (HQ.castEquiv P.X (two_mul n).symm
      ((cupProductOf P.X).cupWedgeMap (n + n) wPnn)) ∈
        algebraicCycleClassSpan P.X _ at hxP0
  rw [g34n_weilImage_cast P.X hkP.symm wPnn] at hxP0
  simp only [wPnn, g34n_exteriorCast_cancel] at hxP0
  change HQ.castEquiv P.X _ ((cupProductOf P.X).cupWedgeMap (_ + _) wP) ∈
    algebraicCycleClassSpan P.X _
  exact hxP0
theorem g34n_transport_of_reverse_aux {n : ℕ} (P Q : wtr_Variety n)
    (hP : wtr_PolarizedWeil n P) (hQ : wtr_PolarizedWeil n Q)
    (reverse : wtr_KIsog P Q → wtr_KIsog Q P) :
    wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q) := by
  intro h
  exact ⟨g34n_weilAlg_pullback_aux Q P hQ hP (reverse h),
    g34n_weilAlg_pullback_aux P Q hP hQ h⟩

theorem g34n_theoremA_of_transfer_aux {n : ℕ}
    {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : g34n_TransferDatum n δ) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) (hM : wtr_IsMember n δ (⟨A, W, pol⟩ : wtr_Variety n)) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.polarized.isWeilType := by
  have transport (P Q : wtr_Variety n) (hP : wtr_IsMember n δ P)
      (hQ : wtr_IsMember n δ Q) (h : wtr_KIsog P Q) :
      wtr_WeilAlg P ↔ wtr_WeilAlg Q :=
    g34n_transport_of_reverse_aux P Q hP.polarized hQ.polarized
      (D.reverse P Q hP hQ) h
  have open_locus : ∃ U : Set D.M, IsOpen U ∧ U.Nonempty ∧
      U ⊆ {m | wtr_WeilAlg (D.univ m)} := by
    obtain ⟨U, hUo, hUne, hU⟩ := D.dominant
    refine ⟨U, hUo, hUne, fun m hm ↦ ?_⟩
    obtain ⟨s, hs⟩ := hU m hm
    have hF : wtr_IsMember n δ (D.fiber s) :=
      ⟨D.fiber_polarized s, D.fiber_disc s⟩
    exact (transport _ _ hF (D.univ_member m) hs).1 (D.fiber_alg s)
  have locus (m : D.M) : wtr_WeilAlg (D.univ m) := by
    obtain ⟨U, hUo, hUne, hU⟩ := open_locus
    obtain ⟨C, hCc, hCZ, hC⟩ := D.spread
    have hall : ⋃₀ C = univ :=
      wtr_eq_univ_of_open_subset_aux n hCc hCZ hUo hUne (hC ▸ hU)
    have hm : m ∈ ⋃₀ C := hall.symm ▸ mem_univ m
    change m ∈ {m | wtr_WeilAlg (D.univ m)}
    rw [hC]
    exact hm
  let P : wtr_Variety n := ⟨A, W, pol⟩
  obtain ⟨m, hm⟩ := D.cover P hM
  exact (transport P (D.univ m) hM (D.univ_member m) hm).2 (locus m)
    hM.polarized.isWeilType

theorem g34n_theoremA_of_premises_aux (B : g34n_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := by
  letI : ConnectedSpace (wtr_Domain 4) := wtr_domain_connectedSpace 4
  let D : g34n_TransferDatum 4 1 :=
    { S := B.P.S
      fiber := B.P.fiber
      fiber_polarized := g34h_fiber_polarized B.P
      fiber_disc := fun s ↦ g34b_fiber_disc B.P.fiber
        (g34h_fiber_polarized B.P) B.hpar s
      fiber_alg := g34s_fiber_alg B.P B.h46
      M := wtr_Domain 4
      univ := B.F.univ
      univ_member := B.F.member
      dominant := g34b_dominant B.F B.P.fiber B.Φ
      spread := B.spread
      cover := B.F.cover
      reverse := B.reverse }
  intro W hW pol hη hRos hPos hDim hDisc
  have hM : wtr_IsMember 4 1 (⟨A, W, pol⟩ : wtr_Variety 4) :=
    ⟨⟨by simpa using hDim, hW, hη, hRos, hPos⟩, hDisc⟩
  exact g34n_theoremA_of_transfer_aux D A W pol hM

theorem g34n_theoremB_of_premises_aux (B : g34n_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (hComp : ∀
      (W : letI := (finiteBetti_abelian A).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
      (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
      (pol : HQ A 2)
      (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
      (_hRos : letI := (finiteBetti_abelian A).finite 1;
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
      (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
      (_hDim : TopologicalSpace.dim A.left = 6),
      (∀ (X : Over (Spec ↧ℂ)),
        [GrpObj X] → [IsCommMonObj X] → [IsIntegral X.left] →
        [Smooth X.hom] → [IsProjective X.hom] → G34TheoremAStatement X) →
      letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW) :
    G34TheoremBStatement A := by
  exact g34c_theoremB_of A
    (fun X _ _ _ _ _ ↦ g34n_theoremA_of_premises_aux B X) hComp

end HodgeLean.Papers
