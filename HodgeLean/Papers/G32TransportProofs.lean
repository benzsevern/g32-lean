import HodgeLean.Papers.G32TransportDefs

/-! # Proof obligations for G32 isogeny transport -/

noncomputable section

set_option maxRecDepth 2000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations

namespace HodgeLean.Papers

theorem g32tr_isogeny_smooth_aux {P Q : g32t_Sixfold} (f : P.X ⟶ Q.X)
    [IsMonHom f] (hf : ccm2_IsogenyOnPoints f) : Smooth f.left := by
  exact ccm3_smooth_surjective_group_hom f hf.2

private theorem g32tr_cycleClass_mem_span (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (c : AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X q c ∈ algebraicCycleClassSpan X q := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let g : {z : X.left // Order.coheight z = q} → HQ X (2 * q) :=
    fun z ↦ c z.1 • cycleComponentSheafClass X z.1 z.2
  have hfin : (Function.support g).Finite := by
    apply (c.finite_support.preimage (Set.injOn_of_injective Subtype.val_injective)).subset
    intro z hz
    intro hcz
    apply hz
    simp only [g, hcz, zero_smul]
    rfl
  unfold ccm3_cycleClass
  rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by
    intro z hz
    exact hfin.mem_toFinset.mpr hz)]
  apply Submodule.sum_mem
  intro z hz
  apply Submodule.smul_mem
  unfold algebraicCycleClassSpan
  apply le_sSup (s := {Submodule.span ℚ {cycleComponentSheafClass X y hy} |
    (y : X.left) (hy : Order.coheight y = q)})
  exact ⟨z.1, z.2, rfl⟩
  exact Submodule.subset_span (Set.mem_singleton _)

theorem g32tr_isogeny_pullback_span_aux {P Q : g32t_Sixfold} (f : P.X ⟶ Q.X)
    [IsMonHom f] (hf : ccm2_IsogenyOnPoints f) (p : ℕ) :
    (algebraicCycleClassSpan Q.X p).map (homPullback f (2 * p)) ≤
      algebraicCycleClassSpan P.X p := by
  letI : Smooth f.left := g32tr_isogeny_smooth_aux f hf
  apply Submodule.map_le_iff_le_comap.mpr
  rw [algebraicCycleClassSpan]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  change homPullback f (2 * p) (cycleComponentSheafClass Q.X x hx) ∈
    algebraicCycleClassSpan P.X p
  rw [ccm6_homPullback_prime f p x hx]
  exact g32tr_cycleClass_mem_span P.X p _

private theorem g32tr_contract_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (f : V →ₗ[ℚ] W)
    (ω : ⋀[ℚ]^2 V) (φ : Module.Dual ℚ W) :
    f (Foundations.Symplectic.contract ω (φ.comp f)) =
      Foundations.Symplectic.contract (exteriorPower.map 2 f ω) φ := by
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
  exact LinearMap.congr_fun hLR ω

private theorem g32tr_surjective_of_map_nondegenerate
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
      have hn := g32tr_contract_map f ωV (φ - ψ)
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

private theorem g32tr_derivationExt_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
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

private def g32tr_exteriorCast {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m n : ℕ} (h : m = n) : ⋀[ℚ]^m V → ⋀[ℚ]^n V := by
  subst n
  exact id

@[simp] private theorem g32tr_exteriorCast_symm {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m n : ℕ} (h : m = n) (w : ⋀[ℚ]^m V) :
    g32tr_exteriorCast h.symm (g32tr_exteriorCast h w) = w := by
  subst n
  rfl

@[simp] private theorem g32tr_exteriorCast_cancel {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m n : ℕ} (h : m = n) (g : n = m) (w : ⋀[ℚ]^m V) :
    g32tr_exteriorCast g (g32tr_exteriorCast h w) = w := by
  subst n
  rfl

private theorem g32tr_kernel_cast {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ}
    (A : HodgeBlocks.WeilAction M d) {k l : ℕ} (h : k = l)
    (w : ⋀[ℚ]^(k + k) V)
    (hw : HodgeBlocks.WeilAction.derivationKernelOperatorQ A k w = 0) :
    HodgeBlocks.WeilAction.derivationKernelOperatorQ A l
      (g32tr_exteriorCast (congrArg (fun n => n + n) h) w) = 0 := by
  subst l
  exact hw

private def g32tr_cohomCast (X : Over (Spec ↧ℂ)) {p q : ℕ} (h : p = q) :
    HQ X (2 * p) →ₗ[ℚ] HQ X (2 * q) :=
  (HQ.castEquiv X (congrArg (fun n => 2 * n) h)).toLinearMap

private theorem g32tr_span_cast (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p q : ℕ} (h : p = q) (x : HQ X (2 * p))
    (hx : x ∈ algebraicCycleClassSpan X p) :
    g32tr_cohomCast X h x ∈ algebraicCycleClassSpan X q := by
  subst q
  simpa [g32tr_cohomCast] using hx

private theorem g32tr_weilImage_cast (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {k l : ℕ} (h : k = l)
    (w : ⋀[ℚ]^(k + k) (HQ X 1)) :
    g32tr_cohomCast X h
        (HQ.castEquiv X (two_mul k).symm ((cupProductOf X).cupWedgeMap (k + k) w)) =
      HQ.castEquiv X (two_mul l).symm
        ((cupProductOf X).cupWedgeMap (l + l)
          (g32tr_exteriorCast (congrArg (fun n => n + n) h) w)) := by
  subst l
  rfl

theorem g32tr_weilAlg_pullback_aux (P Q : g32t_Sixfold)
    (hP : g32t_PolarizedWeil P) (hQ : g32t_PolarizedWeil Q)
    (h : g32t_KIsog P Q) (hAlg : g32t_WeilAlg Q) : g32t_WeilAlg P := by
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
    g32tr_surjective_of_map_nondegenerate φ _ _ hP.nondegenerate c (ne_of_gt hc)
      hpolWedge hdim
  have hφinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hφsurj
  intro hWP
  have hkP : Module.finrank ℂ ↥(P.W.Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
        (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
          (torusCohomology_cupProductOf P.X)).weight1.H
          (1, 0)) = 3 := by
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
          (1, 0)) = 3 := by
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
  have hk : k = 3 := hkP
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
            (torusCohomology_cupProductOf P.X)).weight1.H (1, 0)) = 6 := by omega
  let wP6 : ⋀[ℚ]^6 (HQ P.X 1) :=
    g32tr_exteriorCast (congrArg (fun n => n + n) hkP) wP
  have hφextSurj : Function.Surjective (exteriorPower.map 6 φ) :=
    exteriorPower.map_surjective hφsurj
  obtain ⟨wQ, hwQmap⟩ := hφextSurj wP6
  have hder : (HodgeBlocks.derivationExt P.W.J 6).comp (exteriorPower.map 6 φ) =
      (exteriorPower.map 6 φ).comp (HodgeBlocks.derivationExt Q.W.J 6) :=
    g32tr_derivationExt_map φ Q.W.J P.W.J hJ 6
  have hquad : (HodgeBlocks.WeilAction.derivationKernelOperatorQ P.W 3).comp
      (exteriorPower.map 6 φ) =
      (exteriorPower.map 6 φ).comp
        (HodgeBlocks.WeilAction.derivationKernelOperatorQ Q.W 3) := by
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
  have hwPker : HodgeBlocks.WeilAction.derivationKernelOperatorQ P.W 3 wP6 = 0 := by
    exact g32tr_kernel_cast P.W hkP wP hwPker0
  have hwQker : HodgeBlocks.WeilAction.derivationKernelOperatorQ Q.W 3 wQ = 0 := by
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
            (torusCohomology_cupProductOf Q.X)).weight1.H (1, 0)) = 6 := by omega
  let wQ0 : ⋀[ℚ]^(_ + _) (HQ Q.X 1) :=
    g32tr_exteriorCast (congrArg (fun n => n + n) hkQ).symm wQ
  have hwQ : wQ0 ∈ Q.W.weilClasses
      (h10_sup_h01_eq_top (finiteBetti_abelian Q.X)
        (spec_bettiDeRhamIso_abelian Q.X) (hodgeDecomposition_of_abelian Q.X) TQ)
      hQ.isWeilType := by
    rw [Q.W.weilClasses_eq_ker_derivationKernelOperatorQ _ hQ.isWeilType
      (by norm_num : (0 : ℚ) < 3), LinearMap.mem_ker]
    exact g32tr_kernel_cast Q.W hkQ.symm wQ hwQker
  have hyAlg := hAlg hQ.isWeilType
  rw [WeilClassesAlgebraic] at hyAlg
  have hy0 := hyAlg (Submodule.mem_map_of_mem hwQ)
  have hy : (cupProductOf Q.X).cupWedgeMap 6 wQ ∈ algebraicCycleClassSpan Q.X 3 := by
    have hc := g32tr_span_cast Q.X hkQ _ hy0
    change g32tr_cohomCast Q.X hkQ
      (HQ.castEquiv Q.X (two_mul _).symm
        ((cupProductOf Q.X).cupWedgeMap (_ + _) wQ0)) ∈
          algebraicCycleClassSpan Q.X 3 at hc
    rw [g32tr_weilImage_cast Q.X hkQ wQ0] at hc
    simpa [wQ0] using hc
  have hcup := LinearMap.congr_fun (spec_homPullback_cupWedgeMap f 6) wQ
  have hfixed : homPullback f 6 ((cupProductOf Q.X).cupWedgeMap 6 wQ) =
      (cupProductOf P.X).cupWedgeMap 6 wP6 := by
    simpa [φ, hwQmap] using hcup
  have hxP3 : (cupProductOf P.X).cupWedgeMap 6 wP6 ∈
      algebraicCycleClassSpan P.X 3 := by
    apply g32tr_isogeny_pullback_span_aux f hfisog 3
    refine Submodule.mem_map.mpr ⟨_, hy, ?_⟩
    simpa using hfixed
  have hxP0 := g32tr_span_cast P.X hkP.symm _ hxP3
  change g32tr_cohomCast P.X hkP.symm
    (HQ.castEquiv P.X (two_mul 3).symm
      ((cupProductOf P.X).cupWedgeMap (3 + 3) wP6)) ∈
        algebraicCycleClassSpan P.X _ at hxP0
  rw [g32tr_weilImage_cast P.X hkP.symm wP6] at hxP0
  simp only [wP6, g32tr_exteriorCast_cancel] at hxP0
  change HQ.castEquiv P.X _ ((cupProductOf P.X).cupWedgeMap (_ + _) wP) ∈
    algebraicCycleClassSpan P.X _
  exact hxP0

end HodgeLean.Papers
