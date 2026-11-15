import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedSlicedComponent
import HodgeLean.Foundations.Program.G32Native.SelectedInitialPairedEtale
import HodgeLean.Foundations.Program.SchoenTransferR2AssemblyHelpers
import HodgeLean.Foundations.Program.G32Native.SelectedResidualDeckNative
import HodgeLean.Foundations.Program.G32Native.SelectedTowerP3aClasses
import HodgeLean.Foundations.Program.SchoenCycleC2NeighbourhoodHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ProjectiveCoheightHelpers
import HodgeLean.Foundations.Program.G32Native.JointSelectedComponent
import HodgeLean.Foundations.Program.G32Native.SelectedTowerSliceGeometry
import HodgeLean.Foundations.Program.G32Native.ComponentInstances
import HodgeLean.Foundations.Program.G32Native.NormalizedComponentClass

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
attribute [local instance] G32JointComponent.hQ


/-- Retain source coheights and generic image degrees on the same selected slice. -/
theorem jointSelectedP3aGeometry
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (T.B i) (T.η i) ⟶ R.W₀)
    (hf : f 0 = T.eW.hom ∧ ∀ i : Fin R.r, f i.succ = T.w i ≫ f i.castSucc)
    (C : G32JointSlicedComponent R T W eFinal) :
    TopologicalSpace.dim W.left = 2*R.P.k ∧
    TopologicalSpace.dim R.W₀.left = 2*R.P.k ∧
    (∃ V : W.left.Opens, Set.range C.ι.left ⊆ V ∧ Smooth (V.ι ≫ W.hom)) ∧
    (∀ t : Fin S.m, ∀ x ∈ (s2e_componentCycle
      (C.ι ≫ (End.of (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ^ t.val).asHom) ℚ).support,
      Order.coheight x = R.P.k) ∧
    (∀ t : Fin S.m, 0 < a1p_degree (eFinal.inv ≫ f (Fin.last R.r)).left
      ((C.ι ≫ (End.of (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) ^ t.val).asHom).left
        (genericPoint C.Q.left))) := by
  letI := C.h_T20_slice_immersion
  letI : IsIntegral C.Q.left := C.hQ
  letI := C.h_T20_component_immersion
  obtain ⟨_, hQs, _⟩ := g32n_componentInstances R.P.k C.Q C.eQ
  letI := hQs
  obtain ⟨hfin, hft, hqc, hsep, hdim, U, hU, he⟩ :=
    G32Native.selected_tower_final_slice_neighbourhood S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder W eFinal
      R.P.k R.hselected C.ℓ C.h_T20_avoidance
  letI := hfin
  letI := hft
  letI := hqc
  letI := hsep
  let β := eFinal.inv ≫ s2b_normalizationMap (T.B (Fin.last R.r)) (T.η (Fin.last R.r))
  have hproj : C.ι ≫ β = C.eQ.hom ≫ C.ℓ := by
    simpa only [β, Category.assoc] using C.h_T20_square
  have hrange : Set.range (C.ι ≫ β).left ⊆ U := by
    rw [hproj]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨C.eQ.hom.left x, rfl⟩
  obtain ⟨V, hV, hsm⟩ := s2e_smooth_neighbourhood_of_etale C.ι β U hrange he
  let δ := eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom
  let φ := eFinal.inv ≫ f (Fin.last R.r)
  have hd : δ ≫ β = β := by
    simp only [δ, β, Category.assoc, eFinal.hom_inv_id_assoc, T.hd]
  have hcodim : ∀ t : Fin S.m, ∀ x ∈
      (s2e_componentCycle (C.ι ≫ (End.of δ ^ t.val).asHom) ℚ).support,
      Order.coheight x = R.P.k := by
    intro t
    exact s2e_projective_orbit_component_coheight R.P.k C.eQ C.ℓ C.ι δ β hd hproj
      U hU inferInstance he hdim t.val
  have hdim₀ : TopologicalSpace.dim R.W₀.left = 2*R.P.k := by
    rw [← R.hselected]
    exact s2e_finite_curve_power_target_dimension R.Y R.W₀ R.hdimY (R.h+1) R.q₀ R.hqsurj
  have hdomη := s2v_n2b_dominant_aux S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator T.B T.e₀ T.b T.D T.hD₀ T.htransform T.hcartier T.hblowup T.η T.hη₀ T.hη T.eW T.heW T.hgeneric T.w T.hw T.d T.hd T.hdinit T.hdw T.horder (Fin.last R.r)
  letI := hdomη
  have hdomNorm : IsDominant (T.η (Fin.last R.r)).fromNormalization := by
    letI : IsDominant ((T.η (Fin.last R.r)).toNormalization ≫
        (T.η (Fin.last R.r)).fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]
      exact hdomη
    exact IsDominant.of_comp (T.η (Fin.last R.r)).toNormalization
      (T.η (Fin.last R.r)).fromNormalization
  letI := hdomNorm
  letI : IsDominant β.left := by
    change IsDominant (eFinal.inv.left ≫ (T.η (Fin.last R.r)).fromNormalization)
    infer_instance
  have hdimW : TopologicalSpace.dim W.left = 2*R.P.k := by
    have h := s2e_finite_surjective_krull_dimension β.left
    change ((topologicalKrullDim W.left).unbotD 0).toNat = _
    rw [h]
    exact hdim
  let ℓ₀ := C.slices 0 ≫ T.e₀.hom
  letI : IsClosedImmersion ℓ₀.left := by
    letI := C.sliceImmersion 0
    change IsClosedImmersion ((C.slices 0).left ≫ T.e₀.hom.left)
    infer_instance
  have hslice : ∀ i, C.slices i ≫ s2e_towerTotalMap T.B T.e₀.hom T.b i = ℓ₀ := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [s2e_towerTotalMap_succ, ← Category.assoc, C.sliceComp, ih]
  have hproj₀ : C.ι ≫ φ ≫ R.β₀ = C.eQ.hom ≫ ℓ₀ := by
    have hh := s4_assembly_component_projection R.r T.B T.η T.b T.hη T.w T.hw
      R.W₀ R.B₀ W C.Q _ T.e₀ T.eW R.β₀ T.heW eFinal f hf.1 hf.2
      C.eQ.hom C.ℓ C.ι C.h_T20_square
    rw [← C.sliceLast, Category.assoc, hslice] at hh
    simpa only [φ, Category.assoc] using hh
  have hδ : δ ≫ φ = φ ≫ R.d₀ := by
    have hfu := s2e_towerTotalMap_unique _ T.eW.hom T.w f hf.1 hf.2
    have hh := s2e_towerTotalMap_equivariant _ T.eW.hom T.w T.d R.d₀
      T.hdinit T.hdw (Fin.last R.r)
    simp only [δ, φ, Category.assoc, eFinal.hom_inv_id_assoc]
    rw [hfu, hh]
  have hd₀ : δ ≫ (φ ≫ R.β₀) = φ ≫ R.β₀ := by
    rw [← Category.assoc, hδ, Category.assoc, R.hd₀]
  have hk : 0 < R.P.k := by have := R.hh; have := R.hselected; omega
  have horder₀ : End.of R.d₀ ^ S.m = 1 := by
    have hh := g32w_translation_order S R.Y R.a R.e R.ha1 R.hamul
      (R.h+1) R.q₀ R.hqinv R.hq (s2_delta S (R.h+1) R.hh 1) R.d₀ R.hgenerator
    exact congrArg End.of hh
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (R.P.k+1)) (Spec ↧ℂ))
  have hpair : ∀ i : Fin R.r,
      (s2c_branchIdeal R.Z R.B₀ R.h R.γ (Point.map R.p₀ (R.eY (R.y (R.σ ⟨2*i.val, by omega⟩))))).comap
        (𝟙 PP ≫ ℓ₀).left =
      (s2c_branchIdeal R.Z R.B₀ R.h R.γ (Point.map R.p₀ (R.eY (R.y (R.σ ⟨2*i.val+1, by omega⟩))))).comap
        (𝟙 PP ≫ ℓ₀).left := by
    intro i
    simpa only [Category.id_comp, ℓ₀, Over.comp_left, Scheme.IdealSheafData.comap_comp, ← T.hD₀]
      using C.pairInitial i
  have hsingle : ∀ i : Fin R.r, Nonempty (s2c_subscheme PP
      ((s2c_branchIdeal R.Z R.B₀ R.h R.γ (Point.map R.p₀ (R.eY (R.y (R.σ ⟨2*i.val, by omega⟩))))).comap
        (𝟙 PP ≫ ℓ₀).left) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (R.P.k-1+1)) (Spec ↧ℂ))) := by
    intro i
    simpa only [Category.id_comp, ℓ₀, Over.comp_left, Scheme.IdealSheafData.comap_comp, ← T.hD₀]
      using C.singleInitial i
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral R.P.k
  obtain ⟨U₀, hgenPP, he₀, _⟩ := G32Native.selected_initial_paired_etale_open S R.Y R.Z R.W₀ R.B₀
    R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit
    (rsq_Quot S.χ.ker R.C) (Fin (g32p_exponents S).length) R.eY.toEquiv R.hpointAction
    (fun i => Point.map R.p₀ (R.eY (R.y i))) R.hbranch
    R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ
    R.β₀ R.hβ₀ R.d₀ R.hd₀ horder₀ R.hgenerator PP R.P.k R.r hk (Iso.refl PP) ℓ₀ R.σ hpair hsingle
  have hgen : (C.eQ.hom ≫ ℓ₀).left (genericPoint C.Q.left) ∈ U₀ := by
    change ℓ₀.left (C.eQ.hom.left (genericPoint C.Q.left)) ∈ U₀
    rw [genericPoint_eq_of_isOpenImmersion C.eQ.hom.left]
    exact hgenPP
  have hdimB₀ : TopologicalSpace.dim R.B₀.left = 2*R.P.k := by
    rw [← R.hselected]
    exact s2e_finite_curve_power_target_dimension R.Z R.B₀ R.hdimZ (R.h+1) R.γ R.hγsurj
  letI : IsClosedImmersion (C.eQ.hom ≫ ℓ₀).left := by
    change IsClosedImmersion (C.eQ.hom.left ≫ ℓ₀.left)
    infer_instance
  have hbase : Order.coheight ((C.eQ.hom ≫ ℓ₀).left (genericPoint C.Q.left)) = R.P.k := by
    exact s2e_immersion_generic_coheight_of_dimensions (C.eQ.hom ≫ ℓ₀) R.P.k R.P.k
      (s2e_projective_model_dimension C.Q R.P.k C.eQ) (by simpa only [two_mul] using hdimB₀)
  refine ⟨hdimW, hdim₀, ⟨V, hV, hsm⟩, hcodim, ?_⟩
  intro t
  let x := (C.ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint C.Q.left)
  have hsquare : (C.ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ≫ R.β₀ = C.eQ.hom ≫ ℓ₀ := by
    simpa only [Category.assoc, s2e_power_projection δ (φ ≫ R.β₀) hd₀ t.val] using hproj₀
  have hp : R.β₀.left (φ.left x) = (C.eQ.hom ≫ ℓ₀).left (genericPoint C.Q.left) :=
    congrArg (fun f : C.Q ⟶ R.B₀ => f.left (genericPoint C.Q.left)) hsquare
  have htarget : Order.coheight (φ.left x) = R.P.k :=
    (s2e_coheight_eq_of_finite_etale_near R.β₀ U₀ inferInstance he₀ (φ.left x)
      (hp ▸ hgen)).trans ((congrArg Order.coheight hp).trans hbase)
  have hsource : Order.coheight x = R.P.k := by
    apply hcodim t
    rw [s2e_componentCycle_support]
    exact Set.mem_singleton _
  apply (a1d_degree_pos_iff φ x).2
  have h₁ := HodgeLean.Foundations.QuotientDuality.retained_integral_dimension_formula W x
  have h₂ := HodgeLean.Foundations.QuotientDuality.retained_integral_dimension_formula R.W₀ (φ.left x)
  rw [hsource, hdimW] at h₁
  rw [htarget, hdim₀] at h₂
  exact ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top R.P.k) (h₂.trans h₁.symm)

#print axioms jointSelectedP3aGeometry
end ResidueSelected
end HodgeLean.Foundations.Program
