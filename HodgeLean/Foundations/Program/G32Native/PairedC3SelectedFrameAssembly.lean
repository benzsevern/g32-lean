import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedFrameSteps
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedTotalPullback

/-! # Assembly of the selected local chart statements -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The centre-chart neighbourhoods cover all scheme points of the
retained residue divisor, by Jacobson coverage on the projective slice.
Source: Hartshorne, Algebraic Geometry, II.3. -/
theorem paired_c3_selected_centre_frame_chart_at_point
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
    (hx : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    let σ := (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap σ
    ∃ U : (P.T.B i.castSucc).left.Opens,
      (P.C.slices i.castSucc).left x ∈ U ∧
      ∀ y : (P.T.B i.succ).left, σ y ∈ U →
        σ y ∈ (P.C.slices i.castSucc).left.ker.support →
        ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ (P.T.B i.succ).left)
      (_ : IsOpenImmersion j), y ∈ j.opensRange ∧
      ∃ f : Fin R.P.k → A, RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f) := by
  dsimp only
  let PP : Over (Spec ↧ℂ) := Over.mk
    (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))
  letI : IsProjective PP.hom := s0_projective_space_projective _ _
  letI : JacobsonSpace (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)) := LocallyOfFiniteType.jacobsonSpace PP.hom
  let σ := (P.T.b i).left
  let I := (P.C.slices i.castSucc).left.ker.comap σ
  let 𝒜 : Set (P.T.B i.castSucc).left.Opens := {U |
    ∀ y : (P.T.B i.succ).left, σ y ∈ U →
      σ y ∈ (P.C.slices i.castSucc).left.ker.support →
      ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ (P.T.B i.succ).left)
      (_ : IsOpenImmersion j), y ∈ j.opensRange ∧
      ∃ f : Fin R.P.k → A, RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f)}
  let O : (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)).Opens := ⨆ U : 𝒜, (P.C.slices i.castSucc).left ⁻¹ᵁ U.val
  have hcov : ((s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support :
      Set (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))) ⊆ (O : Set _) := by
    apply G32Native.paired_c3_closed_point_cover
      (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support.isClosed O.isOpen
    intro z hz hclosed
    let p : ComplexPoint PP := Over.homMk (pointOfClosedPoint PP.hom z hclosed)
      (pointOfClosedPoint_comp PP.hom z hclosed)
    have hp : p.underlying = z := pointOfClosedPoint_apply PP.hom z hclosed _
    obtain ⟨U, hpU, hU⟩ := paired_c3_selected_centre_frame_charts_aux R P i hi p (by rwa [hp])
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨⟨U, hU⟩, ?_⟩
    change (P.C.slices i.castSucc).left z ∈ U
    simpa only [hp] using hpU
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
  exact ⟨U.val, hxU, U.property⟩

/-- Select a regular affine chart at each point of the actual total
transform, and take its quotient conormal frame of rank k.
Source: Hartshorne, Algebraic Geometry, II.5, II.7.13 and II.8;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_selected_total_transform_frames
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
    ∀ x : I.subscheme, ∃ (U : I.subscheme.Opens), x ∈ U ∧ IsAffine U.toScheme ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (s2c_conormal I.subschemeι) ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) : U.toScheme.Modules)) := by
  dsimp only
  let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  letI := P.C.sliceImmersion i.castSucc
  apply G32Native.paired_c3_local_frames_of_regular_charts I R.P.k
  intro z
  let y := I.subschemeι z
  have hyI : y ∈ I.support := by
    change y ∈ (I.support : Set (P.T.B i.succ).left)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hs : (P.T.b i).left y ∈ (P.C.slices i.castSucc).left.ker.support := by
    have h := hyI
    change y ∈ (((P.C.slices i.castSucc).left.ker.comap (P.T.b i).left).support : Set _) at h
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h
  by_cases hk : (P.T.b i).left y ∈ K.support
  · have hrange : (P.T.b i).left y ∈ Set.range (P.C.slices i.castSucc).left := by
      change (P.T.b i).left y ∈ ((P.C.slices i.castSucc).left.ker.support : Set _) at hs
      rw [Scheme.Hom.support_ker,
        (P.C.slices i.castSucc).left.isClosedEmbedding.isClosed_range.closure_eq] at hs
      exact hs
    obtain ⟨x, hx⟩ := hrange
    have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
    have hKres : K.comap (P.C.slices i.castSucc).left =
        s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) := by
      dsimp only [K]
      rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]
    have hxH : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support := by
      change x ∈ ((s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support : Set (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)))
      rw [← hKres, Scheme.IdealSheafData.support_comap]
      change (P.C.slices i.castSucc).left x ∈ K.support
      rwa [hx]
    obtain ⟨U, hxU, hU⟩ := paired_c3_selected_centre_frame_chart_at_point R P i hi x hxH
    exact hU y (by rwa [hx] at hxU) hs
  · exact paired_c3_selected_off_centre_frame_chart_aux R P i hi y hs hk

#print axioms paired_c3_selected_centre_frame_chart_at_point
#print axioms paired_c3_selected_total_transform_frames
/-- The selected residual union carries the precise affine-frame input
and cartesian square used by the last-blowup consumer.
Source: Hartshorne, Algebraic Geometry, II.3, II.5 and II.8;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_selected_final_union_frames
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    ∃ σ : (P.T.B (Fin.last R.r)).left ⟶ (P.T.B i.castSucc).left,
      let I := (P.C.slices i.castSucc).left.ker.comap σ
      let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
      let Jres := K.comap σ ⊔ I
      ∃ p : (G32Native.residualUnion P.C.ℓ Jres).left ⟶
          (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left,
        CategoryTheory.IsPullback p (G32Native.residualUnionι P.C.ℓ Jres).left
          (P.C.slices i.castSucc).left σ ∧
        ∀ x : (G32Native.residualUnion P.C.ℓ Jres).left,
          ∃ U : (G32Native.residualUnion P.C.ℓ Jres).left.Opens,
            x ∈ U ∧ IsAffine U.toScheme ∧
            Nonempty ((Scheme.Modules.pullback U.ι).obj
              (s2c_conormal (G32Native.residualUnionι P.C.ℓ Jres).left) ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) :
                U.toScheme.Modules)) := by
  letI := P.C.h_T20_slice_immersion
  letI := P.C.sliceImmersion i.castSucc
  have hsucc : i.succ = Fin.last R.r := Fin.ext (by simpa using hi)
  have hframes := paired_c3_selected_total_transform_frames R P i hi
  have hidentity := pairedC3_selected_last_total_transform R P i hi
  have h : ∃ σ : (P.T.B i.succ).left ⟶ (P.T.B i.castSucc).left,
      let I := (P.C.slices i.castSucc).left.ker.comap σ
      let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
      I = (P.C.slices i.succ).left.ker ⊓ (K.comap σ ⊔ I) ∧
      ∀ x : I.subscheme, ∃ U : I.subscheme.Opens,
        x ∈ U ∧ IsAffine U.toScheme ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj (s2c_conormal I.subschemeι) ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) : U.toScheme.Modules)) :=
    ⟨(P.T.b i).left, hidentity, hframes⟩
  rw [hsucc, P.C.sliceLast] at h
  obtain ⟨σ, hI, hframes⟩ := h
  refine ⟨σ, ?_⟩
  dsimp only
  obtain ⟨p, sq⟩ := G32Native.paired_last_total_transform_pullback P.C.ℓ _
    (P.C.slices i.castSucc).left σ hI
  refine ⟨p, sq, ?_⟩
  change ∀ x : (P.C.ℓ.left.ker ⊓ _).subscheme,
    ∃ U : (P.C.ℓ.left.ker ⊓ _).subscheme.Opens,
      x ∈ U ∧ IsAffine U.toScheme ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj
        (s2c_conormal (P.C.ℓ.left.ker ⊓ _).subschemeι) ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin R.P.k) : U.toScheme.Modules))
  rw [← hI]
  exact hframes

#print axioms paired_c3_selected_final_union_frames
end HodgeLean.Foundations.Program.ResidueSelected
