import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedAdaptedCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateBlowupRegularCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedOffCentre
import HodgeLean.Foundations.Program.G32Native.PairedC3OpenRegularCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedChartCover
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedSliceDimensions
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedAmbientDimension
import HodgeLean.Foundations.Program.G32Native.PairedC3EtaleEquationsInside
import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedChartFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3LocalFrames

/-! # Local statements for the selected total-transform frame construction -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- Around a closed point of the reduced residue divisor, restrict the
supplied Rees charts to pointwise adapted étale equations for the actual slice.
The resulting regular equations refer to the pulled-back ideal itself.
Source: Hartshorne, Algebraic Geometry, II.5, II.7.13 and II.8;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8;
EGA IV, 17.11.1. -/
theorem paired_c3_selected_centre_frame_charts_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))))
    (hx : x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    let σ := (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap σ
    ∃ U : (P.T.B i.castSucc).left.Opens,
      (P.C.slices i.castSucc).left x.underlying ∈ U ∧
      ∀ y : (P.T.B i.succ).left, σ y ∈ U →
        σ y ∈ (P.C.slices i.castSucc).left.ker.support →
        ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ (P.T.B i.succ).left)
      (_ : IsOpenImmersion j), y ∈ j.opensRange ∧
      ∃ f : Fin R.P.k → A, RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f) := by
  dsimp only
  obtain ⟨d, n, hn, U, u, v, a, hxU, hu, hv, F, e, hF, hI, hvc, hdc⟩ :=
    paired_c3_selected_last_adapted_coordinates R P i hi x hx
  letI := HodgeLean.Foundations.Program.s2e_step1_sectionAlgebra (P.T.B i.castSucc) U.1
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  have hK : K.ideal U = Ideal.span
      {F (MvPolynomial.X (e ⟨1, by omega⟩)), F (MvPolynomial.X (e 0))} := by
    change (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U ⊔
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = _
    rw [hu, hv, ← Ideal.span_union, Set.singleton_union,
      ← Ideal.span_pair_sub_mul_right u v a, hdc, hvc]
    rfl
  refine ⟨U.1, hxU, ?_⟩
  intro y hy _
  have H := G32Native.paired_c3_coordinate_blowup_regular_charts
    (P.T.B i.castSucc) (P.T.B i.succ) (P.T.b i) K
    (P.C.slices i.castSucc).left.ker (P.T.hcartier i) (P.T.hblowup i)
    U F.toRingHom hF (n + 1) (by omega) e hK hI y hy
  obtain ⟨A, j, hj, hyj, f, hreg, hgen⟩ := H
  refine ⟨A, j, hj, hyj, (fun t => f (Fin.cast hn.symm t)), ?_, ?_⟩
  · rw [← List.ofFn_congr hn f]
    exact hreg
  · rw [hgen]
    congr 1
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Fin.cast hn t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Fin.cast hn.symm t, rfl⟩

/-- Off the paired centre, transport smooth-slice regular equations through
the actual off-centre isomorphism, retaining the pulled-back ideal.
Source: Hartshorne, Algebraic Geometry, II.5, II.7.14 and II.8. -/
theorem paired_c3_selected_off_centre_frame_chart_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (y : (P.T.B i.succ).left)
    (hslice : (P.T.b i).left y ∈ (P.C.slices i.castSucc).left.ker.support)
    (hcentre : (P.T.b i).left y ∉
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).support) :
    let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
    ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ (P.T.B i.succ).left)
      (_ : IsOpenImmersion j), y ∈ j.opensRange ∧
      ∃ f : Fin R.P.k → A, RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f) := by
  dsimp only
  let σ := (P.T.b i).left
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let U : (P.T.B i.castSucc).left.Opens :=
    ⟨(K.support : Set _)ᶜ, K.support.isClosed.isOpen_compl⟩
  let V := σ ⁻¹ᵁ U
  obtain ⟨e, he, _⟩ := paired_c3_selected_off_centre_iso R P i
  have hfac : e.hom ≫ U.ι = V.ι ≫ σ := by
    rw [he]
    exact morphismRestrict_ι σ U
  let g := e.hom ≫ U.ι
  letI : IsOpenImmersion g := by dsimp only [g]; infer_instance
  let I := (P.C.slices i.castSucc).left.ker
  letI : SmoothOfRelativeDimension (R.P.k + R.P.k) (P.T.B i.castSucc).hom := by
    simpa only [two_mul] using paired_c3_selected_ambient_relative_dimension R P i.castSucc
  letI : SmoothOfRelativeDimension R.P.k (I.subschemeι ≫ (P.T.B i.castSucc).hom) :=
    paired_c3_selected_slice_image_dimension R P i.castSucc
  let z : V.toScheme := ⟨y, hcentre⟩
  have hz : g z ∈ I.support := by
    have h := congrArg (fun f : V.toScheme ⟶ (P.T.B i.castSucc).left => f z) hfac
    change g z = σ y at h
    rw [h]
    exact hslice
  obtain ⟨A, j, hj, hzj, f, hreg, hI⟩ :=
    G32Native.paired_c3_open_regular_chart (P.T.B i.castSucc).hom g I
      R.P.k R.P.k z hz
  letI := hj
  refine ⟨A, j ≫ V.ι, inferInstance, ?_, f, hreg, ?_⟩
  · obtain ⟨w, hw⟩ := hzj
    exact ⟨w, congrArg (fun t : V.toScheme => V.ι t) hw⟩
  · have heq : ((I.comap σ).comap (j ≫ V.ι)) = (I.comap g).comap j := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        Category.assoc, ← hfac]
    change Ideal.map (Scheme.ΓSpecIso A).hom.hom
      (((I.comap σ).comap (j ≫ V.ι)).ideal ⟨⊤, isAffineOpen_top _⟩) = _
    rw [heq]
    exact hI

end HodgeLean.Foundations.Program.ResidueSelected
