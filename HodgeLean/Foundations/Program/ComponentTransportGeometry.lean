import HodgeLean.Foundations.Program.ComponentTransportDefs
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
set_option backward.isDefEq.respectTransparency false
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful


open AlgebraicTopology.Singular

theorem b65y_homology_equivariant {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction b4b_Group X] [MulAction b4b_Group Y]
    (hX : ∀ g : b4b_Group, Continuous (fun x : X ↦ g • x))
    (hY : ∀ g : b4b_Group, Continuous (fun y : Y ↦ g • y))
    (e : X ≃ₜ Y) (he : ∀ (g : b4b_Group) x, e (g • x) = g • e x)
    (g : b4b_Group) (x : b6m_H1 X) :
    b6m_H1Equiv e (homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : X ↦ g • q, hX g⟩) x) =
      homologyMap ℤ 1 (TopCat.ofHom ⟨fun q : Y ↦ g • q, hY g⟩) (b6m_H1Equiv e x) := by
  let E : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom ⟨e, e.continuous⟩
  let Gx : TopCat.of X ⟶ TopCat.of X := TopCat.ofHom ⟨fun q : X ↦ g • q, hX g⟩
  let Gy : TopCat.of Y ⟶ TopCat.of Y := TopCat.ofHom ⟨fun q : Y ↦ g • q, hY g⟩
  have hc : Gx ≫ E = E ≫ Gy := by
    ext q
    exact he g q
  let K := (AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hm := congrArg (fun u ↦ (K.map u).hom x) hc
  change (K.map E).hom ((K.map Gx).hom x) = (K.map Gy).hom ((K.map E).hom x)
  simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using hm

theorem b65y_projector_equivariant {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction b4b_Group X] [MulAction b4b_Group Y]
    (hX : ∀ g : b4b_Group, Continuous (fun x : X ↦ g • x))
    (hY : ∀ g : b4b_Group, Continuous (fun y : Y ↦ g • y))
    (e : X ≃ₜ Y) (he : ∀ (g : b4b_Group) x, e (g • x) = g • e x) (x : b6m_H1 X) :
    b6m_H1Equiv e (b63l_homologyOperator X hX x) =
      b63l_homologyOperator Y hY (b6m_H1Equiv e x) := by
  simp only [b63l_homologyOperator, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  change b6m_H1Equiv e (b4b_projectorCoeff g • homologyMap ℤ 1
    (TopCat.ofHom ⟨fun q : X ↦ g • q, hX g⟩) x) =
    b4b_projectorCoeff g • homologyMap ℤ 1
      (TopCat.ofHom ⟨fun q : Y ↦ g • q, hY g⟩) (b6m_H1Equiv e x)
  rw [map_zsmul, b65y_homology_equivariant hX hY e he]

def b65y_saturation_equiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N) (e : M ≃ₗ[ℤ] N)
    (he : ∀ x, e (A x) = B (e x)) :
    b63l_saturation (LinearMap.range A) ≃ₗ[ℤ] b63l_saturation (LinearMap.range B) := by
  have hm (x : M) (hx : x ∈ b63l_saturation (LinearMap.range A)) :
      e x ∈ b63l_saturation (LinearMap.range B) := by
    obtain ⟨n, hn, y, hy⟩ := hx
    exact ⟨n, hn, e y, by rw [← he, hy, e.map_smul]⟩
  have hn (y : N) (hy : y ∈ b63l_saturation (LinearMap.range B)) :
      e.symm y ∈ b63l_saturation (LinearMap.range A) := by
    obtain ⟨n, hn, x, hx⟩ := hy
    refine ⟨n, hn, e.symm x, ?_⟩
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, hx, e.map_smul, LinearEquiv.apply_symm_apply]
  let f : b63l_saturation (LinearMap.range A) ≃+ b63l_saturation (LinearMap.range B) :=
    { toFun := fun x ↦ ⟨e x.val, hm x.val x.property⟩
      invFun := fun y ↦ ⟨e.symm y.val, hn y.val y.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add e x.val y.val)
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y.val) }
  exact f.toIntLinearEquiv

set_option maxHeartbeats 400000 in
theorem b65y_overlap_transport {c c' : Fin 10 → ℂ} {g g' : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (D' : b65z_SharedFamily c' g')
    (t : b6t_polydisc c) (t' : b6t_polydisc c')
    (e : b65z_fibre c D.C t ≃ₜ b65z_fibre c' D'.C t')
    (hol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e)
    (inv_hol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm)
    (eqv : ∀ (g : b4b_Group) x, e (g • x) = g • e x) :
    ∃ f : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) t ≃ₗ[ℤ]
      b63l_parameterLattice c' D'.C D'.hC (b6t_polydisc c') (Subset.refl _) t',
      (∀ x, f (D.A t x) = D'.A t' (f x)) ∧
      ∀ x y, b63e_singularQ c' D'.C D'.hC (b6t_polydisc c') (Subset.refl _) t'
        (D'.P t') (D'.Q t') (f x) (f y) =
      b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) t (D.P t) (D.Q t) x y := by
  let hX := fun g ↦ (b6m_deck c b4b_Group D.C D.hC t g).continuous
  let hY := fun g ↦ (b6m_deck c' b4b_Group D'.C D'.hC t' g).continuous
  let E := b6m_H1Equiv e
  have hcomm := b65y_projector_equivariant hX hY e eqv
  let f : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) t ≃ₗ[ℤ]
      b63l_parameterLattice c' D'.C D'.hC (b6t_polydisc c') (Subset.refl _) t' :=
    b65y_saturation_equiv (b63l_fibreOperator c D.C D.hC t)
    (b63l_fibreOperator c' D'.C D'.hC t') E (by exact hcomm)
  refine ⟨f, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change E (D.A t x).val = (D'.A t' (f x)).val
    rw [D.hA, D'.hA]
    change E (b63d_operator c D.C D.hC _ _ t x.val) =
      b63d_operator c' D'.C D'.hC _ _ t' (E x.val)
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_add, map_nsmul]
    congr 1
    congr 1
    simp only [b63d_centre, LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs
    · exact b65y_homology_equivariant hX hY e eqv a x.val
    · exact map_zero E
  · intro x y
    exact b6m_intersection_biholomorphic e hol inv_hol (D.P t) (D.hP t)
      (D'.P t') (D'.hP t') (D.Q t) (D.hQ t) (D'.Q t') (D'.hQ t') x.val y.val

set_option maxHeartbeats 400000 in
theorem b65y_chart_transport {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (s t : b6t_polydisc c) :
    ∃ f : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s ≃ₗ[ℤ]
      b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) t,
      (∀ x, f (D.A s x) = D.A t (f x)) ∧
      ∀ x y, b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) t
        (D.P t) (D.Q t) (f x) (f y) =
      b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) s (D.P s) (D.Q s) x y := by
  obtain ⟨-, T, hT, -⟩ := b63l_fibre_image_transport c D.C D.hC s t
  refine ⟨T, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    rw [hT, D.hA, D.hA, hT]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
      map_add, map_nsmul]
    rw [b63d_centre_transport c D.C D.hC (b6t_polydisc c) (Subset.refl _) t s x.val]
  · intro x y
    change D.Q t (D.P t (T x).val) (D.P t (T y).val) = D.Q s (D.P s x.val) (D.P s y.val)
    rw [hT, hT]
    exact b63e_pairing_constant c D.C (b6t_polydisc c) (Subset.refl _)
      D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP s t x.val y.val

set_option maxHeartbeats 400000 in
theorem b65y_edge_transport (H : b65y_HurwitzChain) (i : Fin H.n) :
    ∃ f : b65y_lattice (H.chart i.castSucc) ≃ₗ[ℤ] b65y_lattice (H.chart i.succ),
      (∀ x, f ((H.chart i.castSucc).2.2.A (b65z_s₀ (H.chart i.castSucc).1) x) =
        (H.chart i.succ).2.2.A (b65z_s₀ (H.chart i.succ).1) (f x)) ∧
      ∀ x y, b65y_pairing (H.chart i.succ) (f x) (f y) =
        b65y_pairing (H.chart i.castSucc) x y := by
  let s := (⟨(H.overlap i).val, (H.overlap i).property.1⟩ : b6t_polydisc (H.chart i.castSucc).1)
  let t := (⟨(H.overlap i).val, (H.overlap i).property.2⟩ : b6t_polydisc (H.chart i.succ).1)
  obtain ⟨a, ha, hEa⟩ := b65y_chart_transport (H.chart i.castSucc).2.2
    (b65z_s₀ (H.chart i.castSucc).1) s
  obtain ⟨b, hb, hEb⟩ := b65y_overlap_transport (H.chart i.castSucc).2.2
    (H.chart i.succ).2.2 s t (H.glue i) (H.hol i) (H.inv_hol i) (H.equivariant i)
  obtain ⟨d, hd, hEd⟩ := b65y_chart_transport (H.chart i.succ).2.2 t
    (b65z_s₀ (H.chart i.succ).1)
  refine ⟨(a.trans b).trans d, ?_, ?_⟩
  · intro x
    simp only [LinearEquiv.trans_apply]
    rw [ha, hb, hd]
  · intro x y
    simp only [LinearEquiv.trans_apply]
    exact (hEd _ _).trans ((hEb _ _).trans (hEa x y))

end HodgeLean.Foundations.Program
