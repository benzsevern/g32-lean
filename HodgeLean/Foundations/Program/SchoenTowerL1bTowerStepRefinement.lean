import HodgeLean.Foundations.Program.SchoenTowerL1bAffineGeneratorRefinement
import HodgeLean.Foundations.Program.SchoenTowerL1bStrictTransformChart

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An affine open disjoint from an actual ideal support has the unit ideal. -/
theorem s2v_l1b_ideal_top_of_support_disjoint {X : Scheme}
    (I : X.IdealSheafData) (U : X.affineOpens)
    (h : ∀ x ∈ U.1, x ∉ I.support) : I.ideal U = ⊤ := by
  have hi := U.2.fromSpec_image_zeroLocus (I.ideal U)
  rw [← I.coe_support_inter] at hi
  have hs : U.2.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U)) ⊆ ∅ := by
    rw [hi]
    intro x hx
    exact (h x hx.2 hx.1).elim
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    (Set.image_eq_empty.mp (Set.subset_empty_iff.mp hs))

/-- One affine refinement removes every member of a finite family absent at a
specified point, while retaining that point and a prescribed neighborhood. -/
theorem s2v_l1b_finite_branch_avoidance {X : Scheme} {J : Type*} [Fintype J]
    (D : J → X.IdealSheafData) (x : X) (U : X.Opens) (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U ∧
      ∀ t, x ∉ (D t).support → (D t).ideal V = ⊤ := by
  classical
  let O : X.Opens := U ⊓ ⨅ t : {t : J // x ∉ (D t).support},
    ⟨((D t.val).support : Set X)ᶜ, (D t.val).support.isClosed.isOpen_compl⟩
  have hxO : x ∈ O := by
    refine ⟨hx, ?_⟩
    simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro t
    exact t.property
  obtain ⟨V, hV, hxV, hVO⟩ := exists_isAffineOpen_mem_and_subset hxO
  refine ⟨⟨V, hV⟩, hxV, fun y hy => (hVO hy).1, ?_⟩
  intro t ht
  apply s2v_l1b_ideal_top_of_support_disjoint
  intro y hy
  have hmem := (hVO hy).2
  rw [TopologicalSpace.Opens.coe_iInf] at hmem
  have := (Set.mem_iInter.mp hmem) ⟨t, ht⟩
  exact this

/-- The unit ideal on an affine neighborhood excludes its points from support. -/
theorem s2v_l1b_not_mem_support_of_ideal_top {X : Scheme}
    (I : X.IdealSheafData) (U : X.affineOpens) (hI : I.ideal U = ⊤)
    (x : X) (hx : x ∈ U.1) : x ∉ I.support := by
  have hi := U.2.fromSpec_image_zeroLocus (I.ideal U)
  rw [← I.coe_support_inter, hI, PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl,
    Set.image_empty] at hi
  intro hs
  have : x ∈ (∅ : Set X) := hi.symm ▸ (show x ∈ (I.support : Set X) ∩ U.1 from ⟨hs, hx⟩)
  exact this

/-- A finite family already expressed in distinct etale coordinates can be
restricted to exactly the branches through the chosen point. -/
theorem s2v_l1b_refine_supported_coordinates
    (X : Over (Spec ↧ℂ)) {J σ : Type} [Fintype J]
    (D : J → X.left.IdealSheafData) (Q : J → Prop)
    (U : X.left.affineOpens) (z : σ → Γ(X.left, U))
    (f : {t // Q t} ↪ σ)
    (het : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ U.1 le_top).hom z).Etale)
    (hD : ∀ t, (D t.val).ideal U = Ideal.span {z (f t)})
    (habs : ∀ t, ¬ Q t → (D t).ideal U = ⊤)
    (x : ComplexPoint X) (hx : x.underlying ∈ U.1) :
    ∃ (V : X.left.affineOpens) (w : σ → Γ(X.left, V))
      (g : {t // x.underlying ∈ (D t).support} ↪ σ),
      x.underlying ∈ V.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom w).Etale ∧
      (∀ t, (D t.val).ideal V = Ideal.span {w (g t)}) ∧
      (∀ t, x.underlying ∉ (D t).support → (D t).ideal V = ⊤) := by
  classical
  have hQ (t : J) (ht : x.underlying ∈ (D t).support) : Q t := by
    by_contra hn
    exact s2v_l1b_not_mem_support_of_ideal_top (D t) U (habs t hn) _ hx ht
  let g : {t // x.underlying ∈ (D t).support} ↪ σ :=
    { toFun := fun t => f ⟨t.val, hQ t.val t.property⟩
      inj' := by
        intro t u he
        exact Subtype.ext (congrArg (fun t : {t // Q t} => t.val) (f.injective he)) }
  obtain ⟨V, hxV, hVU, hunit⟩ := s2v_l1b_finite_branch_avoidance D x.underlying U.1 hx
  let w : σ → Γ(X.left, V) := fun i =>
    (X.left.presheaf.map (homOfLE hVU).op).hom (z i)
  refine ⟨V, w, g, hxV,
    s2v_l1b_affine_coordinate_restriction X U V hVU z het, ?_, hunit⟩
  intro t
  rw [← (D t.val).map_ideal hVU, hD ⟨t.val, hQ t.val t.property⟩,
    Ideal.map_span, Set.image_singleton]
  rfl

end HodgeLean.Foundations.Program
