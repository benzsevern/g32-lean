import HodgeLean.Adapters.ChowCorrespondenceDefs
import HodgeLean.Adapters.CycleClassPullbackSpan
import HodgeLean.Foundations.ChowCorrespondenceAffineLine
import HodgeLean.Foundations.ChowCorrespondencePushforward
import HodgeLean.Foundations.ChowCorrespondenceGraph

/-! # Proof obligations for rational equivalence, Chow groups and graph correspondences -/

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial HodgeLean.Foundations.Curves
open HodgeLean.RealDefs
open scoped MonoidalCategory

namespace HodgeLean.Adapters

universe u

theorem a2_ratEquivDim_le_dimCycles_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (R : Type*) [Ring R] (k : ℕ) :
    a2_ratEquivDim X.left R k ≤ a2_dimCycles X.left R k :=
  a2r_ratEquivDim_le_dimCycles X R k

theorem a2_pushforward_ratEquiv_aux {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    [IsProper f.left] (R : Type*) [Ring R] (k : ℕ) (c : AlgebraicCycle X.left R)
    (hc : c ∈ a2_ratEquivDim X.left R k) :
    a1p_pushforward f.left c ∈ a2_ratEquivDim Y.left R k :=
  a2r_pushforward_ratEquiv f R k c hc

theorem a2_ratEquivDim_point_aux (R : Type*) [Ring R] (k : ℕ) :
    a2_ratEquivDim (Spec ↧ℂ) R k = ⊥ :=
  a2r_ratEquivDim_point R k

theorem a2_degree_ratEquiv_aux (X : Over (Spec ↧ℂ)) [IsProper X.hom] (R : Type*) [CommRing R]
    (c : AlgebraicCycle X.left R)
    (hc : c ∈ a2_ratEquivDim X.left R 0) :
    AlgebraicCycle.degree X.hom c = 0 := by
  let P : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
  let f : X ⟶ P := Over.homMk X.hom (by simp [P])
  have : IsProper f.left := inferInstanceAs (IsProper X.hom)
  have : LocallyOfFiniteType P.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  have : QuasiCompact P.hom := inferInstanceAs (QuasiCompact (𝟙 _))
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have h := a2_pushforward_ratEquiv_aux f R 0 c hc
  change a1p_pushforward X.hom c ∈ a2_ratEquivDim (Spec ↧ℂ) R 0 at h
  rw [a2r_ratEquivDim_point, AddSubgroup.mem_bot] at h
  obtain ⟨p⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [a2r_degree_eq_pushforward X.hom c p, h]
  rfl

theorem a2_affineLineOrigin_mem_ratEquivDim_aux [DecidableEq a1p_affineLine.left] :
    Function.locallyFinsuppWithin.single a2_affineLineOrigin (1 : ℤ) ∈
      a2_ratEquivDim a1p_affineLine.left ℤ 0 :=
  a2r_affineLineOrigin_mem_ratEquivDim

/-- The proper pushforward of the frozen spec, `a2_chowPushforward f R k`, unfolds to
`a2_chowMap (a2_pushforwardHom f.left R) (a2_pushforward_mem_dimCycles f R k) _`; the
obligations below are stated in that unfolded form. -/
theorem a2_chowPushforward_mk_aux {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    [IsProper f.left] (R : Type*) [Ring R] (k : ℕ) (c : AlgebraicCycle X.left R)
    (hc : c ∈ a2_dimCycles X.left R k) :
    a2_chowMap (a2_pushforwardHom f.left R) (a2_pushforward_mem_dimCycles f R k)
        (a2_pushforward_ratEquiv_aux f R k) (a2_chowMk X.left c hc) =
      a2_chowMk Y.left (a1p_pushforward f.left c) (a2_pushforward_mem_dimCycles f R k c hc) := by
  rfl

theorem a2_chowPushforward_id_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (R : Type*) [Ring R] (k : ℕ) :
    a2_chowMap (a2_pushforwardHom (𝟙 X : X ⟶ X).left R) (a2_pushforward_mem_dimCycles (𝟙 X) R k)
        (a2_pushforward_ratEquiv_aux (𝟙 X) R k) = AddMonoidHom.id _ := by
  ext c
  change (QuotientAddGroup.mk _ : a2_Chow X.left R k) = QuotientAddGroup.mk _
  congr 1
  exact Subtype.ext (a1p_pushforward_id (X := X.left) c.1)

theorem a2_chowPushforward_comp_aux {X Y Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (R : Type*) [Ring R] (k : ℕ) :
    a2_chowMap (a2_pushforwardHom (f ≫ g).left R) (a2_pushforward_mem_dimCycles (f ≫ g) R k)
        (a2_pushforward_ratEquiv_aux (f ≫ g) R k) =
      (a2_chowMap (a2_pushforwardHom g.left R) (a2_pushforward_mem_dimCycles g R k)
          (a2_pushforward_ratEquiv_aux g R k)).comp
        (a2_chowMap (a2_pushforwardHom f.left R) (a2_pushforward_mem_dimCycles f R k)
          (a2_pushforward_ratEquiv_aux f R k)) := by
  ext c
  change (QuotientAddGroup.mk _ : a2_Chow Z.left R k) = QuotientAddGroup.mk _
  congr 1
  exact Subtype.ext (a1p_pushforward_comp f.left g.left c.1)

theorem a2_transpose_transpose_aux {X Y : Over (Spec ↧ℂ)} (Γ : a2_Corr X Y) :
    a2_transpose (a2_transpose Γ) = Γ := by
  unfold a2_transpose
  rw [← a1p_pushforward_comp]
  have h : (a2_swap X Y).left ≫ (a2_swap Y X).left = 𝟙 _ := by
    rw [← Over.comp_left, a2_swap_swap]; rfl
  simp only [h]
  exact a1p_pushforward_id Γ

theorem a2_naiveCorrAction_graph_aux {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] [IsSeparated Y.hom] (f : X ⟶ Y)
    (α : AlgebraicCycle X.left ℚ) :
    a2_naiveCorrAction (a2_graphCorr f) α = a1p_pushforward f.left α := by
  change a1p_pushforward (a2g_snd X Y) (a2_naiveIntersect (gagam_product X Y).left
    (a2_graphCorr f) (ccm3_flatPullback (a2g_fst X Y) α)) = _
  rw [a2g_naiveIntersect_graph, ← a1p_pushforward_comp]
  exact a2g_pushforward_congr (a2g_graph_snd f) α

theorem a2_naiveCorrAction_transpose_graph_aux {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] [IsSeparated Y.hom] (f : X ⟶ Y)
    (β : AlgebraicCycle Y.left ℚ) :
    a2_naiveCorrAction (a2_transpose (a2_graphCorr f)) β = ccm3_flatPullback f.left β := by
  change a1p_pushforward (a2g_snd Y X) (a2_naiveIntersect (gagam_product Y X).left
    (a2_transpose (a2_graphCorr f)) (ccm3_flatPullback (a2g_fst Y X) β)) = _
  exact a2g_naiveCorrAction_transpose_graph f β

theorem a2_naiveCorrComp_graph_aux {X Y Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsIntegral X.left] [IsIntegral Y.left]
    [IsIntegral Z.left] [IsSeparated Y.hom] [IsSeparated Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) :
    a2_naiveCorrComp (a2_graphCorr f) (a2_graphCorr g) = a2_graphCorr (f ≫ g) := by
  change a1p_pushforward (a2_p13 X Y Z).left (a2_naiveIntersect _
    (ccm3_flatPullback (a2g_fst (gagam_product X Y) Z) (a2_graphCorr f))
    (ccm3_flatPullback (a2_p23 X Y Z).left (a2_graphCorr g))) = _
  exact a2g_naiveCorrComp_graph f g

theorem a2_naiveCorrAction_naiveCorrComp_graph_aux {X Y Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsIntegral X.left] [IsIntegral Y.left]
    [IsIntegral Z.left] [IsSeparated Y.hom] [IsSeparated Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    (α : AlgebraicCycle X.left ℚ) :
    a2_naiveCorrAction (a2_naiveCorrComp (a2_graphCorr f) (a2_graphCorr g)) α =
      a2_naiveCorrAction (a2_graphCorr g) (a2_naiveCorrAction (a2_graphCorr f) α) := by
  rw [a2_naiveCorrComp_graph_aux, a2_naiveCorrAction_graph_aux, a2_naiveCorrAction_graph_aux,
    a2_naiveCorrAction_graph_aux, Over.comp_left, a1p_pushforward_comp]

theorem a2_cycleClass_transpose_graph_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (c : AlgebraicCycle Z.left ℚ)
    (hc : ∀ x : Z.left, c x ≠ 0 → Order.coheight x = q) :
    homPullback f (2 * q) (ccm3_cycleClass Z q c) =
      ccm3_cycleClass X q (a2_naiveCorrAction (a2_transpose (a2_graphCorr f)) c) := by
  rw [a2_naiveCorrAction_transpose_graph_aux]
  exact ccm6_homPullback_cycleClass f q c hc

end HodgeLean.Adapters
