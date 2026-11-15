import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupFramedComparison
import HodgeLean.Foundations.Program.G32Native.UnionConormalIsoPullbackEquivalence
import HodgeLean.Foundations.AlgebraicGeometry.ConormalLocalIsomorphism

/-! # Gluing the finite-rank natural conormal comparison -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An epic morphism between two finite free sheaves of the same rank on
an affine scheme is invertible, including over a nonreduced ring.
Source: Orzech, Onto endomorphisms are isomorphisms, American Mathematical
Monthly 78 (1971), 357–362. -/
theorem paired_affine_sheaf_epi_isIso
    (A : CommRingCat) {M N : (Spec A).Modules} (a : M ⟶ N) [Epi a] (k : ℕ)
    (eM : M ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin k) :
      (Spec A).Modules))
    (eN : N ≅ (SheafOfModules.free (R := (Spec A).ringCatSheaf) (Fin k) :
      (Spec A).Modules)) : IsIso a := by
  let F := ModuleCat.of A (Fin k →₀ A)
  let bM : tilde F ≅ M := tildeFinsupp (R := A) (Fin k) ≪≫ eM.symm
  let bN : tilde F ≅ N := tildeFinsupp (R := A) (Fin k) ≪≫ eN.symm
  let b := bM.hom ≫ a ≫ bN.inv
  let u := (tilde.functor A).preimage b
  have hu : (tilde.functor A).map u = b := (tilde.functor A).map_preimage b
  haveI : Epi ((tilde.functor A).map u) := by
    rw [hu]
    dsimp only [b]
    infer_instance
  haveI := paired_affine_framed_epi_isIso A F F u k
    (tildeFinsupp (R := A) (Fin k)) (tildeFinsupp (R := A) (Fin k))
  haveI : IsIso b := by rw [← hu]; infer_instance
  have ha : a = bM.inv ≫ b ≫ bN.hom := by
    simp only [b, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [ha]
  infer_instance

/-- Local affine frames of equal finite rank turn an epic sheaf map into
an isomorphism. The rank may vary between neighborhoods.
Source: Hartshorne, Algebraic Geometry, II.5, local freeness and stalkwise
criteria for isomorphisms. -/
theorem paired_locally_framed_epi_isIso
    {X : Scheme.{0}} {M N : X.Modules} (a : M ⟶ N) [Epi a]
    (h : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ IsAffine U.toScheme ∧
      ∃ k : ℕ,
        Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    IsIso a := by
  apply Conormal.moduleMap_isIso_of_open_neighborhoods a
  intro x
  obtain ⟨U, hx, hU, k, ⟨eM⟩, ⟨eN⟩⟩ := h x
  letI : IsAffine U.toScheme := hU
  let b := U.toScheme.isoSpec.inv
  let G := Scheme.Modules.pullback b
  letI : G.IsEquivalence := unionConormal_isoPullback_isEquivalence b
  letI : (SheafOfModules.pushforward.{0} b.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward b).IsRightAdjoint
  let e := SheafOfModules.pullbackObjFreeIso b.toRingCatSheafHom (Fin k)
  haveI : IsIso (G.map ((Scheme.Modules.pullback U.ι).map a)) :=
    paired_affine_sheaf_epi_isIso Γ(U.toScheme, ⊤)
      (G.map ((Scheme.Modules.pullback U.ι).map a)) k
      (G.mapIso eM ≪≫ e) (G.mapIso eN ≪≫ e)
  exact ⟨U, hx, isIso_of_reflects_iso _ G⟩

/-- For a cartesian square of closed immersions, equal local affine ranks
suffice for the natural conormal comparison, without ambient flatness.
The local frames must be established on the actual total transform.
Source: Hartshorne, Algebraic Geometry, II.8, conormal of a regular immersion. -/
theorem paired_conormal_comparison_of_local_frames
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : CategoryTheory.IsPullback g i' i f)
    (h : ∀ x : Q', ∃ (U : Q'.Opens), x ∈ U ∧ IsAffine U.toScheme ∧
      ∃ k : ℕ,
        Nonempty ((Scheme.Modules.pullback U.ι).obj
          ((Scheme.Modules.pullback g).obj (Conormal.sheaf i)) ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj (Conormal.sheaf i') ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules))) :
    IsIso (Conormal.comparisonMap i i' f g sq.w) := by
  haveI := unionConormal_comparison_epi_of_isPullback i i' f g sq
  exact paired_locally_framed_epi_isIso _ h

#print axioms paired_affine_sheaf_epi_isIso
#print axioms paired_locally_framed_epi_isIso
#print axioms paired_conormal_comparison_of_local_frames
end HodgeLean.Foundations.Program.G32Native
