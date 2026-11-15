import HodgeLean.Foundations.Program.G32Native.UnionConormalSquarePullback

/-! # Monicity transport for the natural conormal prefix -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- A natural isomorphism transports monicity of a functor's image map. -/
lemma unionConormal_mono_map_of_natIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {M N : C} (f : M ⟶ N) [Mono (F.map f)] : Mono (G.map f) := by
  have he : G.map f = e.inv.app M ≫ F.map f ≫ e.hom.app N := by
    rw [e.hom.naturality f, Iso.inv_hom_id_app_assoc]
  rw [he]
  infer_instance

/-- Equality of the square maps transports the natural ideal comparison. -/
lemma unionConormal_idealMap_congr_transport
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    {f f' : W' ⟶ W} {g g' : Q' ⟶ Q} (hf : f = f') (hg : g = g')
    (h : g ≫ i = i' ≫ f) (h' : g' ≫ i = i' ≫ f') :
    (Scheme.Modules.pullbackCongr hf).hom.app (idealModule i) ≫
      idealPullbackMap i i' f' g' h' = idealPullbackMap i i' f g h := by
  subst f'
  subst g'
  rw [← Iso.app_hom, unionConormal_pullbackCongr_hom_app]
  simp only [eqToHom_refl, Category.id_comp]

/-- The invertible conormal prefix does not change monicity of the pulled ideal map. -/
lemma unionConormal_comparison_mono_iff
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    Mono (comparisonMap i i' f g h) ↔
      Mono ((Scheme.Modules.pullback i').map (idealPullbackMap i i' f g h)) := by
  let e := unionConormalComparisonPrefixIso i i' f g h
  constructor
  · intro hm
    haveI := hm
    have he : (Scheme.Modules.pullback i').map (idealPullbackMap i i' f g h) =
        e.inv ≫ comparisonMap i i' f g h := by
      rw [unionConormal_comparisonMap_eq_prefix]
      exact (Iso.inv_hom_id_assoc e _).symm
    rw [he]
    infer_instance
  · intro hm
    haveI := hm
    rw [unionConormal_comparisonMap_eq_prefix]
    infer_instance

/-- Equality of ambient maps retains monicity of their natural comparisons. -/
lemma unionConormal_comparison_mono_congr
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    {f f' : W' ⟶ W} (hf : f = f') (g : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (h' : g ≫ i = i' ≫ f')
    (hm : Mono (comparisonMap i i' f g h)) : Mono (comparisonMap i i' f' g h') := by
  subst f'
  exact hm

/-- Monicity after iterated pullback can be tested on either side of a commuting square. -/
lemma unionConormal_mono_pullback_square
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f)
    {M N : W.Modules} (u : M ⟶ N)
    [Mono ((Scheme.Modules.pullback i').map ((Scheme.Modules.pullback f).map u))] :
    Mono ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback i).map u)) := by
  haveI : Mono ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback i').map u) :=
    inferInstanceAs (Mono ((Scheme.Modules.pullback i').map ((Scheme.Modules.pullback f).map u)))
  exact unionConormal_mono_map_of_natIso
    (unionConormalSquarePullbackIso i i' f g h).symm u

#print axioms unionConormal_comparison_mono_iff
#print axioms unionConormal_mono_pullback_square
end HodgeLean.Foundations.Program.G32Native
